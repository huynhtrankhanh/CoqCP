(* Independent acceptance gate. This links rocq check's loader and kernel, never
   the vernacular interpreter, notation tables, or candidate ML plugins. *)
open Names
open Declarations
open Mod_declarations
module Check = Coq_checklib.CheckLibrary

let fail message = failwith message
let dirpath name =
  DirPath.make (List.rev_map Id.of_string (String.split_on_char '.' name))
let file_path name = ModPath.MPfile (dirpath name)
let field_path file field = ModPath.MPdot (file_path file, Id.of_string field)

let rec add_path physical logical =
  Check.add_load_path (physical, logical);
  Array.iter (fun name ->
    let path = Filename.concat physical name in
    if name <> "" && name.[0] <> '.' && Sys.is_directory path then
      try add_path path (DirPath.make (Id.of_string name :: DirPath.repr logical))
      with CErrors.UserError _ -> ()) (Sys.readdir physical)

let json_string value =
  let b = Buffer.create (String.length value + 2) in
  Buffer.add_char b '"';
  String.iter (function
    | '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | c when Char.code c < 32 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char b c) value;
  Buffer.add_char b '"'; Buffer.contents b

let safe_flags name flags =
  if not flags.check_guarded || not flags.check_positive ||
     not flags.check_universes || not flags.check_eliminations ||
     flags.impredicative_set || flags.allow_uip then
    fail ("Unsafe typing flags: " ^ name)

let safe_inductive name body =
  safe_flags name body.mind_typing_flags;
  if Array.exists (fun packet -> packet.mind_relies_on_indices_not_mattering) body.mind_packets &&
     not (List.mem name Ci_policy.indices_not_mattering) then
    fail ("Inductive outside CI policy for indices not mattering: " ^ name)

let audit env opac allowed =
  if Environ.is_impredicative_set env || Environ.type_in_type env ||
     Environ.deactivated_guard env || Environ.rewrite_rules_allowed env ||
     not (Environ.typing_flags env).check_eliminations then
    fail "Unsafe global theory settings";
  Environ.fold_constants (fun constant body () ->
    safe_flags (Constant.to_string constant) body.const_typing_flags;
    ()) env ();
  Environ.fold_inductives (fun name body () ->
    safe_inductive (MutInd.to_string name) body) env ();
  (* Global folds omit bodies of unapplied functors. Audit their stored
     implementations too. Parameters of signatures/functor arguments are
     requirements, not global axioms; sealed modules' actual bodies are
     available in Struct, and opac tracks their hidden dependencies. *)
  let opaque_axioms = Coq_checklib.Mod_checking.constants_of_opaques env opac in
  let axioms = ref (List.fold_left (fun acc constant -> Cset_env.add constant acc) Cset_env.empty opaque_axioms) in
  let rec signature check_axioms mp = function
    | NoFunctor fields -> structure check_axioms mp fields
    | MoreFunctor (id, argument, body) ->
      signature false (ModPath.MPbound id) (Mod_declarations.mod_type argument);
      signature check_axioms mp body
  and structure check_axioms mp fields =
    List.iter (fun (label, field) -> match field with
    | SFBconst body ->
      let constant = Constant.make2 mp label in
      safe_flags (Constant.to_string constant) body.const_typing_flags;
      if check_axioms && not (Declareops.constant_has_body body) &&
         (match Environ.lookup_constant_opt constant env with None -> true | Some _ -> false) then begin
        (* The checker keeps sealed-body dependencies in an abstract table.
           Extend a temporary environment to query that table for constants
           in unapplied functor bodies, which global folds do not include. *)
        let local = Environ.add_constant constant body env in
        let dependencies = Coq_checklib.Mod_checking.constants_of_opaques local opac in
        List.iter (fun dependency -> axioms := Cset_env.add dependency !axioms) dependencies
      end
    | SFBmind body -> safe_inductive (ModPath.to_string mp ^ "." ^ Id.to_string label) body
    | SFBmodule body -> implementation check_axioms (ModPath.MPdot (mp, label)) body
    | SFBmodtype body -> signature false (ModPath.MPdot (mp, label)) (Mod_declarations.mod_type body)
    | SFBrules _ -> fail "Rewrite rules are not permitted") fields
  and implementation check_axioms mp body =
    match Mod_declarations.mod_expr body with
    | FullStruct | Abstract -> signature check_axioms mp (Mod_declarations.mod_type body)
    | Struct (_, fields) ->
      signature false mp (Mod_declarations.mod_type body);
      structure check_axioms mp fields
    | Algebraic _ -> signature false mp (Mod_declarations.mod_type body)
  in
  let globals = Environ.Internal.View.view env in
  ModPath.Map.iter (fun mp body -> implementation true mp body) globals.env_modules;
  ModPath.Map.iter (fun mp body -> signature false mp (Mod_declarations.mod_type body)) globals.env_modtypes;
  let names = Cset_env.fold (fun constant acc -> Constant.to_string constant :: acc) !axioms [] in
  List.iter (fun name ->
    if not (List.mem name allowed) then fail ("Unapproved axiom: " ^ name)) names;
  List.sort String.compare names

let () =
  try
    if Coq_config.version <> "9.3.0" then fail "This checker requires Rocq 9.3.0";
    let roots = ref [] and allowed = ref [] and libraries = ref [] in
    let freeze = ref false in
    let rec args = function
      | [] -> ()
      | "--root" :: physical :: logical :: rest ->
        roots := (physical, logical) :: !roots; args rest
      | "--allow-axiom" :: name :: rest -> allowed := name :: !allowed; args rest
      | "--library" :: name :: rest -> libraries := name :: !libraries; args rest
      | "--spec-only" :: rest -> freeze := true; args rest
      | _ -> fail "Invalid checker arguments"
    in
    args (List.tl (Array.to_list Sys.argv));
    List.iter (fun name ->
      if not (List.mem name Ci_policy.allowed_axioms) then
        fail ("Axiom is outside the compiled CI trust policy: " ^ name)) !allowed;
    Flags.quiet := true;
    ignore (Feedback.add_feeder (Feedback.console_feedback_listener Format.err_formatter));
    List.iter (fun (physical, logical) ->
      add_path physical (if logical = "" then DirPath.empty else dirpath logical))
      (List.rev !roots);
    let logical_file name =
      match List.rev (String.split_on_char '.' name) with
      | basename :: reversed_dir ->
        Check.LogicalFile { Check.basename; dirpath = reversed_dir }
      | [] -> fail "Empty library name"
    in
    let check = "Trusted.Spec" ::
      (if !freeze then [] else "Submission.Candidate" :: !libraries) in
    let senv = Safe_typing.empty_environment
      |> Safe_typing.set_impredicative_set false |> Safe_typing.set_indices_matter false
      |> Safe_typing.set_VM false |> Safe_typing.set_native_compiler false
      |> Safe_typing.set_allow_sprop true in
    let senv, opac = Check.recheck_library senv ~norec:[] ~admit:[]
      ~check:(List.map logical_file check) in
    let env = Safe_typing.env_of_safe_env senv in
    let specification = Environ.lookup_modtype (field_path "Trusted.Spec" "SOLUTION") env in
    (match (Mod_declarations.mod_type specification) with
    | NoFunctor fields ->
      List.iter (fun required ->
        if not (List.exists (fun (label, field) ->
          Id.to_string label = required &&
          match field with SFBconst _ -> true | _ -> false) fields)
        then fail ("SOLUTION must contain a " ^ required ^ " field")) ["program"; "correct"]
    | MoreFunctor _ -> fail "SOLUTION must be a concrete module signature");
    let axioms = audit env opac !allowed in
    if not !freeze then begin
      let candidate = Environ.lookup_module
        (field_path "Submission.Candidate" "Implementation") env in
      (match (Mod_declarations.mod_type candidate) with
      | MoreFunctor _ -> fail "Implementation must not be an unapplied functor"
      | NoFunctor _ -> ());
      (try ignore (Subtyping.check_subtypes
         (Environ.universes env, Conversion.checked_universes)
         env (field_path "Submission.Candidate" "Implementation")
         (field_path "Trusted.Spec" "SOLUTION") specification)
       with Modops.ModuleTypingError (Modops.SignatureMismatch (_, label, _)) ->
         fail ("Signature mismatch for field " ^ Id.to_string label)
       | Modops.ModuleTypingError _ -> fail "Implementation does not satisfy Trusted.Spec.SOLUTION")
    end;
    Printf.printf "{\"status\":%s,\"rocq_version\":%s,\"axioms\":[%s]}\n%!"
      (json_string (if !freeze then "spec-checked" else "accepted"))
      (json_string Coq_config.version)
      (String.concat "," (List.map json_string axioms))
  with error ->
    Format.eprintf "Acceptance rejected: %a\n%!" Pp.pp_with (CErrors.print error);
    exit 1
