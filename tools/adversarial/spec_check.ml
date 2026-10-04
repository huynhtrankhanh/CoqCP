(* Independent acceptance gate. This links coqchk's loader and kernel, never
   the vernacular interpreter, notation tables, or candidate ML plugins. *)
open Names
open Declarations
module Check = Coq_checklib.Check

let fail message = failwith message
let dirpath name =
  DirPath.make (List.rev_map Id.of_string (String.split_on_char '.' name))
let file_path name = ModPath.MPfile (dirpath name)
let field_path file field = ModPath.MPdot (file_path file, Label.of_id (Id.of_string field))

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
     not flags.check_universes || flags.impredicative_set || flags.allow_uip then
    fail ("Unsafe typing flags: " ^ name)

let audit env opac allowed =
  if Environ.is_impredicative_set env || Environ.type_in_type env ||
     Environ.deactivated_guard env || Environ.rewrite_rules_allowed env then
    fail "Unsafe global theory settings";
  let axioms = Environ.fold_constants (fun constant body acc ->
    safe_flags (Constant.to_string constant) body.const_typing_flags;
    if Declareops.constant_has_body body then acc else
      match Cmap.find_opt constant opac with
      | None -> Cset.add constant acc
      | Some dependencies -> Cset.union dependencies acc) env Cset.empty in
  Environ.fold_inductives (fun name body () ->
    safe_flags (MutInd.to_string name) body.mind_typing_flags) env ();
  (* Global folds omit bodies of unapplied functors. Audit their stored
     implementations too. Parameters of signatures/functor arguments are
     requirements, not global axioms; sealed modules' actual bodies are
     available in Struct, and opac tracks their hidden dependencies. *)
  let axioms = ref axioms in
  let rec signature check_axioms mp = function
    | NoFunctor fields -> structure check_axioms mp fields
    | MoreFunctor (id, argument, body) ->
      signature false (ModPath.MPbound id) argument.mod_type;
      signature check_axioms mp body
  and structure check_axioms mp fields =
    List.iter (fun (label, field) -> match field with
    | SFBconst body ->
      let constant = Constant.make2 mp label in
      safe_flags (Constant.to_string constant) body.const_typing_flags;
      if check_axioms && not (Declareops.constant_has_body body) then
        axioms := (match Cmap.find_opt constant opac with
          | None -> Cset.add constant !axioms
          | Some dependencies -> Cset.union dependencies !axioms)
    | SFBmind body -> safe_flags (ModPath.to_string mp ^ "." ^ Label.to_string label)
        body.mind_typing_flags
    | SFBmodule body -> implementation check_axioms body
    | SFBmodtype body -> signature false body.mod_mp body.mod_type
    | SFBrules _ -> fail "Rewrite rules are not permitted") fields
  and implementation check_axioms body =
    match body.mod_expr with
    | FullStruct | Abstract -> signature check_axioms body.mod_mp body.mod_type
    | Struct fields ->
      signature false body.mod_mp body.mod_type;
      structure check_axioms body.mod_mp fields
    | Algebraic _ -> signature false body.mod_mp body.mod_type
  in
  let globals = Environ.Globals.view env.Environ.env_globals in
  MPmap.iter (fun _ body -> implementation true body) globals.modules;
  MPmap.iter (fun _ body -> signature false body.mod_mp body.mod_type) globals.modtypes;
  let names = Cset.fold (fun constant acc -> Constant.to_string constant :: acc) !axioms [] in
  List.iter (fun name ->
    if not (List.mem name allowed) then fail ("Unapproved axiom: " ^ name)) names;
  List.sort String.compare names

let () =
  try
    if Coq_config.version <> "8.20.1" then fail "This checker requires Coq 8.20.1";
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
    CWarnings.set_flags ("+" ^ Typeops.warn_bad_relevance_name);
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
    (match specification.mod_type with
    | NoFunctor fields ->
      List.iter (fun required ->
        if not (List.exists (fun (label, field) ->
          Label.to_string label = required &&
          match field with SFBconst _ -> true | _ -> false) fields)
        then fail ("SOLUTION must contain a " ^ required ^ " field")) ["program"; "correct"]
    | MoreFunctor _ -> fail "SOLUTION must be a concrete module signature");
    let axioms = audit env opac !allowed in
    if not !freeze then begin
      let candidate = Environ.lookup_module
        (field_path "Submission.Candidate" "Implementation") env in
      (match candidate.mod_type with
      | MoreFunctor _ -> fail "Implementation must not be an unapplied functor"
      | NoFunctor _ -> ());
      let actual = Modops.module_type_of_module candidate in
      (try ignore (Subtyping.check_subtypes
         (Environ.universes env, Conversion.checked_universes)
         env actual specification)
       with Modops.ModuleTypingError (Modops.SignatureMismatch (_, label, _)) ->
         fail ("Signature mismatch for field " ^ Label.to_string label)
       | Modops.ModuleTypingError _ -> fail "Implementation does not satisfy Trusted.Spec.SOLUTION")
    end;
    Printf.printf "{\"status\":%s,\"coq_version\":%s,\"axioms\":[%s]}\n%!"
      (json_string (if !freeze then "spec-checked" else "accepted"))
      (json_string Coq_config.version)
      (String.concat "," (List.map json_string axioms))
  with error ->
    Format.eprintf "Acceptance rejected: %a\n%!" Pp.pp_with (CErrors.print error);
    exit 1
