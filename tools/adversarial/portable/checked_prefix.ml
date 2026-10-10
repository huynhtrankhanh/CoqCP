(* This is inserted into the pinned CheckLibrary module only in the WASI build.
   Certificates come from evaluator-owned storage, never submitted .vo files.
   Every hit reconstructs VM code and later undergoes the ordinary policy audit. *)
let checked_prefix = ref None
exception Checked_prefix
let prefix_deadline = ref infinity

let set_checked_prefix input output seed seconds =
  checked_prefix := Some (input, output, ref (Digest.BLAKE256.string seed));
  prefix_deadline := Sys.time () +. float_of_string seconds

let prefix_paths dir m =
  match !checked_prefix with
  | None -> None
  | Some (input, output, prefix) ->
    let file = Digest.BLAKE256.file m.library_filename in
    let name = DirPath.to_string dir in
    let next = Digest.BLAKE256.string
      (!prefix ^ string_of_int (String.length name) ^ ":" ^ name ^ file) in
    prefix := next;
    let basename = Digest.BLAKE256.to_hex next ^ ".vo" in
    Some (Filename.concat input basename, Filename.concat output basename)

let read_prefix path =
  let ch = open_in_bin path in
  let payload = Fun.protect ~finally:(fun () -> close_in ch)
    (fun () -> really_input_string ch (in_channel_length ch)) in
  let opac, taint = (Marshal.from_string payload 0 :
    Mod_checking.opaques * (string * Digest.BLAKE256.t) list) in
  if List.exists (fun (file, hash) -> Digest.BLAKE256.file file <> hash) taint
    then raise Not_found;
  opac, payload

let finish_prefix payload =
  match !checked_prefix with
  | None -> ()
  | Some (_, _, prefix) ->
    (* A preceding library's indirect opaque reads also taint its successors.
       Bind the actual saved bytes, retaining their sharing on both cold/hot runs. *)
    prefix := Digest.BLAKE256.string (!prefix ^ Digest.BLAKE256.string payload)

let write_prefix path opac =
  let taint = LibrarySet.fold (fun dir acc ->
    let file = LibraryMap.find dir !library_sources in
    (file, Digest.BLAKE256.file file) :: acc) !opaque_taint [] in
  let payload = Marshal.to_string (opac, taint) [Marshal.Compat_32] in
  let ch = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out ch) (fun () -> output_string ch payload);
  finish_prefix payload;
  (* Return only completed independent checks. A fresh invocation restores
     their certificates; it never restores a partially checked declaration. *)
  if Sys.time () >= !prefix_deadline then raise Checked_prefix
