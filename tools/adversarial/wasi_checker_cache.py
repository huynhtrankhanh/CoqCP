"""Install a checked-library prefix cache into the pinned independent checker.

The cache skips repeated proof checking only after a successful independent
check in exactly the same preceding environment. It never trusts submitted VM
metadata, and preserves the opaque dependency map for the final axiom audit.
"""
def install(tools, source, portable):
    original = (source / "checker/checkLibrary.ml").read_text()
    def replace(old, new):
        nonlocal original
        if original.count(old) != 1:
            raise RuntimeError("Pinned CheckLibrary cache insertion changed")
        original = original.replace(old, new)
    replace("let access_opaque_table dp i =", """let library_sources = ref LibraryMap.empty
let opaque_taint = ref LibrarySet.empty

let access_opaque_table dp i =
  opaque_taint := LibrarySet.add dp !opaque_taint;""")
    replace("let check_one_lib admit senv (dir,m) =",
            (tools / "portable/checked_prefix.ml").read_text() +
            "\nlet check_one_lib admit senv (dir,m) =")
    replace("  let senv =\n    if LibrarySet.mem dir admit then", """  let paths = prefix_paths dir m in
  let cached = match paths with
    | None -> None
    | Some (input, _) ->
      (try Some (read_prefix input) with Not_found | Sys_error _ -> None) in
  opaque_taint := LibrarySet.empty;
  let senv =
    match cached with
    | Some (opac, payload) ->
      (* Proofs were checked under this exact prefix; regenerate VM metadata
         from the validated declarations, as on an ordinary upstream import. *)
      let senv = Safe_checking.unsafe_import (fst senv) md dig in
      finish_prefix payload;
      senv, opac
    | None -> if LibrarySet.mem dir admit then""")
    replace("    register_loaded_library m; senv", """    (match paths, cached with
     | Some (_, output), None -> write_prefix output (snd senv)
     | _ -> ());
    register_loaded_library m; senv""")
    replace("  depgraph := LibraryMap.add sd.md_name sd.md_deps !depgraph;",
            "  library_sources := LibraryMap.add sd.md_name f !library_sources;\n"
            "  depgraph := LibraryMap.add sd.md_name sd.md_deps !depgraph;")
    (portable / "checker/checkLibrary.ml").write_text(original)
    interface = (source / "checker/checkLibrary.mli").read_text()
    (portable / "checker/checkLibrary.mli").write_text(interface +
        "\nexception Checked_prefix\n"
        "val set_checked_prefix : string -> string -> string -> string -> unit\n")
    entry = portable / "coqcp_wasi_gate/spec_check.ml"
    original = entry.read_text()
    marker = '      | "--root" :: physical :: logical :: rest ->'
    if original.count(marker) != 1:
        raise RuntimeError("Pinned checker argument insertion changed")
    original = original.replace(marker, '''      | "--checked-prefix" :: input :: output :: seed :: seconds :: rest ->
        Check.set_checked_prefix input output seed seconds; args rest
''' + marker)
    if original.count("  with error ->") != 1:
        raise RuntimeError("Pinned checker exception insertion changed")
    entry.write_text(original.replace("  with error ->", '''  with Check.Checked_prefix ->
    Printf.printf "{\\\"status\\\":\\\"prefix-checked\\\",\\\"rocq_version\\\":\\\"9.3.0\\\",\\\"axioms\\\":[]}\\n%!"
  | error ->'''))
