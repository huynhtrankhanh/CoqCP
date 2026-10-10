(* Approved tactic plugins are linked into this module by the evaluator.
   The host rejects imports outside its fixed WASI interface. *)
let denied what = CErrors.user_err Pp.(str ("Disabled in the submission compiler: " ^ what))
let () =
  Sys.chdir "/work";
  if Coq_config.version <> "9.3.0" then failwith "This compiler requires Rocq 9.3.0";
  List.iter (Findlib.record_package Findlib.Record_core) Wasi_plugins.allowed;
  Mltop.set_top {
    load_plugin = (fun plugin -> denied ("dynamic ML plugin " ^ Mltop.PluginSpec.to_package plugin));
    load_module = (fun _ -> denied "native ML module loading");
    add_dir = (fun _ -> ());
    ml_loop = (fun ?init_file:_ () -> denied "OCaml toplevel");
  };
  Coqc.main (List.tl (Array.to_list Sys.argv))
