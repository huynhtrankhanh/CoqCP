(* Source files are programs for the vernacular interpreter. Do not let them
   extend that interpreter with native code, even inside the OS sandbox.
   Approved tactic plugins are linked statically by the evaluator's build. *)
external lockdown : unit -> unit = "coqcp_compile_lockdown"

let denied what = CErrors.user_err Pp.(str ("Disabled in the submission compiler: " ^ what))

let () =
  if Coq_config.version <> "9.3.0" then failwith "This compiler requires Rocq 9.3.0";
  Mltop.set_top {
    load_plugin = (fun plugin -> denied ("dynamic ML plugin " ^ Mltop.PluginSpec.to_package plugin));
    load_module = (fun _ -> denied "native ML module loading");
    (* Rocq also calls this for installed packages during initialization.
       Search paths have no purpose with dynamic loading disabled. *)
    add_dir = (fun _ -> ());
    ml_loop = (fun ?init_file:_ () -> denied "OCaml toplevel");
  };
  (* The executable, shared runtime and approved plugins are already mapped.
     This irreversible filter also covers indirect/native loading paths. *)
  lockdown ();
  Coqc.main (List.tl (Array.to_list Sys.argv))
