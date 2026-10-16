(* Raw byte/effect backend for the extracted, proved entry point.
   Decimal parsing, validation, solving, formatting, EOF checks, and flush
   placement are all implemented by Solver.Implementation.program. *)
let () =
  if Sys.int_size < 63 then failwith "A 64-bit OCaml runtime is required";
  let output = Buffer.create 32 in
  let publish () =
    Buffer.output_buffer stdout output;
    Buffer.clear output;
    flush stdout
  in
  let rec execute = function
    | Solver.Done () -> publish ()
    | Solver.Dispatch (operation, next) ->
        match operation with
        | Solver.Trap -> failwith "Invalid input"
        | Solver.Flush -> publish (); execute (next (Obj.repr ()))
        | Solver.ReadChar ->
            let ch =
              try Big_int_Z.big_int_of_int (Char.code (input_char stdin))
              with End_of_file -> Solver.eof
            in
            execute (next (Obj.repr ch))
        | Solver.WriteChar ch ->
            Buffer.add_char output (Char.chr (Big_int_Z.int_of_big_int ch));
            execute (next (Obj.repr ()))
  in
  execute Solver.Implementation.program
