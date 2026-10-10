let () =
  Sys.chdir "/work";
  Coqdeplib.Rocqdep_main.main (List.tl (Array.to_list Sys.argv))
