let () =
  match Sys.argv with
  | [| _; "__serve"; key |] -> Cli.Main.serve key
  | argv -> exit (Cli.Main.run_client (Array.to_list argv))
