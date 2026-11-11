(* The [truss] command. Everything it does is in the [Cli] library: this
   only starts it, as the command a person or agent runs, or, with the
   arguments [__serve] and a project's root, as that project's background
   process. *)

let () =
  match Sys.argv with
  | [| _; "__serve"; key |] -> Cli.Main.serve key
  | argv -> exit (Cli.Main.client (Array.to_list argv))
