(* The [truss] command. Everything it does is in the [Cli] library: this
   only starts it, as the command a person or agent runs, or, with the
   argument [__serve], as the background process. *)

let () =
  match Sys.argv with
  | [| _; "__serve" |] -> Cli.Main.serve ()
  | argv -> exit (Cli.Main.client (Array.to_list argv))
