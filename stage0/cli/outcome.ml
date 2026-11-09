(* How a command ends: with an exit status, or, for [truss run], with a
   program for the client to run on its own terminal, since the background
   process that built it has no terminal of its own. *)

type t = Exit of int | Run_program of { program : string; arguments : string list }
