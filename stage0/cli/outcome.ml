(* A command's result: an exit status, or for [truss run], a program for the
   client to run on its terminal, since the background process that built
   it has no terminal. *)

type t = Exit of int | Run_program of { program : string; arguments : string list }
