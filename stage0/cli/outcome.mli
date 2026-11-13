type t = Exit of int | Run_program of { program : string; arguments : string list }

exception Stop of int
