type t = Exit of int | Run_program of { program : string; arguments : string list }

exception Stop of int
exception Cannot_run of string

val raise_cannot_run : ('a, unit, string, 'b) format4 -> 'a
val raise_problems : Project_catalog.Problem.t list -> 'a
