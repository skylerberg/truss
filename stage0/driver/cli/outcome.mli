type t = Exit of int | Run_program of { program : string; arguments : string list }

exception Stop of int
exception Cannot_run of string

val cannot_run : ('a, unit, string, 'b) format4 -> 'a
