type t = Exit of int | Run_program of { program : string; arguments : string list }

exception Stop of int
exception Cannot_run of string

let raise_cannot_run format = Printf.ksprintf (fun message -> raise (Cannot_run message)) format
