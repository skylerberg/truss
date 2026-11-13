type t = Exit of int | Run_program of { program : string; arguments : string list }

exception Stop of int
(** The command has reported why it ends, and exits with this status. *)
