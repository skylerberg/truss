val serve : string -> unit
val client : string list -> int

module For_testing : sig
  val run_command_line : ?directory:string -> string list -> Outcome.t
end
