val serve : string -> unit
val run_client : string list -> int

module For_testing : sig
  val run_command_line : ?directory:string -> string list -> Outcome.t
end
