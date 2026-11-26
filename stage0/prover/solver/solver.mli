type t

val find : unit -> (t, string) result
val stop : t -> unit

type unknown = Out_of_steps | Incomplete of string
type answer = Proven | Falsifiable | Unknown of unknown
type request

val make_request : Logic.query -> request
val show_input : request -> string

type run = { input : string; output : string }
type solved = { answer : answer; runs : run list }

val solve_all : ?find_output:(string -> string option) -> t -> request list -> solved list

module For_testing : sig
  val count_queries_run : t -> int
  val make : run_z3:(string -> string) -> t
end
