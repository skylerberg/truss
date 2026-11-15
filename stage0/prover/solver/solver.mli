type t
type cache = { find : string -> string option; add : string -> string -> unit }

val find : ?cache:cache -> unit -> (t, string) result

type answer = Proven | Counterexample of (Logic.symbol * string) list | Out_of_steps
type request
type canonical

val request :
  ?symbols:Logic.symbol list -> ?terms:(Logic.symbol * Logic.term) list -> Logic.query -> request

val request_key : request -> string
val solve_all : t -> (request * Logic.query) list -> canonical list
val read : request -> canonical -> answer
val queries_run : t -> int

module For_testing : sig
  val key : Logic.query -> string
end
