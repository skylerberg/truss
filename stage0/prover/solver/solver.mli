type t
type cache = { find : string -> string option; add : string -> string -> unit }

val find : ?cache:cache -> unit -> (t, string) result

type sexp = Atom of string | List of sexp list
type unknown = Out_of_steps | Incomplete of string
type answer = Proven | Counterexample of (Logic.symbol * sexp) list | Unknown of unknown
type request

val make_request :
  ?symbols:Logic.symbol list -> ?terms:(Logic.symbol * Logic.term) list -> Logic.query -> request

val show_input : request * Logic.query -> string
val solve_all : t -> (request * Logic.query) list -> answer list

module For_testing : sig
  val hash_query : Logic.query -> string
  val count_queries_run : t -> int
  val proven_entry : string
  val make_incomplete_entry : string -> string
end
