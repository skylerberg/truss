(* The compiler stages' view of the code database. See query.mli. *)

type context = Incremental.context
type subject = Incremental.subject = { path : Path.t; part : string option }
type ('key, 'value) input = ('key, 'value) Incremental.input
type ('key, 'value) query = ('key, 'value) Incremental.query

let input = Incremental.input
let query = Incremental.query
let find = Incremental.read

let get context input key =
  match Incremental.read context input key with Some value -> value | None -> raise Not_found

let demand = Incremental.demand

exception Cycle = Incremental.Cycle
