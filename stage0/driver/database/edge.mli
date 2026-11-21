type reason = Read | Call | Reference | Claim
type t = { target : Part.t; reasons : reason list }

val add : reason -> reason list -> reason list
val list_targets : reason -> t list -> Part.t list
val keep_reasons : (reason -> bool) -> t list -> t list
val is_equal_beyond_reads : t list -> t list -> bool
