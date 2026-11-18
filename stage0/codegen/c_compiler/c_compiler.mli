type t
type optimization = O1 | O2_lto

val variables : string list
val find : objects:string -> (t, string) result
val make_fingerprint : t -> optimization -> string

val build_executable :
  ?report_progress:(int -> int -> unit) ->
  t ->
  optimization ->
  units:(string * string) list ->
  output:string ->
  (unit, string) result

module For_testing : sig
  val reject_warnings : t -> t
  val compile : t -> optimization -> source:string -> output:string -> (unit, string) result
  val compile_objects : t -> optimization -> (string * string) list -> (string list, string) result
end
