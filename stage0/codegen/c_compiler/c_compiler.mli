type t

val variables : string list
val find : objects:string -> (t, string) result
val make_fingerprint : t -> Profile.t -> string

val build_executable :
  ?report_progress:(int -> int -> unit) ->
  ?dsym_bundle:string ->
  t ->
  Profile.t ->
  units:(string * string) list ->
  output:string ->
  (unit, string) result

module For_testing : sig
  val reject_warnings : t -> t
  val has_sanitizer : t -> bool
  val compile : t -> Profile.t -> text:string -> output:string -> (unit, string) result
  val compile_objects : t -> Profile.t -> (string * string) list -> (string list, string) result
end
