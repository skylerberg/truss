type t

val variables : string list

val find :
  ?debug_prefix_maps:(string * string) list ->
  x86_64_level:X86_64_level.t ->
  objects:string ->
  unit ->
  (t, string) result

val make_fingerprint : t -> Profile.t -> string

type source = { name : string; text_hash : string; read_text : unit -> string }

val hash_text : string -> string
val make_source : name:string -> string -> source

val build_executable :
  ?report_progress:(int -> int -> unit) ->
  ?dsym_bundle:string ->
  t ->
  Profile.t ->
  sources:source list ->
  output:string ->
  (unit, string) result

module For_testing : sig
  val reject_warnings : t -> t
  val has_sanitizer : t -> bool
  val compile : t -> Profile.t -> text:string -> output:string -> (unit, string) result
  val compile_objects : t -> Profile.t -> source list -> (string list, string) result
end
