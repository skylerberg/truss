type cache

val make_cache : string -> cache

type settings = { build : Emit_c.build; optimization : Toolchain.optimization; extra : string list }

val build_program :
  ?progress:(int -> int -> unit) ->
  ?tests:bool ->
  ?copied:(Emit_c.fragment -> Emit_c.fragment list) ->
  Toolchain.t ->
  cache ->
  Memory_layout.env ->
  settings ->
  files:Emit_c.fragment list list ->
  sources:(string * string) list ->
  output:string ->
  (unit, string) result

module For_testing : sig
  val objects :
    ?progress:(int -> int -> unit) ->
    Toolchain.t ->
    cache ->
    settings ->
    (string * string) list ->
    (string list, string) result
end
