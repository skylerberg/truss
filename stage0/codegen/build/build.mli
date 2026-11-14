(* Turning instances' C into a program: assembling C files, compiling them
   to object files through a cache, and linking.

   An object file is keyed by its C text, the C compiler's identity, and the
   flags, so a file whose C came out the same compiles nothing, and a new
   compiler recompiles objects without changing any instance's C. Files that need
   compiling are compiled in parallel, across the machine's cores. *)

(* A directory of cached object files. *)
type cache

val cache : string -> cache

(* The flags a build compiles with, besides [Toolchain.required_flags]. *)
type settings = { build : Emit_c.build; optimization : Toolchain.optimization; extra : string list }

val program :
  ?progress:(int -> int -> unit) ->
  ?tests:bool ->
  ?in_order:bool ->
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
