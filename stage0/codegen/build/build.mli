(* Turning LIR into a program: emitting C, compiling it to object files
   through a cache, and linking.

   An object file is keyed by its C text, the C compiler's identity, and the
   flags, so a file whose C came out the same compiles nothing, and a new
   compiler recompiles objects without changing any LIR. Files that need
   compiling are compiled in parallel, across the machine's cores. *)

(* A directory of cached object files. *)
type cache

val cache : string -> cache

(* The flags a build compiles with, besides [Toolchain.required_flags]. *)
type settings = { build : Emit_c.build; optimization : Toolchain.optimization; extra : string list }

(* Compiles C files, each a name and its text, to object files, and returns
   their paths in the same order. [progress] is told how many of the files
   that were not cached have been compiled, out of how many, before the
   first and after each, from whichever domain compiled it, one call at a
   time. *)
val objects :
  ?progress:(int -> int -> unit) ->
  Toolchain.t ->
  cache ->
  settings ->
  (string * string) list ->
  (string list, string) result

(* A program: each list of compiled instances is one C file, [sources] are
   further C files, such as the startup code and the anchors, and the
   runtime for the target is always linked: a test program's with [tests],
   which the test runner's startup code needs. With [in_order], as a test
   program has it, the runtime runs the branches of a [parallel] statement
   one after another and starts no thread. [copied] gives the small
   callees to emit beside an instance, in its file, as copies the C
   compiler may inline. *)
val program :
  ?progress:(int -> int -> unit) ->
  ?tests:bool ->
  ?in_order:bool ->
  ?copied:(Lir.t -> Lir.t list) ->
  Toolchain.t ->
  cache ->
  Memory_layout.env ->
  settings ->
  files:Lir.compiled list list ->
  sources:(string * string) list ->
  output:string ->
  (unit, string) result
