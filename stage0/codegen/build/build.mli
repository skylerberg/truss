(* Turning LIR into a program: emitting C, compiling it to object files
   through a cache, and linking. See CODEGEN.md, "Building".

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
   their paths in the same order. *)
val objects :
  Toolchain.t -> cache -> settings -> (string * string) list -> (string list, string) result

(* A program: each list of instances and data is one C file, [sources] are
   further C files, such as the startup code and the anchors, and the
   runtime for the target is always linked. *)
val program :
  Toolchain.t ->
  cache ->
  Memory_layout.env ->
  settings ->
  files:((Lir.t * Emit_c.linkage) list * Lir.data list) list ->
  sources:(string * string) list ->
  output:string ->
  (unit, string) result
