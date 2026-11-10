(* The LIR as C.

   A file declares everything it uses itself and includes no header: the
   fixed-width integers, every type its code names, the prototype of every
   function it calls, and the runtime's few functions. The C has no
   undefined behavior even if the prover were wrong about an overflow or a
   shift: shifts are masked, and arithmetic is done where wrapping is
   defined, given the flags [Toolchain] passes. *)

type build = Development | Release

(* An instance defined in a file is [External], called from other files, or
   [Internal], a copy of a small callee that the C compiler may inline. *)
type linkage = External | Internal

(* One C file holding the given instances, in order, and the given static
   data. *)
val file :
  Memory_layout.env ->
  build ->
  ?data:Lir.data list ->
  ?tables:Lir.table list ->
  ?evidence:Lir.evidence list ->
  (Lir.t * linkage) list ->
  string

(* The C type and name of a struct, for the runtime and startup code that
   are written in C. *)
val anchor_struct : string
val runtime_declarations : Memory_layout.target -> string

(* The C symbol of a definition's position anchor. *)
val anchor_symbol : Path.t -> string
