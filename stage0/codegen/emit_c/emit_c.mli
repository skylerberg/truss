(* Instances as C.

   Each instance is emitted on its own, as a fragment: its C, and what a file
   that holds it declares and defines for it. A file declares everything it
   uses itself and includes no header: the fixed-width integers, every type
   its code names, the prototype of every function it calls, and the
   runtime's functions, structs, and helpers that its code names. The C has
   no undefined behavior even if the prover were wrong about an overflow or
   a shift: shifts are masked, and arithmetic is done where wrapping is
   defined, given the flags [Toolchain] passes. *)

type build = Development | Release

(* An instance defined in a file is [External], called from other files, or
   [Internal], a copy of a small callee, which is [static inline], so that
   the C compiler may inline it at any level and drops it where it does. *)
type linkage = External | Internal

(* A position in a definition, relative to the line it starts on. *)
type site = C_runtime.site = { definition : Path.t; line : int; column : int }
type failure = C_runtime.failure = Echo | Todo

(* Writing an instance's C one statement at a time. *)
module Builder = Builder

(* An instance's C, a constant's data, or a capability's table. *)
type compiled = Code of Builder.instance | Data of Lowered.data | Table of Lowered.table

(* The version of code generation, part of every key built from an
   instance's C. *)
val version : int

(* An instance's C, a constant's data, or a capability's table. *)
type fragment

val fragment : Memory_layout.env -> compiled -> fragment
val key : fragment -> Instance.key

(* The instances a fragment names, other than itself. *)
val references : fragment -> Instance.key list

(* The methods of capabilities an instance calls: each capability, with the
   method's place among its methods. *)
val calls : fragment -> (Path.t * int) list

(* The instances an instance calls by name. *)
val called : fragment -> Instance.key list

(* For a table, the capability whose methods its entries are, if any. *)
val table : fragment -> Path.t option option

(* Whether an instance has little code and no nested functions, so that a
   file may hold a copy of it beside its callers. *)
val is_small : fragment -> bool

(* The definitions that the fragment's positions are relative to. *)
val anchors : fragment -> Path.t list

(* The [echo]s and [todo]s an instance holds. *)
val failures : fragment -> (failure * site) list

(* A fragment's C with every name it holds written as a number, for a hash
   that renaming or moving a definition does not change. *)
val text : fragment -> string

(* One C file holding the given fragments, in order. *)
val file : Memory_layout.env -> build -> (fragment * linkage) list -> string

(* The struct of a definition's position, which the runtime and the file of
   anchors define, and the typedefs of the fixed-width integers, which the
   file of anchors starts with. *)
val anchor_struct : string
val integer_typedefs : Memory_layout.target -> string

(* The C symbol of a definition's position anchor. *)
val anchor_symbol : Path.t -> string

module For_testing : sig
  val c : fragment -> string
  (** The C of a fragment's functions and data, as a file holds them. *)
end
