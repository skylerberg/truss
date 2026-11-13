(* Building the LIR of one function a statement at a time, for the code
   generation passes that write LIR rather than transform it: lowering,
   generated functions, and intrinsics. *)

type t

val create : unit -> t

(* A new local, numbered after every earlier one. *)
val local : t -> ?name:string -> Lir.ty -> Lir.local
val local_type : t -> Lir.local -> Lir.ty

(* A new block, which nothing jumps to yet. *)
val block : t -> Lir.block

(* Makes [block] the current block. Statements added since the last
   [finish] are dropped, so [finish] comes first. *)
val start : t -> Lir.block -> unit
val emit : t -> Lir.statement -> unit

(* Ends the current block with a terminator. *)
val finish : t -> Lir.terminator -> unit

(* Writes [block] with [f], then goes back to the block that was current,
   with its statements so far, so a case of a switch can be written before
   the switch itself ends its block. *)
val in_block : t -> Lir.block -> (unit -> unit) -> unit

(* Runs [then_] when [condition] is true, then goes on in a new block. *)
val branch : t -> Lir.operand -> yes:Lir.block -> no:Lir.block -> unit
(** Ends the current block with a jump to [yes] where a Boolean is true, and to [no] where it is
    false. *)

val when_ : t -> Lir.operand -> (unit -> unit) -> unit

(* A counted loop over [0, count), running [body] with the index, a local of
   type [usize]. *)
val loop :
  t ->
  ?integer:Memory_layout.integer ->
  index_type:Lir.ty ->
  count:Lir.operand ->
  (Lir.local -> unit) ->
  unit
(** Runs [body] for each index from 0 to before [count]. The index is a local of [index_type], an
    integer of the kind [integer], [USize] by default. *)

(* The function built: [written_result] is the parameter pointing to where
   a large result is written, if any. *)
val build :
  ?written_result:Lir.local ->
  t ->
  parameters:Lir.local list ->
  result:Lir.ty option ->
  Lir.function_

val at : Lir.local -> Lir.place
val ( / ) : Lir.place -> Lir.projection -> Lir.place
val usize : int -> Lir.operand
