(* Building the LIR of one function a statement at a time, for the code
   generation passes that write LIR rather than transform it: lowering,
   generated functions, and intrinsics. *)

type t

val create : unit -> t

(* A new local, numbered after every earlier one. *)
val local : t -> ?name:string -> Lir.ty -> Lir.local

(* A new block, which nothing jumps to yet. *)
val block : t -> Lir.block

(* The block statements are added to. *)
val current : t -> Lir.block

(* Makes [block] the current block. Statements added since the last
   [finish] are dropped, so [finish] comes first. *)
val start : t -> Lir.block -> unit
val emit : t -> Lir.statement -> unit

(* Ends the current block with a terminator. *)
val finish : t -> Lir.terminator -> unit

(* Writes [block] with [f], then goes back to the block that was current,
   with its statements so far, so a case of a switch can be written before
   the switch itself ends its block. *)
val aside : t -> Lir.block -> (unit -> unit) -> unit

(* Runs [then_] when [condition] is true, then goes on in a new block. *)
val when_ : t -> Lir.operand -> (unit -> unit) -> unit

(* A counted loop over [0, count), running [body] with the index, a local of
   type [usize]. *)
val loop : t -> usize:Ground.ty -> count:Lir.operand -> (Lir.local -> unit) -> unit
val build : t -> parameters:Lir.local list -> result:Lir.ty option -> Lir.function_
val at : Lir.local -> Lir.place
val ( / ) : Lir.place -> Lir.projection -> Lir.place
val usize : int -> Lir.operand
