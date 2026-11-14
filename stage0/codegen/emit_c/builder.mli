(* Writing an instance's C one statement at a time, for the code generation
   that writes code: lowering, generated functions, glue, and intrinsics.
   Each statement is printed as it is written. A builder writes one
   function: an instance's own, or a nested function of it, with the
   functions outlined from it and any separate function. *)

type t

(* An instance's C, once its functions are built. *)
type instance = C_instance.t

val instance_key : instance -> Instance.key

(* A builder of the instance [key]'s own function, which runs from block 0,
   the first block made. *)
val create : Memory_layout.env -> key:Instance.key -> t

(* A builder of the nested function [index] of the instance [parent]
   writes, whose environment has these fields. *)
val nested : t -> index:int -> environment:(string * Lir.ty) list -> t

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

(* Ends the current block with a jump to [yes] where a Boolean is true, and
   to [no] where it is false. *)
val branch : t -> Lir.operand -> yes:Lir.block -> no:Lir.block -> unit

(* Runs [then_] when [condition] is true, then goes on in a new block. *)
val when_ : t -> Lir.operand -> (unit -> unit) -> unit

(* Runs [body] for each index from 0 to before [count]. The index is a local
   of [index_type], an integer of the kind [integer], [USize] by default. *)
val loop :
  t ->
  ?integer:Memory_layout.integer ->
  index_type:Lir.ty ->
  count:Lir.operand ->
  (Lir.local -> unit) ->
  unit

(* Writes code with [body] as an outlined function: a function of its own,
   nested in the instance as [nested], which the code around it runs by
   naming the local this returns, the holder of its environment. The
   function is given [parts], locals of the code around it, as its
   parameters, and reaches every other local of the code around it through
   its environment. [body] starts in the function's entry block and ends
   each of its paths with a return. *)
val outline : t -> nested:int -> parts:Lir.local list -> (unit -> unit) -> Lir.local

(* A separate function: the instance [key]'s own function, written beside
   this one, given [parts], locals of the code around it, as its
   parameters, and no environment, so its code names no other local of the
   code around it. It is written in pieces with [write_in], and runs from
   its entry block. *)
type separate

val separate : t -> key:Instance.key -> parts:Lir.local list -> separate
val separate_entry : t -> separate -> Lir.block

(* Gives the fields of the cursor over [yielding], whose pulled method the
   builder writes, to the code that names them before the cursor's layout
   is known: [fields] holds each field but the state, with its type, as it
   is made. *)
val describe_cursor : t -> Ground.yielding -> (string * Lir.ty) list ref -> unit

(* Writes [body] in a separate function, then goes back to the block that
   was current, with its statements so far. *)
val write_in : t -> separate -> (unit -> unit) -> unit

(* Writes the C of the builder's function, which takes [parameters] and
   gives [result], and of the functions outlined from it and written
   beside it. *)
val build : ?returns:bool -> t -> parameters:Lir.local list -> result:Lir.ty option -> unit

(* The instance the builder's function is part of, and a separate
   function's instance, once they are built. *)
val built : t -> instance
val built_separate : t -> separate -> instance
val at : Lir.local -> Lir.place
val ( / ) : Lir.place -> Lir.projection -> Lir.place
val usize : int -> Lir.operand
