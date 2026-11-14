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
val nested : t -> index:int -> environment:(string * Lowered.ty) list -> t

(* A new local, numbered after every earlier one. [is_zeroed] declares it
   zeroed in the function that owns it, so that it is zero at the start of
   each run of that function: a drop flag, which starts false, or an
   omitted argument, which C must be passed a value for. Every other local
   is declared with no initializer, and must be written before it is
   read. *)
val local : t -> ?name:string -> ?is_zeroed:bool -> Lowered.ty -> Lowered.local
val local_type : t -> Lowered.local -> Lowered.ty

(* A new block, which nothing jumps to yet. *)
val block : t -> Lowered.block

(* Makes [block] the current block. Statements added since the last
   [finish] are dropped, so [finish] comes first. *)
val start : t -> Lowered.block -> unit
val emit : t -> Lowered.statement -> unit

(* Ends the current block with a terminator. *)
val finish : t -> Lowered.terminator -> unit

(* Writes [block] with [f], then goes back to the block that was current,
   with its statements so far, so a case of a switch can be written before
   the switch itself ends its block. *)
val in_block : t -> Lowered.block -> (unit -> unit) -> unit

(* Ends the current block with a jump to [yes] where a Boolean is true, and
   to [no] where it is false. *)
val branch : t -> Lowered.operand -> yes:Lowered.block -> no:Lowered.block -> unit

(* Runs [then_] when [condition] is true, then goes on in a new block. *)
val when_ : t -> Lowered.operand -> (unit -> unit) -> unit

(* Runs [body] for each index from 0 to before [count]. The index is a local
   of [index_type], an integer of the kind [integer], [USize] by default. *)
val loop :
  t ->
  ?integer:Memory_layout.integer ->
  index_type:Lowered.ty ->
  count:Lowered.operand ->
  (Lowered.local -> unit) ->
  unit

val outline : t -> nested:int -> parts:Lowered.local list -> (unit -> unit) -> Lowered.local

(* Writes the C of the builder's function, which takes [parameters] and
   gives [result], and of the functions outlined from it. *)
val build : ?returns:bool -> t -> parameters:Lowered.local list -> result:Lowered.ty option -> unit

(* The instance the builder's function is part of, once it is built. *)
val built : t -> instance
val at : Lowered.local -> Lowered.place
val ( / ) : Lowered.place -> Lowered.projection -> Lowered.place
val usize : int -> Lowered.operand
