type t
type instance = C_instance.t
type prototype = { parameters : Lowered.local list; result : Lowered.ty option; returns : bool }

val instance_key : instance -> Instance.key
val create : Memory_layout.env -> key:Instance.key -> t

val build_nested :
  t -> index:int -> environment:(string * Lowered.ty) list -> (t -> prototype) -> unit

val local : t -> ?name:string -> ?is_zeroed:bool -> Lowered.ty -> Lowered.local
val local_type : t -> Lowered.local -> Lowered.ty
val block : t -> Lowered.block
val start : t -> Lowered.block -> unit
val emit : t -> Lowered.statement -> unit
val finish : t -> Lowered.terminator -> unit
val in_block : t -> Lowered.block -> (unit -> unit) -> unit
val branch : t -> Lowered.operand -> yes:Lowered.block -> no:Lowered.block -> unit
val when_ : t -> Lowered.operand -> (unit -> unit) -> unit

val loop :
  t -> ?integer:Memory_layout.integer -> count:Lowered.operand -> (Lowered.local -> unit) -> unit

val outline : t -> index:int -> parts:Lowered.local list -> (unit -> unit) -> Lowered.local
val build : t -> prototype -> instance
