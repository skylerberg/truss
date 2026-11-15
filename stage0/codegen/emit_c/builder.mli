type t
type instance = C_instance.t

val instance_key : instance -> Instance.key
val create : Memory_layout.env -> key:Instance.key -> t
val nested : t -> index:int -> environment:(string * Lowered.ty) list -> t
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
  t ->
  ?integer:Memory_layout.integer ->
  index_type:Lowered.ty ->
  count:Lowered.operand ->
  (Lowered.local -> unit) ->
  unit

val outline : t -> nested:int -> parts:Lowered.local list -> (unit -> unit) -> Lowered.local
val build : ?returns:bool -> t -> parameters:Lowered.local list -> result:Lowered.ty option -> unit
val built : t -> instance
val at : Lowered.local -> Lowered.place
val ( / ) : Lowered.place -> Lowered.projection -> Lowered.place
val constant_uint64 : int -> Lowered.operand
