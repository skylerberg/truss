type t
type prototype = { parameters : Lowered.local list; result : Lowered.ty option; returns : bool }

val create : ?site:Lowered.site -> Memory_layout.env -> item:Lowered.Item.t -> t
val with_site : t -> Lowered.site -> (unit -> 'a) -> 'a

val build_nested :
  t ->
  index:Lowered.nested_function ->
  environment:(string * Lowered.ty) list ->
  (t -> prototype) ->
  unit

val allocate_local : t -> ?name:string -> ?is_zeroed:bool -> Lowered.ty -> Lowered.local
val lookup_local_type : t -> Lowered.local -> Lowered.ty
val allocate_block : t -> Lowered.block
val start : t -> Lowered.block -> unit
val emit : t -> Lowered.statement -> unit
val finish : t -> Lowered.terminator -> unit
val run_in_block : t -> Lowered.block -> (unit -> unit) -> unit
val emit_value : t -> Lowered.ty -> Lowered.rvalue -> Lowered.operand

type condition =
  | Test of Lowered.test
  | Holds of Lowered.operand
  | Negation of condition
  | Conjunction of condition * condition
  | Disjunction of condition * condition

val branch : t -> condition -> yes:Lowered.block -> no:Lowered.block -> unit
val evaluate : t -> condition -> Lowered.rvalue
val evaluate_test : t -> condition -> Lowered.test
val emit_when : t -> condition -> (unit -> unit) -> unit
val emit_if : t -> condition -> yes:(unit -> unit) -> no:(unit -> unit) -> unit

val emit_loop :
  t -> ?integer:Memory_layout.integer -> count:Lowered.operand -> (Lowered.local -> unit) -> unit

val outline :
  t -> index:Lowered.nested_function -> parts:Lowered.local list -> (unit -> unit) -> Lowered.local

val build : t -> prototype -> Fragment.t
