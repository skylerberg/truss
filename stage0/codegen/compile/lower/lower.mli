type unsupported = { construct : string; at : Lowered.site option }

exception Unsupported of unsupported

type context

val env : context -> Memory_layout.env
val drop_and_copy : context -> Drop_and_copy.t
val monomorphic : Interface.Lookups.t -> Monomorphic.context

val context :
  Lookups.settings ->
  constant:(Path.t -> Lowered.static_value option) ->
  env:Memory_layout.env ->
  Lookups.t ->
  context

type ground_types = Ground_types.t = { types : Ground.ty list; folded_constants : Path.t list }

val ground_types : Lookups.settings -> Lookups.t -> Instance.key -> ground_types
val instance : context -> Instance.key -> Emit_c.Builder.instance

type constant = Folded of Lowered.data | Run of Ground.ty

val constant : context -> Path.t -> constant
val evaluator : context -> Path.t -> Emit_c.Builder.instance
val table : context -> Instance.key -> Lowered.table
val any_table : context -> Instance.key -> Lowered.table
val locked_table : context -> Instance.key -> capability:Path.t -> Lowered.table
val test_key : Path.t -> Instance.key

val template_check :
  context ->
  Instance.key ->
  from_template:Path.t ->
  literals:string list ->
  clauses:int list ->
  Emit_c.Builder.instance

val call_evaluation :
  context -> Instance.key -> function_:Path.t -> arguments:Z.t list -> Emit_c.Builder.instance
