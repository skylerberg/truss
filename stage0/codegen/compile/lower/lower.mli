type unsupported = { construct : string; at : Lowered.site option }

exception Unsupported of unsupported

type context

val env : context -> Memory_layout.env
val glue : context -> Glue.t
val monomorphic : context -> Monomorphic.context

val context :
  ?checks:bool ->
  constant:(context -> Path.t -> Lowered.static_value option) ->
  Query.context ->
  Libc.system ->
  context

val instance : context -> Instance.key -> Emit_c.Builder.instance

type constant = Folded of Lowered.data | Run of Ground.ty

val constant : context -> Path.t -> constant
val evaluator : context -> Path.t -> Emit_c.Builder.instance
val table : context -> Instance.key -> Lowered.table
val any_table : context -> Instance.key -> Lowered.table
val locked_table : context -> Instance.key -> capability:Path.t -> Lowered.table
val test_key : Path.t -> Instance.key

val template_check :
  context -> Instance.key -> from_template:Path.t -> texts:string list -> Emit_c.Builder.instance

val template_checked : context -> Path.t -> int list

val call_evaluation :
  context -> Instance.key -> function_:Path.t -> arguments:Z.t list -> Emit_c.Builder.instance

module For_testing : sig
  val constant_value : context -> Path.t -> Lowered.static_value option
end
