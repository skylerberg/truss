module Lookups = Lookups

type unsupported = { construct : string; at : Lowered.site option }

type lowered =
  | Compiled of Emit_c.fragment
  | Folded of Lowered.data * Emit_c.fragment
  | Evaluate of Path.t * Ground.ty

type lowered_lookups = {
  system : Libc.system;
  read_source : Path.file -> Source.t;
  interface : Interface.Lookups.t;
  find_lowered : Lowered.Item.t -> (lowered, unsupported) result option;
  read_test_key : Lowered.Item.t -> (string, unsupported) result;
  list_reached_todo_types : Lowered.Item.t -> Path.t list;
}

exception Todo_type of Ground.ty
exception Infinite_size of Ground.ty

val make_monomorphic_context : Interface.Lookups.t -> Monomorphic.context
val lower : Libc.system -> Lookups.t -> Lowered.Item.t -> (lowered, unsupported) result
val list_references : lowered -> Lowered.Item.t list

val check_calls :
  Interface.Lookups.t ->
  find_call_edges:(Path.t -> Path.t list option) ->
  Lowered.Item.t ->
  lowered ->
  unit

val derive_test_keys :
  read_lowered:(Lowered.Item.t -> lowered) ->
  read_known_key:(Lowered.Item.t -> string) ->
  Lowered.Item.t list ->
  (Lowered.Item.t * string) list

val test_runner : Lowered.Item.t
val make_root : Path.t -> Lowered.Item.t
val list_roots : tests:Path.t list -> mains:Path.t list -> Lowered.Item.t list

module Encoding : sig
  val decode : Memory_layout.env -> Ground.ty -> string -> Lowered.static_value
end

module For_testing : sig
  module Intrinsics : sig
    type argument = Intrinsics.argument = Place of Lowered.place | Value of Lowered.operand
    type types = Intrinsics.types = { uint64 : Ground.ty; string_slice : Ground.ty }

    val lower :
      ?value_arguments:Z.t list ->
      ?reported:Lowered.operand ->
      Memory_layout.env ->
      Emit_c.Ir_builder.t ->
      types ->
      Intrinsic.operation ->
      type_arguments:Ground.ty list ->
      argument list ->
      destination:Lowered.place option ->
      site:Lowered.site ->
      trace:Lowered.operand option ->
      Lowered.place option
  end

  val drop_and_copy : Memory_layout.env -> Drop_and_copy.t
  val is_trivial : Drop_and_copy.t -> Ground.ty -> bool
  val drop : Drop_and_copy.t -> Ground.ty -> Emit_c.fragment
  val copy : Drop_and_copy.t -> Ground.ty -> Emit_c.fragment
  val copy_signature : Drop_and_copy.t -> Ground.ty -> Lowered.signature
end
