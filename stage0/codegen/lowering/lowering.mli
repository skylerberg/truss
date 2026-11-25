module Lookups = Lookups
module Positions = Positions

type unsupported = { construct : string; at : Lowered.site option }

type lowered =
  | Compiled of Emit_c.fragment
  | Folded of Lowered.data * Emit_c.fragment
  | Evaluate of Lowered.Item.t * Ground.ty

type unbuildable = Unsupported of unsupported | Todo_types of Path.t list
type 'value ran = Ran of 'value | Unfinished of string | Stopped of string
type evaluation = string ran

type linked =
  | Unit of { item : Lowered.Item.t; text_hash : string; sites : Lowered.site list }
  | Evaluated of { item : Lowered.Item.t; evaluator : Lowered.Item.t }
  | Unbuildable of unbuildable

type test_pass = { compiler_fingerprint : string; microseconds : int }

type lowered_lookups = {
  system : Libc.system;
  read_source : Path.file -> Source.t;
  source : Resolve.Names.source;
  interface : Interface.Lookups.t;
  find_lowered : Lowered.Item.t -> (lowered, unbuildable) result option;
  find_evaluation : Lowered.Item.t -> evaluation option;
  record_evaluation : Lowered.Item.t -> evaluation -> unit;
  find_test_pass : Lowered.Item.t -> test_pass option;
  record_test_run : Lowered.Item.t -> test_pass option -> unit;
  read_test_key : Lowered.Item.t -> (string, unbuildable) result;
  list_linked : Profile.t -> Lowered.Item.t list -> linked list;
  render_unit : Profile.t -> Lowered.Item.t -> string;
}

exception Infinite_size of Ground.ty

val make_env : Libc.system -> Interface.Lookups.t -> Memory_layout.env
val lower : Libc.system -> Lookups.t -> Lowered.Item.t -> (lowered, unbuildable) result
val list_references : lowered -> Lowered.Item.t list
val list_sites : lowered -> Lowered.site list
val make_data : Memory_layout.env -> Lowered.Item.t -> Ground.ty -> string -> Emit_c.fragment
val is_evaluated : lowered -> bool

val render_unit :
  Libc.system ->
  Interface.Lookups.t ->
  source:Resolve.Names.source ->
  Profile.t ->
  read_source:(Path.file -> Source.t) ->
  is_worked_on:(Path.package -> bool) ->
  find_lowered:(Lowered.Item.t -> lowered option) ->
  Emit_c.fragment ->
  string

val check_calls :
  Interface.Lookups.t ->
  find_call_edges:(Path.t -> Path.t list option) ->
  Lowered.Item.t ->
  lowered ->
  unit

val derive_test_keys :
  read_lowered:(Lowered.Item.t -> (lowered, unbuildable) result) ->
  read_known_key:(Lowered.Item.t -> (string, unbuildable) result) ->
  Lowered.Item.t list ->
  ((Lowered.Item.t * string) list, unbuildable) result

val test_runner : Lowered.Item.t
val make_root : Path.t -> Lowered.Item.t
val list_roots : tests:Path.t list -> mains:Path.t list -> Lowered.Item.t list

module Encoding : sig
  val decode : Memory_layout.env -> Ground.ty -> string -> Lowered.static_value
end

module For_testing : sig
  module Intrinsics : sig
    type argument = Intrinsics.argument = Place of Lowered.place | Value of Lowered.operand
    type types = Intrinsics.types = { uint64 : Ground.ty; string : Ground.ty }

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
