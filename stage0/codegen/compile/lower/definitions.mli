module Names = Resolve.Names

val bug : ('a, unit, string, 'b) format4 -> 'a

type context = {
  lookups : Lookups.t;
  constant : Path.t -> Lowered.static_value option;
  env : Memory_layout.env;
  drop_and_copy : Drop_and_copy.t;
  monomorphic : Monomorphic.context;
  types : Intrinsics.types;
  bool : Ground.ty;
  checks : bool;
}

val monomorphic : Interface.Lookups.t -> Monomorphic.context
val string_slice : Ground.ty

val context :
  Lookups.settings ->
  constant:(Path.t -> Lowered.static_value option) ->
  env:Memory_layout.env ->
  Lookups.t ->
  context

val test_key : Path.t -> Instance.key

type code = {
  definition_key : Names.key;
  anchor : Path.t;
  enclosing_impl : Path.t option;
  text : string;
  result : Types.result;
  substitution : Types.substitution;
  uses : Types.capability_set;
  real : Path.t list;
  has_defaults : bool;
}

val unwritten :
  definition_key:Names.key ->
  anchor:Path.t ->
  substitution:Types.substitution ->
  result:Types.result ->
  code

val key_of : context -> Path.t -> Resolve.Names.key
val text_of : context -> Names.key -> string
val bind : Types.generic list -> Ground.argument list -> Types.substitution
val impl_interface : context -> Path.t -> Types.impl_interface
val signature_of : context -> Path.t -> Types.signature
val code_of : context -> Path.t -> Ground.argument list -> code
val template_clauses : context -> Path.t -> int list -> Mir.Graph.t list
val panic_path : Path.t
val evidence_for : context -> Types.substitution -> Types.capability_set -> Path.t list
val result_of : context -> Types.substitution -> Types.result -> Convention.result * bool
val lending_parameters : context -> Types.substitution -> Types.result -> Lowered.ty list

val c_signature :
  context ->
  Types.substitution ->
  parameters:(Types.mode * Types.ty) list ->
  has_defaults:bool ->
  ?uses:Types.capability_set ->
  Types.result ->
  Lowered.signature * Convention.result

val has_defaults : Types.signature -> bool
val interface_parameters : Types.signature -> (Types.mode * Types.ty) list
