val raise_bug : ('a, unit, string, 'b) format4 -> 'a

type context = {
  lookups : Lookups.t;
  env : Memory_layout.env;
  drop_and_copy : Drop_and_copy.t;
  monomorphic : Monomorphic.context;
  types : Intrinsics.types;
  bool : Ground.ty;
}

val make_monomorphic_context : Interface.Lookups.t -> Monomorphic.context
val make_context : env:Memory_layout.env -> Lookups.t -> context

type written = { spans : Source.Definition_span.t array; text : string }

type code = {
  definition : Path.t;
  written : written option;
  enclosing_impl : Path.t option;
  result : Types.result;
  substitution : Types.substitution;
  uses : Types.capability_set;
  has_defaults : bool;
  assumes_condition : bool;
}

val make_unwritten_code :
  definition:Path.t -> substitution:Types.substitution -> result:Types.result -> code

val read_written : context -> Resolve.Names.key -> written
val bind : Types.generic list -> Ground.argument list -> Types.substitution
val read_impl_interface : context -> Path.t -> Types.impl_interface
val read_trait_interface : context -> Path.t -> Types.trait_interface
val read_signature : context -> Path.t -> Types.signature
val make_code : context -> Path.t -> Ground.instantiation -> code
val panic_path : Path.t
val list_evidence : context -> Types.substitution -> Types.capability_set -> Path.t list
val has_panic_condition : Types.capability_set -> bool
val remove_panic_condition : Types.capability_set -> Types.capability_set
val classify_result : context -> Types.substitution -> Types.result -> Convention.result * bool
val list_lending_parameters : context -> Types.substitution -> Types.result -> Lowered.ty list

val make_c_signature :
  context ->
  Types.substitution ->
  parameters:(Language.Mode.t * Types.ty) list ->
  has_defaults:bool ->
  ?uses:Types.capability_set ->
  Types.result ->
  Lowered.signature * Convention.result

val has_defaults : Types.signature -> bool
val list_interface_parameters : Types.signature -> (Language.Mode.t * Types.ty) list
