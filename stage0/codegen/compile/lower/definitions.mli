module S = Syntax
module T = Types
module Names = Resolve.Names
module Environment = Interface.Environment

val bug : ('a, unit, string, 'b) format4 -> 'a

type context = {
  database : Query.context;
  env : Memory_layout.env;
  glue : Glue.t;
  monomorphic : Monomorphic.context;
  types : Intrinsics.types;
  bool : Ground.ty;
  cursor_fields : (Ground.yielding -> (string * Memory_layout.member) list) ref;
  checks : bool;
  constant : (Path.t -> Lir.static_value option) ref;
}

val context : ?checks:bool -> Query.context -> Memory_layout.target -> context
val test_key : Path.t -> Instance.key

type code = {
  definition_key : Names.key;
  anchor : Path.t;
  within : Path.t option;
  text : string;
  result : T.result;
  substitution : T.substitution;
  uses : T.capability list;
  real : Path.t list;
  has_defaults : bool;
}

val demand : context -> ('a, 'b) Query.query -> 'a -> 'b

val unwritten :
  definition_key:Names.key ->
  anchor:Path.t ->
  substitution:T.substitution ->
  result:T.result ->
  code

val key_of : context -> Path.t -> Resolve.Names.key
val text_of : context -> Names.key -> string
val back : Ground.ty -> Types.ty
val bind : Types.generic list -> Ground.argument list -> Types.substitution
val impl_interface : context -> Path.t -> Types.impl_interface
val signature_of : context -> Path.t -> Types.signature
val written : context -> Path.t -> (Resolve.Names.key * Syntax.signature * Syntax.block) option
val code_of : context -> Path.t -> Ground.argument list -> code
val panic_path : Path.t
val evidence_for : context -> Types.substitution -> Types.capability list -> Path.t list
val result_of : context -> Types.substitution -> T.result -> Convention.result * bool

val lir_signature :
  context ->
  Types.substitution ->
  parameters:(T.mode * T.ty) list ->
  has_defaults:bool ->
  ?uses:Types.capability list ->
  T.result ->
  Lir.signature * Convention.result

val has_defaults : T.signature -> bool
val interface_parameters : T.signature -> (T.mode * T.ty) list
