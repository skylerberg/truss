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
  checks : bool;
      (** Whether the program checks, as it runs, each operation that is undefined or wrong where
          its precondition does not hold: an index, a slice, arithmetic, a shift, a call of the C
          library, and [unreachable]. No [requires] clause is evaluated. *)
  constant : Path.t -> Lowered.static_value option;
}

val context :
  ?checks:bool ->
  cursor_fields:(context -> Ground.yielding -> (string * Memory_layout.member) list) ->
  constant:(context -> Path.t -> Lowered.static_value option) ->
  Query.context ->
  Memory_layout.target ->
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

val demand : context -> ('a, 'b) Query.query -> 'a -> 'b

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
val panic_path : Path.t
val evidence_for : context -> Types.substitution -> Types.capability_set -> Path.t list
val result_of : context -> Types.substitution -> Types.result -> Convention.result * bool

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
