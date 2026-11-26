type trait_method = {
  trait : Types.trait_reference;
  name : string;
  receiver : Path.receiver;
  self_type : Types.ty;
  evidence : Types.evidence;
}

type definition = {
  path : Path.t;
  contract : State.contract option;
  substitution_of : State.clauses -> Types.substitution;
  type_arguments : Types.argument list;
  declaration : Path.t;
  declaration_substitution : Types.substitution;
  trait_method : trait_method option;
  capability_method : (Path.t * string) option;
}

type target =
  | Definition of definition
  | Function_value
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }

type t = {
  target : target;
  group_member : Path.t option;
  lends : Language.Mode.t option;
  uses : Types.capability_set;
}

val resolve :
  State.context ->
  State.frame ->
  'operand Core.target ->
  lends:Language.Mode.t option ->
  uses:Types.capability_set ->
  t

val may_abort : State.context -> definition -> bool
val is_update_step : State.context -> t -> bool
val find_parameter_type : State.context -> t -> int -> Types.ty option

val find_callback :
  State.context ->
  State.frame ->
  t ->
  int ->
  known:(int * Logic.term) list ->
  (State.source * State.frame * Mir.callback) option
