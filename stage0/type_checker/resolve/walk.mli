type specification_function = Log | Power | Time | Calls

type target =
  | Binding
  | Local of Syntax.id
  | Law_parameter of int
  | Type_parameter of Types.parameter
  | Capability_parameter of Types.parameter
  | Value_parameter of Types.parameter
  | Definition of Names.named * Path.t
  | Variant of Path.t * string
  | Module of Path.module_
  | Field of string
  | Result_value
  | Old
  | Identical
  | Visited
  | Final
  | Specification_function of specification_function
  | Unknown of Diagnostic.reported

type bracket = Index | Type_arguments | Method_bracket
type section = Interface | Contract | Body

type section_names = {
  names : target option array;
  brackets : bracket option array;
  mutable diagnostics : Syntax.diagnostic list;
  mutable used_imports : string list;
}

type state

val create : Names.lookups -> Names.key -> size:int -> walked:section -> state
val names_of : state -> section -> section_names

val report :
  state ->
  ?fixes:Syntax.span Diagnostic.fix list ->
  Diagnostic.Code.resolve ->
  Syntax.span ->
  string ->
  unit

val definition :
  state -> path:Path.t -> ?container:Path.t * Syntax.definition -> Syntax.definition -> unit
