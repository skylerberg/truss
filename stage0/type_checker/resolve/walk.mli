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

type value =
  | Value_local of Syntax.id
  | Value_generic of Types.parameter
  | Value_field of string
  | Value_law_parameter of int

type section_names = {
  names : target option array;
  brackets : bracket option array;
  mutable holes : (Syntax.id * (string * value) list) list;
  mutable diagnostics : Diagnostic.in_definition list;
  mutable used_imports : string list;
}

type state

val create :
  Names.lookups -> Names.key -> spans:Source.Definition_span.t array -> walked:section -> state

val lookup_section_names : state -> section -> section_names

val report :
  state ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  Diagnostic.Code.resolve ->
  Source.Definition_span.t ->
  string ->
  unit

val resolve_definition :
  state -> path:Path.t -> ?container:Path.t * Syntax.definition -> Syntax.definition -> unit
