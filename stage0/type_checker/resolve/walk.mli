module String_map : Map.S with type key = String.t

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
  | Yielded
  | Specification_function of specification_function
  | Unknown of Diagnostic.reported

type bracket = Index | Type_arguments | Method_bracket

type value =
  | Value_local of Syntax.id
  | Value_generic of Types.parameter
  | Value_field of string
  | Value_law_parameter of int

type specification = {
  active : bool;
  names_result : bool;
  cost_bound : bool;
  names_yielded : bool;
  elements : string list;
}

type scope = {
  values : (value * string) String_map.t;
  types : target String_map.t;
  specification : specification;
  lends : bool;
}

type state = {
  database : Query.context;
  file : Path.file;  (** The file the definition is written in, whose imports it reads *)
  names : target option array;
  brackets : bracket option array;
  mutable diagnostics : Syntax.diagnostic list;
  mutable holes : (Syntax.id * (string * value) list) list;
  mutable used_imports : string list;
}

val report :
  state ->
  ?fixes:Syntax.span Diagnostic.fix list ->
  Diagnostic.Code.resolve ->
  Syntax.span ->
  string ->
  unit

val definition :
  state -> path:Path.t -> ?container:Path.t * Syntax.definition -> Syntax.definition -> unit
