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
  | Finished
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
  result : bool;
  cost_bound : bool;
  yielded : bool;
  finished : bool;
}

type scope = {
  values : (value * string) String_map.t;
  types : target String_map.t;
  specification : specification;
  hands_out : bool;
}

type state = {
  database : Query.context;
  module_ : Path.module_;
  names : target option array;
  brackets : bracket option array;
  mutable diagnostics : Diagnostic.t list;
  mutable holes : (Syntax.id * (string * value) list) list;
}

val report :
  state -> ?fixes:Diagnostic.fix list -> Diagnostic.Code.resolve -> Syntax.span -> string -> unit

val definition :
  state -> path:Path.t -> ?container:Path.t * Syntax.definition -> Syntax.definition -> unit
