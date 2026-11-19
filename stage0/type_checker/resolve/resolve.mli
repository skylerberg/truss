module Names : module type of struct
  include Names
end
with module Scope := Names.Scope

module Namespace = Namespace

module Parts : sig
  type part = Parts.part = Header | Body | Member_header of int | Member_body of int
end

module Prelude : sig
  val find_type : string -> Path.module_ option
end

type specification_function = Walk.specification_function =
  | Log
  | Power
  | Call_cost of Language.Metric.t
  | Calls

type target = Walk.target =
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

type bracket = Walk.bracket = Index | Type_arguments | Method_bracket
type section = Walk.section = Interface | Contract | Body

type value = Walk.value =
  | Value_local of Syntax.id
  | Value_generic of Types.parameter
  | Value_field of string
  | Value_law_parameter of int

type resolved = {
  names : target option array;
  brackets : bracket option array;
  holes : (Syntax.id * (string * value) list) list;
  used_imports : string list;
}

val sections : section list
val merge : resolved list -> resolved

type head = {
  name : Syntax.name;
  target : target;
  type_arguments : Syntax.bracket_item list option;
}

val find_head : resolved -> Syntax.expression -> head option

val resolve :
  Names.lookups -> Names.key -> section -> (resolved, Diagnostic.in_definition list) result option

val list_file_diagnostics :
  Names.lookups ->
  Path.file ->
  Syntax.file ->
  text:string ->
  used:string list option ->
  Diagnostic.t list

type trait_header = {
  associated : string list;
  capabilities : string list;
  required : Path.t list;
  laws : string list;
}

val make_trait_header : Syntax.definition -> resolved -> trait_header option
