module Names : module type of struct
  include Names
end
with module Scope := Names.Scope

module Namespace = Namespace

module Parts : sig
  type part = Parts.part = Header | Body | Member_header of int | Member_body of int

  val find_syntax_error :
    spans:Source.Definition_span.t array ->
    syntax_errors:Source.Definition_span.t list ->
    Syntax.definition ->
    part ->
    Diagnostic.reported option
end

module Prelude : sig
  val find_type : string -> Path.module_ option
end

type specification_function = Walk.specification_function =
  | Log
  | Power
  | Call_cost of Language.Metric.t
  | Calls

type module_path = Walk.module_path = {
  module_ : Path.module_;
  imported : Path.module_ option;
  last_name : Syntax.name;
}

type target = Walk.target =
  | Binding
  | Local of Syntax.id
  | Law_parameter of int
  | Type_parameter of Types.parameter
  | Capability_parameter of Types.parameter
  | Value_parameter of Types.parameter
  | Definition of Names.named * Path.t
  | Variant of Path.t * string
  | Module of module_path
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
}

type resolution = { resolved : resolved; used_imports : string list }

val sections : section list
val merge : resolved list -> resolved
val list_referenced_definitions : resolved -> Path.t list

type head = {
  name : Syntax.name;
  target : target;
  type_arguments : Syntax.bracket_item list option;
}

val find_head : resolved -> Syntax.expression -> head option

val resolve :
  Names.lookups ->
  Names.key ->
  (section * (resolution, Catalog.description list) result option) list

val list_file_diagnostics :
  Names.lookups -> Path.file -> Syntax.file -> used:string list option -> Source.span Catalog.t list

type trait_header = {
  associated : string list;
  capabilities : string list;
  required : Path.t list;
  laws : string list;
}

val make_trait_header : Syntax.definition -> resolved -> trait_header option
