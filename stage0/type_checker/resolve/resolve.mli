module Names = Names
module Parts = Parts
module Prelude = Prelude

type specification_function = Walk.specification_function = Log | Power | Time | Calls

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

type resolved = {
  names : target option array;
  brackets : bracket option array;
  used_imports : string list;
}

val sections : section list

val whole :
  ?sections:section list ->
  (section -> Names.key -> resolved option) ->
  Names.key ->
  resolved option

type head = {
  name : Syntax.name;
  target : target;
  type_arguments : Syntax.bracket_item list option;
}

val head : resolved -> Syntax.expression -> head option

val resolve :
  Names.lookups -> Names.key -> section -> (resolved, Syntax.diagnostic list) result option

val file_diagnostics :
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

val trait_header : Syntax.definition -> resolved -> trait_header option
