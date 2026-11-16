module Lookups = Lookups

type resolution = Tables.resolution =
  | Local_value of Syntax.id
  | Global of { path : Path.t; type_arguments : Types.argument list }
  | Field_access of { type_ : Types.ty; field : string }
  | Variant_value of { type_ : Types.ty; variant : string }
  | Type_name of Types.ty
  | Value_parameter of Types.parameter
  | Specification_value

val show_resolution : resolution -> string

type tables = Tables.published = {
  types : Types.ty option array;
  local_types : Types.ty option array;
  resolutions : resolution option array;
  callees : Path.t option array;
}

val statement_diverges : tables -> Syntax.statement -> bool

type checked = Body.checked = {
  form : Core.t;
  tables : tables;
  used_packages : Path.package list;
  places_without_own : Core.origin list;
}

val check_contract :
  Lookups.t -> Resolve.Names.key -> (checked, Diagnostic.in_definition list) result

val check_body : Lookups.t -> Resolve.Names.key -> (checked, Diagnostic.in_definition list) result
val derive_form : Lookups.t -> Path.t -> Core.t option

type form_origin =
  | Written of Resolve.Names.key
  | Derived of Resolve.Names.key
  | Inherited of Resolve.Names.key

val find_form_origin :
  Interface.Lookups.t ->
  is_derived:(Path.t -> bool) ->
  Path.t ->
  (form_origin * Types.substitution) option
