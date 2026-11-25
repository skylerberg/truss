module Lookups = Lookups

type resolution = Tables.resolution =
  | Local_value of Syntax.id
  | Global of { path : Path.t; instantiation : Types.instantiation }
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
  places_without_keyword : (Syntax.id * Language.Mode.t) list;
  mode_keywords : Core.mode_keyword list;
  uses_run_forever : bool;
}

val check_contract : Lookups.t -> Resolve.Names.key -> (checked, Catalog.diagnostic list) result
val check_body : Lookups.t -> Resolve.Names.key -> (checked, Catalog.diagnostic list) result
val derive_form : Lookups.t -> Path.t -> Core.t option
val is_derived_method : Path.t -> bool

module For_testing : sig
  val is_written_expression : Syntax.expression -> Core.kind -> bool
end
