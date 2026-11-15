module Members : sig
  val trait_methods : Query.context -> Path.t -> string -> Types.trait_method list
  val trait_method : Query.context -> Path.t -> string -> Path.receiver -> Types.trait_method option
  val fields : Query.context -> Path.t -> Types.argument list -> Types.field list option
  val variants : Query.context -> Path.t -> Types.argument list -> Types.variant list option
  val shape : Query.context -> Path.t -> Types.shape option
end

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

type type_check_result = Body.type_check_result = {
  tables : tables;
  core : Core.t option;
  diagnostics : Syntax.diagnostic list;
  evidence_packages : Path.package list;
}

val type_check_result : (Resolve.Names.key, type_check_result option) Query.query
val diagnostics : Query.context -> Path.file -> Diagnostic.t list
val derived : (Path.t, Core.t option) Query.query
val core : (Resolve.Names.key, Core.t option) Query.query

type form_origin = Written of Resolve.Names.key | Generated | Inherited of Resolve.Names.key

val form_origin : (Path.t, (form_origin * Types.substitution) option) Query.query
val core_of_path : (Path.t, (Core.t * Types.substitution) option) Query.query
val evidence_packages : (Resolve.Names.key, Path.package list) Query.query
val clean_tables : Query.context -> Resolve.Names.key -> tables option
val is_clean : Query.context -> Resolve.Names.key -> bool
