module Members = Members

type resolution = Tables.resolution =
  | Local_value of Syntax.id
  | Global of { path : Path.t; type_arguments : Types.argument list }
  | Field_access of { type_ : Types.ty; field : string }
  | Variant_value of { type_ : Types.ty; variant : string }
  | Type_name of Types.ty
  | Value_parameter of Types.parameter
  | Specification_value

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

let type_check_result = Body.type_check_result
let derived = Derived.core
let show_resolution = Tables.show_resolution
let diagnostics = Body.diagnostics

let core =
  Query.query ~name:"core" ~phase:Phases.bodies ~show:Resolve.Names.show_key (fun database key ->
      Option.bind (Query.demand database type_check_result key) (fun (result : type_check_result) ->
          result.core))

type form_origin = Written of Resolve.Names.key | Generated | Inherited of Resolve.Names.key

let form_origin =
  Query.query ~name:"form_origin" ~phase:Phases.bodies ~show:Path.show
    (fun database (path : Path.t) ->
      let checked path =
        Option.bind (Query.demand database Interface.Summary.key path) (fun key ->
            Option.map (fun _ -> key) (Query.demand database core key))
      in
      match (checked path, path) with
      | Some key, _ -> Some (Written key, [])
      | None, Method { owner = (Impl _ | Derived _) as owner; name; receiver } -> (
          match Query.demand database derived path with
          | Some _ -> Some (Generated, [])
          | None ->
              Option.bind (Interface.Impls.impl_interface database owner)
                (fun (impl : Types.impl_interface) ->
                  Option.bind (Interface.Impls.trait_substitution database owner)
                    (fun substitution ->
                      Option.map
                        (fun key -> (Inherited key, substitution))
                        (checked (Method { owner = impl.implements.trait; name; receiver })))))
      | None, _ -> None)

let core_of_path =
  Query.query ~name:"core_of_path" ~phase:Phases.bodies ~show:Path.show
    (fun database (path : Path.t) ->
      Option.bind (Query.demand database form_origin path) (fun (origin, substitution) ->
          Option.map
            (fun form -> (form, substitution))
            (match origin with
            | Written key | Inherited key -> Query.demand database core key
            | Generated -> Query.demand database derived path)))

let evidence_packages =
  Query.query ~name:"evidence_packages" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key ->
      match Query.demand database type_check_result key with
      | Some (result : type_check_result) -> result.evidence_packages
      | None -> [])

let clean_tables database key =
  match
    ( Query.demand database Resolve.Names.definition key,
      Query.demand database Resolve.resolved key,
      Query.demand database type_check_result key )
  with
  | Some definition, Some resolved, Some { tables; diagnostics = []; _ }
    when resolved.diagnostics = []
         && (not (Resolve.Parts.broken definition Header || Resolve.Parts.broken definition Body))
         &&
         match Query.demand database Interface.Environment.lowered_interface key with
         | Some { interface = Error_interface _; _ } -> false
         | _ -> true ->
      Some tables
  | _ -> None

let is_clean database key = Option.is_some (clean_tables database key)
