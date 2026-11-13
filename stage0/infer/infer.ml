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
  evidence : Path.package list;
}

let type_check_result = Body.type_check_result
let derived = Derived.core
let show_resolution = Tables.show_resolution
let diagnostics = Body.diagnostics

let core =
  Query.query ~name:"core" ~phase:Phases.bodies ~show:Resolve.Names.show_key (fun database key ->
      Option.bind (Query.demand database type_check_result key) (fun (result : type_check_result) ->
          result.core))

let of_path ~written database (path : Path.t) =
  let written path =
    Option.bind (Query.demand database Interface.Summary.key path) (Query.demand database written)
  in
  match (written path, path) with
  | Some form, _ -> Some (form, [])
  | None, Method { owner = (Impl _ | Derived _) as owner; name; receiver } -> (
      match Query.demand database derived path with
      | Some form -> Some (form, [])
      | None ->
          Option.bind (Interface.Impls.impl_interface database owner)
            (fun (impl : Types.impl_interface) ->
              Option.bind (Interface.Impls.trait_substitution database owner) (fun substitution ->
                  Option.map
                    (fun form -> (form, substitution))
                    (written (Method { owner = impl.implements.trait; name; receiver })))))
  | None, _ -> None

let core_of_path =
  Query.query ~name:"core_of_path" ~phase:Phases.bodies ~show:Path.show (of_path ~written:core)

let callers_read_body database ~same_package (path : Path.t) =
  let provided =
    match path with
    | Method { owner; _ } ->
        Option.is_some (Query.demand database Interface.Environment.trait_interface owner)
    | _ -> false
  in
  let is_function_or_method_of_type =
    match path with
    | Top _ -> Interface.Summary.kind_of database path = Some Function
    | Method { owner = Top _ as owner; _ } -> Interface.Summary.kind_of database owner = Some Type
    | _ -> false
  in
  provided
  || (not is_function_or_method_of_type)
     && Interface.Summary.kind_of database path <> Some Theorem
     &&
     match Interface.Impls.signature database path with
     | Some signature -> Types.body_is_definition signature && same_package
     | None -> true

(* A form without the body of its function. *)
let without_body (form : Core.t) : Core.t =
  match form.definition with
  | Function { parameters; contract; body = Some _ } ->
      { definition = Function { parameters; contract; body = None } }
  | _ -> form

let specification =
  Query.query ~name:"specification" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key ->
      Option.map
        (fun form ->
          if callers_read_body database ~same_package:true key.path then form else without_body form)
        (Query.demand database core key))

let exported_specification =
  Query.query ~name:"exported_specification" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key ->
      Option.map
        (fun form ->
          if callers_read_body database ~same_package:false key.path then form
          else without_body form)
        (Query.demand database core key))

let specification_of_path =
  Query.query ~name:"specification_of_path" ~phase:Phases.bodies ~show:Path.show
    (of_path ~written:specification)

let exported_specification_of_path =
  Query.query ~name:"exported_specification_of_path" ~phase:Phases.bodies ~show:Path.show
    (of_path ~written:exported_specification)

let evidence_packages =
  Query.query ~name:"evidence_packages" ~phase:Phases.bodies ~show:Resolve.Names.show_key
    (fun database key ->
      match Query.demand database type_check_result key with
      | Some (result : type_check_result) -> result.evidence
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
         (* A method inside a type, trait, or impl that did not parse. *)
         match Query.demand database Interface.Environment.lowered_interface key with
         | Some { interface = Error_interface _; _ } -> false
         | _ -> true ->
      Some tables
  | _ -> None

let is_clean database key = Option.is_some (clean_tables database key)

module For_testing = struct
  let specification = specification
  let exported_specification = exported_specification
end
