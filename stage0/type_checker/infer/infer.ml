module Lookups = Lookups

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

type checked = Body.checked = {
  form : Core.t;
  tables : tables;
  evidence_packages : Path.package list;
}

let check lookups (key : Resolve.Names.key) ~checks_body =
  Compiler_bug.while_doing ~stage:"Infer" (Resolve.Names.show_key key) (fun () ->
      Body.check lookups key ~checks_body)

let contract lookups key = check lookups key ~checks_body:false

let body (lookups : Lookups.t) key =
  ignore (lookups.contract key);
  check lookups key ~checks_body:true

let derived = Derived.form
let show_resolution = Tables.show_resolution

let statement_diverges (tables : tables) =
  State.diverges ~is_never:(fun (value : Syntax.expression) ->
      match tables.types.(value.id) with Some Types.Never -> true | _ -> false)

type form_origin = Written of Resolve.Names.key | Generated | Inherited of Resolve.Names.key

let form_origin (interface : Interface.Lookups.t) ~is_derived (path : Path.t) =
  match (interface.names.key path, path) with
  | Some key, _ -> Some (Written key, [])
  | None, Method { owner = Impl _ | Derived _; _ } when is_derived path -> Some (Generated, [])
  | None, Method { owner = (Impl _ | Derived _) as owner; name; receiver } ->
      Option.bind (Interface.Definition.read_impl_interface interface owner)
        (fun (impl : Types.impl_interface) ->
          Option.bind (Interface.Impls.make_impl_substitution interface owner) (fun substitution ->
              Option.map
                (fun key -> (Inherited key, substitution))
                (interface.names.key
                   (Path.Method { owner = impl.implements.trait; name; receiver }))))
  | None, _ -> None
