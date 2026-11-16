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

type checked = Body.checked = { form : Core.t; tables : tables; used_packages : Path.package list }

let check lookups (key : Resolve.Names.key) ~checks_body =
  Compiler_bug.run_while_doing ~stage:"Infer" (Resolve.Names.show_key key) (fun () ->
      try Body.check lookups key ~checks_body
      with Interface.Properties.Recursion_limit message ->
        let names = lookups.interface.names in
        Error
          [
            Diagnostic.make ~code:(Types Recursion_limit)
              (names.read_spans key).((names.read_definition key).id)
              message;
          ])

let check_contract lookups key = check lookups key ~checks_body:false

let check_body (lookups : Lookups.t) key =
  ignore (lookups.read_contract key);
  check lookups key ~checks_body:true

let derive_form = Derived.derive_form
let show_resolution = Tables.show_resolution

let statement_diverges (tables : tables) =
  State.diverges ~is_never:(fun (value : Syntax.expression) ->
      match tables.types.(value.id) with Some Types.Never -> true | _ -> false)

type form_origin =
  | Written of Resolve.Names.key
  | Derived of Resolve.Names.key
  | Inherited of Resolve.Names.key

let find_form_origin (interface : Interface.Lookups.t) ~is_derived (path : Path.t) =
  match (interface.names.find_key path, path) with
  | Some key, _ -> Some (Written key, [])
  | None, Method { owner = Derived { type_; _ }; _ } when is_derived path ->
      Option.map (fun type_key -> (Derived type_key, [])) (interface.names.find_key type_)
  | None, Method { owner = (Impl _ | Derived _) as owner; name; receiver } ->
      Option.bind (Interface.Definition.find_impl_interface interface owner)
        (fun (impl : Types.impl_interface) ->
          Option.bind (Interface.Impls.make_impl_substitution interface owner) (fun substitution ->
              Option.map
                (fun key -> (Inherited key, substitution))
                (interface.names.find_key
                   (Path.Method { owner = impl.implements.trait; name; receiver }))))
  | None, _ -> None
