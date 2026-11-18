let raise_bug format = Compiler_bug.raise_bug ~stage:"Backend" format

let resolve_call_node (interface : Interface.Lookups.t) (path : Path.t) =
  match path with
  | Method { owner; name; receiver } when not (Mir.Call_edges.defines interface.names owner path)
    -> (
      match Interface.Definition.find_impl_interface interface owner with
      | Some impl -> Path.Method { owner = impl.implements.trait; name; receiver }
      | None -> path)
  | _ -> path

let is_runtime_call (path : Path.t) =
  Well_known.is Write_fully path
  ||
  match path with
  | Method { owner = Top { module_; _ }; name = "new"; receiver = Static } ->
      Well_known.is_system_module module_
  | _ -> false

let list_bound_methods (interface : Interface.Lookups.t) path type_arguments =
  match Interface.Impls.read_signature interface path with
  | Some (signature : Types.signature) ->
      let rec pair_generics (generics : Types.generic list) (arguments : Ground.argument list) =
        match (generics, arguments) with
        | ( { kind = Type_generic bounds; _ } :: generics,
            Type (Named { path = head; _ }) :: arguments ) ->
            (bounds, head) :: pair_generics generics arguments
        | _ :: generics, _ :: arguments -> pair_generics generics arguments
        | _ -> []
      in
      List.concat_map
        (fun ((bounds : Types.trait_reference list), head) ->
          let traits =
            List.concat_map
              (fun (bound : Types.trait_reference) ->
                Mir.Call_edges.list_traits_with_required interface bound.trait)
              bounds
          in
          List.concat_map
            (fun package ->
              List.concat_map
                (Mir.Call_edges.list_impl_methods interface)
                (Mir.Call_edges.list_impls_for interface package traits
                   (Named { path = head; arguments = [] })))
            (List.sort_uniq Path.compare_package
               (Path.locate_package head :: List.map Path.locate_package traits)))
        (pair_generics signature.generics type_arguments)
  | None -> []

let check (interface : Interface.Lookups.t) ~find_call_edges (key : Lowered.Item.t) fragment =
  match key with
  | Code { path = caller; instantiation } -> (
      match find_call_edges (resolve_call_node interface caller) with
      | None -> ()
      | Some call_edges ->
          let allowed =
            call_edges
            @ List.concat_map
                (fun callee -> Option.value (find_call_edges callee) ~default:[])
                call_edges
            @ list_bound_methods interface caller instantiation.type_arguments
          in
          List.iter
            (fun (called : Lowered.Item.t) ->
              match called with
              | Code { path = callee; _ }
                when not
                       (is_runtime_call callee
                       || List.exists (Path.equal callee) allowed
                       || List.exists (Path.equal (resolve_call_node interface callee)) allowed) ->
                  raise_bug "%s calls %s, which is not among its call edges"
                    (Lowered.Item.to_string key) (Lowered.Item.to_string called)
              | _ -> ())
            (Emit_c.called fragment))
  | _ -> ()
