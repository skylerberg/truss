let raise_bug format = Compiler_bug.raise_bug ~stage:"Infer" format

let compute (interface : Interface.Lookups.t) ~list_bounds (callee : Core.callee) :
    Types.capability_set =
  let normalize = Interface.Impls.normalize_capabilities interface ~list_bounds in
  let read_method_divergence ~owner ~name ~receiver substitute =
    match Interface.Definition.find_trait_method interface owner ~name ~receiver with
    | Some method_ ->
        Types.list_divergence
          (substitute (Interface.Definition.read_method_signature interface ~owner method_))
    | None -> raise_bug "`%s` has no method `%s`" (Path.show owner) name
  in
  match callee with
  | Function { path; instantiation } -> (
      let signature =
        match Intrinsic.find_operation path with
        | Some operation -> Some (Intrinsic_signatures.make_signature operation)
        | None -> Interface.Impls.read_signature interface path
      in
      match signature with
      | Some signature ->
          normalize
            (Types.substitute_capabilities
               (Types.make_signature_substitution signature instantiation)
               signature.uses)
      | None -> raise_bug "the callee `%s` has no signature" (Path.show path))
  | Trait_method { trait; name; receiver; self_type; instantiation; evidence } -> (
      match
        ( Interface.Definition.find_trait_method interface trait.trait ~name ~receiver,
          Interface.Definition.find_trait_interface interface trait.trait )
      with
      | Some method_, Some trait_interface -> (
          let signature =
            Interface.Definition.read_method_signature interface ~owner:trait.trait method_
          in
          let declared =
            normalize
              (Types.substitute_capabilities
                 (Types.combine_substitutions
                    (Interface.Properties.make_trait_substitution trait_interface ~self:self_type
                       trait)
                    (Types.make_signature_substitution signature instantiation))
                 signature.uses)
          in
          match evidence with
          | Impl { impl; substitution } -> (
              match
                Interface.Impls.read_signature interface (Method { owner = impl; name; receiver })
              with
              | Some implemented ->
                  let own_generics =
                    List.filter
                      (fun (generic : Types.generic) ->
                        Option.is_none (Types.find_argument generic.generic substitution))
                      implemented.generics
                  in
                  Types.union_capabilities
                    (Types.remove_divergence declared)
                    (Types.list_divergence
                       (normalize
                          (Types.substitute_capabilities
                             (Types.combine_substitutions substitution
                                (Types.combine_substitutions
                                   (Types.make_substitution own_generics
                                      instantiation.type_arguments)
                                   (Types.make_capability_substitution
                                      implemented.capability_parameters
                                      instantiation.capability_arguments)))
                             implemented.uses)))
              | None -> declared)
          | Bound | Dynamic -> declared)
      | _ -> raise_bug "`%s` has no method `%s`" (Path.show trait.trait) name)
  | Capability_method { capability; name } ->
      Types.union_capabilities
        (Types.make_capability_set [ Types.Capability capability ])
        (read_method_divergence ~owner:capability ~name ~receiver:Static
           (fun (signature : Types.signature) -> signature.uses))
  | Intrinsic _ -> Types.no_capabilities
  | Indirect function_value -> (
      let type_ =
        match function_value with
        | Value value | Place (Lent value | Temporary value) -> value.type_
        | Place (Local { type_; _ } | Constant { type_; _ } | Field { type_; _ }) -> type_
      in
      match type_ with
      | Types.Function { uses; _ } -> uses
      | Types.Error _ -> Types.no_capabilities
      | other -> raise_bug "a call through a value of type `%s`" (Types.show other))

let make_call interface ~list_bounds ~(callee : Core.callee) ~arguments ~lends : Core.call =
  { callee; arguments; lends; uses = compute interface ~list_bounds callee }
