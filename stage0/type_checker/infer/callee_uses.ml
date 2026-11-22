let raise_bug format = Compiler_bug.raise_bug ~stage:"Infer" format

let instantiate (interface : Interface.Lookups.t) (target : Core.operand Core.target) :
    Types.capability_set =
  match target with
  | Function { path; instantiation } -> (
      let signature =
        match Intrinsic.find_operation path with
        | Some operation -> Some (Intrinsic_signatures.make_signature operation)
        | None -> Interface.Impls.read_signature interface path
      in
      match signature with
      | Some signature ->
          Types.substitute_capabilities
            (Types.make_signature_substitution signature instantiation)
            signature.uses
      | None -> raise_bug "the callee `%s` has no signature" (Path.show path))
  | Trait_method { trait; name; receiver; self_type; instantiation; evidence } -> (
      let trait_interface = Interface.Definition.find_trait_interface interface trait.trait in
      match
        ( Option.bind trait_interface (Interface.Definition.find_method_of_trait ~name ~receiver),
          trait_interface )
      with
      | Some method_, Some trait_interface -> (
          let signature =
            Interface.Definition.read_method_signature interface ~owner:trait.trait method_
          in
          let uses =
            Types.substitute_capabilities
              (Types.combine_substitutions
                 (Types.make_trait_substitution trait_interface.trait_generics ~self:self_type trait)
                 (Types.make_signature_substitution signature instantiation))
              signature.uses
          in
          match evidence with
          | Dynamic ->
              Types.replace_capabilities
                (function
                  | Types.Capability_unless_values capability ->
                      Some (Types.make_capability_set [ capability ])
                  | _ -> None)
                uses
          | Impl _ | Bound -> uses)
      | _ -> raise_bug "`%s` has no method `%s`" (Path.show trait.trait) name)
  | Capability_method { capability; name } -> (
      match Interface.Definition.find_trait_method interface capability ~name ~receiver:Static with
      | Some method_ ->
          Types.union_capabilities
            (Types.make_capability_set [ Types.make_capability capability ])
            (Interface.Definition.read_method_signature interface ~owner:capability method_).uses
      | None -> raise_bug "`%s` has no method `%s`" (Path.show capability) name)
  | Intrinsic { operation; _ } -> (Intrinsic_signatures.make_signature operation).uses
  | Indirect function_value -> (
      let type_ =
        match function_value with
        | Value value | Place (Lent value | Temporary value) -> value.type_
        | Place
            ( Local { type_; _ }
            | Constant { type_; _ }
            | Field { type_; _ }
            | Element { type_; _ }
            | Range { type_; _ } ) ->
            type_
      in
      match type_ with
      | Types.Function { uses; _ } -> uses
      | Types.Error _ -> Types.no_capabilities
      | other -> raise_bug "a call through a value of type `%s`" (Types.show other))

let compute (interface : Interface.Lookups.t) ~list_bounds (target : Core.operand Core.target) :
    Types.capability_set =
  Interface.Impls.normalize_capabilities interface ~list_bounds (instantiate interface target)

let make_callee interface ~list_bounds (target : Core.operand Core.target) : Core.callee =
  { target; uses = compute interface ~list_bounds target }

let make_call interface ~list_bounds ~callee ~arguments ~lends : Core.call =
  {
    callee = make_callee interface ~list_bounds callee;
    arguments;
    evaluation_order = List.init (List.length arguments) Fun.id;
    lends;
  }
