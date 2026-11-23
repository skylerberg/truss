let raise_bug format = Compiler_bug.raise_bug ~stage:"Infer" format

let instantiate signatures (interface : Interface.Lookups.t) (target : Core.operand Core.target) :
    Types.capability_set =
  match (target, Signatures.find_declaration signatures interface target) with
  | (Function _ | Trait_method _), Some { signature; substitution; _ } ->
      Types.substitute_capabilities substitution signature.uses
  | Capability_method { capability; _ }, Some { signature; _ } ->
      Types.union_capabilities
        (Types.make_capability_set [ Types.make_capability capability ])
        signature.uses
  | (Function _ | Trait_method _ | Capability_method _), None ->
      raise_bug "a callee that names no declaration"
  | Intrinsic { operation; _ }, _ -> (Intrinsic_signatures.make_signature operation).uses
  | Indirect function_value, _ -> (
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

let compute signatures (interface : Interface.Lookups.t) ~list_bounds
    (target : Core.operand Core.target) : Types.capability_set =
  Interface.Impls.normalize_capabilities interface ~list_bounds
    (instantiate signatures interface target)

let make_callee signatures interface ~list_bounds (target : Core.operand Core.target) : Core.callee
    =
  { target; uses = compute signatures interface ~list_bounds target }

let make_call signatures interface ~list_bounds ~callee ~arguments ~lends : Core.call =
  {
    callee = make_callee signatures interface ~list_bounds callee;
    arguments;
    evaluation_order = List.init (List.length arguments) Fun.id;
    lends;
  }
