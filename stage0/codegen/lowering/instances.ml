let make_substitution (interface : Interface.Lookups.t) (path : Path.t)
    (signature : Types.signature) (instantiation : Ground.instantiation) =
  let declaring_trait =
    match path with
    | Method { owner = Top _ as owner; _ } -> (
        match Interface.Definition.find_trait_interface interface owner with
        | Some trait when not trait.is_capability -> Some (owner, trait)
        | Some _ | None -> None)
    | _ -> None
  in
  match declaring_trait with
  | Some (trait, { trait_generics; _ }) ->
      Monomorphic.make_declaration_substitution ~trait ~trait_generics signature instantiation
  | None -> Monomorphic.make_signature_substitution signature instantiation
