module Path_table = Hashtbl.Make (Path)

type t = Types.signature option Path_table.t

let create () : t = Path_table.create 16

let read (signatures : t) (interface : Interface.Lookups.t) path =
  match Path_table.find_opt signatures path with
  | Some signature -> signature
  | None ->
      let signature = Interface.Impls.read_signature interface path in
      Path_table.replace signatures path signature;
      signature

let read_of_method signatures interface ~owner (method_ : Types.trait_method) =
  let path =
    Path.Method { owner; name = method_.method_name; receiver = method_.method_receiver }
  in
  match read signatures interface path with
  | Some signature -> signature
  | None ->
      Compiler_bug.raise_bug ~stage:"Infer" "the method `%s` has no signature" (Path.show path)

type declaration = {
  definition : Path.t;
  signature : Types.signature;
  substitution : Types.substitution;
}

let find_declaration signatures (interface : Interface.Lookups.t) (target : _ Core.target) :
    declaration option =
  let raise_bug format = Compiler_bug.raise_bug ~stage:"Infer" format in
  match target with
  | Function { path; instantiation } -> (
      let signature =
        match Intrinsic.find_operation path with
        | Some operation -> Some (Intrinsic_signatures.make_signature operation)
        | None -> read signatures interface path
      in
      match signature with
      | Some signature ->
          Some
            {
              definition = path;
              signature;
              substitution = Types.make_signature_substitution signature instantiation;
            }
      | None -> raise_bug "the callee `%s` has no signature" (Path.show path))
  | Trait_method { trait; name; receiver; self_type; instantiation; _ } -> (
      let trait_interface = Interface.Definition.find_trait_interface interface trait.trait in
      match
        ( Option.bind trait_interface (Interface.Definition.find_method_of_trait ~name ~receiver),
          trait_interface )
      with
      | Some method_, Some trait_interface ->
          let signature = read_of_method signatures interface ~owner:trait.trait method_ in
          Some
            {
              definition =
                Path.Method
                  {
                    owner = trait.trait;
                    name = method_.method_name;
                    receiver = method_.method_receiver;
                  };
              signature;
              substitution =
                Types.combine_substitutions
                  (Types.make_trait_substitution trait_interface.trait_generics ~self:self_type
                     trait)
                  (Types.make_signature_substitution signature instantiation);
            }
      | _ -> raise_bug "`%s` has no method `%s`" (Path.show trait.trait) name)
  | Capability_method { capability; name } -> (
      match Interface.Definition.find_trait_method interface capability ~name ~receiver:Static with
      | Some method_ ->
          Some
            {
              definition = Path.make_capability_method capability name;
              signature = read_of_method signatures interface ~owner:capability method_;
              substitution = Types.no_substitution;
            }
      | None -> raise_bug "`%s` has no method `%s`" (Path.show capability) name)
  | Intrinsic _ | Indirect _ -> None
