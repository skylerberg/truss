let show_generic (generic : Types.generic) =
  match generic.kind with
  | Type_generic [] -> generic.generic.name
  | Type_generic bounds ->
      generic.generic.name ^ ": " ^ String.concat " + " (List.map Types.show_trait bounds)
  | Value_generic -> generic.generic.name ^ ": UInt64"

let show_signature (signature : Types.signature) =
  Printf.sprintf "%s(%s)%s"
    (match signature.generics with
    | [] -> ""
    | generics -> "[" ^ String.concat ", " (List.map show_generic generics) ^ "]")
    (String.concat ", "
       ((match signature.receiver with
          | Some (Read, _) -> [ "self" ]
          | Some (Mut, _) -> [ "mut self" ]
          | Some (Own, _) -> [ "own self" ]
          | _ -> [])
       @ List.map
           (fun (parameter : Types.parameter_info) ->
             Printf.sprintf "%s: %s%s%s" parameter.name (Types.show_mode parameter.mode)
               (Types.show parameter.type_)
               (if parameter.has_default then " = ..." else ""))
           signature.parameters))
    (Types.show_output signature.output)

let list_types (signature : Types.signature) =
  let types = ref [] in
  ignore
    (Types.map_signature
       (fun type_ ->
         types := type_ :: !types;
         type_)
       signature);
  List.rev !types

let signatures_agree (expected : Types.signature) (written : Types.signature) =
  let sort_bounds (signature : Types.signature) =
    { signature with generics = Types.map_bounds (List.sort compare) signature.generics }
  in
  let erase_types (signature : Types.signature) =
    {
      (Types.map_signature (fun _ -> Types.unit) signature) with
      capability_parameters = List.sort compare signature.capability_parameters;
      uses = Types.no_capabilities;
      costs = [];
    }
  in
  let holds_error = Types.exists Types.is_error in
  let expected = sort_bounds expected and written = sort_bounds written in
  erase_types expected = erase_types written
  && List.for_all2
       (fun expected_type written_type ->
         holds_error expected_type || holds_error written_type
         || Types.equal expected_type written_type)
       (list_types expected) (list_types written)

type conformance = {
  implementation : Impls.implementation;
  shown_trait : string;
  list_impl_bounds : Types.parameter -> Types.trait_reference list;
  missing_associated : Diagnostic.in_definition list;
}

let compiler_implements (impl : Types.impl_interface) =
  Well_known.is Copyable impl.implements.trait
  || Well_known.is Plain impl.implements.trait
  || Well_known.is Storable impl.implements.trait

let find_conformance lookups ~list_bounds ~(trait_span : Source.Definition_span.t)
    (impl : Types.impl_interface) (trait_path : Syntax.path_type) =
  let shown_trait = Elaborator.show_path trait_path.path in
  if Types.is_built_in_capability (Capability impl.implements.trait) || compiler_implements impl
  then None
  else
    Option.map
      (fun (implementation : Impls.implementation) ->
        {
          implementation;
          shown_trait;
          list_impl_bounds = Impls.list_impl_bounds impl ~list_bounds;
          missing_associated =
            List.filter_map
              (fun (associated : Types.associated_type) ->
                if List.mem_assoc associated.associated_name impl.implements.associated then None
                else
                  Some
                    (Diagnostic.make ~code:(Types Missing_member) trait_span
                       (Printf.sprintf "This `impl` must give `type %s`, which `%s` declares."
                          associated.associated_name shown_trait)))
              implementation.trait.associated_types;
        })
      (Impls.find_implementation_of lookups impl)

let check_impl (state : Checking.state) (written_members : Syntax.impl_member Syntax.node list)
    (impl : Types.impl_interface) (trait_path : Syntax.path_type) =
  let lookups = state.lookups in
  if Well_known.is Panic impl.implements.trait then
    Checking.report state Implements_built_in_capability state.spans.(trait_path.id)
      "Nothing can implement `Panic`: no Truss code runs after a panic, and two `parallel` \
       branches that called one implementation with state would race."
  else if Well_known.is Run_forever impl.implements.trait then
    Checking.report state Implements_built_in_capability state.spans.(trait_path.id)
      "Nothing can implement `RunForever`, since a `provide` of it would let a function that does \
       not declare `RunForever` run forever."
  else if compiler_implements impl then
    Checking.report state Implements_built_in state.spans.(trait_path.id)
      (Printf.sprintf
         "The compiler implements `%s` from a type's fields; no `impl` of it can be written."
         (Elaborator.show_path trait_path.path))
  else
    match
      find_conformance lookups ~list_bounds:(Checking.list_bounds state)
        ~trait_span:state.spans.(trait_path.id) impl trait_path
    with
    | None -> ()
    | Some { implementation; shown_trait; list_impl_bounds; missing_associated } ->
        let trait = implementation.trait and substitution = implementation.substitution in
        let check_evidence_grants (span : Source.Definition_span.t) evidence =
          state.diagnostics :=
            List.map
              (Diagnostic.make ~code:(Capabilities Not_granted) span)
              (Grants.describe_missing_in_evidence lookups ~package:state.key.module_.package
                 ~list_bounds:list_impl_bounds evidence)
            @ !(state.diagnostics)
        in
        state.diagnostics := missing_associated @ !(state.diagnostics);
        let written_methods =
          List.filter_map
            (fun (member : Resolve.Names.key) ->
              match member.path with
              | Method { name; receiver; _ } -> Some (name, receiver)
              | _ -> None)
            (lookups.names.list_contained state.key)
        in
        List.iter
          (fun (method_ : Types.trait_method) ->
            let is_written =
              List.exists
                (fun (name, receiver) -> Types.is_implemented_by trait method_ ~name ~receiver)
                written_methods
            in
            if (not is_written) && not method_.provided then
              Checking.report state Missing_member state.spans.(trait_path.id)
                (Printf.sprintf "This `impl` must give `%s%s`, which `%s` declares."
                   method_.method_name
                   (show_signature
                      (Impls.normalize_signature_in_impl lookups
                         ~list_bounds:(Checking.list_bounds state) implementation
                         (Definition.read_method_signature lookups ~owner:impl.implements.trait
                            method_)))
                   shown_trait))
          trait.methods;
        List.iter
          (fun (associated : Types.associated_type) ->
            match List.assoc_opt associated.associated_name impl.implements.associated with
            | None -> ()
            | Some chosen ->
                List.iter
                  (fun bound ->
                    let bound = Types.substitute_trait substitution bound in
                    match
                      Impls.find_evidence lookups ~list_bounds:list_impl_bounds chosen bound
                    with
                    | None ->
                        Checking.report state Unsatisfied_bound state.spans.(trait_path.id)
                          (Printf.sprintf "`%s` declares `type %s: %s`, and `%s` is not one."
                             shown_trait associated.associated_name (Types.show_trait bound)
                             (Types.show chosen))
                    | Some evidence -> check_evidence_grants state.spans.(trait_path.id) evidence)
                  associated.associated_bounds)
          trait.associated_types;
        ignore
          (List.fold_left
             (fun defined (line : Syntax.impl_member Syntax.node) ->
               match line.kind with
               | Associated_definition (name, _) ->
                   if
                     not
                       (List.exists
                          (fun (associated : Types.associated_type) ->
                            associated.associated_name = name.text)
                          trait.associated_types)
                   then
                     Checking.report state Extra_member state.spans.(name.id)
                       (Printf.sprintf "`%s` declares no associated type `%s`." shown_trait
                          name.text);
                   defined
               | Capability_definition (name, _) ->
                   if not (List.mem name.text trait.associated_capabilities) then
                     Checking.report state Extra_member state.spans.(name.id)
                       (Printf.sprintf "`%s` declares no associated capability set `%s`."
                          shown_trait name.text)
                   else if List.mem name.text defined then
                     Checking.report state Extra_member state.spans.(name.id)
                       (Printf.sprintf
                          "This `impl` already defines `%s`. List every capability in one \
                           definition, separated by commas."
                          name.text);
                   name.text :: defined
               | Impl_member_error -> defined)
             [] written_members);
        List.iter
          (fun (required : Types.trait_reference) ->
            let required = Types.substitute_trait substitution required in
            match
              Impls.find_evidence lookups ~list_bounds:list_impl_bounds impl.for_type required
            with
            | None ->
                Checking.report state Missing_required_impl state.spans.(trait_path.id)
                  (Printf.sprintf "`%s` requires `%s`, which `%s` does not implement." shown_trait
                     (Types.show_trait required) (Types.show impl.for_type))
            | Some evidence -> check_evidence_grants state.spans.(trait_path.id) evidence)
          trait.requires;
        if (not trait.is_capability) && impl.impl_uses <> Types.no_capabilities then
          Checking.report state Impl_uses state.spans.(trait_path.id)
            "Only an `impl` of a capability can have `uses`. A trait's methods can use only the \
             capabilities the trait declares."

let check_impl_method (state : Checking.state) (name : Syntax.name) (receiver : Path.receiver)
    (written : Types.signature) (impl : Types.impl_interface) ~trait_span
    (trait_path : Syntax.path_type) =
  let list_bounds = Checking.list_bounds state in
  match find_conformance state.lookups ~list_bounds ~trait_span impl trait_path with
  | None -> ()
  | Some { implementation; shown_trait; _ } -> (
      let trait = implementation.trait in
      match Impls.find_implemented_method state.lookups state.key.path with
      | None ->
          Checking.report state Extra_member state.spans.(name.id)
            (Printf.sprintf "`%s` declares no method `%s` with this receiver." shown_trait name.text)
      | Some implemented ->
          if trait.is_capability && not (receiver = Read || receiver = Mut) then
            Checking.report state Wrong_receiver state.spans.(name.id)
              "A capability's implementation takes `self`, or `mut self` if it mutates its own \
               state."
          else
            let normalize_capabilities =
              Impls.normalize_capabilities_in_impl state.lookups ~list_bounds impl
            in
            let expected = Impls.make_expected_signature state.lookups ~written implemented in
            if
              not
                (signatures_agree expected
                   (Impls.normalize_signature_in_impl state.lookups ~list_bounds implementation
                      written))
            then
              Checking.report state Signature_mismatch state.spans.(name.id)
                (Printf.sprintf "`%s` must have the signature `%s%s` that `%s` declares." name.text
                   name.text (show_signature expected) shown_trait)
            else
              let allowed =
                if trait.is_capability then normalize_capabilities impl.impl_uses else expected.uses
              in
              if not (Types.is_capability_subset (normalize_capabilities written.uses) allowed) then
                Checking.report state Impl_uses state.spans.(name.id)
                  (if trait.is_capability then
                     Printf.sprintf
                       "`%s` implements a capability, so it can use only the capabilities its \
                        `impl` declares with `uses`."
                       name.text
                   else
                     Printf.sprintf "`%s` can use only the capabilities `%s` declares for it."
                       name.text shown_trait))
