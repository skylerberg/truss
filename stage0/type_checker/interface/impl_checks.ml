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
          | Some (mode, _) -> [ Language.Mode.show_prefix mode ^ "self" ]
          | None -> [])
       @ List.map
           (fun (parameter : Types.parameter_info) ->
             Printf.sprintf "%s: %s%s%s" parameter.name
               (Language.Mode.show_prefix parameter.mode)
               (Types.show parameter.type_)
               (if parameter.has_default then " = ..." else ""))
           signature.parameters))
    (Types.show_output signature.output)

let has_default (signature : Types.signature) =
  List.exists (fun (parameter : Types.parameter_info) -> parameter.has_default) signature.parameters

let list_types (signature : Types.signature) =
  let types = ref [] in
  ignore
    (Types.map_signature
       (fun type_ ->
         types := type_ :: !types;
         type_)
       signature);
  List.rev !types

let find_unallowed_part ~(expected : Types.signature) ~(written : Types.signature) =
  List.find_map
    (fun (part : Types.modified) ->
      match Types.list_modified_fields expected part.position with
      | Some allowed
        when not
               (List.exists
                  (fun prefix -> Types.is_field_path_prefix prefix part.field_path)
                  allowed) ->
          Some (part.position, part.field_path)
      | Some _ | None -> None)
    written.modifies

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
      modifies = [];
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
  list_impl_bounds : Impls.bounds;
  missing_associated : string list;
}

let panics_beyond_value_condition ~(allowed : Types.capability_set) (written : Types.capability_set)
    =
  Types.has_capability (Capability_unless_values (Built_in Panic)) allowed
  && List.exists
       (fun capability ->
         Types.find_base capability = Built_in Panic
         && capability <> Types.Capability_unless_values (Built_in Panic))
       (Types.list_capabilities written)

let compiler_implements (impl : Types.impl_interface) =
  Well_known.is Copyable impl.implements.trait
  || Well_known.is Plain impl.implements.trait
  || Well_known.is Storable impl.implements.trait

let find_conformance lookups ~list_bounds (impl : Types.impl_interface)
    (trait_path : Syntax.path_type) =
  let shown_trait = Elaborator.show_path trait_path.path in
  if
    Option.is_some (Well_known.find_builtin_capability impl.implements.trait)
    || compiler_implements impl
  then None
  else
    Option.map
      (fun (implementation : Impls.implementation) ->
        {
          implementation;
          shown_trait;
          list_impl_bounds = Impls.Conformance.list_impl_bounds lookups impl ~list_bounds;
          missing_associated =
            List.filter_map
              (fun (associated : Types.associated_type) ->
                if List.mem_assoc associated.associated_name impl.implements.associated then None
                else Some associated.associated_name)
              implementation.trait.associated_types;
        })
      (Impls.Conformance.find_implementation_of lookups impl)

let check_impl (state : Checking.state) (written_members : Syntax.impl_member Syntax.node list)
    (impl : Types.impl_interface) (trait_path : Syntax.path_type) =
  let lookups = state.lookups in
  match Well_known.find_builtin_capability impl.implements.trait with
  | Some builtin_capability ->
      Checking.report state
        (Implements_built_in_capability
           { at = Written trait_path.id; capability = builtin_capability })
  | None when compiler_implements impl ->
      Checking.report state
        (Implements_built_in
           { at = Written trait_path.id; trait = Elaborator.show_path trait_path.path })
  | None -> (
      match find_conformance lookups ~list_bounds:(Checking.list_bounds state) impl trait_path with
      | None -> ()
      | Some { implementation; shown_trait; list_impl_bounds; missing_associated } ->
          let trait = implementation.trait and substitution = implementation.substitution in
          let at : Core.origin = Written trait_path.id in
          let check_evidence_grants evidence =
            state.diagnostics :=
              List.map
                (fun ((interface : Types.impl_interface), package, capability) ->
                  Catalog.Capabilities
                    (Not_granted
                       {
                         at;
                         granted =
                           Implemented_method
                             { implements = interface.implements; for_type = interface.for_type };
                         package;
                         capability;
                       }))
                (Grants.list_missing_in_impls lookups ~package:state.key.module_.package
                   (Grants.list_evidence_uses lookups ~list_bounds:list_impl_bounds evidence))
              @ !(state.diagnostics)
          in
          List.iter
            (fun name ->
              Checking.report state (Missing_associated_type { at; name; trait = shown_trait }))
            missing_associated;
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
                Checking.report state
                  (Missing_method
                     {
                       at = Written trait_path.id;
                       name = method_.method_name;
                       signature =
                         show_signature
                           (Impls.Conformance.normalize_signature_in_impl lookups
                              ~list_bounds:(Checking.list_bounds state) implementation
                              (Definition.read_method_signature lookups ~owner:impl.implements.trait
                                 method_));
                       trait = shown_trait;
                     }))
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
                          Checking.report state
                            (Associated_bound_unmet
                               {
                                 at = Written trait_path.id;
                                 trait = shown_trait;
                                 name = associated.associated_name;
                                 bound;
                                 chosen;
                               })
                      | Some evidence -> check_evidence_grants evidence)
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
                       Checking.report state
                         (Extra_associated
                            {
                              at = Written name.id;
                              trait = shown_trait;
                              name = name.text;
                              associated = Associated_type;
                            });
                     defined
                 | Capability_definition (name, _) ->
                     if not (List.mem name.text trait.associated_capabilities) then
                       Checking.report state
                         (Extra_associated
                            {
                              at = Written name.id;
                              trait = shown_trait;
                              name = name.text;
                              associated = Associated_capability_set;
                            })
                     else if List.mem name.text defined then
                       Checking.report state
                         (Capability_set_defined_twice { at = Written name.id; name = name.text });
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
                  Checking.report state
                    (Missing_required_impl
                       {
                         at = Written trait_path.id;
                         trait = shown_trait;
                         required;
                         for_type = impl.for_type;
                       })
              | Some evidence -> check_evidence_grants evidence)
            trait.requires;
          if (not trait.is_capability) && impl.impl_uses <> Types.no_capabilities then
            Checking.report state (Uses_on_trait_impl { at = Written trait_path.id });
          if
            (Types.is_well_known Slice impl.for_type
            || Types.is_well_known String_slice impl.for_type)
            && List.exists
                 (fun (method_ : Types.trait_method) -> method_.method_receiver = Instance Mut)
                 trait.methods
          then
            Checking.report state
              (Mut_self_for_slice
                 { at = Written trait_path.id; trait = shown_trait; for_type = impl.for_type }))

let list_callback_contracts (definition : Syntax.definition) =
  let parameters =
    match definition.kind with
    | Function { signature; _ } | Method_declaration signature -> signature.parameters
    | _ -> []
  in
  List.filter_map
    (fun (parameter : Syntax.parameter) ->
      match parameter.kind with
      | Named_parameter { name; type_ = { kind = Function_type { clauses; _ }; _ }; _ } ->
          Some
            ( name.text,
              List.filter
                (fun (clause : Syntax.clause) ->
                  match clause.kind with
                  | Requires _ | Ensures _ -> true
                  | Uses _ | Cost _ | Decreases _ | Modifies _ | Clause_error -> false)
                clauses )
      | Named_parameter _ | Self_parameter _ | Parameter_error -> None)
    parameters

let check_callback_contracts (state : Checking.state) (name : Syntax.name) ~shown_trait declaration
    =
  match state.lookups.names.find_key declaration with
  | None -> ()
  | Some key ->
      let written = list_callback_contracts state.definition in
      List.iter
        (fun (parameter, (clauses : Syntax.clause list)) ->
          let written_clauses = Option.value ~default:[] (List.assoc_opt parameter written) in
          if
            List.map Syntax_print.show_clause clauses
            <> List.map Syntax_print.show_clause written_clauses
          then
            Checking.report state
              (Callback_contract_mismatch
                 {
                   at = Written name.id;
                   name = name.text;
                   trait = shown_trait;
                   parameter;
                   declaration = key;
                   clauses =
                     List.map
                       (fun (clause : Syntax.clause) : Core.origin -> Written clause.id)
                       clauses;
                 }))
        (list_callback_contracts (state.lookups.names.read_definition key))

let check_impl_method (state : Checking.state) (name : Syntax.name) (receiver : Path.receiver)
    (written : Types.signature) (impl : Types.impl_interface) (trait_path : Syntax.path_type) =
  let list_bounds = Checking.list_bounds state in
  match find_conformance state.lookups ~list_bounds impl trait_path with
  | None -> ()
  | Some { implementation; shown_trait; _ } -> (
      let trait = implementation.trait in
      match Impls.find_implemented_method state.lookups state.key.path with
      | None -> (
          match
            List.find_opt
              (fun (restated : Types.restated_method) ->
                restated.restated_name = name.text && restated.restated_receiver = receiver)
              trait.restated
          with
          | Some restated ->
              Checking.report state
                (Restated_without_own
                   {
                     at = Written name.id;
                     trait = shown_trait;
                     declared_by = restated.declared_by;
                     name = name.text;
                     for_type = impl.for_type;
                   })
          | None ->
              Checking.report state
                (Undeclared_method { at = Written name.id; trait = shown_trait; name = name.text }))
      | Some implemented -> (
          if trait.is_capability && not (receiver = Instance Read || receiver = Instance Mut) then
            Checking.report state (Capability_method_receiver { at = Written name.id })
          else if
            (not trait.is_capability) && implemented.declared.provided
            && has_default
                 (Definition.read_method_signature state.lookups ~owner:impl.implements.trait
                    implemented.declared)
          then
            Checking.report state
              (Overridden_default { at = Written name.id; trait = shown_trait; name = name.text })
          else
            let normalize_capabilities =
              Impls.Conformance.normalize_capabilities_in_impl state.lookups ~list_bounds impl
            in
            let expected =
              Impls.Conformance.make_expected_signature state.lookups ~written implemented
            in
            if
              not
                (signatures_agree expected
                   (Impls.Conformance.normalize_signature_in_impl state.lookups ~list_bounds
                      implementation written))
            then
              Checking.report state
                (Impl_signature_mismatch
                   {
                     at = Written name.id;
                     name = name.text;
                     signature = show_signature expected;
                     trait = shown_trait;
                   })
            else
              let allowed =
                if trait.is_capability then normalize_capabilities impl.impl_uses else expected.uses
              in
              if
                not
                  (Types.is_capability_subset
                     ~implies:(Impls.implies_condition state.lookups ~list_bounds)
                     (normalize_capabilities written.uses)
                     allowed)
              then
                Checking.report state
                  (if trait.is_capability then
                     Uses_beyond_impl { at = Written name.id; name = name.text }
                   else
                     Uses_beyond_trait
                       { at = Written name.id; name = name.text; trait = shown_trait })
              else if
                (not trait.is_capability)
                && panics_beyond_value_condition ~allowed (normalize_capabilities written.uses)
              then
                Checking.report state
                  (Panic_beyond_condition
                     { at = Written name.id; name = name.text; trait = shown_trait })
              else
                match find_unallowed_part ~expected ~written with
                | Some (position, fields) ->
                    Checking.report state
                      (Impl_modifies
                         {
                           at = Written name.id;
                           name = name.text;
                           parameter = (Types.read_parameter_at written position).name;
                           fields;
                           trait = shown_trait;
                         })
                | None -> check_callback_contracts state name ~shown_trait implemented.declaration))
