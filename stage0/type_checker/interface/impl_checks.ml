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
  missing_associated : Diagnostic.in_definition list;
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

let find_conformance lookups ~list_bounds ~(trait_span : Source.Definition_span.t)
    (impl : Types.impl_interface) (trait_path : Syntax.path_type) =
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
                else
                  Some
                    (Diagnostic.make ~code:(Types Missing_member) trait_span
                       (Printf.sprintf "This `impl` must give `type %s`, which `%s` declares."
                          associated.associated_name shown_trait)))
              implementation.trait.associated_types;
        })
      (Impls.Conformance.find_implementation_of lookups impl)

let check_impl (state : Checking.state) (written_members : Syntax.impl_member Syntax.node list)
    (impl : Types.impl_interface) (trait_path : Syntax.path_type) =
  let lookups = state.lookups in
  match Well_known.find_builtin_capability impl.implements.trait with
  | Some builtin_capability ->
      Checking.report state Implements_built_in_capability state.spans.(trait_path.id)
        (match builtin_capability with
        | Panic ->
            "Nothing can implement `Panic`: no Truss code runs after a panic, and two `parallel` \
             branches that called one implementation with state would race."
        | Run_forever ->
            "Nothing can implement `RunForever`, since a `provide` of it would let a function that \
             does not declare `RunForever` run forever."
        | System ->
            "Nothing can implement `System`: the runtime grants it to the real implementations, \
             and a `provide` of it would let code that does not declare it reach the operating \
             system.")
  | None when compiler_implements impl ->
      Checking.report state Implements_built_in state.spans.(trait_path.id)
        (Printf.sprintf
           "The compiler implements `%s` from a type's fields; no `impl` of it can be written."
           (Elaborator.show_path trait_path.path))
  | None -> (
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
                (Grants.describe_missing_in_impls lookups ~package:state.key.module_.package
                   (Grants.list_evidence_uses lookups ~list_bounds:list_impl_bounds evidence))
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
                        (Impls.Conformance.normalize_signature_in_impl lookups
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
               capabilities the trait declares.";
          if
            (Types.is_well_known Slice impl.for_type
            || Types.is_well_known String_slice impl.for_type)
            && List.exists
                 (fun (method_ : Types.trait_method) -> method_.method_receiver = Instance Mut)
                 trait.methods
          then
            Checking.report state Mut_self_for_slice state.spans.(trait_path.id)
              (Printf.sprintf
                 "`%s` has a `mut self` method, so it cannot be implemented for `%s`. Generic code \
                  could call the method on a copy of a slice, and a copy views the same elements, \
                  so the write would reach elements that were lent read-only."
                 shown_trait (Types.show impl.for_type)))

let list_callback_contracts (definition : Syntax.definition) ~text ~spans =
  let parameters =
    match definition.kind with
    | Function { signature; _ } | Method_declaration signature -> signature.parameters
    | _ -> []
  in
  let quote (value : Syntax.expression) =
    String.concat " "
      (List.filter
         (fun word -> word <> "")
         (String.split_on_char ' '
            (String.map
               (function '\n' | '\t' -> ' ' | character -> character)
               (Source.Definition_span.quote text (Source.Definition_span.locate spans value.id)))))
  in
  List.filter_map
    (fun (parameter : Syntax.parameter) ->
      match parameter.kind with
      | Named_parameter { name; type_ = { kind = Function_type { clauses; _ }; _ }; _ } ->
          Some
            ( name.text,
              List.filter_map
                (fun (clause : Syntax.clause) ->
                  match clause.kind with
                  | Requires value -> Some ("requires " ^ quote value)
                  | Ensures value -> Some ("ensures " ^ quote value)
                  | Uses _ | Cost _ | Decreases _ | Modifies _ | Clause_error -> None)
                clauses )
      | Named_parameter _ | Self_parameter _ | Parameter_error -> None)
    parameters

let check_callback_contracts (state : Checking.state) (name : Syntax.name) ~shown_trait declaration
    =
  match state.lookups.names.find_key declaration with
  | None -> ()
  | Some key ->
      let declared =
        list_callback_contracts
          (state.lookups.names.read_definition key)
          ~text:(state.lookups.names.read_text key)
          ~spans:(state.lookups.names.read_spans key)
      and written =
        list_callback_contracts state.definition
          ~text:(state.lookups.names.read_text state.key)
          ~spans:state.spans
      in
      List.iter
        (fun (parameter, clauses) ->
          let written_clauses = Option.value ~default:[] (List.assoc_opt parameter written) in
          if clauses <> written_clauses then
            Checking.report state Signature_mismatch state.spans.(name.id)
              (Printf.sprintf
                 "`%s` must state the callback contract that `%s` declares for `%s`: %s. A caller \
                  through `%s` relies on that contract, so the method's own callback contract is \
                  that one."
                 name.text shown_trait parameter
                 (match clauses with
                 | [] -> "no `requires` and no `ensures`"
                 | clauses ->
                     String.concat ", " (List.map (fun clause -> "`" ^ clause ^ "`") clauses))
                 shown_trait))
        declared

let check_impl_method (state : Checking.state) (name : Syntax.name) (receiver : Path.receiver)
    (written : Types.signature) (impl : Types.impl_interface) ~trait_span
    (trait_path : Syntax.path_type) =
  let list_bounds = Checking.list_bounds state in
  match find_conformance state.lookups ~list_bounds ~trait_span impl trait_path with
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
              Checking.report state Extra_member state.spans.(name.id)
                (Printf.sprintf
                   "`%s` restates `%s.%s` and declares no method of its own by that name. Give \
                    `%s` in the `impl` of `%s` for `%s`."
                   shown_trait (Path.show restated.declared_by) name.text name.text
                   (Path.show restated.declared_by) (Types.show impl.for_type))
          | None ->
              Checking.report state Extra_member state.spans.(name.id)
                (Printf.sprintf "`%s` declares no method `%s` with this receiver." shown_trait
                   name.text))
      | Some implemented -> (
          if trait.is_capability && not (receiver = Instance Read || receiver = Instance Mut) then
            Checking.report state Wrong_receiver state.spans.(name.id)
              "A capability's implementation takes `self`, or `mut self` if it mutates its own \
               state."
          else if
            (not trait.is_capability) && implemented.declared.provided
            && has_default
                 (Definition.read_method_signature state.lookups ~owner:impl.implements.trait
                    implemented.declared)
          then
            Checking.report state Overridden_method_default state.spans.(name.id)
              (Printf.sprintf
                 "`%s` declares `%s` with a default, so no `impl` overrides it. A call that omits \
                  the argument reads the default from the declaration in `%s`, and this method \
                  would be a second declaration that shows none."
                 shown_trait name.text shown_trait)
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
              Checking.report state Signature_mismatch state.spans.(name.id)
                (Printf.sprintf "`%s` must have the signature `%s%s` that `%s` declares." name.text
                   name.text (show_signature expected) shown_trait)
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
                Checking.report state Impl_uses state.spans.(name.id)
                  (if trait.is_capability then
                     Printf.sprintf
                       "`%s` implements a capability, so it can use only the capabilities its \
                        `impl` declares with `uses`."
                       name.text
                   else
                     Printf.sprintf "`%s` can use only the capabilities `%s` declares for it."
                       name.text shown_trait)
              else if
                (not trait.is_capability)
                && panics_beyond_value_condition ~allowed (normalize_capabilities written.uses)
              then
                Checking.report state Impl_uses state.spans.(name.id)
                  (Printf.sprintf
                     "`%s` declares `%s` with `uses Panic unless` a condition, and this `%s` uses \
                      `Panic` without one, so it could panic where that condition holds. Declare \
                      `uses Panic unless` a condition that `%s`'s implies."
                     shown_trait name.text name.text shown_trait)
              else
                match find_unallowed_part ~expected ~written with
                | Some (position, field_path) ->
                    let parameter = (Types.read_parameter_at written position).name in
                    Checking.report state Impl_modifies state.spans.(name.id)
                      (Printf.sprintf
                         "`%s` names `%s` in `modifies`, and the `modifies` clause of `%s.%s` \
                          names no part that holds it. An implementation changes only the parts \
                          that its trait's method names."
                         name.text
                         (String.concat "." (parameter :: field_path))
                         shown_trait name.text)
                | None -> check_callback_contracts state name ~shown_trait implemented.declaration))
