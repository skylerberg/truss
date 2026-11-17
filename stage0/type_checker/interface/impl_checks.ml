let show_signature (signature : Types.signature) =
  Printf.sprintf "(%s)%s"
    (String.concat ", "
       ((match signature.receiver with
          | Some (Read, _) -> [ "self" ]
          | Some (Mut, _) -> [ "mut self" ]
          | Some (Own, _) -> [ "own self" ]
          | _ -> [])
       @ List.map
           (fun (parameter : Types.parameter_info) ->
             parameter.name ^ ": " ^ Types.show_mode parameter.mode ^ Types.show parameter.type_)
           signature.parameters))
    (Types.show_output signature.output)

let rec agrees (left : Types.ty) (right : Types.ty) =
  match (left, right) with
  | Types.Error _, _ | _, Types.Error _ -> true
  | Types.Named left, Types.Named right ->
      Path.equal left.path right.path
      && List.length left.arguments = List.length right.arguments
      && List.for_all2
           (fun left right ->
             match (left, right) with
             | Types.Type left, Types.Type right -> agrees left right
             | left, right -> left = right)
           left.arguments right.arguments
  | Types.Function left, Types.Function right ->
      List.length left.inputs = List.length right.inputs
      && List.for_all2
           (fun (left_mode, left) (right_mode, right) ->
             left_mode = right_mode && agrees left right)
           left.inputs right.inputs
      && agrees left.output right.output
      && (Types.has_capability_error left.uses
         || Types.has_capability_error right.uses
         || Types.has_same_clauses left right)
  | _ -> Types.equal left right

and results_agree (left : Types.result) (right : Types.result) =
  match (left, right) with
  | Returns left, Returns right -> agrees left right
  | Lends (left_mode, left), Lends (right_mode, right) ->
      left_mode = right_mode && agrees left right
  | _ -> false

type conformance = {
  implementation : Impls.implementation;
  shown_trait : string;
  list_impl_bounds : Types.parameter -> Types.trait_reference list;
  missing_associated : (string * Diagnostic.in_definition) list;
}

let compiler_implements (impl : Types.impl_interface) =
  Well_known.is Copyable impl.implements.trait
  || Well_known.is Plain impl.implements.trait
  || Well_known.is Storable impl.implements.trait

let find_conformance lookups ~list_bounds ~(trait_span : Source.Definition_span.t)
    (impl : Types.impl_interface) (trait_path : Syntax.path_type) =
  let shown_trait = Elaborator.show_path trait_path.path in
  if Well_known.is Panic impl.implements.trait || compiler_implements impl then None
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
                    ( associated.associated_name,
                      Diagnostic.make ~code:(Types Missing_member) trait_span
                        (Printf.sprintf "This `impl` must give `type %s`, which `%s` declares."
                           associated.associated_name shown_trait) ))
              implementation.trait.associated_types;
        })
      (Impls.find_implementation_of lookups impl)

let check_impl (state : Checking.state) (written_members : Syntax.impl_member Syntax.node list)
    (impl : Types.impl_interface) (trait_path : Syntax.path_type) =
  let lookups = state.lookups in
  if Well_known.is Panic impl.implements.trait then
    Checking.report state Implements_panic state.spans.(trait_path.id)
      "Nothing can implement `Panic`, since a panic cannot be caught."
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
        state.diagnostics := List.map snd missing_associated @ !(state.diagnostics);
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
                         ~list_bounds:(Checking.list_bounds state) ~missing_associated
                         implementation
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
  | Some { implementation; shown_trait; missing_associated; _ } -> (
      let trait = implementation.trait in
      match
        Definition.find_trait_method state.lookups impl.implements.trait ~name:name.text ~receiver
      with
      | None ->
          Checking.report state Extra_member state.spans.(name.id)
            (Printf.sprintf "`%s` declares no method `%s` with this receiver." shown_trait name.text)
      | Some declared ->
          let declared =
            Definition.read_method_signature state.lookups ~owner:impl.implements.trait declared
          in
          if trait.is_capability && not (receiver = Read || receiver = Mut) then
            Checking.report state Wrong_receiver state.spans.(name.id)
              "A capability's implementation takes `self`, or `mut self` if it mutates its own \
               state."
          else begin
            let normalize_capabilities =
              Impls.normalize_capabilities_in_impl state.lookups ~list_bounds impl
            in
            let normalize_function_types =
              Types.map_signature
                (Types.map ~map_capabilities:normalize_capabilities (fun _ -> None))
            in
            let written = normalize_function_types written in
            let written_generics = Types.list_generic_arguments written.generics in
            let capability_renaming =
              Types.make_capability_substitution declared.capability_parameters
                (Types.list_capability_arguments written.capability_parameters)
            in
            let expected =
              normalize_function_types
                (Impls.normalize_signature_in_impl state.lookups ~list_bounds ~missing_associated
                   implementation
                   (Types.substitute_signature
                      (if List.length declared.generics = List.length written_generics then
                         Types.combine_substitutions
                           (Types.make_substitution declared.generics written_generics)
                           capability_renaming
                       else capability_renaming)
                      declared))
            in
            let expected =
              if trait.is_capability then { expected with receiver = written.receiver }
              else expected
            in
            let parameters_agree =
              List.length expected.parameters = List.length written.parameters
              && List.for_all2
                   (fun (expected_parameter : Types.parameter_info)
                        (written_parameter : Types.parameter_info) ->
                     expected_parameter.name = written_parameter.name
                     && expected_parameter.mode = written_parameter.mode
                     && agrees expected_parameter.type_ written_parameter.type_)
                   expected.parameters written.parameters
            in
            let receivers_agree =
              Option.map fst expected.receiver = Option.map fst written.receiver
            in
            let generics_agree =
              List.length expected.generics = List.length written.generics
              && List.for_all2
                   (fun (expected_generic : Types.generic) (given_generic : Types.generic) ->
                     match (expected_generic.kind, given_generic.kind) with
                     | Type_generic expected_bounds, Type_generic given_bounds ->
                         List.for_all
                           (fun (bound : Types.trait_reference) ->
                             List.exists
                               (fun (allowed : Types.trait_reference) ->
                                 Path.equal allowed.trait bound.trait)
                               expected_bounds)
                           given_bounds
                     | left, right -> left = right)
                   expected.generics written.generics
            in
            let list_names (parameters : Types.parameter list) =
              List.sort String.compare
                (List.map (fun (parameter : Types.parameter) -> parameter.name) parameters)
            in
            let capability_parameters_agree =
              list_names declared.capability_parameters = list_names written.capability_parameters
            in
            if
              not
                (parameters_agree && receivers_agree && generics_agree
               && capability_parameters_agree
                && results_agree expected.output written.output)
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
                     (normalize_capabilities (Types.remove_divergence written.uses))
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
              else if Types.terminates written.uses then
                let followed =
                  Types.compute_missing_capabilities
                    ~required:(normalize_capabilities (Types.list_divergence written.uses))
                    ~available:expected.uses
                in
                match
                  List.find_map
                    (function
                      | Types.Divergence (Of_impl_method { self_type; trait; name; _ }) ->
                          Some (Types.show_impl_method self_type trait name)
                      | _ -> None)
                    (followed :> Types.capability list)
                with
                | Some followed_method ->
                    Checking.report state Impl_uses state.spans.(name.id)
                      (Printf.sprintf
                         "The `time` clause of `%s` follows %s, which may not terminate, and the \
                          `time` clause that `%s` declares for `%s` does not follow it."
                         name.text followed_method shown_trait name.text)
                | None when followed <> Types.no_capabilities ->
                    Checking.report state Impl_uses state.spans.(name.id)
                      (Printf.sprintf
                         "The `time` clause of `%s` names a function that may not terminate, and \
                          `%s` declares that `%s` terminates whatever it is passed."
                         name.text shown_trait name.text)
                | None -> ()
          end)
