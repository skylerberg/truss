open Syntax
module Names = Resolve.Names
open Checking

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
  | _ -> Types.equal left right

and results_agree (left : Types.result) (right : Types.result) =
  match (left, right) with
  | Returns left, Returns right -> agrees left right
  | Lends (left_mode, left), Lends (right_mode, right) ->
      left_mode = right_mode && agrees left right
  | _ -> false

type conformance = {
  trait : Types.trait_interface;
  shown_trait : string;
  substitution : Types.substitution;
  impl_bounds : Types.parameter -> Types.trait_reference list;
  normalize : Types.ty -> Types.ty;
  normalize_capabilities : Types.capability_set -> Types.capability_set;
  missing_associated : (string * Diagnostic.in_definition) list;
}

let compiler_implements (impl : Types.impl_interface) =
  Well_known.is Copyable impl.implements.trait
  || Well_known.is Plain impl.implements.trait
  || Well_known.is Storable impl.implements.trait

let make_conformance lookups ~bounds ~(trait_span : Source.Definition_span.t)
    (impl : Types.impl_interface) (trait_path : path_type) =
  let shown_trait = Elaborate.show_path trait_path.path in
  let impl_bounds parameter =
    match
      List.find_opt
        (fun (generic : Types.generic) -> generic.generic = parameter)
        impl.impl_generics
    with
    | Some { kind = Type_generic bounds; _ } -> bounds
    | _ -> bounds parameter
  in
  if Well_known.is Panic impl.implements.trait || compiler_implements impl then None
  else
    Option.map
      (fun (trait : Types.trait_interface) ->
        let substitution =
          Properties.make_trait_substitution trait ~self:impl.for_type impl.implements
        in
        let missing_associated =
          List.filter_map
            (fun (associated : Types.associated_type) ->
              if List.mem_assoc associated.associated_name impl.implements.associated then None
              else
                Some
                  ( associated.associated_name,
                    Diagnostic.make ~code:(Types Missing_member) trait_span
                      (Printf.sprintf "This `impl` must give `type %s`, which `%s` declares."
                         associated.associated_name shown_trait) ))
            trait.associated_types
        in
        let normalize type_ =
          Types.map
            (function
              | Types.Projection { base; trait = projected; name }
                when Types.equal base impl.for_type -> (
                  match
                    ( List.assoc_opt name impl.implements.associated,
                      List.assoc_opt name missing_associated )
                  with
                  | Some fixed, _ -> Some fixed
                  | None, Some missing when Path.equal projected.trait impl.implements.trait ->
                      Some (Types.Error (Diagnostic.reported missing))
                  | None, _ ->
                      Impls.project_associated_type lookups ~bounds:impl_bounds impl.for_type
                        projected name)
              | _ -> None)
            (Types.substitute substitution type_)
        in
        let normalize_capabilities capabilities =
          Types.flat_map_capabilities
            (fun capability ->
              let set =
                match capability with
                | Types.Capability_projection { base; trait = projected; name }
                  when Types.equal base impl.for_type
                       && Path.equal projected.trait impl.implements.trait ->
                    Option.value ~default:Types.no_capabilities
                      (List.assoc_opt name impl.capability_sets)
                | capability ->
                    Impls.normalize_capabilities lookups ~bounds:impl_bounds
                      (Types.make_capability_set [ capability ])
              in
              (set :> Types.capability list))
            (Types.substitute_capabilities substitution capabilities)
        in
        {
          trait;
          shown_trait;
          substitution;
          impl_bounds;
          normalize;
          normalize_capabilities;
          missing_associated;
        })
      (Definition.read_trait_interface lookups impl.implements.trait)

let check_impl state (written_members : impl_member node list) (impl : Types.impl_interface)
    (trait_path : path_type) =
  let lookups = state.lookups in
  if Well_known.is Panic impl.implements.trait then
    report state Implements_panic state.spans.(trait_path.id)
      "Nothing can implement `Panic`, since a panic cannot be caught."
  else if compiler_implements impl then
    report state Implements_built_in state.spans.(trait_path.id)
      (Printf.sprintf
         "The compiler implements `%s` from a type's fields; no `impl` of it can be written."
         (Elaborate.show_path trait_path.path))
  else
    match
      make_conformance lookups ~bounds:(list_bounds state) ~trait_span:state.spans.(trait_path.id)
        impl trait_path
    with
    | None -> ()
    | Some { trait; shown_trait; substitution; impl_bounds; normalize; missing_associated; _ } ->
        let check_evidence_grants (span : Source.Definition_span.t) evidence =
          state.diagnostics :=
            List.map
              (Diagnostic.make ~code:(Capabilities Not_granted) span)
              (Grants.describe_missing_in_evidence lookups ~package:state.key.module_.package
                 ~bounds:impl_bounds evidence)
            @ !(state.diagnostics)
        in
        state.diagnostics := List.map snd missing_associated @ !(state.diagnostics);
        let written_methods =
          List.filter_map
            (fun (member : Names.key) ->
              match member.path with
              | Method { name; receiver; _ } -> Some (name, receiver)
              | _ -> None)
            (lookups.names.contained state.key)
        in
        List.iter
          (fun (method_ : Types.trait_method) ->
            let is_written =
              List.exists
                (fun (name, receiver) ->
                  name = method_.method_name
                  && (trait.is_capability || receiver = method_.method_receiver))
                written_methods
            in
            if (not is_written) && not method_.provided then
              report state Missing_member state.spans.(trait_path.id)
                (Printf.sprintf "This `impl` must give `%s%s`, which `%s` declares."
                   method_.method_name
                   (show_signature
                      (Types.map_signature normalize
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
                    match Impls.implements lookups ~bounds:impl_bounds chosen bound with
                    | None ->
                        report state Unsatisfied_bound state.spans.(trait_path.id)
                          (Printf.sprintf "`%s` declares `type %s: %s`, and `%s` is not one."
                             shown_trait associated.associated_name (Types.show_trait bound)
                             (Types.show chosen))
                    | Some evidence -> check_evidence_grants state.spans.(trait_path.id) evidence)
                  associated.associated_bounds)
          trait.associated_types;
        ignore
          (List.fold_left
             (fun defined (line : impl_member node) ->
               match line.kind with
               | Associated_definition (name, _) ->
                   if
                     not
                       (List.exists
                          (fun (associated : Types.associated_type) ->
                            associated.associated_name = name.text)
                          trait.associated_types)
                   then
                     report state Extra_member state.spans.(name.id)
                       (Printf.sprintf "`%s` declares no associated type `%s`." shown_trait
                          name.text);
                   defined
               | Capability_definition (name, _) ->
                   if not (List.mem name.text trait.associated_capabilities) then
                     report state Extra_member state.spans.(name.id)
                       (Printf.sprintf "`%s` declares no associated capability set `%s`."
                          shown_trait name.text)
                   else if List.mem name.text defined then
                     report state Extra_member state.spans.(name.id)
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
            match Impls.implements lookups ~bounds:impl_bounds impl.for_type required with
            | None ->
                report state Missing_required_impl state.spans.(trait_path.id)
                  (Printf.sprintf "`%s` requires `%s`, which `%s` does not implement." shown_trait
                     (Types.show_trait required) (Types.show impl.for_type))
            | Some evidence -> check_evidence_grants state.spans.(trait_path.id) evidence)
          trait.requires;
        if (not trait.is_capability) && impl.impl_uses <> Types.no_capabilities then
          report state Impl_uses state.spans.(trait_path.id)
            "Only an `impl` of a capability can have `uses`. A trait's methods can use only the \
             capabilities the trait declares."

let check_impl_method state (name : name) (receiver : Path.receiver) (written : Types.signature)
    (impl : Types.impl_interface) ~trait_span (trait_path : path_type) =
  match make_conformance state.lookups ~bounds:(list_bounds state) ~trait_span impl trait_path with
  | None -> ()
  | Some { trait; shown_trait; normalize; normalize_capabilities; _ } -> (
      let declared =
        List.find_opt
          (fun (method_ : Types.trait_method) ->
            method_.method_name = name.text
            && (trait.is_capability || method_.method_receiver = receiver))
          trait.methods
      in
      match declared with
      | None ->
          report state Extra_member state.spans.(name.id)
            (Printf.sprintf "`%s` declares no method `%s` with this receiver." shown_trait name.text)
      | Some declared ->
          let declared =
            Definition.read_method_signature state.lookups ~owner:impl.implements.trait declared
          in
          if trait.is_capability && not (receiver = Read || receiver = Mut) then
            report state Wrong_receiver state.spans.(name.id)
              "A capability's implementation takes `self`, or `mut self` if it mutates its own \
               state."
          else begin
            let written =
              {
                written with
                generics =
                  List.filteri
                    (fun index _ -> index >= List.length impl.impl_generics)
                    written.generics;
                uses = Types.subtract_capabilities written.uses impl.impl_uses;
              }
            in
            let expected =
              Types.map_signature normalize
                (Types.substitute_signature
                   (Option.value ~default:[]
                      (Types.make_substitution declared.generics
                         (Types.list_generic_arguments written.generics)))
                   declared)
            in
            let expected =
              if trait.is_capability then { expected with receiver = written.receiver }
              else expected
            in
            let expected = { expected with uses = normalize_capabilities expected.uses } in
            let parameters_agree =
              List.length expected.parameters = List.length written.parameters
              && List.for_all2
                   (fun (left : Types.parameter_info) (right : Types.parameter_info) ->
                     left.name = right.name && left.mode = right.mode
                     && agrees left.type_ right.type_)
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
            if
              not
                (parameters_agree && receivers_agree && generics_agree
                && results_agree expected.output written.output)
            then
              report state Signature_mismatch state.spans.(name.id)
                (Printf.sprintf "`%s` must have the signature `%s%s` that `%s` declares." name.text
                   name.text (show_signature expected) shown_trait)
            else
              let allowed = if trait.is_capability then Types.no_capabilities else expected.uses in
              if not (Types.is_capability_subset (normalize_capabilities written.uses) allowed) then
                report state Impl_uses state.spans.(name.id)
                  (if trait.is_capability then
                     Printf.sprintf
                       "`%s` implements a capability, so it can use only the capabilities its \
                        `impl` declares with `uses`."
                       name.text
                   else
                     Printf.sprintf "`%s` can use only the capabilities `%s` declares for it."
                       name.text shown_trait)
          end)
