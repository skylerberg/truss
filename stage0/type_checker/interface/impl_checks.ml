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

(* Whether two types agree, where an error on either side agrees with
   anything, since it was reported already. *)
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
      && agrees_result left.output right.output
  | _ -> Types.equal left right

and agrees_result (left : Types.result) (right : Types.result) =
  match (left, right) with
  | Returns left, Returns right -> agrees left right
  | Lends (left_mode, left), Lends (right_mode, right) ->
      left_mode = right_mode && agrees left right
  | _ -> false

(* An [impl]'s view of its trait: the trait, the substitution for the
   trait's [Self] and parameters, and the trait's types under that
   substitution, in which [Self] is the [impl]'s type and each associated
   type of [Self] is the definition given by this [impl] or by the [impl] of
   a required trait. An associated type that the trait declares and the
   [impl] does not define is an error wherever a method's signature mentions
   it. The [impl] itself reports it, once. The trait's sets of capabilities
   are read in the same way: each associated capability set of [Self] is the
   set that this [impl] defines. *)
type view = {
  trait : Types.trait_interface;
  shown_trait : string;
  substitution : Types.substitution;
  impl_bounds : Types.parameter -> Types.trait_reference list;
  normalize : Types.ty -> Types.ty;
  normalize_capabilities : Types.capability_set -> Types.capability_set;
  missing_associated : (string * Syntax.diagnostic) list;
}

let compiler_implements (impl : Types.impl_interface) =
  Path.equal impl.implements.trait Properties.copyable_trait
  || Path.equal impl.implements.trait Properties.plain_trait
  || Path.equal impl.implements.trait Properties.storable_trait

let impl_view database ~bounds (impl : Types.impl_interface) (trait_path : path_type) =
  let shown_trait = Names.spell_path trait_path.path in
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
          Properties.trait_substitution trait ~self:impl.for_type impl.implements
        in
        let missing_associated =
          List.filter_map
            (fun (associated : Types.associated_type) ->
              if List.mem_assoc associated.associated_name impl.implements.associated then None
              else
                Some
                  ( associated.associated_name,
                    Diagnostic.make ~code:(Types Missing_member) trait_path.span
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
                      Impls.associated_type database ~bounds:impl_bounds impl.for_type projected
                        name)
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
                    Impls.normalize_capabilities database ~bounds:impl_bounds
                      (Types.capability_set [ capability ])
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
      (Query.demand database Environment.trait_interface impl.implements.trait)

(* The checks of an [impl]'s own header: it defines every member that its
   trait requires, and its type implements the traits that the trait
   requires. Each method written inside it is checked against the trait's
   method as a definition of its own. *)
let check_impl state (written_members : impl_member line list) (impl : Types.impl_interface)
    (trait_path : path_type) =
  let database = state.database in
  if Well_known.is Panic impl.implements.trait then
    report state Implements_panic trait_path.span
      "Nothing can implement `Panic`, since a panic cannot be caught."
  else if compiler_implements impl then
    report state Implements_built_in trait_path.span
      (Printf.sprintf
         "The compiler implements `%s` from a type's fields; no `impl` of it can be written."
         (Names.spell_path trait_path.path))
  else
    match impl_view database ~bounds:(bounds state) impl trait_path with
    | None -> ()
    | Some { trait; shown_trait; substitution; impl_bounds; normalize; missing_associated; _ } ->
        let check_evidence_grants (span : span) evidence =
          state.diagnostics <-
            List.map
              (Diagnostic.make ~code:(Capabilities Not_granted) span)
              (Grants.evidence_messages database ~package:state.key.module_.package
                 ~bounds:impl_bounds evidence)
            @ state.diagnostics
        in
        state.diagnostics <- List.map snd missing_associated @ state.diagnostics;
        let written_methods =
          List.filter_map
            (fun (member : Names.key) ->
              match member.path with
              | Method { name; receiver; _ } -> Some (name, receiver)
              | _ -> None)
            (Query.demand database Names.contained state.key)
        in
        (* The [impl] must define every method without a body. For a
           capability that is every method, because a capability's methods
           have no bodies. *)
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
              report state Missing_member trait_path.span
                (Printf.sprintf "This `impl` must give `%s%s`, which `%s` declares."
                   method_.method_name
                   (show_signature (Types.map_signature normalize method_.method_signature))
                   shown_trait))
          trait.methods;
        List.iter
          (fun (associated : Types.associated_type) ->
            match List.assoc_opt associated.associated_name impl.implements.associated with
            | None -> ()
            | Some chosen ->
                (* Each associated type that the [impl] defines must satisfy
                   the bounds that the trait declares for it. *)
                List.iter
                  (fun bound ->
                    let bound = Types.substitute_trait substitution bound in
                    match Impls.implements database ~bounds:impl_bounds chosen bound with
                    | None ->
                        report state Unsatisfied_bound trait_path.span
                          (Printf.sprintf "`%s` declares `type %s: %s`, and `%s` is not one."
                             shown_trait associated.associated_name (Types.show_trait bound)
                             (Types.show chosen))
                    | Some evidence -> check_evidence_grants trait_path.span evidence)
                  associated.associated_bounds)
          trait.associated_types;
        ignore
          (List.fold_left
             (fun defined (line : impl_member line) ->
               match line.kind with
               | Associated_definition (name, _) ->
                   if
                     not
                       (List.exists
                          (fun (associated : Types.associated_type) ->
                            associated.associated_name = name.text)
                          trait.associated_types)
                   then
                     report state Extra_member name.span
                       (Printf.sprintf "`%s` declares no associated type `%s`." shown_trait
                          name.text);
                   defined
               | Capability_definition (name, _) ->
                   if not (List.mem name.text trait.associated_capabilities) then
                     report state Extra_member name.span
                       (Printf.sprintf "`%s` declares no associated capability set `%s`."
                          shown_trait name.text)
                   else if List.mem name.text defined then
                     report state Extra_member name.span
                       (Printf.sprintf
                          "This `impl` already defines `%s`. List every capability in one \
                           definition, separated by commas."
                          name.text);
                   name.text :: defined
               | Impl_member_error -> defined)
             [] written_members);
        (* The traits a trait requires are implemented for the same type. *)
        List.iter
          (fun (required : Types.trait_reference) ->
            let required = Types.substitute_trait substitution required in
            match Impls.implements database ~bounds:impl_bounds impl.for_type required with
            | None ->
                report state Missing_required_impl trait_path.span
                  (Printf.sprintf "`%s` requires `%s`, which `%s` does not implement." shown_trait
                     (Types.show_trait required) (Types.show impl.for_type))
            | Some evidence -> check_evidence_grants trait_path.span evidence)
          trait.requires;
        if (not trait.is_capability) && impl.impl_uses <> Types.no_capabilities then
          report state Impl_uses trait_path.span
            "Only an `impl` of a capability can have `uses`. A trait's methods can use only the \
             capabilities the trait declares."

(* A method written inside an [impl], against the method its trait
   declares. *)
let check_impl_method state (name : name) (receiver : Path.receiver) (written : Types.signature)
    (impl : Types.impl_interface) (trait_path : path_type) =
  match impl_view state.database ~bounds:(bounds state) impl trait_path with
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
          report state Extra_member name.span
            (Printf.sprintf "`%s` declares no method `%s` with this receiver." shown_trait name.text)
      | Some declared ->
          let replaceable (signature : Types.signature) =
            signature.uses = Types.no_capabilities
            && signature.terminates
            && List.for_all
                 (fun (info : Types.parameter_info) -> info.mode <> Types.Mut)
                 signature.parameters
            && match signature.receiver with Some (Mut, _) -> false | _ -> true
          in
          if declared.provided && not (replaceable declared.method_signature) then
            report state Not_replaceable name.span
              (Printf.sprintf
                 "`%s` gives `%s` a body, which an `impl` can replace only by a version proven to \
                  give the same result, and so only when the provided one is pure, has a `time` \
                  clause, and changes none of its arguments, so that its body is its definition."
                 shown_trait name.text);
          if trait.is_capability && not (receiver = Read || receiver = Mut) then
            report state Wrong_receiver name.span
              "A capability's implementation takes `self`, or `mut self` if it changes its own \
               state."
          else begin
            (* The method's own generic parameters and [uses], after the
               [impl]'s, which every method written inside it has. *)
            let written =
              {
                written with
                generics =
                  List.filteri
                    (fun index _ -> index >= List.length impl.impl_generics)
                    written.generics;
                uses = Types.capability_difference written.uses impl.impl_uses;
              }
            in
            (* The trait method's own generic parameters are substituted by
               the [impl] method's, by position. *)
            let expected =
              Types.map_signature normalize
                (Types.substitute_signature
                   (Option.value ~default:[]
                      (Types.substitution_of declared.method_signature.generics
                         (Types.generic_arguments written.generics)))
                   declared.method_signature)
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
                         (* No stronger bounds than the trait's. *)
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
                && agrees_result expected.output written.output)
            then
              report state Signature_mismatch name.span
                (Printf.sprintf "`%s` must have the signature `%s%s` that `%s` declares." name.text
                   name.text (show_signature expected) shown_trait)
            else
              (* A caller of a capability holds only that capability, so the
                 implementation can use the capabilities that its [impl]
                 declares and no others. *)
              let allowed = if trait.is_capability then Types.no_capabilities else expected.uses in
              if not (Types.capability_subset (normalize_capabilities written.uses) allowed) then
                report state Impl_uses name.span
                  (if trait.is_capability then
                     Printf.sprintf
                       "`%s` implements a capability, so it can use only the capabilities its \
                        `impl` declares with `uses`."
                       name.text
                   else
                     Printf.sprintf "`%s` can use only the capabilities `%s` declares for it."
                       name.text shown_trait)
          end)
