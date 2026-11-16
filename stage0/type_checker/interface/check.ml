open Syntax
module Names = Resolve.Names
open Checking
open Impl_checks

let bound_diagnostics lookups ~package ~bounds ~spans named =
  List.concat_map
    (fun (id, (type_ : Types.ty)) ->
      let diagnostic code message = Diagnostic.make ~code spans.(id) message in
      match type_ with
      | Named { path; arguments } -> (
          match
            Option.bind (Definition.type_interface lookups path)
              (fun (interface : Types.type_interface) ->
                Option.map
                  (Impls.required interface.type_generics)
                  (Types.substitution_of interface.type_generics arguments))
          with
          | Some required ->
              List.concat_map
                (fun (argument, bound) ->
                  match Impls.implements lookups ~bounds argument bound with
                  | None ->
                      [
                        diagnostic (Types Unsatisfied_bound)
                          (Printf.sprintf "`%s` needs `%s: %s`, which does not hold here."
                             (Types.show type_) (Types.show argument) (Types.show_trait bound));
                      ]
                  | Some evidence ->
                      List.map
                        (diagnostic (Capabilities Not_granted))
                        (Grants.describe_missing_in_evidence lookups ~package ~bounds evidence))
                required
          | None -> [])
      | _ -> [])
    named

let check_bounds state =
  state.diagnostics <-
    bound_diagnostics state.lookups ~package:state.key.module_.package ~bounds:(bounds state)
      ~spans:state.spans state.lowered.named
    @ state.diagnostics

let rec mentioned = function
  | Types.Named { path; arguments } -> path :: List.concat_map mentioned_argument arguments
  | Types.Function { inputs; output; _ } ->
      List.concat_map (fun (_, type_) -> mentioned type_) inputs @ mentioned output
  | Types.Any trait -> trait.trait :: List.concat_map mentioned_argument trait.trait_arguments
  | Types.Projection { base; _ } -> mentioned base
  | _ -> []

and mentioned_argument = function
  | Types.Type type_ -> mentioned type_
  | Types.Value _ | Types.Capabilities _ -> []

let visibility_of state (path : Path.t) =
  match path with
  | Top { module_; name } -> (
      match state.lookups.names.find module_ name with
      | Some entry -> Some entry.visibility
      | None -> None)
  | _ -> None

let check_private_in_public state ~visibility types (span : Source.Definition_span.t) =
  if Names.is_public visibility then
    List.iter
      (fun path ->
        match visibility_of state path with
        | Some (Private | Internal) ->
            report state Private_in_public span
              (Printf.sprintf
                 "This public definition mentions `%s`, which other packages cannot name. Make \
                  `%s` public, or this definition not."
                 (Path.show path) (Path.show path))
        | _ -> ())
      (List.sort_uniq Path.compare (List.concat_map mentioned types))

let check_method_location state (head : type_head) =
  let owner =
    match state.key.path with
    | Method { owner; _ } | Member_constant { owner; _ } -> Some owner
    | _ -> None
  in
  match owner with
  | Some (Top { module_ = owner_module; name } as owner) -> (
      match state.lookups.names.find owner_module name with
      | Some { kind = Type; visibility; _ } ->
          if owner_module.package <> state.key.module_.package then
            report state Method_outside_package state.spans.(head.id)
              (Printf.sprintf
                 "`%s` is defined in the package `%s`, so its methods and constants must be too. A \
                  function of this package can take it as a parameter instead."
                 (Path.show owner)
                 (Path.show_package owner_module.package))
          else if visibility = Private && owner_module <> state.key.module_ then
            report state Method_outside_package state.spans.(head.id)
              (Printf.sprintf
                 "`%s` is private to its module, so its methods and constants must be in that \
                  module."
                 (Path.show owner))
      | _ -> ())
  | _ -> ()

let signature_types (signature : Types.signature) =
  Types.result_type signature.output
  :: List.map (fun (parameter : Types.parameter_info) -> parameter.type_) signature.parameters
  @ List.concat_map
      (fun (generic : Types.generic) ->
        match generic.kind with
        | Type_generic bounds -> List.map (fun bound -> Types.Any bound) bounds
        | _ -> [])
      signature.generics

let main_message =
  "`main` must have exactly the signature `fn main(arguments: List[String]) -> ExitCode`."

let check_main state (signature : Types.signature) span =
  let list_of_string =
    match signature.parameters with
    | [
     {
       name = "arguments";
       mode = Read;
       type_ = Named { path = list; arguments = [ Type (Named { path = string; arguments = [] }) ] };
       has_default = false;
     };
    ] ->
        Well_known.is List list && Well_known.is String string
    | _ -> false
  in
  let exit_code =
    match signature.output with
    | Returns (Named { path; arguments = [] }) -> Well_known.is Exit_code path
    | _ -> false
  in
  if not (list_of_string && exit_code && signature.generics = [] && signature.receiver = None) then
    report state Main_signature span main_message

let check_duplicates state member_kind (names : name list) =
  ignore
    (List.fold_left
       (fun seen (name : name) ->
         if List.mem name.text seen then
           report state Duplicate_field state.spans.(name.id)
             (Printf.sprintf "Another %s of this type is already named `%s`." member_kind name.text);
         name.text :: seen)
       [] names)

let field_names (fields : field list) =
  List.filter_map
    (fun (field : field) ->
      match field.kind with Field_declaration { name; _ } -> Some name | Field_error -> None)
    fields

let remove_derived (spans : Source.Definition_span.t array) (clause : type_clause)
    (traits : path_type list) (written : path_type) =
  let delete start stop = Diagnostic.delete (Source.Definition_span.make start stop) in
  match traits with
  | [ _ ] -> delete spans.(clause.id).start spans.(clause.id).stop
  | _ -> (
      let rec after = function
        | (first : path_type) :: (next :: _ as rest) ->
            if first == written then Some next else after rest
        | _ -> None
      in
      match after traits with
      | Some next -> delete spans.(written.id).start spans.(next.id).start
      | None -> (
          let rec before = function
            | (previous : path_type) :: (next :: _ as rest) ->
                if next == written then Some previous else before rest
            | _ -> None
          in
          match before traits with
          | Some previous -> delete spans.(previous.id).stop spans.(written.id).stop
          | None -> delete spans.(written.id).start spans.(written.id).stop))

let check_derives state (interface : Types.type_interface) (clauses : type_clause list) resolved =
  let field_types =
    match interface.shape with
    | Record fields -> List.map (fun (field : Types.field) -> field.field_type) fields
    | Sum variants ->
        List.concat_map
          (fun (variant : Types.variant) ->
            List.map
              (fun (field : Types.field) -> field.field_type)
              (Option.value ~default:[] variant.fields))
          variants
    | Todo_type | Builtin_type _ -> []
  in
  let derived_bounds trait parameter =
    if
      List.exists
        (fun (generic : Types.generic) -> generic.generic = parameter)
        interface.type_generics
    then bounds state parameter @ [ { Types.trait; trait_arguments = []; associated = [] } ]
    else bounds state parameter
  in
  List.iter
    (fun (clause : type_clause) ->
      match clause.kind with
      | Derives traits ->
          List.iter
            (fun (written : path_type) ->
              match (resolved : Resolve.resolved).names.(written.path.last.id) with
              | Some (Definition (_, trait)) ->
                  let shown = Lower.show_path written.path in
                  if
                    not
                      (Names.derivable trait || Well_known.is Copyable trait
                     || Well_known.is Plain trait)
                  then
                    report state Not_derivable state.spans.(written.id)
                      (Printf.sprintf
                         "Only `Equal`, `Hash`, `Ordered`, `Default`, `Copyable`, `Plain`, \
                          `serialization::Serialize`, and `serialization::Deserialize` can be \
                          derived, not `%s`."
                         shown)
                  else if Well_known.is Copyable trait || Well_known.is Plain trait then
                    begin if not interface.opaque then
                      report state Derives_inferred state.spans.(written.id)
                        ~fixes:
                          [
                            Diagnostic.fix "Remove the declaration."
                              [ remove_derived state.spans clause traits written ];
                          ]
                        (Printf.sprintf
                           "Whether `%s` holds for this type is derived from its fields, which are \
                            visible. Only an opaque type declares it."
                           shown)
                    else
                      let property_holds =
                        List.for_all
                          (fun type_ ->
                            if Well_known.is Plain trait then
                              Impls.plain state.lookups ~bounds:(derived_bounds trait) type_
                            else Impls.copyable state.lookups ~bounds:(derived_bounds trait) type_)
                          field_types
                      in
                      let allocates =
                        match interface.shape with
                        | Sum variants ->
                            List.exists (fun (variant : Types.variant) -> variant.indirect) variants
                        | _ -> false
                      in
                      if (not property_holds) || (Well_known.is Plain trait && allocates) then
                        report state Cannot_derive state.spans.(written.id)
                          (Printf.sprintf "A field of this type is not `%s`, so the type cannot be."
                             shown)
                    end
                  else begin
                    (if Well_known.is Default trait then
                       match interface.shape with
                       | Sum _ ->
                           report state Cannot_derive state.spans.(written.id)
                             "`Default` is derived as each field's default, so only a record can \
                              derive it: no variant of this type is its default. Write the `impl`, \
                              which says which variant is."
                       | Record _ | Todo_type | Builtin_type _ -> ());
                    if Well_known.is Ordered trait || Well_known.is Hash trait then
                      if not (List.exists (Well_known.is Equal) interface.derives) then
                        report state Cannot_derive state.spans.(written.id)
                          (Printf.sprintf
                             "Deriving `%s` needs `Equal` to be derived too, so that the two agree."
                             shown);
                    let needed =
                      match interface.shape with
                      | Record fields when Well_known.is Default trait ->
                          List.filter_map
                            (fun (field : Types.field) ->
                              if field.field_has_default then None else Some field.field_type)
                            fields
                      | _ -> field_types
                    in
                    List.iter
                      (fun type_ ->
                        let wanted : Types.trait_reference =
                          { trait; trait_arguments = []; associated = [] }
                        in
                        if
                          Option.is_none
                            (Impls.implements state.lookups ~bounds:(derived_bounds trait) type_
                               wanted)
                        then
                          report state Cannot_derive state.spans.(written.id)
                            (Printf.sprintf
                               "A field of type `%s` does not implement `%s`, so `%s` cannot be \
                                derived."
                               (Types.show type_) shown shown))
                      needed
                  end
              | _ -> ())
            traits
      | _ -> ())
    clauses

let check_no_capability_parameter state definition_kind (name : name)
    (generics : generic_parameter list) =
  List.iter
    (fun (generic : generic_parameter) ->
      match generic.kind with
      | Capability_parameter parameter ->
          report state Misplaced_capability_parameter state.spans.(generic.id)
            (Printf.sprintf
               "Only a function can take a capability parameter. No type argument can \
                be                 written for `%s`, so no signature or field could name %s `%s` \
                with the                 capabilities that it uses. Write the capabilities in the \
                function type, as in                 `(fn() uses Clock)`."
               parameter.text definition_kind name.text)
      | Type_parameter _ | Value_parameter _ | Generic_error -> ())
    generics

let check_trait_cycle state (requires : path_type list) =
  let visited = Hashtbl.create 16 in
  let rec reaches path =
    if Path.equal path state.key.path then true
    else if Hashtbl.mem visited path then false
    else begin
      Hashtbl.replace visited path ();
      match state.lookups.trait_header path with
      | Some header -> List.exists reaches header.required
      | None -> false
    end
  in
  match state.lookups.trait_header state.key.path with
  | Some header when List.exists reaches header.required -> (
      match requires with
      | first :: _ ->
          report state Trait_cycle state.spans.(first.id)
            "This trait requires itself through the traits it requires."
      | [] -> ())
  | _ -> ()

let check_redeclared state (name : name) (receiver : Path.receiver) ~(trait_path : Path.t)
    (trait : Types.trait_interface) =
  let inherited =
    List.concat_map
      (fun (required : Types.trait_reference) ->
        List.concat_map
          (fun (bound : Types.trait_reference) ->
            match Definition.trait_interface state.lookups bound.trait with
            | Some interface ->
                List.map
                  (fun (method_ : Types.trait_method) ->
                    ((method_.method_name, method_.method_receiver), bound.trait))
                  interface.methods
            | None -> [])
          (Properties.bound_closure state.lookups
             ~self:(Types.Parameter { owner = trait_path; name = "Self" })
             required))
      trait.requires
  in
  match List.assoc_opt (name.text, receiver) inherited with
  | Some from ->
      report state Redeclared_method state.spans.(name.id)
        (Printf.sprintf
           "`%s` already declares a `%s` that takes %s, so a trait that requires it cannot declare \
            it again."
           (Path.show from) name.text (Path.show_receiver receiver))
  | None -> ()

let check_proof_bounds state (written : type_head) (generics : Types.generic list)
    (impl : Types.impl_interface) =
  if List.length generics = List.length impl.impl_generics then begin
    let renaming : Types.substitution =
      List.map2
        (fun (proof : Types.generic) (of_impl : Types.generic) ->
          ( proof.generic,
            match of_impl.kind with
            | Type_generic _ -> Types.Type (Types.Parameter of_impl.generic)
            | Value_generic -> Types.Value (Types.Value_parameter of_impl.generic)
            | Capability_generic ->
                Types.Capabilities
                  (Types.capability_set [ Types.Capability_parameter of_impl.generic ]) ))
        generics impl.impl_generics
    in
    let impl_bounds = Types.bounds_of impl.impl_generics in
    List.iteri
      (fun index ((proof : Types.generic), (of_impl : Types.generic)) ->
        match proof.kind with
        | Type_generic bounds ->
            List.iter
              (fun (bound : Types.trait_reference) ->
                if
                  Option.is_none
                    (Impls.implements state.lookups ~bounds:impl_bounds
                       (Types.Parameter of_impl.generic)
                       (Types.substitute_trait renaming bound))
                then
                  let span =
                    match List.nth_opt written.generics index with
                    | Some (generic : generic_parameter) -> state.spans.(generic.id)
                    | None -> state.spans.(written.id)
                  in
                  report state Unsatisfied_bound span
                    (Printf.sprintf
                       "The `impl` does not require `%s: %s`, so this proof cannot assume it: the \
                        law is proven for every type that the `impl` is for."
                       proof.generic.name (Types.show_trait bound)))
              bounds
        | Value_generic | Capability_generic -> ())
      (List.combine generics impl.impl_generics)
  end

let check state =
  let lookups = state.lookups in
  let definition = state.definition in
  let broken part = Names.is_broken lookups.names state.key part in
  check_bounds state;
  match lookups.resolved Interface state.key with
  | None -> ()
  | Some resolved -> (
      if not (broken Header) then
        match (lookups.names.container state.key, definition.kind, state.lowered.interface) with
        | ( Some container,
            (Function { signature; _ } | Method_declaration signature),
            Function_interface written ) -> (
            let name = Names.signature_name signature in
            match
              ( lookups.names.definition container,
                lookups.names.spans container,
                Option.map
                  (fun (lowered : Environment.lowered_interface) -> lowered.interface)
                  (lookups.lowered_interface container) )
            with
            | Some { kind = Trait _; visibility; _ }, _, Some (Trait_interface trait) ->
                check_redeclared state name
                  (Names.receiver signature.parameters)
                  ~trait_path:container.path trait;
                check_private_in_public state ~visibility (signature_types written)
                  state.spans.(name.id)
            | Some { kind = Impl { trait_; _ }; _ }, Some impl_spans, Some (Impl_interface impl) ->
                check_impl_method state name
                  (Names.receiver signature.parameters)
                  written impl ~trait_span:impl_spans.(trait_.id) trait_
            | _ -> ())
        | Some _, _, _ -> ()
        | None, Function { signature; _ }, Function_interface lowered ->
            (match signature.name with
            | Member_name (head, _) -> check_method_location state head
            | Plain_name name ->
                if name.text = "main" && state.key.module_.modules = [] then
                  check_main state lowered state.spans.(name.id));
            let span =
              match signature.name with
              | Plain_name name | Member_name (_, name) -> state.spans.(name.id)
            in
            check_private_in_public state ~visibility:definition.visibility
              (signature_types lowered) span
        | None, Law_proof { law; type_; _ }, Law_proof_interface { generics; trait; for_type; _ }
          -> (
            (match lookups.trait_header trait.trait with
            | Some header when not (List.mem law.text header.laws) ->
                report state Unknown_member state.spans.(law.id)
                  (Printf.sprintf "`%s` has no law `%s`." (Types.show_trait trait) law.text)
            | _ -> ());
            let arity_matches =
              match for_type with
              | Types.Named { path; _ } -> (
                  match Names.generics_of lookups.names path with
                  | Some expected -> List.length expected = List.length generics
                  | None -> true)
              | _ -> true
            in
            if arity_matches && not (Types.is_error for_type) then
              match implements state for_type trait with
              | None ->
                  report state No_impl state.spans.(type_.id)
                    (Printf.sprintf "`%s` does not implement `%s`, so it has no law of it to keep."
                       (Types.show for_type) (Types.show_trait trait))
              | Some (Impls.From_impl { impl; _ }) ->
                  Option.iter
                    (check_proof_bounds state type_ generics)
                    (Impls.impl_interface lookups impl)
              | Some _ -> ())
        | None, Type_definition { name; generics; body; clauses }, Type_interface interface ->
            check_no_capability_parameter state "the type" name generics;
            (match body with
            | Fields fields -> check_duplicates state "field" (field_names fields)
            | Variants variants ->
                check_duplicates state "variant"
                  (List.map (fun (variant : variant) -> variant.name) variants);
                List.iter
                  (fun (variant : variant) ->
                    Option.iter
                      (fun fields -> check_duplicates state "field" (field_names fields))
                      variant.fields)
                  variants
            | Type_todo -> ());
            check_derives state interface clauses resolved;
            if definition.visibility = Public then
              check_private_in_public state ~visibility:definition.visibility
                (match interface.shape with
                | Record fields -> List.map (fun (field : Types.field) -> field.field_type) fields
                | Sum variants ->
                    List.concat_map
                      (fun (variant : Types.variant) ->
                        List.map
                          (fun (field : Types.field) -> field.field_type)
                          (Option.value ~default:[] variant.fields))
                      variants
                | _ -> [])
                state.spans.(name.id)
        | None, Trait { name; generics; requires; _ }, Trait_interface trait ->
            check_no_capability_parameter state "the trait" name generics;
            check_trait_cycle state requires;
            check_private_in_public state ~visibility:definition.visibility
              (List.map (fun (bound : Types.trait_reference) -> Types.Any bound) trait.requires)
              state.spans.(name.id)
        | None, Constant { name = Plain_name name; _ }, Constant_interface constant ->
            check_private_in_public state ~visibility:definition.visibility
              [ constant.constant_type ] state.spans.(name.id)
        | None, Impl { trait_; members; _ }, Impl_interface impl ->
            check_impl state members impl trait_
        | None, Constant { name = Member_name (head, _); _ }, _ -> check_method_location state head
        | None, _, _ -> ())

let diagnostics (lookups : Lookups.t) key =
  match (lookups.names.definition key, lookups.names.spans key, lookups.lowered_interface key) with
  | Some definition, Some spans, Some lowered ->
      let state = { lookups; key; definition; lowered; spans; diagnostics = [] } in
      check state;
      List.sort
        (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
          compare (left.span, left.code) (right.span, right.code))
        state.diagnostics
  | _ -> []
