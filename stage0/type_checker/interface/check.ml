let list_bound_diagnostics lookups ~package ~list_bounds ~spans named =
  List.concat_map
    (fun (id, (type_ : Types.ty)) ->
      let make_diagnostic code message = Diagnostic.make ~code spans.(id) message in
      match type_ with
      | Named { path; arguments } -> (
          match
            Option.map
              (fun (interface : Types.type_interface) ->
                Impls.list_required_bounds interface.type_generics
                  (Types.make_substitution interface.type_generics arguments))
              (Definition.find_type_interface lookups path)
          with
          | Some required ->
              List.concat_map
                (fun (argument, bound) ->
                  match Impls.find_evidence lookups ~list_bounds argument bound with
                  | None ->
                      [
                        make_diagnostic (Types Unsatisfied_bound)
                          (Printf.sprintf "`%s` needs `%s: %s`, which does not hold here."
                             (Types.show type_) (Types.show argument) (Types.show_trait bound));
                      ]
                  | Some evidence ->
                      List.map
                        (make_diagnostic (Capabilities Not_granted))
                        (Grants.describe_missing_in_impls lookups ~package
                           (Grants.list_evidence_uses lookups ~list_bounds evidence)))
                required
          | None -> [])
      | _ -> [])
    named

let check_bounds (state : Checking.state) =
  state.diagnostics :=
    list_bound_diagnostics state.lookups ~package:state.key.module_.package
      ~list_bounds:(Checking.list_bounds state) ~spans:state.spans state.elaborated.named
    @ !(state.diagnostics)

let rec list_mentioned_paths = function
  | Types.Named { path; arguments } -> path :: List.concat_map list_argument_paths arguments
  | Types.Function { inputs; output; _ } ->
      List.concat_map (fun (_, type_) -> list_mentioned_paths type_) inputs
      @ list_mentioned_paths output
  | Types.Projection { base; _ } -> list_mentioned_paths base
  | _ -> []

and list_argument_paths = function
  | Types.Type type_ -> list_mentioned_paths type_
  | Types.Value _ -> []

let list_trait_paths (trait : Types.trait_reference) =
  trait.trait :: List.concat_map list_argument_paths trait.trait_arguments

let find_visibility (state : Checking.state) (path : Path.t) =
  match path with
  | Top { module_; name } -> (
      match state.lookups.names.find module_ name with
      | Some entry -> Some entry.visibility
      | None -> None)
  | _ -> None

let check_private_in_public state ~visibility paths (span : Source.Definition_span.t) =
  if Resolve.Names.is_public visibility then
    List.iter
      (fun path ->
        match find_visibility state path with
        | Some (Private | Internal) ->
            Checking.report state Private_in_public span
              (Printf.sprintf
                 "This public definition mentions `%s`, which other packages cannot name. Make \
                  `%s` public, or this definition not."
                 (Path.show path) (Path.show path))
        | _ -> ())
      (List.sort_uniq Path.compare paths)

let check_method_location (state : Checking.state) (head : Syntax.type_head) =
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
            Checking.report state Method_outside_package state.spans.(head.id)
              (Printf.sprintf
                 "`%s` is defined in the package `%s`, so its methods and constants must be too. A \
                  function of this package can take it as a parameter instead."
                 (Path.show owner)
                 (Path.show_package owner_module.package))
          else if visibility = Private && owner_module <> state.key.module_ then
            Checking.report state Method_outside_package state.spans.(head.id)
              (Printf.sprintf
                 "`%s` is private to its module, so its methods and constants must be in that \
                  module."
                 (Path.show owner))
      | _ -> ())
  | _ -> ()

let list_signature_paths (signature : Types.signature) =
  List.concat_map list_mentioned_paths
    (Types.extract_result_type signature.output
    :: List.map (fun (parameter : Types.parameter_info) -> parameter.type_) signature.parameters)
  @ List.concat_map
      (fun (generic : Types.generic) ->
        match generic.kind with
        | Type_generic bounds -> List.concat_map list_trait_paths bounds
        | _ -> [])
      signature.generics

let check_real_implementations (state : Checking.state) (resolved : Resolve.resolved) ~recipient
    (uses : Syntax.capability_reference list) =
  List.iter
    (fun (capability : Syntax.capability_reference) ->
      match capability.kind with
      | Capability_path written -> (
          match resolved.names.(written.path.last.id) with
          | Some (Definition (Capability, path)) -> (
              match Well_known.find_builtin_capability path with
              | Some (Panic | Run_forever) -> ()
              | Some System ->
                  Checking.report state No_real_implementation state.spans.(capability.id)
                    (Printf.sprintf
                       "The runtime grants `System` only to the real implementations of the \
                        standard capabilities, so it cannot provide it to %s."
                       recipient)
              | None when Option.is_none (Definition.find_real_implementation state.lookups path) ->
                  Checking.report state No_real_implementation state.spans.(capability.id)
                    (Printf.sprintf
                       "`%s` has no real implementation, so the runtime cannot provide it to %s. \
                        Provide an implementation in the body with `provide`."
                       (Elaborator.show_path written.path)
                       recipient)
              | None -> ())
          | _ -> ())
      | Self_capabilities _ | Associated_capabilities _ | Generic_capability _ -> ())
    uses

let main_message =
  "`main` must have exactly the signature `fn main(arguments: List[String]) -> ExitCode`."

let check_main state resolved (clauses : Syntax.clause list) (signature : Types.signature) span =
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
    Checking.report state Main_signature span main_message;
  check_real_implementations state resolved ~recipient:"`main`"
    (List.concat_map
       (fun (clause : Syntax.clause) ->
         match clause.kind with
         | Uses uses -> List.map (fun (use : Syntax.capability_use) -> use.capability) uses
         | _ -> [])
       clauses)

let make_element_removal (spans : Source.Definition_span.t array)
    ~(clause : Source.Definition_span.t) (elements : Syntax.id list) (removed : Syntax.id) =
  let delete start stop = Diagnostic.delete (Source.Definition_span.make start stop) in
  let rec find_neighbors previous = function
    | element :: next :: _ when element = removed -> (previous, Some next)
    | [ element ] when element = removed -> (previous, None)
    | element :: rest -> find_neighbors (Some element) rest
    | [] -> Compiler_bug.raise_bug ~stage:"Interface" "the removed element is not in its list"
  in
  match find_neighbors None elements with
  | _, Some next -> delete spans.(removed).start spans.(next).start
  | Some previous, None -> delete spans.(previous).stop spans.(removed).stop
  | None, None -> delete clause.start clause.stop

let check_duplicates state member_kind (names : Syntax.name list) =
  ignore
    (List.fold_left
       (fun seen (name : Syntax.name) ->
         if List.mem name.text seen then
           Checking.report state Duplicate_field state.spans.(name.id)
             (Printf.sprintf "Another %s of this type is already named `%s`." member_kind name.text);
         name.text :: seen)
       [] names)

let list_field_names (fields : Syntax.field list) =
  List.filter_map
    (fun (field : Syntax.field) ->
      match field.kind with Field_declaration { name; _ } -> Some name | Field_error -> None)
    fields

let check_derives state (interface : Types.type_interface) (clauses : Syntax.type_clause list)
    resolved =
  let field_types = Types.list_field_types interface in
  let list_derived_bounds trait =
    Properties.Bounds.append (Checking.list_bounds state)
      (Properties.Bounds.close state.lookups (fun parameter ->
           if
             List.exists
               (fun (generic : Types.generic) -> generic.generic = parameter)
               interface.type_generics
           then [ { Types.trait; trait_arguments = []; associated = [] } ]
           else []))
  in
  List.iter
    (fun ((clause : Syntax.type_clause), (written : Syntax.path_type), trait) ->
      let shown = Elaborator.show_path written.path in
      if
        not
          (Resolve.Names.is_derivable trait || Well_known.is Copyable trait
         || Well_known.is Plain trait)
      then
        Checking.report state Not_derivable state.spans.(written.id)
          (Printf.sprintf
             "Only `Equal`, `Hash`, `Ordered`, `Default`, `Copyable`, `Plain`, \
              `serialization.Serialize`, and `serialization.Deserialize` can be derived, not `%s`."
             shown)
      else if Well_known.is Copyable trait || Well_known.is Plain trait then
        begin if not interface.opaque then
          Checking.report state Derives_inferred state.spans.(written.id)
            ~fixes:
              [
                Diagnostic.fix "Remove the declaration."
                  [
                    make_element_removal state.spans ~clause:state.spans.(clause.id)
                      (match clause.kind with
                      | Derives traits ->
                          List.map (fun (trait : Syntax.path_type) -> trait.id) traits
                      | Type_invariant _ | Potential _ -> [])
                      written.id;
                  ];
              ]
            (Printf.sprintf
               "Whether `%s` holds for this type is derived from its fields, which are visible. \
                Only an opaque type declares it."
               shown)
        else
          let self : Types.ty =
            Named
              {
                path = state.key.path;
                arguments = Types.list_generic_arguments interface.type_generics;
              }
          in
          let list_bounds = list_derived_bounds trait in
          let holds =
            if Well_known.is Plain trait then Impls.is_plain state.lookups ~list_bounds self
            else Impls.is_copyable state.lookups ~list_bounds self
          in
          if not holds then
            Checking.report state Cannot_derive state.spans.(written.id)
              (Printf.sprintf "A field of this type is not `%s`, so the type cannot be." shown)
        end
      else begin
        (if Well_known.is Default trait then
           match interface.shape with
           | Sum _ ->
               Checking.report state Cannot_derive state.spans.(written.id)
                 "`Default` is derived as each field's default, so only a record can derive it: no \
                  variant of this type is its default. Write the `impl`, which says which variant \
                  is."
           | Record _ | Todo_type | Builtin_type _ -> ());
        if Well_known.is Ordered trait || Well_known.is Hash trait then
          if not (List.exists (Well_known.is Equal) interface.derives) then
            Checking.report state Cannot_derive state.spans.(written.id)
              (Printf.sprintf
                 "Deriving `%s` needs `Equal` to be derived too, so that the two agree." shown);
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
            let wanted : Types.trait_reference = { trait; trait_arguments = []; associated = [] } in
            if
              Option.is_none
                (Impls.find_evidence state.lookups ~list_bounds:(list_derived_bounds trait) type_
                   wanted)
            then
              Checking.report state Cannot_derive state.spans.(written.id)
                (Printf.sprintf
                   "A field of type `%s` does not implement `%s`, so `%s` cannot be derived."
                   (Types.show type_) shown shown))
          needed
      end)
    (Definition.list_derives_entries resolved clauses)

let check_trait_cycle (state : Checking.state) (requires : Syntax.path_type list) =
  let is_required_by required =
    List.exists (Path.equal state.key.path) (Elaborator.list_trait_closure state.lookups required)
  in
  match state.lookups.find_trait_header state.key.path with
  | Some header when List.exists is_required_by header.required -> (
      match requires with
      | first :: _ ->
          Checking.report state Trait_cycle state.spans.(first.id)
            "This trait requires itself through the traits it requires."
      | [] -> ())
  | _ -> ()

let rec name_declaring_traits lookups (type_ : Types.ty) =
  Types.map
    ~map_capabilities:(name_declaring_capability_traits lookups)
    (function
      | Types.Projection { base; trait; name } ->
          let base = name_declaring_traits lookups base in
          Some
            (Types.Projection
               {
                 base;
                 trait =
                   Option.value ~default:trait
                     (Properties.find_trait_declaring_type lookups ~base trait name);
                 name;
               })
      | _ -> None)
    type_

and name_declaring_capability_traits lookups capabilities =
  Types.replace_capabilities
    (function
      | Types.Capability_projection { base; trait; name } ->
          let base = name_declaring_traits lookups base in
          Some
            (Types.make_capability_set
               [
                 Types.Capability_projection
                   {
                     base;
                     trait =
                       Option.value ~default:trait
                         (Properties.find_trait_declaring_capability_set lookups ~base trait name);
                     name;
                   };
               ])
      | _ -> None)
    (Types.map_conditions
       (Types.map_condition_types (name_declaring_traits lookups) (fun trait ->
            {
              trait with
              trait_arguments =
                List.map
                  (function
                    | Types.Type type_ -> Types.Type (name_declaring_traits lookups type_)
                    | value -> value)
                  trait.trait_arguments;
            }))
       capabilities)

let name_signature_declaring_traits lookups (signature : Types.signature) =
  let signature = Types.map_signature (name_declaring_traits lookups) signature in
  { signature with uses = name_declaring_capability_traits lookups signature.uses }

let check_restated (state : Checking.state) (signature : Syntax.signature) ~has_body
    (written : Types.signature) ~(trait_path : Path.t) (trait : Types.trait_interface) =
  let name = Resolve.Names.extract_signature_name signature in
  let receiver = Resolve.Names.classify_receiver signature.parameters in
  match
    List.find_opt
      (fun (restated : Types.restated_method) ->
        restated.restated_name = name.text && restated.restated_receiver = receiver)
      trait.restated
  with
  | None -> ()
  | Some restated ->
      let declared_by = Path.show restated.declared_by in
      let original =
        Definition.read_method_signature state.lookups ~owner:restated.declared_by
          { method_name = name.text; method_receiver = receiver; provided = false }
      in
      let is_added (clause : Syntax.clause) =
        match clause.kind with Ensures _ | Cost _ -> true | _ -> false
      in
      List.iter
        (fun (clause : Syntax.clause) ->
          match clause.kind with
          | Requires _ ->
              Checking.report state Restated_method_clause state.spans.(clause.id)
                (Printf.sprintf
                   "`%s` restates `%s.%s`, so it adds only `ensures` and `cost` clauses. A caller \
                    through `%s` would never prove this `requires`."
                   name.text declared_by name.text declared_by)
          | Decreases _ ->
              Checking.report state Restated_method_clause state.spans.(clause.id)
                (Printf.sprintf
                   "`%s` restates `%s.%s`, so it adds only `ensures` and `cost` clauses. It has no \
                    body, so it has no recursion to measure."
                   name.text declared_by name.text)
          | Ensures _ | Cost _ | Uses _ | Clause_error -> ())
        signature.clauses;
      if Impl_checks.has_default original then
        Checking.report state Restated_method_default state.spans.(name.id)
          (Printf.sprintf
             "`%s` restates `%s.%s`, which has a default, and a method with a default has one \
              declaration. A call that omits the argument reads the default from `%s`, and this \
              restatement would be a second declaration that shows none."
             name.text declared_by name.text declared_by)
      else if has_body then
        Checking.report state Restated_method_body state.spans.(name.id)
          (Printf.sprintf
             "`%s` restates `%s.%s`, so it has no body: each type's `impl` of `%s` gives the body."
             name.text declared_by name.text declared_by)
      else if not (List.exists is_added signature.clauses) then
        Checking.report state Redeclared_method state.spans.(name.id)
          (Printf.sprintf
             "`%s` already declares a `%s` that takes %s, and this restatement adds no `ensures` \
              or `cost` clause. Add the clauses that the trait promises, or delete the method."
             declared_by name.text (Path.show_receiver receiver))
      else
        let self = Types.Parameter (Types.make_self_parameter trait_path) in
        let substitution =
          match
            List.find_opt
              (fun (bound : Types.trait_reference) -> Path.equal bound.trait restated.declared_by)
              (List.concat_map (Properties.list_bound_closure state.lookups ~self) trait.requires)
          with
          | Some reference ->
              Types.make_trait_substitution
                (Definition.read_trait_interface state.lookups restated.declared_by).trait_generics
                ~self reference
          | None ->
              Compiler_bug.raise_bug ~stage:"Interface"
                "`%s` restates a method of `%s`, which it does not require" (Path.show trait_path)
                declared_by
        in
        let expected =
          name_signature_declaring_traits state.lookups
            (Types.substitute_signature substitution original)
        and written = name_signature_declaring_traits state.lookups written in
        let implies =
          Impls.implies_condition state.lookups
            ~list_bounds:
              (Properties.Bounds.close state.lookups (Types.list_bounds expected.generics))
        in
        if
          not
            (Impl_checks.signatures_agree expected written
            && Types.is_capability_subset ~implies expected.uses written.uses
            && Types.is_capability_subset ~implies written.uses expected.uses)
        then
          Checking.report state Signature_mismatch state.spans.(name.id)
            (Printf.sprintf "`%s` restates `%s.%s`, so it has the signature `%s%s%s`." name.text
               declared_by name.text name.text
               (Impl_checks.show_signature expected)
               (match Types.list_capabilities expected.uses with
               | [] -> ""
               | capabilities ->
                   " uses " ^ String.concat ", " (List.map Types.show_capability capabilities)))

let check_defaults_without_body (state : Checking.state) (signature : Syntax.signature) =
  let name = Resolve.Names.extract_signature_name signature in
  List.iter
    (fun (parameter : Syntax.parameter) ->
      match parameter.kind with
      | Named_parameter { type_; default = Some default; _ } ->
          Checking.report state Default_without_body state.spans.(default.id)
            ~fixes:
              [
                Diagnostic.fix "Remove the default"
                  [
                    Diagnostic.delete
                      (Source.Definition_span.make state.spans.(type_.id).stop
                         state.spans.(default.id).stop);
                  ];
              ]
            (Printf.sprintf
               "`%s` has no body, so each `impl` writes it, and a method that an `impl` writes has \
                no default: a call on a known type names the `impl`'s method, which would not show \
                the default. Remove the default, or give `%s` a body."
               name.text name.text)
      | Named_parameter { default = None; _ } | Self_parameter _ | Parameter_error -> ())
    signature.parameters

let check_proof_bounds (state : Checking.state) (written : Syntax.type_head)
    (generics : Types.generic list) (impl : Types.impl_interface) =
  if List.length generics = List.length impl.impl_generics then begin
    let renaming =
      Types.make_substitution generics (Types.list_generic_arguments impl.impl_generics)
    in
    let list_impl_bounds =
      Properties.Bounds.close state.lookups (Types.list_bounds impl.impl_generics)
    in
    List.iteri
      (fun index ((proof : Types.generic), (of_impl : Types.generic)) ->
        match proof.kind with
        | Type_generic bounds ->
            List.iter
              (fun (bound : Types.trait_reference) ->
                if
                  Option.is_none
                    (Impls.find_evidence state.lookups ~list_bounds:list_impl_bounds
                       (Types.Parameter of_impl.generic)
                       (Types.substitute_trait renaming bound))
                then
                  let span =
                    match List.nth_opt written.generics index with
                    | Some (generic : Syntax.generic_parameter) -> state.spans.(generic.id)
                    | None -> state.spans.(written.id)
                  in
                  Checking.report state Unsatisfied_bound span
                    (Printf.sprintf
                       "The `impl` does not require `%s: %s`, so this proof cannot assume it: the \
                        law is proven for every type that the `impl` is for."
                       proof.generic.name (Types.show_trait bound)))
              bounds
        | Value_generic -> ())
      (List.combine generics impl.impl_generics)
  end

let check (state : Checking.state) =
  let lookups = state.lookups in
  let definition = state.definition in
  let visibility = (lookups.names.read_declaration state.key).visibility in
  let is_broken part = Resolve.Names.is_broken lookups.names state.key part in
  check_bounds state;
  let resolved = lookups.read_resolved Interface state.key in
  if not (is_broken Header) then
    match (lookups.names.find_container state.key, definition.kind, state.elaborated.interface) with
    | ( Some container,
        (Function { signature; _ } | Method_declaration signature),
        Function_interface written ) -> (
        let name = Resolve.Names.extract_signature_name signature in
        match (lookups.names.read_definition container, lookups.read_interface container) with
        | { kind = Trait _; _ }, Trait_interface trait ->
            let has_body = match definition.kind with Function _ -> true | _ -> false in
            let is_restated =
              List.exists
                (fun (restated : Types.restated_method) ->
                  restated.restated_name = name.text
                  && restated.restated_receiver
                     = Resolve.Names.classify_receiver signature.parameters)
                trait.restated
            in
            if not (has_body || is_restated) then check_defaults_without_body state signature;
            check_restated state signature ~has_body written ~trait_path:container.path trait;
            check_private_in_public state ~visibility (list_signature_paths written)
              state.spans.(name.id)
        | { kind = Impl { trait_; _ }; _ }, Impl_interface impl ->
            Impl_checks.check_impl_method state name
              (Resolve.Names.classify_receiver signature.parameters)
              written impl
              ~trait_span:(lookups.names.read_spans container).(trait_.id)
              trait_
        | _ -> ())
    | Some _, _, _ -> ()
    | None, Function { signature; _ }, Function_interface elaborated ->
        (match signature.name with
        | Member_name (head, _) -> check_method_location state head
        | Plain_name name ->
            if Path.is_entry_point state.key.path then
              check_main state resolved signature.clauses elaborated state.spans.(name.id));
        let span =
          match signature.name with
          | Plain_name name | Member_name (_, name) -> state.spans.(name.id)
        in
        check_private_in_public state ~visibility (list_signature_paths elaborated) span
    | None, Law_proof { law; type_; _ }, Law_proof_interface { generics; trait; for_type; _ } -> (
        (match lookups.find_trait_header trait.trait with
        | Some header when not (List.mem law.text header.laws) ->
            Checking.report state Unknown_member state.spans.(law.id)
              (Printf.sprintf "`%s` has no law `%s`." (Types.show_trait trait) law.text)
        | _ -> ());
        let arity_matches =
          match for_type with
          | Types.Named { path; _ } -> (
              match Resolve.Names.find_generics lookups.names path with
              | Some expected -> List.length expected = List.length generics
              | None -> true)
          | _ -> true
        in
        if arity_matches && not (Types.is_error for_type) then
          match Checking.find_evidence state for_type trait with
          | None ->
              Checking.report state No_impl state.spans.(type_.id)
                (Printf.sprintf "`%s` does not implement `%s`, so it has no law of it to keep."
                   (Types.show for_type) (Types.show_trait trait))
          | Some (Impls.Evidence (Impl { impl; _ })) ->
              Option.iter
                (check_proof_bounds state type_ generics)
                (Definition.find_impl_interface lookups impl)
          | Some _ -> ())
    | None, Type_definition { name; body; clauses; _ }, Type_interface interface ->
        (match body with
        | Fields fields -> check_duplicates state "field" (list_field_names fields)
        | Variants variants ->
            check_duplicates state "variant"
              (List.map (fun (variant : Syntax.variant) -> variant.name) variants);
            List.iter
              (fun (variant : Syntax.variant) ->
                Option.iter
                  (fun fields -> check_duplicates state "field" (list_field_names fields))
                  variant.fields)
              variants
        | Type_todo -> ());
        check_derives state interface clauses resolved;
        if visibility = Public then
          check_private_in_public state ~visibility
            (List.concat_map list_mentioned_paths (Types.list_field_types interface))
            state.spans.(name.id)
    | None, Trait { name; requires; _ }, Trait_interface trait ->
        check_trait_cycle state requires;
        check_private_in_public state ~visibility
          (List.concat_map list_trait_paths trait.requires)
          state.spans.(name.id)
    | None, Constant { name = Plain_name name; _ }, Constant_interface constant ->
        check_private_in_public state ~visibility
          (list_mentioned_paths constant.constant_type)
          state.spans.(name.id)
    | None, Impl { trait_; members; _ }, Impl_interface impl ->
        Impl_checks.check_impl state members impl trait_
    | None, Constant { name = Member_name (head, _); _ }, _ -> check_method_location state head
    | None, Test { uses; _ }, Test_interface _ ->
        check_real_implementations state resolved ~recipient:"a test" uses
    | None, _, _ -> ()

let list_diagnostics (lookups : Lookups.t) key =
  let state =
    {
      Checking.lookups;
      key;
      definition = lookups.names.read_definition key;
      elaborated = lookups.read_elaborated_interface key;
      spans = lookups.names.read_spans key;
      diagnostics = ref [];
    }
  in
  (try check state
   with Properties.Recursion_limit message ->
     Checking.report state Recursion_limit state.spans.(state.definition.id) message);
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code) (right.span, right.code))
    !(state.diagnostics)
