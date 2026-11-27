let takes_literal (state : State.state) (collection : Types.ty) (trait : Types.trait_reference) =
  match collection with
  | Types.Named _ | Types.Parameter _ | Types.Projection _ -> (
      match
        Interface.Impls.find_evidence state.lookups.interface
          ~list_bounds:(State.lookup_bounds state) ~checks_conditions:false collection trait
      with
      | Some (Evidence (Impl _ | Derived_for_view _ | Bound)) -> true
      | Some (Built_in | Accepted _) | None -> false)
  | _ -> false

let record_conversion (state : State.state) (value : Syntax.expression) elements
    (collection : Types.ty) (trait : Types.trait_reference) method_ =
  State.elaborate state value.id
    (Converted_literal
       {
         elements;
         call = Tables.make_method_call trait method_ ~self_type:collection ~result:collection [];
       });
  Solver.require state (Method_call (Written value.id)) collection trait

let find_all options =
  List.fold_right
    (fun option all -> Option.bind option (fun each -> Option.map (List.cons each) all))
    options (Some [])

let check_parameter_annotation (state : State.state) ~mode ~input
    ((annotation : Syntax.parameter_annotation), annotated_mode, annotated) =
  if annotated_mode <> mode then
    State.report state
      (Lambda_parameter_mode
         {
           at = Written annotation.id;
           type_expression = Written annotation.type_.id;
           passed = mode;
           annotated = annotated_mode;
         });
  if not (State.unify state input annotated) then
    ignore
      (Failures.add_mismatch_diagnostic state (Written annotation.type_.id)
         ~sides:[ (input, annotated) ]
         (Lambda_parameter_type
            { passed = State.make_shown state input; annotated = State.make_shown state annotated }))

let require_decided_parameter (state : State.state) (parameter : Syntax.lambda_parameter) input =
  let list_undecided () =
    List.filter
      (function
        | Unify.Unknown_type index -> Option.is_none (Unify.find_domain state.unifier index)
        | Unknown_value _ -> true)
      (Unify.list_unknowns state.unifier input)
  in
  List.iter
    (function Unify.Unknown_type index -> Solver.solve_head state index | Unknown_value _ -> ())
    (list_undecided ());
  match (list_undecided (), parameter.pattern.kind) with
  | [], _ | _, Pattern_error -> ()
  | undecided, _ ->
      let reported =
        State.add_diagnostic state
          (Undetermined { at = Written parameter.pattern.id; undetermined = Lambda_parameter })
      in
      List.iter (fun unknown -> Unify.poison state.unifier unknown reported) undecided

let rec check_string_literal state env ?expected (value : Syntax.expression)
    (literal : Syntax.string_literal) =
  let interpolations =
    List.map
      (fun (interpolated, _) -> (interpolated, Hooks.check_expression state env interpolated))
      literal.rest
  in
  match literal.tag with
  | None ->
      if interpolations <> [] then
        State.check_when_final state (fun () ->
            let display = Types.make_trait_reference ~arguments:[] (Well_known.make_path Display) in
            Option.iter
              (fun displays ->
                State.elaborate state value.id (Template (Interpolated { displays })))
              (find_all
                 (List.map
                    (fun ((interpolated : Syntax.expression), interpolated_type) ->
                      let interpolated_type = State.finalize_type state interpolated_type in
                      match State.find_evidence state interpolated_type display with
                      | Some _ ->
                          Some
                            (Tables.make_method_call display Display_display
                               ~self_type:interpolated_type ~result:Types.unit
                               [ (interpolated, Read) ])
                      | None ->
                          State.report state
                            (Not_displayable
                               { at = Written interpolated.id; type_ = interpolated_type });
                          None)
                    interpolations)));
      Types.string_type
  | Some tag -> (
      match State.find_target state tag.last with
      | Some (Definition (Type, tag_path)) ->
          let tag_type =
            Types.Named
              {
                path = tag_path;
                arguments = Instantiation.instantiate_type state ~written:tag.last.id tag_path;
              }
          in
          List.iter
            (fun (interpolated, _) -> Modes.note_owned_value state env interpolated)
            interpolations;
          (match expected with
          | Some expected -> ignore (State.unify state tag_type expected)
          | None -> ());
          let template_trait =
            Types.make_trait_reference ~arguments:[] (Well_known.make_path From_template)
          in
          State.check_when_final state (fun () ->
              let tag_type = State.finalize_type state tag_type in
              match State.find_evidence state tag_type template_trait with
              | Some _ ->
                  let from_template =
                    Tables.make_method_call template_trait From_template_from_template
                      ~self_type:tag_type ~result:tag_type []
                  in
                  let interpolation_type =
                    Solver.resolve_associated_type state tag_type template_trait
                      From_template_interpolation ~at:(Written literal.id)
                  in
                  Option.iter
                    (fun conversions ->
                      State.elaborate state value.id
                        (Template (Tagged { from_template; interpolation_type; conversions })))
                    (find_all
                       (List.map
                          (fun ((interpolated : Syntax.expression), interpolated_type) ->
                            let interpolated_type = State.finalize_type state interpolated_type in
                            let make_from source =
                              Types.make_trait_reference ~arguments:[ Types.Type source ]
                                (Well_known.make_path From)
                            in
                            let convert_from from =
                              Some
                                (Some
                                   (Tables.make_method_call from From_from
                                      ~self_type:interpolation_type ~result:interpolation_type
                                      [ (interpolated, Own) ]))
                            in
                            let view = Types.make_view interpolated_type in
                            if
                              Types.is_viewable interpolated_type
                              && Places.is_borrowed state.State.resolved state.State.tables
                                   interpolated
                              && Option.is_some
                                   (State.find_evidence state interpolation_type (make_from view))
                            then begin
                              let rec strip_parentheses (written : Syntax.expression) =
                                match written.kind with
                                | Parenthesized inner -> strip_parentheses inner
                                | _ -> written
                              in
                              let place = strip_parentheses interpolated in
                              state.places_without_keyword <-
                                List.filter
                                  (fun (noted, _) -> noted <> place.id)
                                  state.places_without_keyword;
                              Conversions.convert state env ~expression:interpolated
                                (Written interpolated.id) ~actual:interpolated_type ~expected:view;
                              convert_from (make_from view)
                            end
                            else if Types.equal interpolated_type interpolation_type then Some None
                            else
                              let from = make_from interpolated_type in
                              match State.find_evidence state interpolation_type from with
                              | Some _ -> convert_from from
                              | None ->
                                  State.report state
                                    (Interpolation_not_convertible
                                       {
                                         at = Written interpolated.id;
                                         interpolated_type;
                                         interpolation_type;
                                         tag_type;
                                       });
                                  None)
                          interpolations))
              | None ->
                  if not (Types.is_error tag_type) then
                    State.report state (Not_a_tag { at = Written literal.id; tag_type }));
          tag_type
      | Some (Unknown report) -> Types.Error report
      | _ -> State.make_error_type state (Tag_not_a_type { at = Written tag.last.id }))

and check_owned state env (value : Syntax.expression) expected =
  let actual = Hooks.check_expression state env ~expected value in
  Modes.infer_view_of_borrowed_place state env value ~actual ~expected;
  Conversions.coerce state env value ~actual ~expected;
  Modes.note_owned_value state env value

and check_list_literal state env ?expected (value : Syntax.expression) items =
  let check_items element = List.iter (fun item -> check_owned state env item element) items in
  let from_elements =
    Types.make_trait_reference ~arguments:[] (Well_known.make_path From_elements)
  in
  match Option.map (Conversions.read_expected_head state) expected with
  | Some (Types.Named { path; arguments = [ Types.Type element ] } as collection)
    when Well_known.is List path || Well_known.is Sequence path || Well_known.is Finite_set path ->
      check_items element;
      collection
  | Some (Types.Named { path; arguments = [ Types.Type element; count ] } as array)
    when Well_known.find_builtin_type path = Some Array ->
      (match count with
      | Types.Value (Known count)
        when (not (Z.fits_int count)) || Z.to_int count <> List.length items ->
          State.report state
            (Array_length { at = Written value.id; given = List.length items; count })
      | _ -> ());
      check_items element;
      array
  | Some collection when takes_literal state collection from_elements ->
      let element =
        Solver.resolve_associated_type state collection from_elements From_elements_element
          ~at:(Written value.id)
      in
      check_items element;
      record_conversion state value (List_element element) collection from_elements
        From_elements_from_elements;
      collection
  | _ ->
      let element = State.make_fresh_type state (List_literal value.id) in
      check_items element;
      Types.make_named (Well_known.make_path List) [ element ]

and check_map_literal state env ?expected (value : Syntax.expression) entries =
  let check_entries key value_type =
    List.iter
      (fun (entry_key, entry_value) ->
        check_owned state env entry_key key;
        check_owned state env entry_value value_type)
      entries
  in
  let from_entries = Types.make_trait_reference ~arguments:[] (Well_known.make_path From_entries) in
  match Option.map (Conversions.read_expected_head state) expected with
  | Some (Types.Named { path; arguments = [ Types.Type key; Types.Type value_type ] } as map)
    when Well_known.is Finite_map path ->
      check_entries key value_type;
      map
  | expected ->
      let map =
        match expected with
        | Some collection when takes_literal state collection from_entries ->
            if Option.is_some (State.find_evidence state collection from_entries) then collection
            else Types.erase_views collection
        | _ ->
            Types.make_named (Well_known.make_path Map)
              [
                State.make_fresh_type state (Map_literal value.id);
                State.make_fresh_type state (Map_literal value.id);
              ]
      in
      let at = Core.Written value.id in
      let key = Solver.resolve_associated_type state map from_entries From_entries_key ~at in
      let value_type =
        Solver.resolve_associated_type state map from_entries From_entries_value ~at
      in
      check_entries key value_type;
      record_conversion state value
        (Map_entry { key; value = value_type })
        map from_entries From_entries_from_entries;
      map

and check_lambda (state : State.state) env ?expected (value : Syntax.expression)
    (parameters : Syntax.lambda_parameter list) body =
  let locals_read_before = state.locals_read in
  state.lambdas <- value.id :: state.lambdas;
  let annotations =
    List.map
      (fun (parameter : Syntax.lambda_parameter) ->
        Option.map
          (fun (annotation : Syntax.parameter_annotation) ->
            ( annotation,
              Interface.Elaborator.elaborate_mode annotation.mode,
              Interface.Elaborator.elaborate_type (State.read_context state) annotation.type_ ))
          parameter.annotation)
      parameters
  in
  let list_annotated_inputs ~make_unannotated =
    List.map
      (function
        | Some (_, mode, annotated) -> (mode, annotated)
        | None -> (Language.Mode.Read, make_unannotated ()))
      annotations
  in
  let make_untyped unknown =
    List.iter2
      (fun (parameter : Syntax.lambda_parameter) (mode, type_) ->
        Pattern_typing.check_pattern state env parameter.pattern type_ ~mode)
      parameters
      (list_annotated_inputs ~make_unannotated:(fun () -> unknown));
    ignore (Statements.check_block_value state env body);
    unknown
  in
  let check_as (function_type : Types.function_type) =
    List.iter2
      (fun ((parameter : Syntax.lambda_parameter), annotation) (mode, input) ->
        Option.iter (check_parameter_annotation state ~mode ~input) annotation;
        require_decided_parameter state parameter input;
        Pattern_typing.check_parameter_pattern state env parameter.pattern input ~mode)
      (List.combine parameters annotations)
      function_type.inputs;
    let output = function_type.output in
    let lambda_env = { env with output = Some (Returns output) } in
    let body_type = Statements.check_block_value state lambda_env ~expected:output body in
    Conversions.convert state lambda_env ?expression:(find_block_value body) (Written body.id)
      ~actual:body_type ~expected:output;
    Types.Function function_type
  in
  let result =
    match Option.map (Conversions.read_expected_head state) expected with
    | Some (Types.Function function_type)
      when List.length function_type.inputs = List.length parameters ->
        check_as function_type
    | Some (Types.Function function_type) ->
        make_untyped
          (State.make_error_type state
             (Lambda_arity
                {
                  at = Written value.id;
                  given = List.length parameters;
                  function_type = Types.Function function_type;
                  expected = List.length function_type.inputs;
                }))
    | Some ((Types.Error _ | Types.Hole) as unknown) -> make_untyped unknown
    | _ ->
        check_as
          {
            inputs =
              list_annotated_inputs ~make_unannotated:(fun () ->
                  Unify.make_fresh_type state.unifier);
            output = Unify.make_fresh_type state.unifier;
            uses = Unify.make_fresh_capability_variable state.unifier;
            costs = [];
          }
  in
  state.lambdas <- List.tl state.lambdas;
  let rec list_newer acc list =
    if list == locals_read_before then acc
    else match list with [] -> acc | id :: rest -> list_newer (id :: acc) rest
  in
  let read = list_newer [] state.locals_read in
  let is_outer id = not (State.contains state ~outer:value.id ~inner:id) in
  let captures =
    List.fold_left
      (fun acc id -> if is_outer id && not (List.mem id acc) then acc @ [ id ] else acc)
      [] read
  in
  State.elaborate state value.id
    (Lambda
       {
         captures =
           List.map
             (fun id : (Syntax.id * Core.local) ->
               if id = state.definition.id then (id, Self)
               else
                 match Hashtbl.find_opt state.locals id with
                 | Some local -> (id, Declared { origin = id; name = local.name })
                 | None -> State.raise_bug "a lambda captures a local that nothing declares")
             captures;
       });
  result

and check_if state env ?expected (test : Syntax.expression) then_ else_ =
  let condition_type =
    Solver.run_in_statement state env (Written test.id) (fun () ->
        Hooks.check_expression state env test)
  in
  Conversions.coerce state env test ~actual:condition_type ~expected:Types.bool;
  match else_ with
  | None ->
      let then_type = Statements.check_block_value state env ~expected:Types.unit then_ in
      (match Conversions.read_expected_head state then_type with
      | Types.Never -> ()
      | _ ->
          if not (State.unify state then_type Types.unit) then
            Failures.report_mismatch state (Written then_.id) ~expected:Types.unit ~actual:then_type);
      Types.unit
  | Some branch ->
      let then_type = Statements.check_block_value state env ?expected then_ in
      let else_type, else_span, else_end =
        match branch with
        | Syntax.Else block ->
            ( Statements.check_block_value state env ?expected block,
              Core.Written block.id,
              find_block_value block )
        | Else_if branch_expression ->
            ( Hooks.check_expression state env ?expected branch_expression,
              Core.Written branch_expression.id,
              Some branch_expression )
      in
      join state env ~expected
        [
          (then_type, Core.Written then_.id, find_block_value then_);
          (else_type, else_span, else_end);
        ]

and check_block state env ?expected (body : Syntax.block) =
  let type_ = Statements.check_block_value state env ?expected body in
  join state env ~expected [ (type_, Core.Written body.id, find_block_value body) ]

and find_block_value (written : Syntax.block) =
  match List.rev written.statements with
  | { kind = Expression value; _ } :: _ -> Some value
  | _ -> None

and join state env ~expected branches =
  let live =
    List.filter
      (fun (type_, _, _) -> Conversions.read_expected_head state type_ <> Types.Never)
      branches
  in
  match (live, expected) with
  | [], _ -> Types.Never
  | _, Some expected ->
      List.iter
        (fun (actual, span, expression) ->
          Conversions.convert state env ?expression span ~actual ~expected)
        live;
      expected
  | (first, _, _) :: rest, None -> (
      let is_view (type_, _, _) = Types.is_view (Conversions.read_expected_head state type_) in
      let is_borrowed_place ((type_, _, (expression : Syntax.expression option)) as branch) =
        (not (is_view branch))
        && Types.is_viewable (Conversions.read_expected_head state type_)
        &&
        match expression with
        | Some written -> Places.is_borrowed state.State.resolved state.State.tables written
        | None -> false
      in
      let joined_view =
        match List.find_opt is_view live with
        | Some branch -> Some branch
        | None when env.State.binds_view && List.for_all is_borrowed_place live ->
            Some (List.hd live)
        | None -> None
      in
      match joined_view with
      | Some (view, _, _) ->
          let view = Types.make_view (Conversions.read_expected_head state view) in
          List.iter
            (fun (actual, span, expression) ->
              Conversions.convert state env ?expression span ~actual ~expected:view)
            live;
          view
      | None ->
          List.iter
            (fun (type_, span, _) ->
              if not (State.unify state first type_) then
                Failures.report_mismatch state span ~expected:first ~actual:type_)
            rest;
          first)

and match_ state env ?expected scrutinees arms =
  let types =
    List.map
      (fun (scrutinee : Syntax.expression) ->
        ( scrutinee,
          Solver.run_in_statement state env (Written scrutinee.id) (fun () ->
              Hooks.check_expression state env scrutinee) ))
      scrutinees
  in
  let branch_types =
    List.map
      (fun (arm : Syntax.arm) ->
        if List.length arm.patterns <> List.length types then
          let unknown =
            State.make_error_type state
              (Arm_pattern_count
                 {
                   at = Written arm.id;
                   given = List.length arm.patterns;
                   expected = List.length types;
                 })
          in
          List.iter
            (fun written ->
              Pattern_typing.check_pattern state env written unknown ~mode:Language.Mode.Read)
            arm.patterns
        else
          List.iter2
            (fun written (scrutinee, type_) ->
              Pattern_typing.check_pattern state env written type_
                ~mode:
                  (Places.classify_scrutinee_mode state.State.resolved state.State.tables scrutinee))
            arm.patterns types;
        Option.iter (fun guard -> Hooks.check state env guard Types.bool) arm.guard;
        ( check_arm_value state env ?expected arm.body,
          Core.Written arm.body.id,
          match arm.body.kind with Expression value -> Some value | _ -> None ))
      arms
  in
  join state env ~expected branch_types

and check_arm_value state env ?expected (body : Syntax.statement) =
  match body.kind with
  | Expression value -> Hooks.check_expression state env ?expected value
  | _ ->
      ignore (Statements.check_statement state env body ~last:false);
      Types.unit

and check_collection_element state env ~(quantifier : Syntax.expression)
    (collection : Syntax.expression) =
  let collection_type = Conversions.read_checked_head state env collection in
  match (collection.kind, collection_type) with
  | ( Range { start = Some _; stop = Some _; inclusive; _ },
      Types.Named { path; arguments = [ Types.Type element ] } )
    when Well_known.is Range path ->
      Statements.record_integer_range state ~loop:quantifier.id ~owner:Range_of_quantifier
        ~admits_integer:true collection element ~inclusive;
      element
  | _, (Types.Error _ | Types.Hole) -> collection_type
  | _ -> (
      let at = Core.Written collection.id in
      match
        Statements.find_elements_loop state ~cause:(Quantifier at) ~at collection_type
          Language.Mode.Read
      with
      | Some (loop, element, _) ->
          State.elaborate state quantifier.id (Loop loop);
          element
      | None ->
          State.make_error_type state
            (Not_iterable_quantifier { at; type_ = State.make_shown state collection_type }))
