let takes_literal (state : State.state) (collection : Types.ty) (trait : Types.trait_reference) =
  match collection with
  | Types.Named _ | Types.Parameter _ | Types.Projection _ -> (
      match
        Interface.Impls.find_evidence state.lookups.interface
          ~list_bounds:(State.lookup_bounds state) ~checks_conditions:false collection trait
      with
      | Some (Evidence (Impl _) | Evidence Bound) -> true
      | Some (Evidence Dynamic | Built_in | Accepted _) | None -> false)
  | _ -> false

let record_conversion (state : State.state) (value : Syntax.expression) elements
    (collection : Types.ty) (trait : Types.trait_reference) method_ =
  State.elaborate state value.id
    (Converted_literal
       {
         elements;
         call = Tables.make_method_call trait method_ ~self_type:collection ~result:collection [];
       });
  Solver.require state (Method_call (State.read_span state value.id)) collection trait

let find_all options =
  List.fold_right
    (fun option all -> Option.bind option (fun each -> Option.map (List.cons each) all))
    options (Some [])

let rec check_string_literal state env ?expected (value : Syntax.expression)
    (literal : Syntax.string_literal) =
  let parts =
    List.map (fun (part, _) -> (part, Hooks.check_expression state env part)) literal.rest
  in
  match literal.tag with
  | None ->
      if parts <> [] then
        State.check_when_final state (fun () ->
            let display = Types.make_trait_reference ~arguments:[] (Well_known.make_path Display) in
            Option.iter
              (fun displays ->
                State.elaborate state value.id (Template (Interpolated { displays })))
              (find_all
                 (List.map
                    (fun ((part : Syntax.expression), part_type) ->
                      let part_type = State.finalize_type state part_type in
                      match State.find_evidence state part_type display with
                      | Some _ ->
                          Some
                            (Tables.make_method_call display Display_display ~self_type:part_type
                               ~result:Types.unit
                               [ (part, Read) ])
                      | None ->
                          State.report state No_impl (State.read_span state part.id)
                            (Printf.sprintf
                               "`%s` does not implement `Display`, so it cannot be interpolated."
                               (Types.show part_type));
                          None)
                    parts)));
      let is_view_expected =
        parts = []
        &&
        match Option.map (Conversions.read_expected_head state) expected with
        | Some expected -> Types.is_well_known String_slice expected
        | None -> false
      in
      if is_view_expected then Types.make_named (Well_known.make_path String_slice) []
      else Types.string_type
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
          List.iter (fun (part, _) -> Modes.note_owned_value state env part) parts;
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
                  let part =
                    Solver.resolve_associated_type state tag_type template_trait From_template_part
                      ~at:(State.read_span state literal.id)
                  in
                  Option.iter
                    (fun part_conversions ->
                      State.elaborate state value.id
                        (Template (Tagged { from_template; part; part_conversions })))
                    (find_all
                       (List.map
                          (fun ((part_expression : Syntax.expression), part_type) ->
                            let part_type = State.finalize_type state part_type in
                            if Types.equal part_type part then Some None
                            else
                              let from =
                                Types.make_trait_reference ~arguments:[ Types.Type part_type ]
                                  (Well_known.make_path From)
                              in
                              match State.find_evidence state part from with
                              | Some _ ->
                                  Some
                                    (Some
                                       (Tables.make_method_call from From_from ~self_type:part
                                          ~result:part
                                          [ (part_expression, Own) ]))
                              | None ->
                                  State.report state No_impl
                                    (State.read_span state part_expression.id)
                                    (Printf.sprintf
                                       "`%s` cannot become a `%s`, the part type of `%s`."
                                       (Types.show part_type) (Types.show part)
                                       (Types.show tag_type));
                                  None)
                          parts))
              | None ->
                  if not (Types.is_error tag_type) then
                    State.report state No_impl
                      (State.read_span state literal.id)
                      (Printf.sprintf "`%s` does not implement `FromTemplate`, so it is not a tag."
                         (Types.show tag_type)));
          tag_type
      | Some (Unknown report) -> Types.Error report
      | _ ->
          State.make_error_type state Not_a_type
            (State.read_span state tag.last.id)
            "A string's tag is a type.")

and check_list_literal state env ?expected (value : Syntax.expression) items =
  let check_items element =
    List.iter (fun item -> Hooks.check state env item element) items;
    List.iter (Modes.note_owned_value state env) items
  in
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
          State.report state Mismatch (State.read_span state value.id)
            (Printf.sprintf "This array has %d elements, and its type says %s." (List.length items)
               (Z.to_string count))
      | _ -> ());
      check_items element;
      array
  | Some collection when takes_literal state collection from_elements ->
      let element =
        Solver.resolve_associated_type state collection from_elements From_elements_element
          ~at:(State.read_span state value.id)
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
        Hooks.check state env entry_key key;
        Hooks.check state env entry_value value_type;
        Modes.note_owned_value state env entry_key;
        Modes.note_owned_value state env entry_value)
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
        | Some collection when takes_literal state collection from_entries -> collection
        | _ ->
            Types.make_named (Well_known.make_path Map)
              [
                State.make_fresh_type state (Map_literal value.id);
                State.make_fresh_type state (Map_literal value.id);
              ]
      in
      let at = State.read_span state value.id in
      let key = Solver.resolve_associated_type state map from_entries From_entries_key ~at in
      let value_type =
        Solver.resolve_associated_type state map from_entries From_entries_value ~at
      in
      check_entries key value_type;
      record_conversion state value
        (Map_entry { key; value = value_type })
        map from_entries From_entries_from_entries;
      map

and check_lambda (state : State.state) env ?expected (value : Syntax.expression) parameters body =
  let locals_read_before = state.locals_read in
  state.lambdas <- State.read_span state value.id :: state.lambdas;
  let expected = Option.map (Conversions.read_expected_head state) expected in
  let make_untyped unknown =
    List.iter
      (fun written ->
        Pattern_typing.check_pattern state env written unknown ~mode:Language.Mode.Read)
      parameters;
    ignore (Statements.check_block_value state env body);
    unknown
  in
  let result =
    match expected with
    | Some (Types.Function function_type)
      when List.length function_type.inputs = List.length parameters ->
        List.iter2
          (fun written (mode, input) ->
            Pattern_typing.check_parameter_pattern state env written input ~mode)
          parameters function_type.inputs;
        let output = function_type.output in
        let lambda_env = { env with output = Some (Returns output) } in
        let body_type = Statements.check_block_value state lambda_env ~expected:output body in
        Conversions.convert state lambda_env ?expression:(find_block_value body)
          (State.read_span state body.id) ~actual:body_type ~expected:output;
        Types.Function function_type
    | Some (Types.Function function_type) ->
        make_untyped
          (State.make_error_type state Mismatch (State.read_span state value.id)
             (Printf.sprintf "This lambda takes %d parameters, and `%s` takes %d."
                (List.length parameters)
                (Types.show (Types.Function function_type))
                (List.length function_type.inputs)))
    | Some ((Types.Error _ | Types.Hole) as unknown) -> make_untyped unknown
    | _ ->
        let remedy =
          match Option.bind expected (State.find_variable_origin state) with
          | Some (Generic_argument { declared_on; parameter; _ }) ->
              Failures.make_bracket_remedy declared_on parameter
          | Some (List_literal _ | Map_literal _) | None ->
              "Bind it with a typed `let`, such as `let double: fn(Int64) -> Int64 = fn(x) { x * 2 \
               }`."
        in
        make_untyped
          (State.make_error_type state Lambda_needs_type (State.read_span state value.id)
             ("A lambda's parameter types come from where it is used, and nothing here gives them. "
            ^ remedy))
  in
  state.lambdas <- List.tl state.lambdas;
  let rec list_newer acc list =
    if list == locals_read_before then acc
    else match list with [] -> acc | id :: rest -> list_newer (id :: acc) rest
  in
  let read = list_newer [] state.locals_read in
  let inside = State.read_span state value.id in
  let is_outer id =
    let binding = State.read_span state id in
    binding.start < inside.start || binding.start >= inside.stop
  in
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
    Solver.run_in_statement state env (State.read_span state test.id) (fun () ->
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
            Failures.report_mismatch state (State.read_span state then_.id) ~expected:Types.unit
              ~actual:then_type);
      Types.unit
  | Some branch ->
      let then_type = Statements.check_block_value state env ?expected then_ in
      let else_type, else_span, else_end =
        match branch with
        | Syntax.Else block ->
            ( Statements.check_block_value state env ?expected block,
              State.read_span state block.id,
              find_block_value block )
        | Else_if branch_expression ->
            ( Hooks.check_expression state env ?expected branch_expression,
              State.read_span state branch_expression.id,
              Some branch_expression )
      in
      join state env ~expected
        [
          (then_type, State.read_span state then_.id, find_block_value then_);
          (else_type, else_span, else_end);
        ]

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
  | (first, _, _) :: rest, None ->
      List.iter
        (fun (type_, span, _) ->
          if not (State.unify state first type_) then
            Failures.report_mismatch state span ~expected:first ~actual:type_)
        rest;
      first

and match_ state env ?expected scrutinees arms =
  let types =
    List.map
      (fun (scrutinee : Syntax.expression) ->
        ( scrutinee,
          Solver.run_in_statement state env (State.read_span state scrutinee.id) (fun () ->
              Hooks.check_expression state env scrutinee) ))
      scrutinees
  in
  let branch_types =
    List.map
      (fun (arm : Syntax.arm) ->
        if List.length arm.patterns <> List.length types then
          let unknown =
            State.make_error_type state Mismatch (State.read_span state arm.id)
              (Printf.sprintf "This arm has %d patterns, and the `match` has %d values."
                 (List.length arm.patterns) (List.length types))
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
          State.read_span state arm.body.id,
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
      Statements.record_integer_range state ~loop:quantifier.id ~described:"A quantifier's"
        ~admits_integer:true collection element ~inclusive;
      element
  | _, (Types.Error _ | Types.Hole) -> collection_type
  | _ -> (
      let at = State.read_span state collection.id in
      match
        Statements.find_elements_loop state ~cause:(Quantifier at) ~at collection_type
          Language.Mode.Read
      with
      | Some (loop, element, _) ->
          State.elaborate state quantifier.id (Loop loop);
          element
      | None ->
          State.make_error_type state Not_iterable at
            (Printf.sprintf "A quantifier cannot go over %s: it does not implement `Iterable`."
               (State.describe state collection_type)))
