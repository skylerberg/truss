let takes_literal (state : State.state) (collection : Types.ty) (trait : Types.trait_reference) =
  match collection with
  | Types.Named _ | Types.Parameter _ | Types.Projection _ -> (
      match
        Interface.Impls.find_evidence state.lookups.interface
          ~list_bounds:(State.lookup_bounds state) ~checks_conditions:false collection trait
      with
      | Some (From_impl _ | From_bound) -> true
      | Some (From_any | Built_in | Accepted _) | None -> false)
  | _ -> false

let record_conversion (state : State.state) (value : Syntax.expression) (collection : Types.ty)
    (trait : Types.trait_reference) name =
  state.tables.calls.(value.id) <-
    Some
      {
        callee =
          Trait_method
            {
              trait;
              name;
              receiver = Static;
              self_type = collection;
              instantiation = Types.no_instantiation;
              evidence = Built_in;
            };
        arguments = [];
        omitted_defaults = [];
        callee_result = collection;
      };
  Name_lookup.resolve_evidence state value collection trait

let rec check_string_literal state env ?expected (value : Syntax.expression)
    (literal : Syntax.string_literal) =
  let parts =
    List.map (fun (part, _) -> (part, Hooks.check_expression state env part)) literal.rest
  in
  let template : Tables.template =
    {
      from_template = None;
      part_conversions = List.map (fun _ -> None) parts;
      interpolated = parts <> [];
    }
  in
  state.tables.templates.(literal.id) <- Some template;
  let set_part index call =
    match state.tables.templates.(literal.id) with
    | Some template ->
        state.tables.templates.(literal.id) <-
          Some
            {
              template with
              part_conversions =
                List.mapi
                  (fun other existing -> if other = index then Some call else existing)
                  template.part_conversions;
            }
    | None -> ()
  in
  let trait_call ?(mode = Types.Read) trait name receiver self_type evidence arguments result :
      Tables.call =
    {
      callee =
        Trait_method
          {
            trait;
            name;
            receiver;
            self_type;
            instantiation = Types.no_instantiation;
            evidence = State.convert_evidence evidence;
          };
      arguments =
        List.mapi
          (fun index (written : Syntax.expression) ->
            { Tables.expression = written.id; core_argument_index = index; mode })
          arguments;
      omitted_defaults = [];
      callee_result = result;
    }
  in
  match literal.tag with
  | None ->
      State.register_expression state value (fun () ->
          Form.build_untagged_string state ~origin:value.id literal);
      List.iteri
        (fun index ((part : Syntax.expression), part_type) ->
          let display = State.make_trait_reference ~arguments:[] (Well_known.make_path Display) in
          Solver.require state part_type display
            ~on_met:(fun evidence ->
              set_part index
                (trait_call display "display" Path.Read (State.normalize state part_type) evidence
                   [ part ] Types.unit))
            ~on_unmet:(fun part_type _ ->
              State.add_diagnostic state No_impl (State.read_span state part.id)
                (Printf.sprintf "`%s` does not implement `Display`, so it cannot be interpolated."
                   (Types.show part_type))))
        parts;
      let is_view_expected =
        parts = []
        &&
        match Option.map (State.normalize state) expected with
        | Some expected -> Types.is_well_known String_slice expected
        | None -> false
      in
      if is_view_expected then Types.make_named (Well_known.make_path String_slice) []
      else State.string_type
  | Some tag -> (
      match State.find_target state tag.last with
      | Some (Definition (Type, tag_path)) ->
          let tag_type =
            Types.Named
              {
                path = tag_path;
                arguments =
                  Instantiation.instantiate_type state (State.read_span state tag.last.id) tag_path;
              }
          in
          List.iter (fun (part, _) -> Modes.note_owned_value state env part) parts;
          (match expected with
          | Some expected -> ignore (State.unify state tag_type expected)
          | None -> ());
          let template_trait =
            State.make_trait_reference ~arguments:[] (Well_known.make_path From_template)
          in
          let part_type = ref None in
          State.register_expression state value (fun () ->
              match !part_type with
              | Some part ->
                  Form.build_tagged_string state value literal
                    ~part:(State.finalize_type state part)
              | None -> State.raise_bug "a tagged string's part type was not inferred");
          Solver.require state tag_type template_trait
            ~on_met:(fun evidence ->
              let tag_type = State.normalize state tag_type in
              (match state.tables.templates.(literal.id) with
              | Some template ->
                  state.tables.templates.(literal.id) <-
                    Some
                      {
                        template with
                        from_template =
                          Some
                            (trait_call template_trait "from_template" Path.Static tag_type evidence
                               [] tag_type);
                      }
              | None -> ());
              let part =
                State.resolve_associated_type state tag_type template_trait "Part"
                  ~at:(State.read_span state literal.id)
              in
              part_type := Some part;
              List.iteri
                (fun index ((part_expression : Syntax.expression), part_type) ->
                  Solver.check_solved state part_type (fun part_type ->
                      if not (Types.equal part_type part) then
                        let from =
                          State.make_trait_reference ~arguments:[ Types.Type part_type ]
                            (Well_known.make_path From)
                        in
                        Solver.require state part from
                          ~on_met:(fun evidence ->
                            set_part index
                              (trait_call ~mode:Own from "from" Path.Static part evidence
                                 [ part_expression ] part))
                          ~on_unmet:(fun _ _ ->
                            State.add_diagnostic state No_impl
                              (State.read_span state part_expression.id)
                              (Printf.sprintf "`%s` cannot become a `%s`, the part type of `%s`."
                                 (Types.show part_type) (Types.show part) (Types.show tag_type)))))
                parts)
            ~on_unmet:(fun tag_type _ ->
              State.add_diagnostic state No_impl
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
  let register_collection () =
    State.register_expression state value (fun () ->
        Form.build_collection_literal state value (List.map (State.build_expression state) items))
  in
  let from_elements =
    State.make_trait_reference ~arguments:[] (Well_known.make_path From_elements)
  in
  match Option.map (State.normalize state) expected with
  | Some (Types.Named { path; arguments = [ Types.Type element ] } as collection)
    when Well_known.is List path || Well_known.is Sequence path || Well_known.is Finite_set path ->
      check_items element;
      register_collection ();
      collection
  | Some (Types.Named { path; arguments = [ Types.Type element; count ] } as array)
    when Intrinsic.find_builtin path = Some Array ->
      (match count with
      | Types.Value (Known count)
        when (not (Z.fits_int count)) || Z.to_int count <> List.length items ->
          State.report state Mismatch (State.read_span state value.id)
            (Printf.sprintf "This array has %d elements, and its type says %s." (List.length items)
               (Z.to_string count))
      | _ -> ());
      check_items element;
      register_collection ();
      array
  | Some collection when takes_literal state collection from_elements ->
      let element =
        State.resolve_associated_type state collection from_elements "Element"
          ~at:(State.read_span state value.id)
      in
      check_items element;
      record_conversion state value collection from_elements "from_elements";
      State.register_expression state value (fun () ->
          Form.build_converted_literal state value
            ~element:(State.finalize_type state element)
            (List.map (State.build_expression state) items));
      collection
  | _ ->
      let element = State.make_fresh_type state in
      check_items element;
      register_collection ();
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
  let build_entries () =
    List.map
      (fun (entry_key, entry_value) ->
        let entry_key = State.build_expression state entry_key in
        (entry_key, State.build_expression state entry_value))
      entries
  in
  let from_entries = State.make_trait_reference ~arguments:[] (Well_known.make_path From_entries) in
  match Option.map (State.normalize state) expected with
  | Some (Types.Named { path; arguments = [ Types.Type key; Types.Type value_type ] } as map)
    when Well_known.is Finite_map path ->
      check_entries key value_type;
      State.register_expression state value (fun () -> Map_literal { entries = build_entries () });
      map
  | expected ->
      let map =
        match expected with
        | Some collection when takes_literal state collection from_entries -> collection
        | _ ->
            Types.make_named (Well_known.make_path Map)
              [ State.make_fresh_type state; State.make_fresh_type state ]
      in
      let at = State.read_span state value.id in
      let key = State.resolve_associated_type state map from_entries "Key" ~at in
      let value_type = State.resolve_associated_type state map from_entries "Value" ~at in
      check_entries key value_type;
      record_conversion state value map from_entries "from_entries";
      State.register_expression state value (fun () ->
          Form.build_converted_map_literal state value ~key:(State.finalize_type state key)
            ~value_type:(State.finalize_type state value_type)
            (build_entries ()));
      map

and check_lambda (state : State.state) env ?expected (value : Syntax.expression) parameters body =
  let locals_read_before = state.locals_read in
  state.lambdas <- State.read_span state value.id :: state.lambdas;
  let expected = Option.map (State.normalize state) expected in
  let make_untyped unknown =
    List.iter
      (fun written -> Pattern_typing.check_pattern state env written unknown ~mode:Types.Read)
      parameters;
    ignore (Statements.check_block_value state env body);
    unknown
  in
  let result =
    match expected with
    | Some (Types.Function function_type)
      when List.length function_type.inputs = List.length parameters ->
        List.iter2
          (fun written (mode, input) -> Pattern_typing.check_pattern state env written input ~mode)
          parameters function_type.inputs;
        let output = function_type.output in
        let lambda_env = { env with output = Some (Returns output) } in
        let body_type = Statements.check_block_value state lambda_env ~expected:output body in
        State.convert state lambda_env ?expression:(find_block_value_id body)
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
        make_untyped
          (State.make_error_type state Lambda_needs_type (State.read_span state value.id)
             "A lambda's parameter types come from where it is used, and nothing here gives them. \
              Give the `let` a function type, or the call type arguments.")
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
  State.register_expression state value (fun () ->
      let parameters = List.map (State.build_pattern state) parameters in
      Lambda
        {
          parameters;
          captures =
            List.filter_map
              (fun id : Core.capture option ->
                if id = state.definition.id then
                  Some { local = Self; type_ = Form.read_self_type state env }
                else if State.was_hole state (fun tables -> tables.local_types) id then None
                else
                  Some
                    {
                      local = Form.build_declared_local state id;
                      type_ = Form.read_local_type state id;
                    })
              captures;
          body = State.build_block state body;
          result =
            (match Form.read_type state value with
            | Types.Function function_type -> function_type.output
            | type_ -> State.raise_bug "a lambda of type `%s`" (Types.show type_));
        });
  result

and check_if state env ?expected (value : Syntax.expression) (test : Syntax.expression) then_ else_
    =
  let condition_type =
    Solver.run_in_statement state env (State.read_span state test.id) (fun () ->
        Hooks.check_expression state env test)
  in
  Name_lookup.coerce state env test ~actual:condition_type ~expected:Types.bool;
  State.register_expression state value (fun () ->
      let condition = State.build_expression state test in
      let then_ = State.build_block state then_ in
      If
        {
          condition;
          then_;
          else_ =
            Option.map
              (function
                | Syntax.Else block -> State.build_block state block
                | Else_if branch ->
                    let branch = State.build_expression state branch in
                    { Core.statements = []; value = Some branch })
              else_;
          binds_lent_part = Form.binds_lent_part state condition;
        });
  match else_ with
  | None ->
      let then_type = Statements.check_block_value state env ~expected:Types.unit then_ in
      (match State.resolve state then_type with
      | Types.Never -> ()
      | _ ->
          if not (State.unify state then_type Types.unit) then
            State.report_mismatch state (State.read_span state then_.id) ~expected:Types.unit
              ~actual:then_type);
      Types.unit
  | Some branch ->
      let then_type = Statements.check_block_value state env ?expected then_ in
      let else_type, else_span, else_end =
        match branch with
        | Else block ->
            ( Statements.check_block_value state env ?expected block,
              State.read_span state block.id,
              find_block_value_id block )
        | Else_if branch_expression ->
            ( Hooks.check_expression state env ?expected branch_expression,
              State.read_span state branch_expression.id,
              Some branch_expression.id )
      in
      join state env ~expected
        [
          (then_type, State.read_span state then_.id, find_block_value_id then_);
          (else_type, else_span, else_end);
        ]

and find_block_value_id (written : Syntax.block) =
  match List.rev written.statements with
  | { kind = Expression value; _ } :: _ -> Some value.id
  | _ -> None

and join state env ~expected branches =
  let live = List.filter (fun (type_, _, _) -> State.resolve state type_ <> Types.Never) branches in
  match (live, expected) with
  | [], _ -> Types.Never
  | _, Some expected ->
      List.iter
        (fun (actual, span, expression) ->
          State.convert state env ?expression span ~actual ~expected)
        live;
      expected
  | (first, _, _) :: rest, None ->
      List.iter
        (fun (type_, span, _) ->
          if not (State.unify state first type_) then
            State.report_mismatch state span ~expected:first ~actual:type_)
        rest;
      first

and match_ state env ?expected (value : Syntax.expression) scrutinees arms =
  let types =
    List.map
      (fun (scrutinee : Syntax.expression) ->
        ( scrutinee,
          Solver.run_in_statement ~escaping:scrutinee state env (State.read_span state scrutinee.id)
            (fun () -> Hooks.check_expression state env scrutinee) ))
      scrutinees
  in
  State.register_expression state value (fun () ->
      let scrutinees =
        List.map
          (fun scrutinee ->
            Operands.build
              (Modes.classify_scrutinee_mode state scrutinee)
              (State.build_expression state scrutinee))
          scrutinees
      in
      Match
        {
          scrutinees;
          arms =
            List.map
              (fun (arm : Syntax.arm) : Core.arm ->
                let patterns = List.map (State.build_scrutinee_pattern state) arm.patterns in
                let guard = Option.map (State.build_expression state) arm.guard in
                {
                  patterns;
                  guard;
                  body = State.build_block state { statements = [ arm.body ]; id = arm.body.id };
                  origin = arm.id;
                })
              arms;
        });
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
            (fun written -> Pattern_typing.check_pattern state env written unknown ~mode:Types.Read)
            arm.patterns
        else
          List.iter2
            (fun written (scrutinee, type_) ->
              Pattern_typing.check_pattern state env written type_
                ~mode:(Modes.classify_scrutinee_mode state scrutinee))
            arm.patterns types;
        Option.iter (fun guard -> Hooks.check state env guard Types.bool) arm.guard;
        ( check_arm_value state env ?expected arm.body,
          State.read_span state arm.body.id,
          match arm.body.kind with Expression value -> Some value.id | _ -> None ))
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
  let collection_type = State.normalize state (Hooks.check_expression state env collection) in
  match (collection.kind, collection_type) with
  | ( Range { start = Some _; stop = Some _; inclusive; _ },
      Types.Named { path; arguments = [ Types.Type element ] } )
    when Well_known.is Range path ->
      Statements.record_integer_range state ~loop:quantifier.id ~described:"A quantifier's"
        ~admits_integer:true collection element ~inclusive;
      element
  | _, (Types.Error _ | Types.Hole) -> collection_type
  | _ -> (
      match
        Name_lookup.find_elements_calls state
          (State.read_span state collection.id)
          collection_type Types.Read
      with
      | Visible (loop, element, _) ->
          State.record_loop state ~loop:quantifier.id ~iterable:collection loop;
          element
      | Hidden hidden ->
          Members.make_hidden_error state (State.read_span state collection.id) hidden
      | Absent ->
          State.make_error_type state Not_indexable
            (State.read_span state collection.id)
            (Printf.sprintf "`%s` cannot be looped over." (Types.show collection_type)))
