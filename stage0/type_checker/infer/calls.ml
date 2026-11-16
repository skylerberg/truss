let check_arguments_alone state env (arguments : Syntax.argument list) (type_ : Types.ty) =
  List.iter
    (fun (argument : Syntax.argument) -> ignore (Hooks.check_expression state env argument.value))
    arguments;
  type_

let find_mode_keyword (value : Syntax.expression) : Core.mode_keyword option =
  match value.kind with
  | Mode (_, operand) -> Some { written = value.id; operand = operand.id }
  | _ -> None

let make_arity_error state ?constructor ~has_receiver (value : Syntax.expression) ~parameter_count
    ~argument_count =
  let show_count count singular plural =
    Printf.sprintf "%d %s" count (if count = 1 then singular else plural)
  in
  let verb = if argument_count = 1 then "is" else "are" in
  State.make_error_type state
    (if argument_count < parameter_count then Missing_argument else Too_many_arguments)
    (State.read_span state value.id)
    (match constructor with
    | Some name ->
        Printf.sprintf "`%s` has %s, and %s %s given." name
          (show_count parameter_count "field" "fields")
          (show_count argument_count "argument" "arguments")
          verb
    | None when has_receiver ->
        Printf.sprintf "This method takes %s besides `self`, and %d %s given."
          (show_count parameter_count "argument" "arguments")
          argument_count verb
    | None ->
        Printf.sprintf "This function takes %s, and %d %s given."
          (show_count parameter_count "argument" "arguments")
          argument_count verb)

let rec check_function_value_call state env (value : Syntax.expression) (callee : Syntax.expression)
    arguments =
  let callee_type = State.normalize state (Hooks.check_expression state env callee) in
  match callee_type with
  | Types.Function function_type when List.length function_type.inputs <> List.length arguments ->
      check_arguments_alone state env arguments
        (make_arity_error state ~has_receiver:false value
           ~parameter_count:(List.length function_type.inputs)
           ~argument_count:(List.length arguments))
  | Types.Function function_type ->
      let checked =
        List.mapi
          (fun index (argument : Syntax.argument) ->
            (match argument.label with
            | Some label ->
                State.report state Unknown_label (State.read_span state label.id)
                  ~fixes:
                    [
                      State.fix "Remove the label."
                        [
                          Diagnostic.delete
                            (Source.Definition_span.make (State.read_span state label.id).start
                               (State.read_span state argument.value.id).start);
                        ];
                    ]
                  "A call through a function value passes its arguments by position, without \
                   labels."
            | None -> ());
            let mode, input = List.nth function_type.inputs index in
            let parameter : Types.parameter_info =
              { name = "the function value"; mode; type_ = input; has_default = false }
            in
            let mode = check_argument state env argument.value parameter in
            {
              Tables.expression = argument.value.id;
              core_argument_index = index;
              mode;
              mode_keyword = find_mode_keyword argument.value;
            })
          arguments
      in
      let result = function_type.output in
      state.tables.calls.(value.id) <-
        Some
          {
            callee = Indirect;
            arguments = checked;
            omitted_defaults = [];
            uses = function_type.uses;
            callee_result = result;
          };
      Form.register_call ~function_value:callee state value;
      result
  | Types.Error _ | Types.Hole -> check_arguments_alone state env arguments callee_type
  | _ ->
      check_arguments_alone state env arguments
        (State.make_error_type state Not_callable (State.read_span state callee.id)
           (Printf.sprintf "`%s` is not a function, so it cannot be called."
              (State.show state callee_type)))

and check_argument state env (value : Syntax.expression) (parameter : Types.parameter_info) =
  let inner =
    match value.kind with
    | Mode (_, inner) when Option.is_none (State.find_call_with_mode_keyword state inner) -> inner
    | _ -> value
  in
  let actual = Hooks.check_expression state env ~expected:parameter.type_ inner in
  if inner != value then begin
    State.record state value actual;
    State.alias_expression state value inner
  end;
  let parameter =
    match Modes.find_lent_field_mode state value actual with
    | Some mode -> { parameter with mode }
    | None -> parameter
  in
  Name_lookup.coerce state env ~argument:parameter.mode value ~actual ~expected:parameter.type_;
  Modes.check_mode state env value parameter actual;
  parameter.mode

and match_arguments state ?constructor (value : Syntax.expression)
    (parameters : Types.parameter_info list) (arguments : Syntax.argument list) =
  let named =
    List.mapi (fun index (parameter : Types.parameter_info) -> (parameter.name, index)) parameters
  in
  let find_bare_name_index (argument : Syntax.argument) =
    let rec find_name (expression : Syntax.expression) =
      match expression.kind with
      | Name { modules = []; last } -> Some last.text
      | Mode (_, inner) -> find_name inner
      | _ -> None
    in
    Option.bind (find_name argument.value) (fun name -> List.assoc_opt name named)
  in
  let has_several_fields = Option.is_some constructor && List.length parameters > 1 in
  let takes_bare_value position = position = 0 && not has_several_fields in
  let assigned = Hashtbl.create 8 in
  let matched =
    List.mapi
      (fun position (argument : Syntax.argument) ->
        let parameter_index =
          match argument.label with
          | Some label -> (
              match List.assoc_opt label.text named with
              | Some index -> Some index
              | None ->
                  State.report state Unknown_label (State.read_span state label.id)
                    ~fixes:
                      (match Diagnostic.find_closest label.text (List.map fst named) with
                      | Some candidate ->
                          [
                            State.fix
                              (Printf.sprintf "Write `%s`." candidate)
                              [ State.replace (State.read_span state label.id) candidate ];
                          ]
                      | None -> [])
                    (Printf.sprintf "No parameter is named `%s`." label.text);
                  None)
          | None -> (
              match find_bare_name_index argument with
              | Some index -> Some index
              | None ->
                  if takes_bare_value position then Some 0
                  else begin
                    let claimed =
                      List.concat
                        (List.mapi
                           (fun position (other : Syntax.argument) ->
                             match other.label with
                             | Some label -> Option.to_list (List.assoc_opt label.text named)
                             | None -> (
                                 match find_bare_name_index other with
                                 | Some index -> [ index ]
                                 | None -> if takes_bare_value position then [ 0 ] else []))
                           arguments)
                    in
                    let unlabeled =
                      List.length
                        (List.filteri
                           (fun position (other : Syntax.argument) ->
                             other.label = None
                             && Option.is_none (find_bare_name_index other)
                             && not (takes_bare_value position))
                           arguments)
                    in
                    let open_parameters =
                      List.filter (fun (_, index) -> not (List.mem index claimed)) named
                    in
                    let fixes =
                      match (open_parameters, unlabeled) with
                      | [ (label, _) ], 1 ->
                          [
                            State.fix
                              (Printf.sprintf "Label it `%s`." label)
                              [
                                State.insert (State.read_span state argument.value.id).start
                                  (label ^ ": ");
                              ];
                          ]
                      | _ -> []
                    in
                    State.report state Missing_label
                      (State.read_span state argument.value.id)
                      ~fixes
                      (match constructor with
                      | Some name ->
                          Printf.sprintf
                            "`%s` has %d fields, and fields have no order. Every argument needs a \
                             label, or a variable with its field's name."
                            name (List.length parameters)
                      | None ->
                          "Every argument after the first needs a label, or a variable with its \
                           parameter's name.");
                    None
                  end)
        in
        (match parameter_index with
        | Some index ->
            if Hashtbl.mem assigned index then begin
              State.report state Repeated_argument
                (State.read_span state argument.value.id)
                (Printf.sprintf "`%s` is given more than once." (List.nth parameters index).name)
            end
            else Hashtbl.replace assigned index ()
        | None -> ());
        (argument, parameter_index))
      arguments
  in
  (if Option.is_none constructor then
     let indexes = List.filter_map snd matched in
     let sorted = List.sort compare indexes in
     if indexes <> sorted && List.length matched = List.length indexes then
       match (arguments, List.rev arguments) with
       | first :: _, last :: _ ->
           let ordered =
             List.map fst
               (List.sort
                  (fun (_, left) (_, right) -> compare left right)
                  (List.map (fun (argument, index) -> (argument, Option.get index)) matched))
           in
           let spell_written (argument : Syntax.argument) =
             let start =
               match argument.label with
               | Some label -> (State.read_span state label.id).start
               | None -> (State.read_span state argument.value.id).start
             in
             State.quote_span state
               (Source.Definition_span.make start (State.read_span state argument.value.id).stop)
           in
           let start =
             match first.label with
             | Some label -> (State.read_span state label.id).start
             | None -> (State.read_span state first.value.id).start
           in
           State.report state Out_of_order (State.read_span state value.id)
             ~fixes:
               [
                 State.fix "Put the arguments in the order of the parameters."
                   [
                     State.replace
                       (Source.Definition_span.make start (State.read_span state last.value.id).stop)
                       (String.concat ", " (List.map spell_written ordered));
                   ];
               ]
             "The arguments must come in the order of the parameters."
       | _ -> ());
  let missing =
    List.filter
      (fun (_, index) ->
        (not (Hashtbl.mem assigned index)) && not (List.nth parameters index).has_default)
      named
  in
  if List.for_all (fun (_, parameter_index) -> Option.is_some parameter_index) matched then
    List.iter
      (fun (name, _) ->
        State.report state Missing_argument (State.read_span state value.id)
          (Printf.sprintf "`%s` is not given, and has no default." name))
      missing;
  let left_out =
    List.filter_map
      (fun (name, index) ->
        if (not (Hashtbl.mem assigned index)) && (List.nth parameters index).has_default then
          Some name
        else None)
      named
  in
  ( List.filter_map
      (fun (argument, parameter_index) ->
        Option.map (fun index -> (argument, index)) parameter_index)
      matched,
    left_out )

and check_arguments state env ?constructor (value : Syntax.expression)
    (parameters : Types.parameter_info list) (arguments : Syntax.argument list) ~has_receiver =
  if List.length arguments > List.length parameters then
    Error
      (check_arguments_alone state env arguments
         (make_arity_error state ?constructor ~has_receiver value
            ~parameter_count:(List.length parameters) ~argument_count:(List.length arguments)))
  else
    let matched, left_out = match_arguments state ?constructor value parameters arguments in
    let is_lambda ((argument : Syntax.argument), _) =
      match argument.value.kind with Lambda _ -> true | _ -> false
    in
    let check ((argument : Syntax.argument), index) =
      let parameter = List.nth parameters index in
      let mode = check_argument state env argument.value parameter in
      {
        Tables.expression = argument.value.id;
        core_argument_index = (if has_receiver then index + 1 else index);
        mode;
        mode_keyword = find_mode_keyword argument.value;
      }
    in
    let non_lambdas = List.map check (List.filter (fun pair -> not (is_lambda pair)) matched) in
    let lambdas = List.map check (List.filter is_lambda matched) in
    let order = List.map (fun ((argument : Syntax.argument), _) -> argument.value.id) matched in
    Ok
      ( List.filter_map
          (fun id ->
            List.find_opt
              (fun (checked : Tables.argument) -> checked.expression = id)
              (non_lambdas @ lambdas))
          order,
        left_out )

and check_named_call state env ?expected (value : Syntax.expression) path
    (signature : Types.signature) ~type_arguments arguments =
  let instance = Instantiation.instantiate state (State.read_span state value.id) signature in
  match Name_lookup.check_explicit_type_arguments state value instance type_arguments with
  | Error error -> check_arguments_alone state env arguments error
  | Ok () -> (
      (match (expected, instance.signature.output) with
      | Some expected, Returns output -> State.unify_as_hint state output expected
      | _ -> ());
      match
        check_arguments state env value instance.signature.parameters arguments ~has_receiver:false
      with
      | Error error -> error
      | Ok (checked, left_out) ->
          let callee =
            match Intrinsic.operation_of_path path with
            | Some operation ->
                Tables.Intrinsic { operation; type_arguments = instance.type_arguments }
            | None -> Tables.Function { path; type_arguments = instance.type_arguments }
          in
          Name_lookup.finish_call state env value path callee instance checked left_out)

and construct state env ?expected ?type_arguments (value : Syntax.expression) type_path variant
    arguments =
  let type_arguments =
    match type_arguments with
    | Some written -> written
    | None -> Instantiation.instantiate_type state (State.read_span state value.id) type_path
  in
  let type_ = Types.Named { path = type_path; arguments = type_arguments } in
  (match expected with Some expected -> State.unify_as_hint state type_ expected | None -> ());
  let report_unknown_variant variant =
    Error
      (State.make_error_type state Unknown_variant (State.read_span state value.id)
         (Printf.sprintf "`%s` has no variant `%s`." (State.show state type_) variant))
  in
  let fields =
    match variant with
    | None -> (
        match Members.find_fields state.lookups type_path type_arguments with
        | Some fields -> Ok fields
        | None ->
            Error
              (State.make_error_type state Not_a_record (State.read_span state value.id)
                 (Printf.sprintf "`%s` is not a record, so it cannot be built this way."
                    (State.show state type_))))
    | Some variant -> (
        match Members.find_variants state.lookups type_path type_arguments with
        | Some variants -> (
            match
              List.find_opt
                (fun (written : Types.variant) -> written.variant_name = variant)
                variants
            with
            | Some { fields = Some fields; _ } -> Ok fields
            | Some { fields = None; _ } ->
                Error
                  (State.make_error_type state Too_many_arguments (State.read_span state value.id)
                     (Printf.sprintf "`%s` has no fields." variant))
            | None -> report_unknown_variant variant)
        | None -> report_unknown_variant variant)
  in
  if not (Members.are_fields_visible state.lookups ~package:state.package type_path) then
    State.report state Private_field (State.read_span state value.id)
      (Printf.sprintf "`%s` is opaque, so only its own package can build it."
         (State.show state type_));
  match fields with
  | Error error -> check_arguments_alone state env arguments error
  | Ok fields -> (
      let parameters =
        List.map
          (fun (field : Types.field) ->
            {
              Types.name = field.field_name;
              mode = Own;
              type_ = field.field_type;
              has_default = field.field_has_default;
            })
          fields
      in
      Option.iter
        (fun mode ->
          List.iter
            (fun (argument : Syntax.argument) ->
              Hashtbl.replace state.yielded argument.value.id mode)
            arguments)
        (Hashtbl.find_opt state.yielded value.id);
      let constructor =
        match variant with
        | Some variant -> variant
        | None -> Types.show (Types.Named { path = type_path; arguments = [] })
      in
      match
        check_arguments state env ~constructor value parameters arguments ~has_receiver:false
      with
      | Error error -> error
      | Ok (checked, left_out) ->
          state.tables.calls.(value.id) <-
            Some
              {
                callee = Constructor { type_ = type_path; variant; type_arguments };
                arguments = checked;
                omitted_defaults = left_out;
                uses = Types.no_capabilities;
                callee_result = type_;
              };
          Form.register_call state value;
          type_)
