type matching = {
  matched : (Syntax.argument * int) list;
  unmatched : Syntax.argument list;
  left_out : string list;
  error : Types.ty option;
}

let check_arguments_alone state env (arguments : Syntax.argument list) (unknown : Types.ty) =
  (match unknown with
  | Types.Error _ | Types.Hole -> ()
  | _ -> State.raise_bug "arguments without parameters checked against `%s`" (Types.show unknown));
  List.iter
    (fun (argument : Syntax.argument) ->
      match argument.value.kind with
      | Lambda _ -> ignore (Hooks.check_expression state env ~expected:unknown argument.value)
      | _ -> ignore (State.unify state (Hooks.check_expression state env argument.value) unknown))
    arguments;
  unknown

let make_arity_error state ?constructor ~has_receiver (value : Syntax.expression) ~parameter_count
    ~argument_count =
  let given = Diagnostic.show_count argument_count "is" "are" in
  State.make_error_type state
    (if argument_count < parameter_count then Missing_argument else Too_many_arguments)
    (State.read_span state value.id)
    (match constructor with
    | Some name ->
        Printf.sprintf "`%s` has %s, and %s given." name
          (Diagnostic.show_count parameter_count "field" "fields")
          (Diagnostic.show_count argument_count "argument is" "arguments are")
    | None when has_receiver ->
        Printf.sprintf "This method takes %s besides `self`, and %s given."
          (Diagnostic.show_count parameter_count "argument" "arguments")
          given
    | None ->
        Printf.sprintf "This function takes %s, and %s given."
          (Diagnostic.show_count parameter_count "argument" "arguments")
          given)

let rec check_function_value_call state env (value : Syntax.expression) (callee : Syntax.expression)
    arguments =
  let callee_type = Conversions.read_checked_head state env callee in
  match callee_type with
  | Types.Function function_type when List.length function_type.inputs <> List.length arguments ->
      check_arguments_alone state env arguments
        (make_arity_error state ~has_receiver:false value
           ~parameter_count:(List.length function_type.inputs)
           ~argument_count:(List.length arguments))
  | Types.Function function_type -> (
      let label_errors =
        List.filter_map
          (fun (argument : Syntax.argument) ->
            Option.map
              (fun (label : Syntax.name) ->
                State.make_error_type state Unknown_label (State.read_span state label.id)
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
                   labels.")
              argument.label)
          arguments
      in
      let checked =
        List.mapi
          (fun index (argument : Syntax.argument) ->
            let mode, input = List.nth function_type.inputs index in
            let parameter : Types.parameter_info =
              { name = "the function value"; mode; type_ = input; has_default = false }
            in
            let mode = check_argument state env argument.value parameter ~has_generic_type:false in
            { Tables.expression = argument.value; core_argument_index = index; mode })
          arguments
      in
      match label_errors with
      | error :: _ -> error
      | [] ->
          let result = function_type.output in
          State.elaborate state value.id
            (Call
               {
                 callee = Indirect;
                 arguments = checked;
                 omitted_defaults = [];
                 callee_result = result;
                 lends = None;
               });
          result)
  | Types.Error _ | Types.Hole -> check_arguments_alone state env arguments callee_type
  | _ ->
      check_arguments_alone state env arguments
        (State.make_error_type state Not_callable (State.read_span state callee.id)
           (Printf.sprintf "%s is not a function, so it cannot be called."
              (String.capitalize_ascii (State.describe state callee_type))))

and check_argument state env (value : Syntax.expression) (parameter : Types.parameter_info)
    ~has_generic_type =
  let inner =
    match value.kind with
    | Mode (mode, inner)
      when Option.is_none
             (Places.find_keyword_operation state.State.resolved state.State.tables inner) ->
        State.note_mode_keyword state value mode inner;
        inner
    | _ -> value
  in
  let actual = Hooks.check_expression state env ~expected:parameter.type_ inner in
  if inner != value then begin
    State.record state value actual
  end;
  let parameter =
    match Modes.find_lent_field_mode state value actual with
    | Some mode -> { parameter with mode }
    | None -> parameter
  in
  Conversions.coerce state env ~argument:parameter.mode
    ~takes_view_as_owner:(has_generic_type && parameter.mode = Read)
    value ~actual ~expected:parameter.type_;
  Modes.check_mode state env value parameter actual ~has_generic_type;
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
  let first_error = ref None in
  let reject ?fixes code span message =
    let error = State.make_error_type state ?fixes code span message in
    if Option.is_none !first_error then first_error := Some error
  in
  let assigned = Hashtbl.create 8 in
  let assignments =
    List.mapi
      (fun position (argument : Syntax.argument) ->
        let parameter_index =
          match argument.label with
          | Some label -> (
              match List.assoc_opt label.text named with
              | Some index -> Some index
              | None ->
                  reject Unknown_label (State.read_span state label.id)
                    ~fixes:
                      (Diagnostic.list_spelling_fixes (State.read_span state label.id)
                         ~written:label.text (List.map fst named))
                    (match constructor with
                    | Some name -> Printf.sprintf "`%s` has no field `%s`." name label.text
                    | None -> Printf.sprintf "No parameter is named `%s`." label.text);
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
                    reject Missing_label
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
        match parameter_index with
        | Some index when Hashtbl.mem assigned index ->
            reject Repeated_argument
              (State.read_span state
                 (match argument.label with Some label -> label.id | None -> argument.value.id))
              (Printf.sprintf "`%s` is given more than once." (List.nth parameters index).name);
            (argument, None)
        | Some index ->
            Hashtbl.replace assigned index ();
            (argument, Some index)
        | None -> (argument, None))
      arguments
  in
  (if Option.is_none constructor then
     let indexes = List.filter_map snd assignments in
     let sorted = List.sort compare indexes in
     if indexes <> sorted && List.length assignments = List.length indexes then
       match (arguments, List.rev arguments) with
       | first :: _, last :: _ ->
           let ordered =
             List.map fst
               (List.sort
                  (fun (_, left) (_, right) -> compare left right)
                  (List.map (fun (argument, index) -> (argument, Option.get index)) assignments))
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
           reject Out_of_order (State.read_span state value.id)
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
  if List.for_all (fun (_, parameter_index) -> Option.is_some parameter_index) assignments then
    List.iter
      (fun (name, _) ->
        reject Missing_argument (State.read_span state value.id)
          (Printf.sprintf "`%s` is not given, and has no default." name))
      missing;
  {
    matched =
      List.filter_map
        (fun (argument, parameter_index) ->
          Option.map (fun index -> (argument, index)) parameter_index)
        assignments;
    unmatched =
      List.filter_map
        (fun (argument, parameter_index) ->
          if Option.is_none parameter_index then Some argument else None)
        assignments;
    left_out =
      List.filter_map
        (fun (name, index) ->
          if (not (Hashtbl.mem assigned index)) && (List.nth parameters index).has_default then
            Some name
          else None)
        named;
    error = !first_error;
  }

and check_arguments state env ?constructor (value : Syntax.expression)
    (parameters : Types.parameter_info list) ~(declared : Types.parameter_info list) ~flatten
    (arguments : Syntax.argument list) ~has_receiver =
  if List.length arguments > List.length parameters then
    Error
      (check_arguments_alone state env arguments
         (make_arity_error state ?constructor ~has_receiver value
            ~parameter_count:(List.length parameters) ~argument_count:(List.length arguments)))
  else
    let { matched; unmatched; left_out; error } =
      match_arguments state ?constructor value parameters arguments
    in
    let is_lambda ((argument : Syntax.argument), _) =
      match argument.value.kind with Lambda _ -> true | _ -> false
    in
    let has_generic_type (_, index) =
      match (List.nth declared index).type_ with
      | Types.Parameter _ | Projection _ -> true
      | _ -> false
    in
    let is_checked_late (_, index) =
      match (List.nth declared index).type_ with
      | Types.Projection _ -> true
      | Types.Parameter _ -> (List.nth parameters index).mode = Read
      | _ -> false
    in
    let check ((argument : Syntax.argument), index) =
      let parameter = List.nth parameters index in
      let parameter = { parameter with type_ = flatten parameter.type_ } in
      let mode =
        check_argument state env argument.value parameter
          ~has_generic_type:(has_generic_type (argument, index))
      in
      {
        Tables.expression = argument.value;
        core_argument_index = (if has_receiver then index + 1 else index);
        mode;
      }
    in
    let values, lambdas = List.partition (fun pair -> not (is_lambda pair)) matched in
    let late, others = List.partition is_checked_late values in
    let others = List.map check others in
    let late = List.map check late in
    let lambdas = List.map check lambdas in
    match (error, unmatched) with
    | Some error, _ -> Error (check_arguments_alone state env unmatched error)
    | None, _ :: _ -> State.raise_bug "an argument has no parameter, and no diagnostic says why"
    | None, [] ->
        let order = List.map (fun ((argument : Syntax.argument), _) -> argument.value.id) matched in
        Ok
          ( List.filter_map
              (fun id ->
                List.find_opt
                  (fun (checked : Tables.argument) -> checked.expression.id = id)
                  (others @ late @ lambdas))
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
        check_arguments state env value instance.signature.parameters
          ~declared:instance.declared.parameters ~flatten:instance.flatten arguments
          ~has_receiver:false
      with
      | Error error -> error
      | Ok (checked, left_out) ->
          let callee =
            match Intrinsic.find_operation path with
            | Some operation ->
                Tables.Intrinsic
                  { operation; type_arguments = instance.instantiation.type_arguments }
            | None -> Tables.Function { path; instantiation = instance.instantiation }
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
    | None -> Result.map snd (find_record_fields state (State.read_span state value.id) type_)
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
  let opaque_error = find_opaque_error state (State.read_span state value.id) type_path type_ in
  match fields with
  | Error error -> check_arguments_alone state env arguments error
  | Ok fields -> (
      let parameters = make_field_parameters ~keeps_unlisted:false fields in
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
        ( check_arguments state env ~constructor value parameters ~declared:parameters
            ~flatten:
              (Solver.flatten state (Bound { at = State.read_span state value.id; of_type = None }))
            arguments ~has_receiver:false,
          opaque_error )
      with
      | Error error, _ | Ok _, Some error -> error
      | Ok (checked, left_out), None ->
          State.elaborate state value.id
            (Call
               {
                 callee = Constructor { type_ = type_path; variant; type_arguments };
                 arguments = checked;
                 omitted_defaults = left_out;
                 callee_result = type_;
                 lends = None;
               });
          type_)

and find_record_fields state span type_ =
  match State.normalize state type_ with
  | Types.Named { path; arguments } as type_ -> (
      match Members.find_fields state.lookups path arguments with
      | Some fields -> Ok (path, fields)
      | None -> Error (report_not_a_record state span type_))
  | (Types.Error _ | Types.Hole) as unknown -> Error unknown
  | type_ -> Error (report_not_a_record state span type_)

and report_not_a_record state span type_ =
  State.make_error_type state Not_a_record span
    (Printf.sprintf "`%s` is not a record, so it cannot be built this way." (State.show state type_))

and find_opaque_error state span type_path type_ =
  if Members.are_fields_visible state.lookups ~package:state.package type_path then None
  else
    Some
      (State.make_error_type state Private_field span
         (Printf.sprintf "`%s` is opaque, so only its own package can build it."
            (State.show state type_)))

and make_field_parameters ~keeps_unlisted (fields : Types.field list) =
  List.map
    (fun (field : Types.field) ->
      {
        Types.name = field.field_name;
        mode = Own;
        type_ = field.field_type;
        has_default = keeps_unlisted || field.field_has_default;
      })
    fields

and check_record_update state env (value : Syntax.expression) (base : Syntax.expression) updates =
  let base_type = Conversions.read_checked_head state env base in
  (match List.assoc_opt value.id state.keyword_modes with
  | None -> Modes.note_owned_value state env base
  | Some Own -> ()
  | Some Mut ->
      State.report state Wrong_mode (State.read_span state base.id)
        "`with` takes ownership of its base, so the base is passed `own`, not `mut`."
  | Some Read -> State.raise_bug "a mode keyword recorded as `Read`");
  let written =
    List.filter_map
      (fun (update : Syntax.update) ->
        match update.kind with Update { path; value } -> Some (path, value) | Update_error -> None)
      updates
  in
  State.elaborate state value.id
    (Record_update
       {
         paths =
           check_updates state env value ~at:(State.read_span state value.id) base_type written;
       });
  base_type

and check_updates state env (value : Syntax.expression) ~at record_type
    (updates : (Syntax.name list * Syntax.expression) list) =
  match find_record_fields state at (Conversions.read_actual_head state value record_type) with
  | Error unknown ->
      ignore (check_arguments_alone state env (List.map make_update_argument updates) unknown);
      []
  | Ok (path, fields) ->
      ignore (find_opaque_error state at path record_type);
      let parameters = make_field_parameters ~keeps_unlisted:true fields in
      let groups = group_updates updates in
      let { matched; unmatched; error; _ } =
        match_arguments state ~constructor:(State.show state record_type) value parameters
          (List.map fst groups)
      in
      Option.iter (fun error -> ignore (check_arguments_alone state env unmatched error)) error;
      List.concat_map
        (fun ((argument : Syntax.argument), index) ->
          let declared = List.nth parameters index in
          let parameter =
            {
              declared with
              type_ = Solver.flatten state (Bound { at; of_type = None }) declared.type_;
            }
          in
          match List.assq argument groups with
          | [] ->
              ignore
                (check_argument state env argument.value parameter
                   ~has_generic_type:
                     (match declared.type_ with
                     | Types.Parameter _ | Projection _ -> true
                     | _ -> false));
              [ (argument.value.id, [ parameter.name ]) ]
          | nested ->
              let at =
                match argument.label with
                | Some label -> State.read_span state label.id
                | None -> at
              in
              List.map
                (fun (id, path) -> (id, parameter.name :: path))
                (check_updates state env value ~at parameter.type_ nested))
        matched

and make_update_argument ((path : Syntax.name list), value) : Syntax.argument =
  { label = List.nth_opt path 0; value }

and group_updates (updates : (Syntax.name list * Syntax.expression) list) =
  match updates with
  | [] -> []
  | ((([] | [ _ ]), _) as update) :: rest -> (make_update_argument update, []) :: group_updates rest
  | (((field : Syntax.name) :: _ :: _, _) as first) :: _ ->
      let is_inside (names, _) =
        match names with (name : Syntax.name) :: _ :: _ -> name.text = field.text | _ -> false
      in
      let inside, outside = List.partition is_inside updates in
      ( make_update_argument first,
        List.filter_map
          (fun (names, written) ->
            match names with _ :: rest -> Some (rest, written) | [] -> None)
          inside )
      :: group_updates outside
