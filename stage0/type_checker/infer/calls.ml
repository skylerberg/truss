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

let make_arity_error state site ~has_receiver (value : Syntax.expression) ~parameter_count
    ~argument_count =
  State.make_error_type state
    (Argument_count
       {
         at = Written value.id;
         callee =
           (match Argument_matching.find_owner site with
           | Some owner -> Fields_of owner
           | None when has_receiver -> Method_besides_self
           | None -> Plain_function);
         expected = parameter_count;
         given = argument_count;
       })

let rec check_function_value_call state env (value : Syntax.expression) (callee : Syntax.expression)
    arguments =
  let callee_type = Conversions.read_checked_head state env callee in
  match callee_type with
  | Types.Function function_type when List.length function_type.inputs <> List.length arguments ->
      check_arguments_alone state env arguments
        (make_arity_error state Argument_matching.Call ~has_receiver:false value
           ~parameter_count:(List.length function_type.inputs)
           ~argument_count:(List.length arguments))
  | Types.Function function_type -> (
      let label_errors =
        List.filter_map
          (fun (argument : Syntax.argument) ->
            Option.map
              (fun (label : Syntax.name) ->
                State.make_error_type state
                  (Label_in_indirect_call
                     { label = Written label.id; value = Written argument.value.id }))
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
            let mode = check_argument state env argument.value parameter in
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
        (State.make_error_type state
           (Not_callable { at = Written callee.id; callee = State.make_shown state callee_type }))

and check_argument state env (value : Syntax.expression) (parameter : Types.parameter_info) =
  let inner =
    match value.kind with
    | Mode (mode, inner)
      when Option.is_none
             (Places.find_keyword_operation state.State.resolved state.State.tables inner) ->
        State.note_mode_keyword state value mode inner;
        inner
    | _ -> value
  in
  let rec view_parts type_ =
    match State.normalize state type_ with
    | Types.Named { path; arguments } as known when not (Types.is_view known) ->
        Types.Named
          {
            path;
            arguments =
              List.map
                (function
                  | Types.Type argument ->
                      let argument = State.normalize state argument in
                      Types.Type
                        (if Types.is_viewable argument then Types.make_view argument
                         else view_parts argument)
                  | Types.Value _ as count -> count)
                arguments;
          }
    | other -> other
  in
  let rec is_construction (written : Syntax.expression) =
    match written.kind with
    | List _ | Map _ -> true
    | Call ({ kind = Name { case = Upper; _ } | Member (_, { case = Upper; _ }); _ }, _) -> true
    | Parenthesized inner -> is_construction inner
    | _ -> false
  in
  let expected =
    match (parameter.mode, inner.kind) with
    | Read, (If _ | Match _ | Block _)
      when Types.is_viewable (Conversions.read_expected_head state parameter.type_) ->
        Types.make_view parameter.type_
    | Read, _ when is_construction inner -> view_parts parameter.type_
    | _ -> parameter.type_
  in
  let actual = Hooks.check_expression state env ~expected inner in
  if inner != value then begin
    State.record state value actual
  end;
  let parameter =
    match Modes.find_lent_field_mode state value actual with
    | Some mode -> { parameter with mode }
    | None -> parameter
  in
  if parameter.mode = Own then
    Modes.infer_view_of_borrowed_place state env value ~actual ~expected:parameter.type_;
  Conversions.coerce state env ~argument:parameter.mode value ~actual ~expected:parameter.type_;
  Modes.check_mode state env value parameter actual;
  parameter.mode

and match_arguments state site (value : Syntax.expression) (parameters : Types.parameter_info list)
    (arguments : Syntax.argument list) =
  let rec find_name (expression : Syntax.expression) =
    match expression.kind with
    | Name last -> Some last.text
    | Mode (_, inner) -> find_name inner
    | _ -> None
  in
  let indexes =
    Argument_matching.list_indexes state site
      ~parameter_names:
        (List.map (fun (parameter : Types.parameter_info) -> parameter.name) parameters)
      (List.map
         (fun (argument : Syntax.argument) ->
           {
             Argument_matching.label = argument.label;
             punned = find_name argument.value;
             origin = Written argument.value.id;
           })
         arguments)
  in
  let assignments = List.combine arguments (List.map Result.to_option indexes) in
  let is_given index = List.exists (fun (_, given) -> given = Some index) assignments in
  let argument_error =
    List.find_map (function Error error -> Some error | Ok _ -> None) indexes
  in
  let missing_errors =
    match argument_error with
    | Some _ -> []
    | None ->
        List.filter_map Fun.id
          (List.mapi
             (fun index (parameter : Types.parameter_info) ->
               if is_given index || parameter.has_default then None
               else
                 Some
                   (State.make_error_type state
                      (Missing_parameter { at = Written value.id; parameter = parameter.name })))
             parameters)
  in
  {
    matched =
      List.filter_map
        (fun (argument, index) -> Option.map (fun index -> (argument, index)) index)
        assignments;
    unmatched =
      List.filter_map
        (fun (argument, index) -> if Option.is_none index then Some argument else None)
        assignments;
    left_out =
      List.filter_map Fun.id
        (List.mapi
           (fun index (parameter : Types.parameter_info) ->
             if (not (is_given index)) && parameter.has_default then Some parameter.name else None)
           parameters);
    error =
      (match argument_error with Some _ -> argument_error | None -> List.nth_opt missing_errors 0);
  }

and check_arguments state env site (value : Syntax.expression)
    (parameters : Types.parameter_info list) ~(declared : Types.parameter_info list) ~flatten
    (arguments : Syntax.argument list) ~has_receiver =
  if List.length arguments > List.length parameters then
    Error
      (check_arguments_alone state env arguments
         (make_arity_error state site ~has_receiver value ~parameter_count:(List.length parameters)
            ~argument_count:(List.length arguments)))
  else
    let { matched; unmatched; left_out; error } =
      match_arguments state site value parameters arguments
    in
    let is_lambda ((argument : Syntax.argument), _) =
      match argument.value.kind with Lambda _ -> true | _ -> false
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
      let mode = check_argument state env argument.value parameter in
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
  let instance = Instantiation.instantiate state ~written:value.id ~declared_on:path signature in
  match Name_lookup.check_explicit_type_arguments state value instance type_arguments with
  | Error error -> check_arguments_alone state env arguments error
  | Ok () -> (
      (match (expected, instance.signature.output) with
      | Some expected, Returns output -> State.unify_as_hint state output expected
      | _ -> ());
      match
        check_arguments state env Argument_matching.Call value instance.signature.parameters
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
    | None -> Instantiation.instantiate_type state ~written:value.id type_path
  in
  let type_ = Types.Named { path = type_path; arguments = type_arguments } in
  (match expected with Some expected -> State.unify_as_hint state type_ expected | None -> ());
  let report_unknown_variant variant =
    Error
      (State.make_error_type state
         (Unknown_variant
            { at = Written value.id; type_ = State.zonk state type_; variant; candidates = [] }))
  in
  let fields =
    match variant with
    | None -> Result.map snd (find_record_fields state (Core.Written value.id) type_)
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
                  (State.make_error_type state
                     (Variant_without_fields { at = Written value.id; variant }))
            | None -> report_unknown_variant variant)
        | None -> report_unknown_variant variant)
  in
  let opaque_error = find_opaque_error state (Core.Written value.id) type_path type_ in
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
      let site =
        match variant with
        | None when Members.is_tuple_type state.lookups type_path ->
            Argument_matching.Tuple_construction
              (Type_named (Types.Named { path = type_path; arguments = [] }))
        | _ ->
            Argument_matching.Construction
              (match variant with
              | Some variant -> Variant_name variant
              | None -> Type_named (Types.Named { path = type_path; arguments = [] }))
      in
      match
        ( check_arguments state env site value parameters ~declared:parameters
            ~flatten:(Solver.flatten state (Bound { at = Written value.id; of_type = None }))
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

and find_record_fields state at type_ =
  match State.normalize state type_ with
  | Types.Named { path; arguments } as type_ -> (
      match Members.find_fields state.lookups path arguments with
      | Some fields -> Ok (path, fields)
      | None -> Error (report_not_a_record state at type_))
  | (Types.Error _ | Types.Hole) as unknown -> Error unknown
  | type_ -> Error (report_not_a_record state at type_)

and report_not_a_record state at type_ =
  State.make_error_type state (Not_a_record_construction { at; type_ = State.zonk state type_ })

and find_opaque_error state at type_path type_ =
  if Members.are_fields_visible state.lookups ~package:state.package type_path then None
  else
    Some (State.make_error_type state (Opaque_construction { at; type_ = State.zonk state type_ }))

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
  | Some Mut -> State.report state (Mut_base_of_with { at = Written base.id })
  | Some Read -> State.raise_bug "a mode keyword recorded as `Read`");
  let written =
    List.filter_map
      (fun (update : Syntax.update) ->
        match update.kind with Update { path; value } -> Some (path, value) | Update_error -> None)
      updates
  in
  State.elaborate state value.id
    (Record_update
       { paths = check_updates state env value ~at:(Core.Written value.id) base_type written });
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
        match_arguments state
          (Construction (Type_named (State.zonk state record_type)))
          value parameters (List.map fst groups)
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
              ignore (check_argument state env argument.value parameter);
              [ (argument.value.id, [ parameter.name ]) ]
          | nested ->
              let at =
                match argument.label with Some label -> Core.Written label.id | None -> at
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
