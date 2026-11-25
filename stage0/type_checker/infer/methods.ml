let report_unmatched_receiver_mode state env arguments (member : Syntax.name) =
  Calls.check_arguments_alone state env arguments
    (State.make_error_type state
       (No_receiver_overload { at = Written member.id; name = member.text }))

let rec check_call state env ?expected (value : Syntax.expression) (callee : Syntax.expression)
    (arguments : Syntax.argument list) : Types.ty =
  match (callee.kind, State.find_head state callee) with
  | Member (base, { text = "ensures"; _ }), None ->
      check_callback_ensures state env value base arguments
  | Member (base, member), None -> (
      match Instantiation.find_static state base with
      | Some (Static_type type_) ->
          check_static_call state env ?expected value type_ member arguments
      | Some (Static_trait (trait, trait_arguments)) ->
          check_trait_call_in_full state env value trait ~trait_arguments member arguments
      | Some (Static_capability capability) ->
          check_capability_call state env value capability member arguments
      | None -> check_method_call state env ?expected value base member ~type_arguments:[] arguments
      )
  | Bracket ({ kind = Member (base, member); _ }, items), _
    when state.resolved.brackets.(callee.id) = Some Method_bracket ->
      check_method_call state env ?expected value base member ~type_arguments:items arguments
  | _, Some resolution ->
      check_named_method_call state env ?expected value callee resolution arguments
  | _, None -> Calls.check_function_value_call state env value callee arguments

and check_named_method_call state env ?expected (value : Syntax.expression)
    (callee : Syntax.expression) ({ name; target; type_arguments } : Resolve.head) arguments =
  match target with
  | Old -> (
      match arguments with
      | [ argument ] ->
          State.elaborate state value.id (Specification_call Old);
          Hooks.check_expression state env ?expected argument.value
      | _ ->
          Calls.check_arguments_alone state env arguments
            (State.make_error_type state
               (Old_arity { at = Written value.id; given = List.length arguments })))
  | Final -> (
      let names_result (argument : Syntax.expression) =
        match argument.kind with
        | Name name -> State.find_target state name = Some Result_value
        | _ -> false
      in
      match (arguments, env.output) with
      | [ argument ], Some (Lends (_, part)) when names_result argument.value ->
          ignore (Hooks.check_expression state env argument.value);
          let part = State.normalize state part in
          state.tables.resolutions.(value.id) <- Some Specification_value;
          State.elaborate state value.id (Specification_call (Final { part }));
          part
      | _ ->
          Calls.check_arguments_alone state env arguments
            (State.make_error_type state (Final_misused { at = Written value.id })))
  | Identical -> (
      match arguments with
      | [ first; second ] ->
          State.elaborate state value.id (Specification_call Identical);
          let first_type = Hooks.check_expression state env first.value in
          let second_type = Hooks.check_expression state env ~expected:first_type second.value in
          if not (State.unify state first_type second_type) then
            Failures.report_mismatch state (Written second.value.id) ~expected:first_type
              ~actual:second_type;
          Types.bool
      | _ ->
          Calls.check_arguments_alone state env arguments
            (State.make_error_type state
               (Identical_arity { at = Written value.id; given = List.length arguments })))
  | Specification_function (Call_cost metric) -> check_callee_cost state env value metric arguments
  | Specification_function Log -> check_specification_function state env value Log arguments
  | Specification_function Power -> check_specification_function state env value Power arguments
  | Specification_function Calls -> check_specification_function state env value Calls arguments
  | Definition (Type, path) -> (
      match Instantiation.check_named_type state callee path type_arguments with
      | Types.Named { arguments = type_arguments; _ } ->
          Calls.construct state env ?expected ~type_arguments value path None arguments
      | Types.Error _ as error -> Calls.check_arguments_alone state env arguments error
      | _ -> Calls.construct state env ?expected value path None arguments)
  | Variant (type_path, variant) ->
      Calls.construct state env ?expected value type_path (Some variant) arguments
  | Definition ((Function | Theorem), path) -> (
      match Instantiation.find_function_signature state.signatures state.lookups path with
      | Some signature ->
          Calls.check_named_call state env ?expected value path signature
            ~type_arguments:(Option.value ~default:[] type_arguments)
            arguments
      | None -> State.raise_bug "`%s` has no signature" (Path.show path))
  | Definition ((Trait | Capability), _) | Type_parameter _ | Capability_parameter _ ->
      Calls.check_arguments_alone state env arguments
        (State.make_error_type state
           (Not_a_function_or_type { at = Written callee.id; name = name.text }))
  | Unknown report -> Calls.check_arguments_alone state env arguments (Types.Error report)
  | Local _ | Law_parameter _ | Value_parameter _
  | Definition (Constant, _)
  | Field _ | Result_value | Visited ->
      Calls.check_function_value_call state env value callee arguments
  | Binding | Module _ -> State.raise_bug "the name `%s` is not resolved" name.text

and check_specification_function state env (value : Syntax.expression)
    (function_ : Core.specification_function) (arguments : Syntax.argument list) =
  State.elaborate state value.id (Specification_call (Specification_function function_));
  List.iter
    (fun (argument : Syntax.argument) ->
      match function_ with
      | Log -> Clauses.require_integer state env argument.value ~subject:Log_argument
      | Power -> Clauses.require_integer state env argument.value ~subject:Power_argument
      | Callback_cost _ | Calls -> ignore (Hooks.check_expression state env argument.value)
      | Callback_ensures -> State.raise_bug "`.ensures` checked as an integer function")
    arguments;
  Types.Integer

and check_callback_ensures state env (value : Syntax.expression) (base : Syntax.expression)
    (arguments : Syntax.argument list) =
  let at : Core.origin = Written value.id in
  let reject diagnostic =
    Calls.check_arguments_alone state env arguments (State.make_error_type state diagnostic)
  in
  let base_type = Conversions.read_actual_head state base (Hooks.check_expression state env base) in
  match (base.kind, base_type) with
  | Name last, Types.Function function_type
    when match State.find_local state last with
         | Some { binding = Parameter; _ } -> true
         | _ -> false -> (
      let expected =
        List.concat_map
          (fun ((mode : Language.Mode.t), input) ->
            match mode with Mut -> [ input; input ] | Read | Own -> [ input ])
          function_type.inputs
        @
        match function_type.output with
        | Returns output when Types.equal output Types.unit -> []
        | Returns output | Lends (_, output) -> [ output ]
      in
      match List.find_map (fun (argument : Syntax.argument) -> argument.label) arguments with
      | _ when not env.specification ->
          Calls.check_arguments_alone state env arguments
            (Types.Error
               (State.report_specification_only state
                  (Callback_ensures_in_code { at; name = last.text })))
      | Some label ->
          Calls.check_arguments_alone state env arguments
            (State.make_error_type state
               (Callback_ensures_label { at = Written label.id; name = last.text }))
      | None when List.length expected <> List.length arguments ->
          reject
            (Callback_ensures_arity
               {
                 at;
                 name = last.text;
                 inputs = List.map fst function_type.inputs;
                 has_result = function_type.output <> Returns Types.unit;
                 given = List.length arguments;
               })
      | None ->
          List.iter2
            (fun (argument : Syntax.argument) expected_type ->
              Hooks.check state env argument.value expected_type)
            arguments expected;
          State.elaborate state value.id
            (Specification_call (Specification_function Callback_ensures));
          Types.bool)
  | Name last, Types.Function _ -> reject (Ensures_of_non_parameter { at; name = last.text })
  | _, (Types.Error _ as error) -> Calls.check_arguments_alone state env arguments error
  | _ -> reject (Ensures_without_function { at; base = State.make_shown state base_type })

and check_callee_cost state env (value : Syntax.expression) (metric : Language.Metric.t)
    (arguments : Syntax.argument list) =
  let report_not_a_callee operand =
    State.make_error_type state (Cost_operand_not_callee { at = Written value.id; metric; operand })
  in
  match arguments with
  | [ { value = { kind = Member (base, member); _ }; _ } ] -> (
      match Interface.Elaborator.find_bounded_type (State.read_context state) base with
      | Some type_ -> check_method_cost state value metric type_ member
      | None -> report_not_a_callee Operand_is_neither)
  | [ { value = { kind = Name last; _ } as operand; _ } ] -> (
      match
        ( State.find_target state last,
          Option.map (Conversions.read_actual_head state operand) (State.find_local_type state last)
        )
      with
      | ( Some (Local _),
          (Some (Types.Function _ | Types.Variable _ | Types.Hole | Types.Error _) | None) )
      | Some (Unknown _), _ ->
          check_specification_function state env value (Callback_cost metric) arguments
      | Some (Local _), Some other ->
          report_not_a_callee (Local_of_type { name = last.text; type_ = State.zonk state other })
      | _ -> report_not_a_callee (Name_is_neither last.text))
  | _ -> report_not_a_callee Operand_is_neither

and check_method_cost state (value : Syntax.expression) (metric : Language.Metric.t)
    (type_ : Types.ty) (member : Syntax.name) =
  let overloads =
    Interface.Elaborator.list_bound_methods (State.read_context state) type_ member.text
  in
  match (Interface.Elaborator.find_operand_method overloads, overloads) with
  | Some { self_type; trait; name; receiver }, _ ->
      State.elaborate state value.id
        (Specification_call (Method_cost { metric; trait; name; receiver; self_type }));
      Types.Integer
  | None, [] ->
      State.make_error_type state
        (No_bound_method
           { at = Written member.id; type_ = State.zonk state type_; name = member.text })
  | None, _ ->
      State.make_error_type state
        (Ambiguous_cost_method
           { at = Written member.id; type_ = State.zonk state type_; name = member.text; metric })

and report_unknown_static_method state ?expected (value : Syntax.expression) type_
    (member : Syntax.name) (arguments : Syntax.argument list) =
  let implements known =
    Option.is_some
      (State.find_evidence state type_
         (Types.make_trait_reference ~arguments:[] (Well_known.make_path known)))
  in
  let empty_literal =
    if member.text <> "new" || arguments <> [] then None
    else if implements From_elements then Some Catalog.Inference.Empty_list
    else if implements From_entries then Some Empty_map
    else None
  in
  let is_expected =
    match (Option.map (Conversions.read_expected_head state) expected, type_) with
    | Some (Types.Named { path = expected; _ }), Types.Named { path; _ } -> Path.equal expected path
    | _ -> false
  in
  let error =
    match empty_literal with
    | Some literal ->
        State.make_error_type state
          (New_on_literal_type
             {
               at = Written member.id;
               type_ = State.zonk state type_;
               literal;
               call = (if is_expected then Some (Written value.id) else None);
             })
    | None ->
        State.make_error_type state
          (No_method
             {
               at = Written member.id;
               owner = Name_lookup.make_method_owner state type_;
               name = member.text;
               candidates = [];
             })
  in
  ignore (State.unify state type_ error);
  error

and check_static_call state env ?expected (value : Syntax.expression) type_ (member : Syntax.name)
    arguments =
  let report_ambiguous (traits : Types.trait_reference list) =
    Calls.check_arguments_alone state env arguments
      (State.make_error_type state
         (Ambiguous_static_method
            { at = Written member.id; type_ = State.zonk state type_; name = member.text; traits }))
  in
  let wanted_mode = Name_lookup.classify_receiver_mode arguments in
  let wanted = Path.Instance wanted_mode in
  match type_ with
  | Types.Named { path; arguments = type_arguments } when member.case = Upper ->
      Calls.construct state env ?expected ~type_arguments value path (Some member.text) arguments
  | Types.Named { path; _ } -> (
      let static_method = Members.lookup_method state path member.text Static in
      match static_method with
      | Visible method_path -> (
          match
            Instantiation.find_function_signature state.signatures state.lookups method_path
          with
          | Some signature -> (
              let instance =
                Instantiation.instantiate state ~written:value.id ~declared_on:method_path signature
              in
              let head =
                List.take
                  (List.length
                     (match type_ with Types.Named { arguments; _ } -> arguments | _ -> []))
                  instance.instantiation.type_arguments
              in
              ignore
                (Unify.unify_arguments state.unifier head
                   (match type_ with Types.Named { arguments; _ } -> arguments | _ -> []));
              (match (expected, instance.signature.output) with
              | Some expected, Returns output -> State.unify_as_hint state output expected
              | _ -> ());
              match
                Calls.check_arguments state env Argument_matching.Call value
                  instance.signature.parameters ~declared:instance.declared.parameters
                  ~flatten:instance.flatten arguments ~has_receiver:false
              with
              | Error error -> error
              | Ok (checked, left_out) ->
                  Name_lookup.finish_call state env value method_path
                    (Tables.Function { path = method_path; instantiation = instance.instantiation })
                    instance checked left_out)
          | None -> State.raise_bug "the method `%s` has no signature" (Path.show method_path))
      | Hidden _ | Absent -> (
          match Name_lookup.lookup_trait_static_methods state path member.text with
          | Visible [ (trait, method_) ] ->
              check_trait_method_through_type state env ?expected value type_ trait method_
                arguments
          | Visible several -> report_ambiguous (List.map fst several)
          | (Hidden _ | Absent) as trait_static_method -> (
              match Name_lookup.resolve_overloads state type_ member.text with
              | Error traits -> report_ambiguous traits
              | Ok ((Hidden _ | Absent) as overloads) -> (
                  match (static_method, trait_static_method, overloads) with
                  | Hidden hidden, _, _ | _, Hidden hidden, _ | _, _, Hidden hidden ->
                      Calls.check_arguments_alone state env arguments
                        (Members.make_hidden_error state (Written member.id) hidden)
                  | _ ->
                      Calls.check_arguments_alone state env arguments
                        (report_unknown_static_method state ?expected value type_ member arguments))
              | Ok (Visible overloads) -> (
                  match (arguments, List.assoc_opt wanted overloads) with
                  | ([] | { Syntax.label = Some _; _ } :: _), _ ->
                      report_missing_receiver state env value arguments
                  | receiver :: rest, Some (Type_overload method_path | List_overload method_path)
                    ->
                      let inner =
                        match receiver.value.kind with
                        | Mode (mode, inner) ->
                            State.note_mode_keyword state receiver.value mode inner;
                            inner
                        | _ -> receiver.value
                      in
                      let receiver_type = Hooks.check_expression state env inner in
                      let receiver_head = Conversions.read_actual_head state inner receiver_type in
                      if inner != receiver.value then begin
                        State.record state receiver.value receiver_type
                      end;
                      let receiver_as_self =
                        match Types.find_list_of_array receiver_head with
                        | Some list when Types.is_well_known List type_ -> list
                        | _ -> receiver_type
                      in
                      if not (State.unify ~modulo_views:true state receiver_as_self type_) then
                        Failures.report_mismatch state (Written inner.id) ~expected:type_
                          ~actual:receiver_type;
                      Modes.check_mode state env receiver.value
                        ~recipient:(Catalog.Inference.Named_parameter "self") wanted_mode
                        receiver_type;
                      check_method_with_receiver state env ?expected value ~receiver:receiver.value
                        ~receiver_type method_path rest
                  | _ :: _, Some (Trait_overload (trait, method_)) ->
                      check_trait_method_through_type state env ?expected value type_ trait method_
                        arguments
                  | _ :: _, None -> report_unmatched_receiver_mode state env arguments member))))
  | Types.Parameter parameter -> (
      let without_self =
        List.fold_left
          (fun methods (bound : Types.trait_reference) ->
            match
              Interface.Definition.find_trait_method state.lookups.interface bound.trait
                ~name:member.text ~receiver:Static
            with
            | Some method_
              when not
                     (List.exists
                        (fun ((other : Types.trait_reference), _) ->
                          Path.equal other.trait bound.trait)
                        methods) ->
                methods @ [ (bound, method_) ]
            | _ -> methods)
          []
          (Interface.Properties.list_known_bounds state.lookups.interface
             ~list_bounds:(State.lookup_bounds state) (Types.Parameter parameter))
      in
      match (without_self, Name_lookup.resolve_overloads state type_ member.text) with
      | [ (trait, method_) ], _ ->
          check_trait_method_through_type state env ?expected value type_ trait method_ arguments
      | (_ :: _ :: _ as several), _ -> report_ambiguous (List.map fst several)
      | [], Error traits -> report_ambiguous traits
      | [], Ok (Visible overloads) -> (
          match List.assoc_opt wanted overloads with
          | Some (Trait_overload (trait, method_)) ->
              check_trait_method_through_type state env ?expected value type_ trait method_
                arguments
          | Some (Type_overload _ | List_overload _) ->
              State.raise_bug "a generic parameter has a method of its own"
          | None -> report_unmatched_receiver_mode state env arguments member)
      | [], Ok (Hidden _) -> State.raise_bug "a generic parameter has a method of its own"
      | [], Ok Absent ->
          State.make_error_type state
            (No_method
               {
                 at = Written member.id;
                 owner = Named_owner parameter.name;
                 name = member.text;
                 candidates = [];
               }))
  | Types.Error _ | Types.Hole -> Calls.check_arguments_alone state env arguments type_
  | _ ->
      Calls.check_arguments_alone state env arguments
        (State.make_error_type state
           (No_method
              {
                at = Written member.id;
                owner = Type_owner { type_ = State.zonk state type_; list = None };
                name = member.text;
                candidates = [];
              }))

and check_trait_method_through_type state env ?expected:_ ?trait_arguments
    (value : Syntax.expression) self_type (trait : Types.trait_reference)
    (method_ : Types.trait_method) arguments =
  let trait_generics = Members.list_trait_generics state.lookups trait.trait in
  match trait_arguments with
  | Some written when List.length written <> List.length trait_generics ->
      Calls.check_arguments_alone state env arguments
        (State.make_error_type state
           (Trait_arity
              {
                at = Written value.id;
                trait;
                expected = List.length trait_generics;
                given = List.length written;
              }))
  | Some trait_arguments ->
      check_trait_method_call state env value self_type trait method_ arguments ~trait_arguments
  | None ->
      check_trait_method_call state env value self_type trait method_ arguments
        ~trait_arguments:(List.map (Unify.make_fresh_argument state.unifier) trait_generics)

and check_trait_method_call state env (value : Syntax.expression) self_type
    (trait : Types.trait_reference) (method_ : Types.trait_method) arguments ~trait_arguments =
  let reference = { trait with trait_arguments } in
  let instance, callee =
    Name_lookup.instantiate_trait_method state ~written:value.id ~self_type reference method_
  in
  let receiver_and_arguments =
    match (instance.signature.receiver, arguments) with
    | None, _ -> Ok ([], arguments)
    | Some (mode, receiver_type), ({ Syntax.label = None; _ } as receiver) :: rest ->
        let parameter : Types.parameter_info =
          { name = "self"; mode; type_ = receiver_type; has_default = false }
        in
        let mode = Calls.check_argument state env receiver.value parameter in
        Ok ([ { Tables.expression = receiver.value; core_argument_index = 0; mode } ], rest)
    | Some _, ([] | { label = Some _; _ } :: _) ->
        Error (report_missing_receiver state env value arguments)
  in
  match receiver_and_arguments with
  | Error error -> error
  | Ok (receiver_argument, arguments) -> (
      match
        Calls.check_arguments state env Argument_matching.Call value instance.signature.parameters
          ~declared:instance.declared.parameters ~flatten:instance.flatten arguments
          ~has_receiver:(Option.is_some instance.signature.receiver)
      with
      | Error error -> error
      | Ok (checked, left_out) ->
          let result = Types.extract_result_type instance.signature.output in
          State.elaborate state value.id
            (Call
               {
                 callee;
                 arguments = receiver_argument @ checked;
                 omitted_defaults = left_out;
                 callee_result = result;
                 lends = Types.find_lent_mode instance.signature.output;
               });
          Solver.require state (Method_call (Written value.id)) self_type reference;
          State.normalize state result)

and report_missing_receiver state env (value : Syntax.expression) arguments =
  Calls.check_arguments_alone state env arguments
    (State.make_error_type state (Receiver_missing_in_full_call { at = Written value.id }))

and check_trait_call_in_full state env (value : Syntax.expression) trait ~trait_arguments
    (member : Syntax.name) arguments =
  let find_overload receiver =
    Interface.Definition.find_trait_method state.lookups.interface trait ~name:member.text ~receiver
  in
  let wanted : Path.receiver =
    match (Name_lookup.classify_receiver_mode arguments, arguments) with
    | Read, { value = receiver; label = None } :: _
      when Option.is_some (find_overload (Instance Own))
           && ((not (Places.is_place state.resolved state.tables receiver))
              || Option.is_none (find_overload (Instance Read))) ->
        Instance Own
    | mode, _ -> Instance mode
  in
  match
    match find_overload Static with None -> find_overload wanted | trait_method -> trait_method
  with
  | Some method_ ->
      check_trait_method_through_type state env ?trait_arguments value
        (Unify.make_fresh_type state.unifier)
        (Instantiation.make_fresh_trait_reference state trait)
        method_ arguments
  | None when Members.list_trait_methods state.lookups trait member.text <> [] ->
      report_unmatched_receiver_mode state env arguments member
  | None -> (
      let restated =
        match Interface.Definition.find_trait_interface state.lookups.interface trait with
        | Some interface ->
            List.find_opt
              (fun (restated : Types.restated_method) ->
                restated.restated_name = member.text && restated.restated_receiver = wanted)
              interface.restated
        | None -> None
      in
      match
        Option.bind restated (fun (restated : Types.restated_method) ->
            Option.map
              (fun method_ -> (restated.declared_by, method_))
              (Interface.Definition.find_trait_method state.lookups.interface restated.declared_by
                 ~name:member.text ~receiver:wanted))
      with
      | Some (declared_by, method_) ->
          let self_type = Unify.make_fresh_type state.unifier in
          Solver.require state (Method_call (Written value.id)) self_type
            (Instantiation.make_fresh_trait_reference state trait);
          check_trait_method_through_type state env value self_type
            (Instantiation.make_fresh_trait_reference state declared_by)
            method_ arguments
      | None ->
          State.make_error_type state
            (No_method
               {
                 at = Written member.id;
                 owner = Path_owner trait;
                 name = member.text;
                 candidates = [];
               }))

and check_capability_call state env (value : Syntax.expression) capability (member : Syntax.name)
    arguments =
  match
    Interface.Definition.find_trait_method state.lookups.interface capability ~name:member.text
      ~receiver:Static
  with
  | Some method_ -> (
      let instance =
        Instantiation.instantiate state ~written:value.id
          ~declared_on:(Method { owner = capability; name = member.text; receiver = Static })
          (Members.read_method_signature state.signatures state.lookups capability method_)
      in
      match
        Calls.check_arguments state env Argument_matching.Call value instance.signature.parameters
          ~declared:instance.declared.parameters ~flatten:instance.flatten arguments
          ~has_receiver:false
      with
      | Error error -> error
      | Ok (checked, left_out) ->
          let result = Types.extract_result_type instance.signature.output in
          State.elaborate state value.id
            (Call
               {
                 callee = Capability_method { capability; name = member.text };
                 arguments = checked;
                 omitted_defaults = left_out;
                 callee_result = result;
                 lends = None;
               });
          result)
  | None ->
      Calls.check_arguments_alone state env arguments
        (State.make_error_type state
           (No_method
              {
                at = Written member.id;
                owner = Path_owner capability;
                name = member.text;
                candidates = [];
              }))

and check_method_call state env ?expected (value : Syntax.expression) (base : Syntax.expression)
    (member : Syntax.name) ~type_arguments arguments =
  let written_receiver_type =
    let head = Conversions.read_expected_head state (Hooks.check_expression state env base) in
    if Name_lookup.has_sealed_method state head member.text then head
    else
      Solver.decide_default state ~site:Method_call ~at:(Written value.id)
        (Conversions.read_actual_head state base head)
  in
  let is_view_receiver = Types.is_view written_receiver_type in
  let receiver_type =
    Conversions.read_expected_head state (Types.strip_view written_receiver_type)
  in
  let is_implemented_by_the_view (trait : Types.trait_reference) =
    match State.find_evidence state written_receiver_type trait with
    | Some (Evidence (Derived_for_view _)) -> true
    | Some (Evidence (Impl _ | Bound) | Built_in | Accepted _) | None -> false
  in
  let has_mode_keyword = List.mem_assoc value.id state.keyword_modes in
  let lent_mode =
    if has_mode_keyword then None
    else Places.find_lent_mode state.State.resolved state.State.tables base
  in
  let wanted : Path.receiver =
    match (List.assoc_opt value.id state.keyword_modes, lent_mode) with
    | Some Mut, _ | None, Some Mut -> Instance Mut
    | Some Own, _ -> Instance Own
    | _ -> Instance Read
  in
  let place =
    Places.is_place state.State.resolved state.State.tables base || Option.is_some lent_mode
  in
  let choose overloads =
    match List.assoc_opt wanted overloads with
    | Some method_path -> Some (wanted, method_path)
    | None when lent_mode = Some Language.Mode.Mut && List.mem_assoc (Path.Instance Read) overloads
      ->
        Some (Path.Instance Read, List.assoc (Path.Instance Read) overloads)
    | None
      when (not has_mode_keyword)
           && ((not place)
              || State.decide_property state Interface.Properties.Plain written_receiver_type
                 <> Interface.Properties.Fails
              || not (List.mem_assoc (Path.Instance Mut) overloads)) -> (
        match List.assoc_opt (Path.Instance Own) overloads with
        | Some method_path ->
            if Places.is_place state.State.resolved state.State.tables base then
              Modes.note_place_without_keyword state env base ~needs:Own;
            Some (Path.Instance Own, method_path)
        | None -> None)
    | None -> None
  in
  let choose_temporary overloads =
    let chosen =
      if (not has_mode_keyword) && not place then
        match List.assoc_opt (Path.Instance Own) overloads with
        | Some method_path -> Some (Path.Instance Own, method_path)
        | None -> choose overloads
      else choose overloads
    in
    (match chosen with
    | Some (Path.Instance Mut, _) -> Modes.mutate state env ~by:Passed_mut base
    | _ -> ());
    chosen
  in
  let report_wrong_receiver overloads =
    State.make_error_type state
      (Wrong_receiver_overload
         { at = Written member.id; name = member.text; wanted; overloads = List.map fst overloads })
  in
  let report_missing_receiver_mode : 'a. (Path.receiver * 'a) list -> Types.ty =
   fun overloads ->
    if (not has_mode_keyword) && place && List.mem_assoc (Path.Instance Mut) overloads then
      State.make_error_type state
        (Missing_receiver_mode { receiver = Written base.id; name = member.text })
    else report_wrong_receiver (List.map (fun (receiver, _) -> (receiver, ())) overloads)
  in
  match receiver_type with
  | Types.Error _ | Types.Hole ->
      List.iter
        (fun (argument : Syntax.argument) ->
          ignore (Hooks.check_expression state env argument.value))
        arguments;
      receiver_type
  | _ -> (
      match Name_lookup.resolve_overloads state receiver_type member.text with
      | Ok (Hidden hidden) ->
          Calls.check_arguments_alone state env arguments
            (Members.make_hidden_error state (Written member.id) hidden)
      | Ok Absent ->
          let candidates =
            match receiver_type with
            | Types.Named { path; arguments } -> (
                match Members.find_fields state.lookups path arguments with
                | Some fields -> List.map (fun (field : Types.field) -> field.field_name) fields
                | None -> [])
            | _ -> []
          in
          Calls.check_arguments_alone state env arguments
            (State.make_error_type state
               (No_method
                  {
                    at = Written member.id;
                    owner = Name_lookup.make_method_owner state receiver_type;
                    name = member.text;
                    candidates;
                  }))
      | Ok (Visible overloads) -> (
          match
            choose_temporary
              (if is_view_receiver then
                 List.filter
                   (fun (receiver, overload) ->
                     match overload with
                     | Name_lookup.Trait_overload (trait, _) when is_implemented_by_the_view trait
                       ->
                         true
                     | _ -> receiver = Path.Instance Read)
                   overloads
               else overloads)
          with
          | None when is_view_receiver ->
              State.make_error_type state
                (View_receiver
                   {
                     at = Written member.id;
                     name = member.text;
                     receivers = List.map fst overloads;
                   })
          | None -> report_missing_receiver_mode overloads
          | Some (_, (Type_overload method_path | List_overload method_path)) ->
              check_method_with_receiver state env ?expected ~type_arguments value ~receiver:base
                ~receiver_type:written_receiver_type method_path arguments
          | Some (_, Trait_overload (trait, method_)) ->
              check_trait_method_with_receiver state env value ~receiver:base
                ~receiver_type:
                  (if is_implemented_by_the_view trait then written_receiver_type else receiver_type)
                trait method_ ~type_arguments arguments)
      | Error traits ->
          let find_receiver_mode (trait : Types.trait_reference) : Language.Mode.t option =
            let modes =
              List.filter_map
                (fun (method_ : Types.trait_method) ->
                  match method_.method_receiver with Instance mode -> Some mode | Static -> None)
                (Members.list_trait_methods state.lookups trait.trait member.text)
            in
            if List.mem Language.Mode.Read modes then Some Read
            else if List.mem Language.Mode.Own modes then
              if
                (not place)
                || State.decide_property state Interface.Properties.Plain receiver_type
                   <> Interface.Properties.Fails
              then Some Read
              else Some Own
            else if List.mem Language.Mode.Mut modes && place && Modes.is_mutable state env base
            then Some Mut
            else None
          in
          State.make_error_type state
            (Ambiguous_method_call
               {
                 at = Written member.id;
                 call = Written value.id;
                 type_ = State.zonk state receiver_type;
                 name = member.text;
                 receiver = Written base.id;
                 arguments =
                   List.map
                     (fun (argument : Syntax.argument) : Core.origin Catalog.range ->
                       {
                         covering =
                           (match argument.label with
                           | Some label -> [ Written label.id; Written argument.value.id ]
                           | None -> [ Written argument.value.id ]);
                       })
                     arguments;
                 traits =
                   List.filter_map
                     (fun trait ->
                       Option.map (fun mode -> (trait, mode)) (find_receiver_mode trait))
                     traits;
               }))

and check_method_with_receiver state env ?expected ?(type_arguments = [])
    (value : Syntax.expression) ~(receiver : Syntax.expression) ~receiver_type method_path arguments
    =
  match Instantiation.find_function_signature state.signatures state.lookups method_path with
  | None -> State.raise_bug "the method `%s` has no signature" (Path.show method_path)
  | Some signature -> (
      let instance =
        Instantiation.instantiate state ~written:value.id ~declared_on:method_path signature
      in
      match
        Name_lookup.check_explicit_type_arguments
          ~head:
            (match instance.signature.receiver with
            | Some (_, Types.Named { arguments; _ }) -> List.length arguments
            | _ -> 0)
          state value instance type_arguments
      with
      | Error error -> Calls.check_arguments_alone state env arguments error
      | Ok () -> (
          (match instance.signature.receiver with
          | Some (mode, self_type) ->
              Conversions.coerce state env ~argument:mode receiver ~actual:receiver_type
                ~expected:self_type
          | None -> ());
          (match (expected, instance.signature.output) with
          | Some expected, Returns output -> State.unify_as_hint state output expected
          | _ -> ());
          match
            Calls.check_arguments state env Argument_matching.Call value
              instance.signature.parameters ~declared:instance.declared.parameters
              ~flatten:instance.flatten arguments ~has_receiver:true
          with
          | Error error -> error
          | Ok (checked, left_out) ->
              let receiver_argument =
                {
                  Tables.expression = receiver;
                  core_argument_index = 0;
                  mode = (match signature.receiver with Some (mode, _) -> mode | None -> Read);
                }
              in
              Name_lookup.finish_call state env value method_path
                (Tables.Function { path = method_path; instantiation = instance.instantiation })
                instance (receiver_argument :: checked) left_out))

and check_trait_method_with_receiver state env (value : Syntax.expression)
    ~(receiver : Syntax.expression) ~receiver_type (trait : Types.trait_reference)
    (method_ : Types.trait_method) ~type_arguments arguments =
  let instance, callee =
    Name_lookup.instantiate_trait_method state ~written:value.id ~self_type:receiver_type trait
      method_
  in
  match Name_lookup.check_explicit_type_arguments state value instance type_arguments with
  | Error error -> Calls.check_arguments_alone state env arguments error
  | Ok () -> (
      match
        Calls.check_arguments state env Argument_matching.Call value instance.signature.parameters
          ~declared:instance.declared.parameters ~flatten:instance.flatten arguments
          ~has_receiver:true
      with
      | Error error -> error
      | Ok (checked, left_out) ->
          let result = Types.extract_result_type instance.signature.output in
          let receiver_argument =
            {
              Tables.expression = receiver;
              core_argument_index = 0;
              mode = (match method_.method_receiver with Instance mode -> mode | Static -> Read);
            }
          in
          State.elaborate state value.id
            (Call
               {
                 callee;
                 arguments = receiver_argument :: checked;
                 omitted_defaults = left_out;
                 callee_result = result;
                 lends = Types.find_lent_mode instance.signature.output;
               });
          List.iter
            (Solver.require state (Method_call (Written value.id)) receiver_type)
            (Option.to_list (Name_lookup.find_sealed_provider state receiver_type trait) @ [ trait ]);
          State.normalize state result)
