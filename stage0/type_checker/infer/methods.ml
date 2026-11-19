let report_unmatched_receiver_mode state env arguments (member : Syntax.name) =
  Calls.check_arguments_alone state env arguments
    (State.make_error_type state Wrong_receiver (State.read_span state member.id)
       (Printf.sprintf
          "`%s` has no overload for this receiver's mode; pass the receiver `mut` or `own` as its \
           overloads take."
          member.text))

let rec check_call state env ?expected (value : Syntax.expression) (callee : Syntax.expression)
    (arguments : Syntax.argument list) : Types.ty =
  match callee.kind with
  | Member (base, member) -> (
      match Instantiation.find_static state base with
      | Some (Static_type type_) ->
          check_static_call state env ?expected value type_ member arguments
      | Some (Static_trait (trait, trait_arguments)) ->
          check_trait_call_in_full state env value trait ~trait_arguments member arguments
      | Some (Static_capability capability) ->
          check_capability_call state env value capability member arguments
      | None -> check_method_call state env ?expected value base member ~type_arguments:[] arguments
      )
  | Bracket ({ kind = Member (base, member); _ }, items)
    when state.resolved.brackets.(callee.id) = Some Method_bracket ->
      check_method_call state env ?expected value base member ~type_arguments:items arguments
  | _ -> (
      match State.find_head state callee with
      | Some resolution ->
          check_named_method_call state env ?expected value callee resolution arguments
      | None -> Calls.check_function_value_call state env value callee arguments)

and check_named_method_call state env ?expected (value : Syntax.expression)
    (callee : Syntax.expression) ({ name; target; type_arguments } : Resolve.head) arguments =
  match target with
  | Old -> (
      match arguments with
      | [ argument ] ->
          State.register_expression state value (fun () ->
              Old (State.build_expression state argument.value));
          Hooks.check_expression state env ?expected argument.value
      | _ ->
          Calls.check_arguments_alone state env arguments
            (State.make_error_type state
               (if arguments = [] then Missing_argument else Too_many_arguments)
               (State.read_span state value.id) "`old` takes one value: `old(value)`."))
  | Final -> (
      let names_result (argument : Syntax.expression) =
        match argument.kind with
        | Name path -> State.find_target state path.last = Some Result_value
        | _ -> false
      in
      match (arguments, env.output) with
      | [ argument ], Some (Lends (_, part)) when names_result argument.value ->
          ignore (Hooks.check_expression state env argument.value);
          let part = State.normalize state part in
          let parts : Types.ty =
            Named { path = Well_known.make_path Sequence; arguments = [ Types.Type part ] }
          in
          let { Well_known.owner; name; receiver } = Well_known.locate_method Index_at in
          let index = State.make_trait_reference ~arguments:[] (Well_known.make_path owner) in
          let evidence =
            match State.find_evidence state parts index with
            | Some evidence -> Form.convert_evidence (State.convert_evidence evidence)
            | None -> State.raise_bug "`Sequence` does not implement `Index`"
          in
          state.tables.resolutions.(value.id) <- Some Specification_value;
          State.register_expression state value (fun () ->
              let make = State.make_synthetic_expression state ~origin:value.id in
              let build_read_argument = Operands.build_argument Read in
              let first =
                make part
                  (Call
                     (State.make_call state
                        ~callee:
                          (Trait_method
                             {
                               trait = index;
                               name;
                               receiver;
                               self_type = parts;
                               instantiation = Types.no_instantiation;
                               evidence;
                             })
                        ~arguments:
                          [
                            build_read_argument (make parts Yielded);
                            build_read_argument (make Types.Integer (Integer Z.zero));
                          ]
                        ~lends:(Some Read)))
              in
              Use (Lent first));
          part
      | _ ->
          Calls.check_arguments_alone state env arguments
            (State.make_error_type state Not_callable (State.read_span state value.id)
               "`final` takes the part that a lending method lends: `final(result)` is that part \
                as the caller left it."))
  | Identical -> (
      match arguments with
      | [ first; second ] ->
          let first_type = Hooks.check_expression state env first.value in
          let second_type = Hooks.check_expression state env ~expected:first_type second.value in
          if not (State.unify state first_type second_type) then
            State.report_mismatch state
              (State.read_span state second.value.id)
              ~expected:first_type ~actual:second_type;
          State.register_expression state value (fun () ->
              let first = State.build_expression state first.value in
              Identical (first, State.build_expression state second.value));
          Types.bool
      | _ ->
          Calls.check_arguments_alone state env arguments
            (State.make_error_type state
               (if List.length arguments < 2 then Missing_argument else Too_many_arguments)
               (State.read_span state value.id) "`identical` takes two values of one type."))
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
      match Instantiation.find_function_signature state path with
      | Some signature ->
          Calls.check_named_call state env ?expected value path signature
            ~type_arguments:(Option.value ~default:[] type_arguments)
            arguments
      | None -> State.raise_bug "`%s` has no signature" (Path.show path))
  | Definition ((Trait | Capability), _) | Type_parameter _ | Capability_parameter _ ->
      Calls.check_arguments_alone state env arguments
        (State.make_error_type state Not_callable (State.read_span state callee.id)
           (Printf.sprintf "`%s` is not a function or a type, so it cannot be called." name.text))
  | Unknown report -> Calls.check_arguments_alone state env arguments (Types.Error report)
  | Local _ | Law_parameter _ | Value_parameter _
  | Definition (Constant, _)
  | Field _ | Result_value | Visited ->
      Calls.check_function_value_call state env value callee arguments
  | Binding | Module _ -> State.raise_bug "the name `%s` is not resolved" name.text

and check_specification_function state env (value : Syntax.expression)
    (function_ : Core.specification_function) (arguments : Syntax.argument list) =
  State.register_expression state value (fun () ->
      Specification_function
        {
          function_;
          arguments =
            List.map
              (fun (argument : Syntax.argument) -> State.build_expression state argument.value)
              arguments;
        });
  List.iter
    (fun (argument : Syntax.argument) -> ignore (Hooks.check_expression state env argument.value))
    arguments;
  Types.Integer

and check_callee_cost state env (value : Syntax.expression) (metric : Metric.t)
    (arguments : Syntax.argument list) =
  let report_not_a_callee operand_description =
    let cost_function = Metric.show metric in
    State.make_error_type state Not_callable (State.read_span state value.id)
      (Printf.sprintf
         "`%s` takes a function parameter, as in `%s(visit)`, or a method of a bound, as in \
          `%s(Element.equal)`, and %s."
         cost_function cost_function cost_function operand_description)
  in
  match arguments with
  | [ { value = { kind = Member (base, member); _ }; _ } ] -> (
      match Interface.Elaborator.find_bounded_type state.context base with
      | Some type_ -> check_method_cost state value metric type_ member
      | None -> report_not_a_callee "its operand is neither")
  | [ { value = { kind = Name { modules = []; last }; _ }; _ } ] -> (
      match (State.find_target state last, State.find_local_type state last) with
      | ( Some (Local _),
          (Some (Types.Function _ | Types.Variable _ | Types.Hole | Types.Error _) | None) )
      | Some (Unknown _), _ ->
          check_specification_function state env value (Callback_cost metric) arguments
      | Some (Local _), Some other ->
          report_not_a_callee (Printf.sprintf "`%s` is a `%s`" last.text (State.show state other))
      | _ -> report_not_a_callee (Printf.sprintf "`%s` is neither" last.text))
  | _ -> report_not_a_callee "its operand is neither"

and check_method_cost state (value : Syntax.expression) (metric : Metric.t) (type_ : Types.ty)
    (member : Syntax.name) =
  let overloads = Interface.Elaborator.list_bound_methods state.context type_ member.text in
  match (Interface.Elaborator.find_operand_method overloads, overloads) with
  | Some { self_type; trait; name; receiver }, _ ->
      State.register_expression state value (fun () ->
          Method_cost
            {
              metric;
              method_ =
                Trait_method
                  {
                    trait;
                    name;
                    receiver;
                    self_type;
                    instantiation = Types.no_instantiation;
                    evidence = Bound;
                  };
            });
      Types.Integer
  | None, [] ->
      State.make_error_type state Unknown_member (State.read_span state member.id)
        (Printf.sprintf "`%s` has no method `%s`: no trait that bounds it declares one."
           (State.show state type_) member.text)
  | None, _ ->
      State.make_error_type state Ambiguous_method (State.read_span state member.id)
        (Printf.sprintf
           "`%s` has more than one method `%s`, and none of them is the only one that takes `self` \
            read-only, so `%s` cannot tell which one is meant."
           (State.show state type_) member.text (Metric.show metric))

and report_unknown_static_method state ?expected (value : Syntax.expression) type_
    (member : Syntax.name) (arguments : Syntax.argument list) =
  let implements known =
    Option.is_some
      (State.find_evidence state type_
         (State.make_trait_reference ~arguments:[] (Well_known.make_path known)))
  in
  let empty_literal =
    if member.text <> "new" || arguments <> [] then None
    else if implements From_elements then Some "[]"
    else if implements From_entries then Some "[:]"
    else None
  in
  let is_expected =
    match (Option.map (State.normalize state) expected, type_) with
    | Some (Types.Named { path = expected; _ }), Types.Named { path; _ } -> Path.equal expected path
    | _ -> false
  in
  match empty_literal with
  | Some literal ->
      State.make_error_type state Unknown_member (State.read_span state member.id)
        ~fixes:
          (if is_expected then
             [
               State.fix
                 (Printf.sprintf "Write `%s`." literal)
                 [ State.replace (State.read_span state value.id) literal ];
             ]
           else [])
        (Printf.sprintf "`%s` has no method `new`. The literal `%s` is an empty `%s`."
           (State.show state type_) literal (State.show state type_))
  | None ->
      State.make_error_type state Unknown_member (State.read_span state member.id)
        (Name_lookup.describe_missing_method state type_ member.text)

and check_static_call state env ?expected (value : Syntax.expression) type_ (member : Syntax.name)
    arguments =
  let report_ambiguous (traits : Types.trait_reference list) =
    Calls.check_arguments_alone state env arguments
      (State.make_error_type state Ambiguous_method (State.read_span state member.id)
         (Printf.sprintf
            "More than one trait gives `%s` a method `%s`: %s. Call it through the trait to say \
             which."
            (State.show state type_) member.text
            (String.concat ", " (List.map (fun trait -> "`" ^ Types.show_trait trait ^ "`") traits))))
  in
  let wanted : Path.receiver =
    match arguments with
    | receiver :: _ -> Name_lookup.classify_receiver receiver.value
    | [] -> Read
  in
  match type_ with
  | Types.Named { path; arguments = type_arguments } when member.case = Upper ->
      Calls.construct state env ?expected ~type_arguments value path (Some member.text) arguments
  | Types.Named { path; _ } -> (
      let static_method = Members.lookup_method state path member.text Static in
      match static_method with
      | Visible method_path -> (
          match Instantiation.find_function_signature state method_path with
          | Some signature -> (
              let instance =
                Instantiation.instantiate state (State.read_span state value.id) signature
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
                Calls.check_arguments state env value instance.signature.parameters
                  ~declared:instance.declared.parameters arguments ~has_receiver:false
              with
              | Error error -> error
              | Ok (checked, left_out) ->
                  Name_lookup.finish_call state env value method_path
                    (Tables.Function { path = method_path; instantiation = instance.instantiation })
                    instance checked left_out)
          | None -> State.raise_bug "the method `%s` has no signature" (Path.show method_path))
      | Hidden _ | Absent -> (
          match Name_lookup.list_trait_static_methods state path member.text Static with
          | [ (trait, method_) ] ->
              check_trait_method_through_type state env ?expected value type_ trait method_
                arguments
          | _ :: _ :: _ as several -> report_ambiguous (List.map fst several)
          | [] -> (
              match Name_lookup.resolve_overloads state type_ member.text with
              | Error traits -> report_ambiguous traits
              | Ok ((Hidden _ | Absent) as overloads) -> (
                  match (static_method, overloads) with
                  | Hidden hidden, _ | _, Hidden hidden ->
                      Calls.check_arguments_alone state env arguments
                        (Members.make_hidden_error state (State.read_span state member.id) hidden)
                  | _ ->
                      Calls.check_arguments_alone state env arguments
                        (report_unknown_static_method state ?expected value type_ member arguments))
              | Ok (Visible overloads) -> (
                  match (arguments, List.assoc_opt wanted overloads) with
                  | receiver :: rest, Some (Type_overload method_path | View_overload method_path)
                    ->
                      let inner =
                        match receiver.value.kind with
                        | Mode (mode, inner) ->
                            State.note_mode_keyword state receiver.value mode inner;
                            inner
                        | _ -> receiver.value
                      in
                      let receiver_type = Hooks.check_expression state env inner in
                      if inner != receiver.value then begin
                        State.record state receiver.value receiver_type;
                        State.alias_expression state receiver.value inner
                      end;
                      if
                        not
                          (State.unify state
                             (Option.value ~default:receiver_type
                                (State.find_view_as state ~owned:receiver_type ~view:type_))
                             type_)
                      then
                        State.report_mismatch state (State.read_span state inner.id) ~expected:type_
                          ~actual:receiver_type;
                      let mode : Types.mode =
                        match wanted with Mut -> Mut | Own -> Own | _ -> Read
                      in
                      Modes.check_mode state env receiver.value
                        { name = "self"; mode; type_; has_default = false }
                        receiver_type;
                      check_method_with_receiver state env ?expected value ~receiver:receiver.value
                        ~receiver_type method_path rest
                  | _ :: _, Some (Trait_overload (trait, method_)) ->
                      check_trait_method_through_type state env ?expected value type_ trait method_
                        arguments
                  | _ :: _, None -> report_unmatched_receiver_mode state env arguments member
                  | [], _ ->
                      State.make_error_type state Missing_argument (State.read_span state value.id)
                        "A method written in full takes its receiver as its first argument."))))
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
          | Some (Type_overload _ | View_overload _) ->
              State.raise_bug "a generic parameter has a method of its own"
          | None -> report_unmatched_receiver_mode state env arguments member)
      | [], Ok (Hidden _) -> State.raise_bug "a generic parameter has a method of its own"
      | [], Ok Absent ->
          State.make_error_type state Unknown_member (State.read_span state member.id)
            (Printf.sprintf "`%s` has no method `%s`." parameter.name member.text))
  | Types.Error _ | Types.Hole -> Calls.check_arguments_alone state env arguments type_
  | _ ->
      Calls.check_arguments_alone state env arguments
        (State.make_error_type state Unknown_member (State.read_span state member.id)
           (Printf.sprintf "`%s` has no method `%s`." (State.show state type_) member.text))

and check_trait_method_through_type state env ?expected:_ ?trait_arguments
    (value : Syntax.expression) self_type (trait : Types.trait_reference)
    (method_ : Types.trait_method) arguments =
  let trait_generics = Members.list_trait_generics state.lookups trait.trait in
  match trait_arguments with
  | Some written when List.length written <> List.length trait_generics ->
      Calls.check_arguments_alone state env arguments
        (State.make_error_type state Arity (State.read_span state value.id)
           (Printf.sprintf "`%s` takes %s, and %s given." (Types.show_trait trait)
              (Diagnostic.show_count (List.length trait_generics) "type argument" "type arguments")
              (Diagnostic.show_count (List.length written) "is" "are")))
  | Some trait_arguments ->
      check_trait_method_call state env value self_type trait method_ arguments ~trait_arguments
  | None ->
      check_trait_method_call state env value self_type trait method_ arguments
        ~trait_arguments:(Instantiation.make_fresh_generic_arguments state trait_generics)

and check_trait_method_call state env (value : Syntax.expression) self_type
    (trait : Types.trait_reference) (method_ : Types.trait_method) arguments ~trait_arguments =
  let reference = { trait with trait_arguments } in
  let instance, callee =
    Name_lookup.instantiate_trait_method state (State.read_span state value.id) ~self_type reference
      method_ ~evidence:Built_in
  in
  let receiver_argument, arguments =
    match instance.signature.receiver with
    | Some (receiver, receiver_type) -> (
        match arguments with
        | first :: rest ->
            let mode : Types.mode = match receiver with Mut -> Mut | Own -> Own | _ -> Read in
            let parameter : Types.parameter_info =
              { name = "self"; mode; type_ = receiver_type; has_default = false }
            in
            let mode =
              Calls.check_argument state env first.value parameter ~has_generic_type:false
            in
            ignore
              (State.decide_default_literal state ~at:(State.read_span state value.id) self_type);
            ([ { Tables.expression = first.value.id; core_argument_index = 0; mode } ], rest)
        | [] -> ([], []))
    | None -> ([], arguments)
  in
  match
    Calls.check_arguments state env value instance.signature.parameters
      ~declared:instance.declared.parameters arguments
      ~has_receiver:(Option.is_some instance.signature.receiver)
  with
  | Error error -> error
  | Ok (checked, left_out) ->
      let result = Types.extract_result_type instance.signature.output in
      Modes.note_lending state value instance.signature.output;
      state.tables.calls.(value.id) <-
        Some
          {
            callee;
            arguments = receiver_argument @ checked;
            omitted_defaults = left_out;
            callee_result = result;
          };
      Form.register_call state value;
      Name_lookup.resolve_evidence state value self_type reference;
      State.normalize state result

and check_trait_call_in_full state env (value : Syntax.expression) trait ~trait_arguments
    (member : Syntax.name) arguments =
  let wanted : Path.receiver =
    match arguments with
    | receiver :: _ -> Name_lookup.classify_receiver receiver.value
    | [] -> Read
  in
  let find_overload receiver =
    Interface.Definition.find_trait_method state.lookups.interface trait ~name:member.text ~receiver
  in
  match
    match find_overload Static with None -> find_overload wanted | trait_method -> trait_method
  with
  | Some method_ ->
      check_trait_method_through_type state env ?trait_arguments value (State.make_fresh_type state)
        (Instantiation.make_fresh_trait_reference state trait)
        method_ arguments
  | None when Members.list_trait_methods state.lookups trait member.text <> [] ->
      report_unmatched_receiver_mode state env arguments member
  | None ->
      State.make_error_type state Unknown_member (State.read_span state member.id)
        (Printf.sprintf "`%s` has no method `%s`." (Path.show trait) member.text)

and check_capability_call state env (value : Syntax.expression) capability (member : Syntax.name)
    arguments =
  match
    Interface.Definition.find_trait_method state.lookups.interface capability ~name:member.text
      ~receiver:Static
  with
  | Some method_ -> (
      let instance =
        Instantiation.instantiate state (State.read_span state value.id)
          (Members.read_method_signature state.lookups capability method_)
      in
      match
        Calls.check_arguments state env value instance.signature.parameters
          ~declared:instance.declared.parameters arguments ~has_receiver:false
      with
      | Error error -> error
      | Ok (checked, left_out) ->
          let result = Types.extract_result_type instance.signature.output in
          state.tables.calls.(value.id) <-
            Some
              {
                callee = Capability_method { capability; name = member.text };
                arguments = checked;
                omitted_defaults = left_out;
                callee_result = result;
              };
          Form.register_call state value;
          result)
  | None ->
      Calls.check_arguments_alone state env arguments
        (State.make_error_type state Unknown_member (State.read_span state member.id)
           (Printf.sprintf "`%s` has no method `%s`." (Path.show capability) member.text))

and check_method_call state env ?expected (value : Syntax.expression) (base : Syntax.expression)
    (member : Syntax.name) ~type_arguments arguments =
  let receiver_type =
    State.decide_default_literal state ~at:(State.read_span state value.id)
      (State.normalize state (Hooks.check_expression state env base))
  in
  let has_mode_keyword = List.mem_assoc value.id state.keyword_modes in
  let lent_mode = if has_mode_keyword then None else Modes.find_lent_mode state base in
  let wanted : Path.receiver =
    match (List.assoc_opt value.id state.keyword_modes, lent_mode) with
    | Some Mut, _ | None, Some Mut -> Mut
    | Some Own, _ -> Own
    | _ -> Read
  in
  let place = State.is_place state base || Option.is_some lent_mode in
  let choose overloads =
    match List.assoc_opt wanted overloads with
    | Some method_path -> Some (wanted, method_path)
    | None when lent_mode = Some Types.Mut && List.mem_assoc Path.Read overloads ->
        Some (Path.Read, List.assoc Path.Read overloads)
    | None
      when (not has_mode_keyword)
           && ((not place)
              || State.decide_property state Interface.Properties.Plain receiver_type
                 <> Interface.Properties.Fails
              || not (List.mem_assoc Path.Mut overloads)) -> (
        match List.assoc_opt Path.Own overloads with
        | Some method_path ->
            if State.is_place state base then
              Modes.note_place_without_keyword state env base ~needs:Own;
            Some (Path.Own, method_path)
        | None -> None)
    | None -> None
  in
  let choose_temporary overloads =
    let chosen =
      if (not has_mode_keyword) && not place then
        match List.assoc_opt Path.Own overloads with
        | Some method_path -> Some (Path.Own, method_path)
        | None -> choose overloads
      else choose overloads
    in
    (match chosen with Some (Path.Mut, _) -> Modes.mutate state env ~by:Passed_mut base | _ -> ());
    chosen
  in
  let report_wrong_receiver overloads =
    State.make_error_type state Wrong_receiver (State.read_span state member.id)
      (Printf.sprintf "`%s` has no overload that takes %s here; it has %s." member.text
         (Path.show_receiver wanted)
         (String.concat ", "
            (List.map (fun (receiver, _) -> Path.show_receiver receiver) overloads)))
  in
  let report_missing_receiver_mode : 'a. (Path.receiver * 'a) list -> Types.ty =
   fun overloads ->
    if (not has_mode_keyword) && place && List.mem_assoc Path.Mut overloads then
      State.make_error_type state Missing_mode (State.read_span state base.id)
        ~fixes:
          [
            State.fix "Pass it `mut`." [ State.insert (State.read_span state base.id).start "mut " ];
          ]
        (Printf.sprintf "`%s` takes `mut self`, so the call site passes its receiver `mut`."
           member.text)
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
            (Members.make_hidden_error state (State.read_span state member.id) hidden)
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
            (State.make_error_type state Unknown_member (State.read_span state member.id)
               ~fixes:
                 (Diagnostic.list_spelling_fixes (State.read_span state member.id)
                    ~written:member.text candidates)
               (Name_lookup.describe_missing_method state receiver_type member.text))
      | Ok (Visible overloads) -> (
          match choose_temporary overloads with
          | None -> report_missing_receiver_mode overloads
          | Some (_, (Type_overload method_path | View_overload method_path)) ->
              check_method_with_receiver state env ?expected ~type_arguments value ~receiver:base
                ~receiver_type method_path arguments
          | Some (_, Trait_overload (trait, method_)) ->
              check_trait_method_with_receiver state env value ~receiver:base ~receiver_type trait
                method_ ~type_arguments arguments)
      | Error traits ->
          let receiver_text = State.quote_span state (State.read_span state base.id) in
          let arguments_text =
            List.map
              (fun (argument : Syntax.argument) ->
                let start =
                  match argument.label with
                  | Some label -> (State.read_span state label.id).start
                  | None -> (State.read_span state argument.value.id).start
                in
                State.quote_span state
                  (Source.Definition_span.make start (State.read_span state argument.value.id).stop))
              arguments
          in
          State.make_error_type state Ambiguous_method (State.read_span state member.id)
            ~fixes:
              (List.map
                 (fun (trait : Types.trait_reference) ->
                   let name =
                     match trait.trait with Top { name; _ } -> name | path -> Path.show path
                   in
                   State.fix
                     (Printf.sprintf "Call `%s`'s `%s`." name member.text)
                     [
                       State.replace (State.read_span state value.id)
                         (Printf.sprintf "%s.%s(%s)" name member.text
                            (String.concat ", " (receiver_text :: arguments_text)));
                     ])
                 traits)
            (Printf.sprintf
               "More than one trait gives `%s` a method `%s`. Write the call in full to say which."
               (State.show state receiver_type) member.text))

and check_method_with_receiver state env ?expected ?(type_arguments = [])
    (value : Syntax.expression) ~(receiver : Syntax.expression) ~receiver_type method_path arguments
    =
  match Instantiation.find_function_signature state method_path with
  | None -> State.raise_bug "the method `%s` has no signature" (Path.show method_path)
  | Some signature -> (
      let instance = Instantiation.instantiate state (State.read_span state value.id) signature in
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
          | Some (mode, self_type) -> (
              match State.find_view_as state ~owned:receiver_type ~view:self_type with
              | Some _ ->
                  Name_lookup.coerce state env
                    ~argument:(match mode with Mut -> Mut | Own -> Own | Read | Static -> Read)
                    receiver ~actual:receiver_type ~expected:self_type
              | None ->
                  if not (State.unify state self_type receiver_type) then
                    State.report_mismatch state
                      (State.read_span state receiver.id)
                      ~expected:self_type ~actual:receiver_type)
          | None -> ());
          (match (expected, instance.signature.output) with
          | Some expected, Returns output -> State.unify_as_hint state output expected
          | _ -> ());
          match
            Calls.check_arguments state env value instance.signature.parameters
              ~declared:instance.declared.parameters arguments ~has_receiver:true
          with
          | Error error -> error
          | Ok (checked, left_out) ->
              let receiver_argument =
                {
                  Tables.expression = receiver.id;
                  core_argument_index = 0;
                  mode =
                    (match signature.receiver with
                    | Some (Mut, _) -> Mut
                    | Some (Own, _) -> Own
                    | _ -> Read);
                }
              in
              Name_lookup.finish_call state env value method_path
                (Tables.Function { path = method_path; instantiation = instance.instantiation })
                instance (receiver_argument :: checked) left_out))

and check_trait_method_with_receiver state env (value : Syntax.expression)
    ~(receiver : Syntax.expression) ~receiver_type (trait : Types.trait_reference)
    (method_ : Types.trait_method) ~type_arguments arguments =
  let not_callable =
    match receiver_type with
    | Types.Any _ -> (
        match
          Interface.Impls.classify_through_any state.lookups.interface ~trait:trait.trait method_
        with
        | Callable -> None
        | Has_generics ->
            Some
              (State.make_error_type state Not_callable (State.read_span state value.id)
                 (Printf.sprintf
                    "`%s` has generic or capability parameters of its own, so it cannot be called \
                     through `%s`: an `any` value holds one instance of each method, and this one \
                     has an instance for each set of arguments. Call it on a value whose type is \
                     known."
                    method_.method_name (State.show state receiver_type)))
        | Names_self ->
            Some
              (State.make_error_type state Not_callable (State.read_span state value.id)
                 (Printf.sprintf
                    "`%s` takes or returns a type that names `Self`, which is the type `%s` hides, \
                     so it cannot be called through it. Call it on a value whose type is known."
                    method_.method_name (State.show state receiver_type))))
    | _ -> None
  in
  match not_callable with
  | Some error -> Calls.check_arguments_alone state env arguments error
  | None -> (
      let instance, callee =
        Name_lookup.instantiate_trait_method state (State.read_span state value.id)
          ~self_type:receiver_type trait method_
          ~evidence:(match receiver_type with Types.Any _ -> Dynamic | _ -> Built_in)
      in
      match Name_lookup.check_explicit_type_arguments state value instance type_arguments with
      | Error error -> Calls.check_arguments_alone state env arguments error
      | Ok () -> (
          match
            Calls.check_arguments state env value instance.signature.parameters
              ~declared:instance.declared.parameters arguments ~has_receiver:true
          with
          | Error error -> error
          | Ok (checked, left_out) ->
              let result = Types.extract_result_type instance.signature.output in
              Modes.note_lending state value instance.signature.output;
              let receiver_argument =
                {
                  Tables.expression = receiver.id;
                  core_argument_index = 0;
                  mode = (match method_.method_receiver with Mut -> Mut | Own -> Own | _ -> Read);
                }
              in
              state.tables.calls.(value.id) <-
                Some
                  {
                    callee;
                    arguments = receiver_argument :: checked;
                    omitted_defaults = left_out;
                    callee_result = result;
                  };
              Form.register_call state value;
              Name_lookup.resolve_evidence state value receiver_type trait;
              State.normalize state result))
