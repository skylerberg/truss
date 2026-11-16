let note_lending (state : State.state) (value : Syntax.expression) (output : Types.result) =
  match output with
  | Lends (mode, _) -> state.tables.lend_modes.(value.id) <- Some mode
  | Returns _ -> ()

let rec find_lent_mode (state : State.state) (value : Syntax.expression) : Types.mode option =
  match value.kind with
  | Call _ -> state.tables.lend_modes.(value.id)
  | Member (base, _) | Parenthesized base -> find_lent_mode state base
  | Bracket (base, _) when state.resolved.brackets.(value.id) <> Some Type_arguments ->
      find_lent_mode state base
  | Mode (_, inner) when Option.is_some (State.find_call_with_mode_keyword state inner) ->
      find_lent_mode state inner
  | _ -> None

let rec is_slice (value : Syntax.expression) =
  match value.kind with
  | Bracket (_, [ Item { kind = Range _; _ } ]) -> true
  | Parenthesized inner | Mode (_, inner) -> is_slice inner
  | _ -> false

let rec is_plain_string_literal (value : Syntax.expression) =
  match value.kind with
  | String { tag = None; rest = []; _ } -> true
  | Parenthesized inner -> is_plain_string_literal inner
  | _ -> false

let is_borrowed state (value : Syntax.expression) =
  (State.is_place state value || is_plain_string_literal value
  || Option.is_some (find_lent_mode state value))
  && not (is_slice value)

let classify_scrutinee_mode state (scrutinee : Syntax.expression) : Types.mode =
  match scrutinee.kind with
  | Mode (Own, inner) when Option.is_none (State.find_call_with_mode_keyword state inner) -> Own
  | Mode (Mut, inner)
    when Option.is_none (State.find_call_with_mode_keyword state inner) && not (is_slice inner) ->
      Mut
  | _ -> if is_borrowed state scrutinee then Read else Own

type immutable = Read_only of string | Captured of string | Lent_read_only | Not_a_place

let rec find_immutable state (env : State.env) (value : Syntax.expression) : immutable option =
  match value.kind with
  | Name path -> (
      match State.find_target state path.last with
      | Some (Local id) -> (
          let captured =
            match state.lambdas with
            | (lambda : Source.Definition_span.t) :: _ ->
                let binding = State.read_span state id in
                binding.start < lambda.start || binding.start >= lambda.stop
            | [] -> false
          in
          match Hashtbl.find_opt state.locals id with
          | _ when captured -> Some (Captured path.last.text)
          | Some local ->
              if local.is_var || local.mode = Mut then None else Some (Read_only path.last.text)
          | None -> None)
      | Some (Definition _ | Law_parameter _) -> Some (Read_only path.last.text)
      | _ -> None)
  | Self_value ->
      if state.lambdas <> [] then Some (Captured "self")
      else if env.self_mode = Types.Mut then None
      else Some (Read_only "self")
  | Member (base, _) | Bracket (base, _) | Parenthesized base -> find_immutable state env base
  | Mode (Mut, inner) when Option.is_some (State.find_call_with_mode_keyword state inner) ->
      find_immutable state env inner
  | Call _ -> (
      match find_lent_mode state value with
      | Some Types.Mut -> None
      | Some _ -> Some Lent_read_only
      | None -> Some Not_a_place)
  | _ -> Some Not_a_place

let rec use_mutable_indexes (state : State.state) ~(report_with : Diagnostic.Code.types option)
    (value : Syntax.expression) =
  match value.kind with
  | Member (base, _) | Parenthesized base | Mode (_, base) ->
      use_mutable_indexes state ~report_with base
  | Bracket (base, _) ->
      (match state.tables.calls.(value.id) with
      | Some
          ({ callee = Trait_method ({ name = "at"; self_type; _ } as method_); arguments; _ } as
           call) -> (
          let index_mut =
            State.make_trait_reference ~arguments:[] (Well_known.make_path Index_mut)
          in
          match State.find_evidence state self_type index_mut with
          | Some evidence ->
              state.tables.calls.(value.id) <-
                Some
                  {
                    call with
                    callee =
                      Trait_method
                        {
                          method_ with
                          trait = index_mut;
                          receiver = Mut;
                          evidence = State.convert_evidence evidence;
                        };
                    arguments =
                      List.map
                        (fun (argument : Tables.argument) ->
                          if argument.core_argument_index = 0 then
                            { argument with mode = Types.Mut }
                          else argument)
                        arguments;
                  }
          | None ->
              Option.iter
                (fun code ->
                  let assigns =
                    Option.is_some
                      (State.find_evidence state self_type
                         (State.make_trait_reference ~arguments:[]
                            (Well_known.make_path Index_assign)))
                  in
                  State.report state code (State.read_span state value.id)
                    (Printf.sprintf
                       "An element of `%s` cannot be mutated in place: `%s` implements `Index`, \
                        which lends an element read-only, and not `IndexMut`.%s"
                       (State.show state self_type) (State.show state self_type)
                       (if assigns then " Assign the whole element with `=`." else "")))
                report_with)
      | _ -> ());
      use_mutable_indexes state ~report_with base
  | _ -> ()

type mutation = Assignment | Passed_mut

let mutate state env ~(by : mutation) (value : Syntax.expression) =
  let code : Diagnostic.Code.types =
    match by with Assignment -> Not_assignable | Passed_mut -> Wrong_mode
  in
  (match (find_immutable state env value, by) with
  | _ when State.is_formula env ->
      State.report state Not_in_specification (State.read_span state value.id)
        (Printf.sprintf
           "Nothing in a specification, a proof, or a quantifier's body can be %s: the prover \
            reads them as formulas, which mutate nothing."
           (match by with Assignment -> "assigned" | Passed_mut -> "passed `mut`"))
  | None, _ -> ()
  | Some (Captured name), _ ->
      State.report state code (State.read_span state value.id)
        (Printf.sprintf
           "A lambda cannot mutate its captures, and `%s` is from outside it. Return the new value \
            instead, or use a loop."
           name)
  | Some (Read_only name), _ ->
      State.report state code (State.read_span state value.id)
        (Printf.sprintf
           "`%s` cannot be mutated here: only a `var`, a `mut` parameter, or `mut self`, and their \
            parts, can be %s."
           name
           (match by with Assignment -> "assigned" | Passed_mut -> "passed `mut`"))
  | Some Lent_read_only, Assignment ->
      State.report state code (State.read_span state value.id)
        ~fixes:
          [
            State.fix "Pass it `mut`."
              [ State.insert (State.read_span state value.id).start "mut " ];
          ]
        "This part is lent read-only, so it cannot be mutated. Pass the place it is lent from \
         `mut`, so that it is lent `mut`."
  | Some Not_a_place, Assignment ->
      State.report state code (State.read_span state value.id)
        "Only a place, such as a variable, a field, or an element, can be assigned."
  | Some (Lent_read_only | Not_a_place), Passed_mut -> ());
  use_mutable_indexes state value
    ~report_with:
      (match find_immutable state env value with
      | None when not (State.is_formula env) -> Some code
      | _ -> None)

let rec note_place_without_own (state : State.state) env (place : Syntax.expression) =
  match place.kind with
  | Parenthesized inner -> note_place_without_own state env inner
  | _ -> if State.runs env then state.places_without_own <- place.id :: state.places_without_own

type argument_form =
  | With_mode of Types.mode * Syntax.expression
  | Place
  | Lent of Types.mode
  | Temporary

let classify_argument state (value : Syntax.expression) =
  match value.kind with
  | Mode (mode, inner) when Option.is_none (State.find_call_with_mode_keyword state inner) ->
      With_mode ((match mode with Mut -> Mut | Own -> Own), inner)
  | _ -> (
      match find_lent_mode state value with
      | Some mode -> Lent mode
      | None -> if State.is_place state value then Place else Temporary)

let run_once_solved state type_ check =
  State.defer state (fun () ->
      let is_solved =
        not
          (Types.exists (function Types.Variable _ -> true | _ -> false) (State.zonk state type_))
      in
      if is_solved then check ();
      is_solved)

let is_known_not_plain state type_ =
  State.decide_property state Interface.Properties.Plain type_ = Interface.Properties.Fails

let find_lent_field_mode (state : State.state) (value : Syntax.expression) type_ : Types.mode option
    =
  match (Hashtbl.find_opt state.yielded value.id, classify_argument state value) with
  | _ when is_slice value -> None
  | Some Read, With_mode (Mut, _) -> Some Read
  | Some Read, (Place | Lent _) when is_known_not_plain state type_ -> Some Read
  | Some Mut, With_mode (Mut, _) -> Some Mut
  | _ -> None

let locate_mode_keyword state (value : Syntax.expression) (inner : Syntax.expression) =
  Source.Definition_span.make (State.read_span state value.id).start
    (State.read_span state inner.id).start

let check_mode state env (value : Syntax.expression) (parameter : Types.parameter_info) type_ =
  let name = parameter.name in
  match (parameter.mode, classify_argument state value) with
  | Read, (Place | Temporary | Lent _) -> ()
  | Read, With_mode (_, inner) ->
      State.report state Redundant_mode (State.read_span state value.id)
        ~fixes:
          [
            State.fix "Remove the keyword."
              [
                Diagnostic.delete
                  (Source.Definition_span.make (State.read_span state value.id).start
                     (State.read_span state inner.id).start);
              ];
          ]
        (Printf.sprintf "`%s` only reads its argument, so it takes no mode keyword." name)
  | Mut, With_mode (Mut, inner) -> mutate state env ~by:Passed_mut inner
  | Mut, Place ->
      State.report state Missing_mode (State.read_span state value.id)
        ~fixes:
          [
            State.fix "Pass it `mut`."
              [ State.insert (State.read_span state value.id).start "mut " ];
          ]
        (Printf.sprintf "`%s` may mutate its argument, so the call site passes it `mut`." name)
  | Mut, Lent Mut -> mutate state env ~by:Passed_mut value
  | Mut, Lent (Read | Own) ->
      State.report state Wrong_mode (State.read_span state value.id)
        (Printf.sprintf
           "`%s` may mutate its argument, and this part is lent read-only. Pass the place it is \
            lent from `mut`, so that it is lent `mut`."
           name)
  | Mut, (Temporary | With_mode (Own, _)) ->
      State.report state Wrong_mode (State.read_span state value.id)
        (Printf.sprintf "`%s` mutates its argument in place, so it must be a place passed `mut`."
           name)
  | Own, With_mode (Own, inner) ->
      run_once_solved state type_ (fun () ->
          if
            State.decide_property state Interface.Properties.Plain type_
            = Interface.Properties.Holds
          then
            State.report state Redundant_mode (State.read_span state value.id)
              ~fixes:
                [
                  State.fix "Remove the keyword."
                    [ Diagnostic.delete (locate_mode_keyword state value inner) ];
                ]
              (Printf.sprintf "`%s` copies implicitly, so it needs no `own`."
                 (State.show state type_)))
  | Own, (Temporary | Lent _) -> ()
  | Own, Place when Hashtbl.find_opt state.yielded value.id = Some Mut ->
      run_once_solved state type_ (fun () ->
          if is_known_not_plain state type_ then
            State.report state Missing_mode (State.read_span state value.id)
              ~fixes:
                (State.fix "Lend it `mut`."
                   [ State.insert (State.read_span state value.id).start "mut " ]
                ::
                (if
                   State.decide_property state Interface.Properties.Copyable type_
                   = Interface.Properties.Holds
                 then
                   [
                     State.fix "Pass a copy."
                       [ State.insert (State.read_span state value.id).stop ".copy()" ];
                   ]
                 else []))
              (Printf.sprintf
                 "`%s` is a field of a value that is lent `mut`. Pass the place `mut` to lend it \
                  too, or pass a copy."
                 name))
  | Own, Place -> note_place_without_own state env value
  | Own, With_mode (Mut, _) ->
      State.report state Wrong_mode (State.read_span state value.id)
        (Printf.sprintf "`%s` takes ownership of its argument, so it is passed `own`, not `mut`."
           name)
  | (Mut | Own), With_mode (Read, _) -> ()

let check_lent_value (state : State.state) env (operand : Syntax.expression) =
  let rec check_fields ~variant (value : Syntax.expression) =
    match (value.kind, state.tables.calls.(value.id)) with
    | ( Call (_, arguments),
        Some { callee = Constructor { variant = constructed; _ }; arguments = checked; _ } ) ->
        let variant = if Option.is_some constructed then constructed else variant in
        List.iter
          (fun (argument : Syntax.argument) ->
            match
              List.find_opt
                (fun (checked_argument : Tables.argument) ->
                  checked_argument.expression = argument.value.id)
                checked
            with
            | Some { mode = Read; _ } -> ()
            | Some { mode = Mut; _ } -> (
                match variant with
                | Some variant when State.runs env ->
                    state.diagnostics <-
                      Diagnostic.make ~code:(Ownership Lent_mut_in_variant)
                        (State.read_span state argument.value.id)
                        (Printf.sprintf
                           "This place is lent `mut` inside the variant `%s`. The caller could \
                            replace the variant, and the place would be left without a value. Lend \
                            the place itself, and give the caller another method that says whether \
                            the place is there."
                           variant)
                      :: state.diagnostics
                | _ -> ())
            | _ -> check_fields ~variant argument.value)
          arguments
    | _ -> ()
  in
  check_fields ~variant:None operand

let note_owned_value state env (value : Syntax.expression) =
  match classify_argument state value with
  | Place -> note_place_without_own state env value
  | With_mode _ | Lent _ | Temporary -> ()
