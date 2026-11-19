let note_lending (state : State.state) (value : Syntax.expression) (output : Types.result) =
  match output with
  | Lends (mode, _) -> state.tables.lend_modes.(value.id) <- Some mode
  | Returns _ -> ()

let rec find_lent_mode (state : State.state) (value : Syntax.expression) : Language.Mode.t option =
  match value.kind with
  | Call _ -> state.tables.lend_modes.(value.id)
  | Member (base, _) | Parenthesized base -> find_lent_mode state base
  | Bracket (base, _) when state.resolved.brackets.(value.id) <> Some Type_arguments ->
      find_lent_mode state base
  | Mode (_, inner) when Option.is_some (State.find_keyword_operation state inner) ->
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

let classify_scrutinee_mode state (scrutinee : Syntax.expression) : Language.Mode.t =
  match scrutinee.kind with
  | Mode (Own, inner) when Option.is_none (State.find_keyword_operation state inner) -> Own
  | Mode (Mut, inner)
    when Option.is_none (State.find_keyword_operation state inner) && not (is_slice inner) ->
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
      else if env.self_mode = Language.Mode.Mut then None
      else Some (Read_only "self")
  | Member (base, _) | Bracket (base, _) | Parenthesized base -> find_immutable state env base
  | Mode (Mut, inner) when Option.is_some (State.find_keyword_operation state inner) ->
      find_immutable state env inner
  | Call _ -> (
      match find_lent_mode state value with
      | Some Language.Mode.Mut -> None
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
          ({
             callee = Trait_method ({ trait; name; receiver; self_type; _ } as method_);
             arguments;
             _;
           } as call)
        when Well_known.is_method Index_at (Method { owner = trait.trait; name; receiver }) -> (
          let index_mut_at = Well_known.locate_method Index_mut_at in
          let index_mut =
            State.make_trait_reference ~arguments:[] (Well_known.make_path index_mut_at.owner)
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
                          name = index_mut_at.name;
                          receiver = index_mut_at.receiver;
                          evidence = State.convert_evidence evidence;
                        };
                    arguments =
                      List.map
                        (fun (argument : Tables.argument) ->
                          if argument.core_argument_index = 0 then
                            { argument with mode = Language.Mode.Mut }
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

let rec note_place_without_keyword (state : State.state) env (place : Syntax.expression) ~needs =
  match place.kind with
  | Parenthesized inner -> note_place_without_keyword state env inner ~needs
  | _ ->
      if State.runs env then
        state.places_without_keyword <- (place.id, needs) :: state.places_without_keyword

type argument_form =
  | With_mode of Language.Mode.t * Syntax.expression
  | Place
  | Lent of Language.Mode.t
  | Temporary

let classify_argument state (value : Syntax.expression) =
  match value.kind with
  | Mode (mode, inner) when Option.is_none (State.find_keyword_operation state inner) ->
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

let find_lent_field_mode (state : State.state) (value : Syntax.expression) type_ :
    Language.Mode.t option =
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
              (Printf.sprintf "%s copies implicitly, so it needs no `own`."
                 (String.capitalize_ascii (State.describe state type_))))
  | Own, (Temporary | Lent _) -> ()
  | Own, Place when Hashtbl.find_opt state.yielded value.id = Some Mut ->
      note_place_without_keyword state env value ~needs:Mut
  | Own, Place -> note_place_without_keyword state env value ~needs:Own
  | Own, With_mode (Mut, _) ->
      State.report state Wrong_mode (State.read_span state value.id)
        (Printf.sprintf "`%s` takes ownership of its argument, so it is passed `own`, not `mut`."
           name)
  | (Mut | Own), With_mode (Read, _) -> ()

let note_owned_value state env (value : Syntax.expression) =
  match classify_argument state value with
  | Place -> note_place_without_keyword state env value ~needs:Own
  | With_mode _ | Lent _ | Temporary -> ()
