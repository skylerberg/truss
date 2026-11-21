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
              if local.binding = Var || local.mode = Mut then None
              else Some (Read_only path.last.text)
          | None -> None)
      | Some (Definition _ | Law_parameter _) -> Some (Read_only path.last.text)
      | _ -> None)
  | Self_value ->
      if state.lambdas <> [] then Some (Captured "self")
      else if env.self_mode = Language.Mode.Mut then None
      else Some (Read_only "self")
  | Member (base, _) | Bracket (base, _) | Parenthesized base -> find_immutable state env base
  | Mode (Mut, inner)
    when Option.is_some
           (Places.find_keyword_operation state.State.resolved state.State.tables inner) ->
      find_immutable state env inner
  | Call _ -> (
      match Places.find_lent_mode state.State.resolved state.State.tables value with
      | Some Language.Mode.Mut -> None
      | Some _ -> Some Lent_read_only
      | None -> Some Not_a_place)
  | _ -> Some Not_a_place

let use_mutable_index (state : State.state) ~(report_with : Diagnostic.Code.types option)
    (value : Syntax.expression) =
  match Tables.find_call state.tables value.id with
  | Some
      ({ callee = Trait_method ({ trait; name; receiver; self_type; _ } as method_); arguments; _ }
       as call)
    when Well_known.is_method Index_at (Method { owner = trait.trait; name; receiver }) -> (
      let index_mut_at = Well_known.locate_method Index_mut_at in
      let index_mut =
        Types.make_trait_reference ~arguments:[] (Well_known.make_path index_mut_at.owner)
      in
      match State.find_evidence state self_type index_mut with
      | Some _ ->
          State.elaborate state value.id
            (Call
               {
                 call with
                 callee =
                   Trait_method
                     {
                       method_ with
                       trait = index_mut;
                       name = index_mut_at.name;
                       receiver = index_mut_at.receiver;
                     };
                 arguments =
                   List.map
                     (fun (argument : Tables.argument) ->
                       if argument.core_argument_index = 0 then
                         { argument with mode = Language.Mode.Mut }
                       else argument)
                     arguments;
                 lends = Some Mut;
               })
      | None ->
          Option.iter
            (fun code ->
              let assigns =
                Option.is_some
                  (State.find_evidence state self_type
                     (Types.make_trait_reference ~arguments:[] (Well_known.make_path Index_assign)))
              in
              State.report state code (State.read_span state value.id)
                (Printf.sprintf
                   "An element of `%s` cannot be mutated in place: `%s` implements `Index`, which \
                    lends an element read-only, and not `IndexMut`.%s"
                   (State.show state self_type) (State.show state self_type)
                   (if assigns then " Assign the whole element with `=`." else "")))
            report_with)
  | _ -> ()

let rec use_mutable_indexes (state : State.state) ~(report_with : Diagnostic.Code.types option)
    (value : Syntax.expression) =
  match value.kind with
  | Member (base, _) | Parenthesized base | Mode (_, base) ->
      use_mutable_indexes state ~report_with base
  | Bracket (base, _) ->
      State.check_when_final state (fun () -> use_mutable_index state ~report_with value);
      use_mutable_indexes state ~report_with base
  | _ -> ()

type mutation = Assignment | Passed_mut

let has_slice_type (state : State.state) (value : Syntax.expression) =
  match state.tables.types.((value.id :> int)) with
  | Some type_ ->
      let type_ = State.normalize state type_ in
      Types.is_well_known Slice type_ || Types.is_well_known String_slice type_
  | None -> false

type stored_slice = Held_by of string | In_field | In_element | Lent_by_a_call

let rec find_stored_slice state (slice : Syntax.expression) =
  match slice.kind with
  | Parenthesized inner | Mode (_, inner) -> find_stored_slice state inner
  | Name path -> (
      match State.find_target state path.last with
      | Some (Local id) -> (
          match Hashtbl.find_opt state.locals id with
          | Some { binding = Parameter; mode = Mut; _ } | None -> None
          | Some { name; _ } -> Some (Held_by name))
      | _ -> None)
  | Bracket (base, [ Item { kind = Range _; _ } ]) -> find_slice_written_through state base
  | Member _ -> Some In_field
  | Bracket _ -> Some In_element
  | Call _ -> Some Lent_by_a_call
  | _ -> None

and find_slice_written_through state (place : Syntax.expression) =
  if has_slice_type state place then find_stored_slice state place
  else
    match place.kind with
    | Parenthesized inner | Mode (_, inner) -> find_slice_written_through state inner
    | Member (base, _) | Bracket (base, _) -> find_slice_written_through state base
    | _ -> None

let rec find_assigned_slice_parameter state (target : Syntax.expression) =
  let is_writable slice = has_slice_type state slice && find_stored_slice state slice = None in
  match target.kind with
  | Parenthesized inner -> find_assigned_slice_parameter state inner
  | (Name _ | Self_value) when is_writable target -> Some target
  | Member (base, _) when is_writable base -> Some base
  | _ -> None

let show_slice_parameter (parameter : Syntax.expression) =
  match parameter.kind with Name path -> path.last.text | _ -> "self"

let describe_stored_slice = function
  | Held_by name -> Printf.sprintf "`%s` holds a slice" name
  | In_field -> "This slice is held in a field"
  | In_element -> "This slice is an element of a collection"
  | Lent_by_a_call -> "This slice is lent by a call"

let check_slice_writes state ~(by : mutation) ~is_to_generic ~code (value : Syntax.expression) =
  let report message = State.report state code (State.read_span state value.id) message in
  let report_stored stored =
    report
      (Printf.sprintf
         "%s, so its elements cannot be written through it: a slice held in a variable, a field, \
          or an element may alias another view of the same elements. Write through a range of the \
          collection, as in `mut items[1..]`, or through a `mut Slice` parameter."
         (describe_stored_slice stored))
  in
  State.check_when_final state (fun () ->
      match by with
      | Assignment -> (
          match find_assigned_slice_parameter state value with
          | Some parameter ->
              report
                (Printf.sprintf
                   "`%s` is a `mut` slice parameter, so it cannot be assigned: the caller lends it \
                    write access to a range of elements, and a different slice would carry that \
                    access to elements the caller did not lend. Write its elements instead."
                   (show_slice_parameter parameter))
          | None -> (
              match value.kind with
              | Member (base, _) | Bracket (base, _) ->
                  Option.iter report_stored (find_slice_written_through state base)
              | _ -> ()))
      | Passed_mut when is_to_generic && has_slice_type state value ->
          report
            "A slice is passed `mut` only to a `mut Slice` parameter, and this parameter's \
             declared type is a type parameter or an associated type. The callee could assign it a \
             different slice, which would leave the elements the caller lent unchanged while its \
             contract describes them as written."
      | Passed_mut -> Option.iter report_stored (find_slice_written_through state value))

let mutate_with state env ~(by : mutation) ~is_to_generic (value : Syntax.expression) =
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
  (match find_immutable state env value with
  | None when not (State.is_formula env) -> check_slice_writes state ~by ~is_to_generic ~code value
  | Some _ | None -> ());
  use_mutable_indexes state value
    ~report_with:
      (match find_immutable state env value with
      | None when not (State.is_formula env) -> Some code
      | _ -> None)

let mutate state env ~by value = mutate_with state env ~by ~is_to_generic:false value

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
  | Mode (mode, inner)
    when Option.is_none
           (Places.find_keyword_operation state.State.resolved state.State.tables inner) ->
      With_mode ((match mode with Mut -> Mut | Own -> Own), inner)
  | _ -> (
      match Places.find_lent_mode state.State.resolved state.State.tables value with
      | Some mode -> Lent mode
      | None ->
          if Places.is_place state.State.resolved state.State.tables value then Place else Temporary
      )

let is_known_not_plain state type_ =
  State.decide_property state Interface.Properties.Plain type_ = Interface.Properties.Fails

let find_lent_field_mode (state : State.state) (value : Syntax.expression) type_ :
    Language.Mode.t option =
  match (Hashtbl.find_opt state.yielded value.id, classify_argument state value) with
  | _ when Places.is_slice value -> None
  | Some Read, With_mode (Mut, _) -> Some Read
  | Some Read, (Place | Lent _) when is_known_not_plain state type_ -> Some Read
  | Some Mut, With_mode (Mut, _) -> Some Mut
  | _ -> None

let locate_mode_keyword state (value : Syntax.expression) (inner : Syntax.expression) =
  Source.Definition_span.make (State.read_span state value.id).start
    (State.read_span state inner.id).start

let check_mode state env (value : Syntax.expression) (parameter : Types.parameter_info) type_
    ~has_generic_type =
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
  | Mut, With_mode (Mut, inner) ->
      mutate_with state env ~by:Passed_mut ~is_to_generic:has_generic_type inner
  | Mut, Place ->
      State.report state Missing_mode (State.read_span state value.id)
        ~fixes:
          [
            State.fix "Pass it `mut`."
              [ State.insert (State.read_span state value.id).start "mut " ];
          ]
        (Printf.sprintf "`%s` may mutate its argument, so the call site passes it `mut`." name)
  | Mut, Lent Mut -> mutate_with state env ~by:Passed_mut ~is_to_generic:has_generic_type value
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
      State.check_when_final state (fun () ->
          let final_type = State.finalize_type state type_ in
          if
            State.decide_property state Interface.Properties.Plain final_type
            = Interface.Properties.Holds
          then
            State.report state Redundant_mode (State.read_span state value.id)
              ~fixes:
                [
                  State.fix "Remove the keyword."
                    [ Diagnostic.delete (locate_mode_keyword state value inner) ];
                ]
              (Printf.sprintf "`%s` copies implicitly, so it needs no `own`."
                 (Types.show final_type)))
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
