open Syntax
open State

let note_lending state (value : expression) (output : Types.result) =
  match output with
  | Lends (mode, _) -> state.tables.lend_modes.(value.id) <- Some mode
  | Returns _ -> ()

let rec lent state (value : expression) : Types.mode option =
  match value.kind with
  | Call _ -> state.tables.lend_modes.(value.id)
  | Member (base, _) | Parenthesized base -> lent state base
  | Bracket (base, _) when state.resolved.brackets.(value.id) <> Some Type_arguments ->
      lent state base
  | Mode (_, inner) when Option.is_some (call_with_mode_keyword state inner) -> lent state inner
  | _ -> None

let rec is_slice (value : expression) =
  match value.kind with
  | Bracket (_, [ Item { kind = Range _; _ } ]) -> true
  | Parenthesized inner | Mode (_, inner) -> is_slice inner
  | _ -> false

let borrowed state (value : expression) =
  (is_place state value || Option.is_some (lent state value)) && not (is_slice value)

let scrutinee_mode state (scrutinee : expression) : Types.mode =
  match scrutinee.kind with
  | Mode (Own, inner) when Option.is_none (call_with_mode_keyword state inner) -> Own
  | Mode (Mut, inner)
    when Option.is_none (call_with_mode_keyword state inner) && not (is_slice inner) ->
      Mut
  | _ -> if borrowed state scrutinee then Read else Own

type immutable = Read_only of string | Captured of string | Lent_read_only | Not_a_place

let rec immutable state env (value : expression) : immutable option =
  match value.kind with
  | Name path -> (
      match target state path.last with
      | Some (Local id) -> (
          let captured =
            match state.lambdas with
            | (lambda : Source.Definition_span.t) :: _ ->
                let binding = read_span state id in
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
  | Member (base, _) | Bracket (base, _) | Parenthesized base -> immutable state env base
  | Mode (Mut, inner) when Option.is_some (call_with_mode_keyword state inner) ->
      immutable state env inner
  | Call _ -> (
      match lent state value with
      | Some Types.Mut -> None
      | Some _ -> Some Lent_read_only
      | None -> Some Not_a_place)
  | _ -> Some Not_a_place

let rec use_mutable_indexes state ~(report_with : Diagnostic.Code.types option) (value : expression)
    =
  match value.kind with
  | Member (base, _) | Parenthesized base | Mode (_, base) ->
      use_mutable_indexes state ~report_with base
  | Bracket (base, _) ->
      (match state.tables.calls.(value.id) with
      | Some
          ({ callee = Trait_method ({ name = "at"; self_type; _ } as method_); arguments; _ } as
           call) -> (
          let index_mut = trait_reference (Well_known.path Index_mut) in
          match implements state self_type index_mut with
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
                          evidence = evidence_of evidence;
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
                      (implements state self_type (trait_reference (Well_known.path Index_assign)))
                  in
                  report state code (read_span state value.id)
                    (Printf.sprintf
                       "An element of `%s` cannot be mutated in place: `%s` implements `Index`, \
                        which lends an element read-only, and not `IndexMut`.%s"
                       (show state self_type) (show state self_type)
                       (if assigns then " Assign the whole element with `=`." else "")))
                report_with)
      | _ -> ());
      use_mutable_indexes state ~report_with base
  | _ -> ()

type mutation = Assignment | Passed_mut

let mutate state env ~(by : mutation) (value : expression) =
  let code : Diagnostic.Code.types =
    match by with Assignment -> Not_assignable | Passed_mut -> Wrong_mode
  in
  (match (immutable state env value, by) with
  | _ when is_formula env ->
      report state Not_in_specification (read_span state value.id)
        (Printf.sprintf
           "Nothing in a specification, a proof, or a quantifier's body can be %s: the prover \
            reads them as formulas, which mutate nothing."
           (match by with Assignment -> "assigned" | Passed_mut -> "passed `mut`"))
  | None, _ -> ()
  | Some (Captured name), _ ->
      report state code (read_span state value.id)
        (Printf.sprintf
           "A lambda cannot mutate its captures, and `%s` is from outside it. Return the new value \
            instead, or use a loop."
           name)
  | Some (Read_only name), _ ->
      report state code (read_span state value.id)
        (Printf.sprintf
           "`%s` cannot be mutated here: only a `var`, a `mut` parameter, or `mut self`, and their \
            parts, can be %s."
           name
           (match by with Assignment -> "assigned" | Passed_mut -> "passed `mut`"))
  | Some Lent_read_only, Assignment ->
      report state code (read_span state value.id)
        ~fixes:[ fix "Pass it `mut`." [ insert (read_span state value.id).start "mut " ] ]
        "This part is lent read-only, so it cannot be mutated. Pass the place it is lent from \
         `mut`, so that it is lent `mut`."
  | Some Not_a_place, Assignment ->
      report state code (read_span state value.id)
        "Only a place, such as a variable, a field, or an element, can be assigned."
  | Some (Lent_read_only | Not_a_place), Passed_mut -> ());
  use_mutable_indexes state value
    ~report_with:
      (match immutable state env value with
      | None when not (is_formula env) -> Some code
      | _ -> None)

let rec is_part_of_constant state (value : expression) =
  match value.kind with
  | Name path -> (
      match target state path.last with Some (Definition (Constant, _)) -> true | _ -> false)
  | Member (base, _) -> is_member_constant state value || is_part_of_constant state base
  | Bracket (base, _) | Parenthesized base -> is_part_of_constant state base
  | _ -> false

type argument_form = With_mode of Types.mode * expression | Place | Lent of Types.mode | Temporary

let argument_form state (value : expression) =
  match value.kind with
  | Mode (mode, inner) when Option.is_none (call_with_mode_keyword state inner) ->
      With_mode ((match mode with Mut -> Mut | Own -> Own), inner)
  | _ -> (
      match lent state value with
      | Some mode -> Lent mode
      | None -> if is_place state value then Place else Temporary)

let lent_field state (value : expression) type_ : Types.mode option =
  match (Hashtbl.find_opt state.yielded value.id, argument_form state value) with
  | _ when is_slice value -> None
  | Some Read, With_mode (Mut, _) -> Some Read
  | Some Read, (Place | Lent _) when not (plain state type_) -> Some Read
  | Some Mut, With_mode (Mut, _) -> Some Mut
  | _ -> None

let mode_keyword_span state (value : expression) (inner : expression) =
  Source.Definition_span.make (read_span state value.id).start (read_span state inner.id).start

let check_mode state env (value : expression) (parameter : Types.parameter_info) type_ =
  let name = parameter.name in
  match (parameter.mode, argument_form state value) with
  | Read, (Place | Temporary | Lent _) -> ()
  | Read, With_mode (_, inner) ->
      report state Redundant_mode (read_span state value.id)
        ~fixes:
          [
            fix "Remove the keyword."
              [
                Diagnostic.delete
                  (Source.Definition_span.make (read_span state value.id).start
                     (read_span state inner.id).start);
              ];
          ]
        (Printf.sprintf "`%s` only reads its argument, so it takes no mode keyword." name)
  | Mut, With_mode (Mut, inner) -> mutate state env ~by:Passed_mut inner
  | Mut, Place ->
      report state Missing_mode (read_span state value.id)
        ~fixes:[ fix "Pass it `mut`." [ insert (read_span state value.id).start "mut " ] ]
        (Printf.sprintf "`%s` may mutate its argument, so the call site passes it `mut`." name)
  | Mut, Lent Mut -> mutate state env ~by:Passed_mut value
  | Mut, Lent (Read | Own) ->
      report state Wrong_mode (read_span state value.id)
        (Printf.sprintf
           "`%s` may mutate its argument, and this part is lent read-only. Pass the place it is \
            lent from `mut`, so that it is lent `mut`."
           name)
  | Own, Lent _ ->
      if not (plain state type_) then
        report state Missing_mode (read_span state value.id)
          ~fixes:
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert (read_span state value.id).stop ".copy()" ] ]
             else [])
          (Printf.sprintf
             "`%s` takes ownership of its argument, and a part that is lent cannot be moved. Pass \
              a copy."
             name)
  | Mut, (Temporary | With_mode (Own, _)) ->
      report state Wrong_mode (read_span state value.id)
        (Printf.sprintf "`%s` mutates its argument in place, so it must be a place passed `mut`."
           name)
  | Own, With_mode (Own, inner) ->
      if plain state type_ then
        report state Redundant_mode (read_span state value.id)
          ~fixes:
            [
              fix "Remove the keyword." [ Diagnostic.delete (mode_keyword_span state value inner) ];
            ]
          (Printf.sprintf "`%s` copies implicitly, so it needs no `own`." (show state type_))
  | Own, Temporary -> ()
  | Own, Place when Hashtbl.find_opt state.yielded value.id = Some Mut ->
      if not (plain state type_) then
        report state Missing_mode (read_span state value.id)
          ~fixes:
            (fix "Lend it `mut`." [ insert (read_span state value.id).start "mut " ]
            ::
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert (read_span state value.id).stop ".copy()" ] ]
             else []))
          (Printf.sprintf
             "`%s` is a field of a value that is lent `mut`. Pass the place `mut` to lend it too, \
              or pass a copy."
             name)
  | Own, Place when is_part_of_constant state value ->
      if not (plain state type_) then
        report state Missing_mode (read_span state value.id)
          ~fixes:
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert (read_span state value.id).stop ".copy()" ] ]
             else [])
          (Printf.sprintf
             "`%s` takes ownership of its argument, and a constant cannot be moved. Pass a copy."
             name)
  | Own, Place ->
      if not (plain state type_) then
        report state Missing_mode (read_span state value.id)
          ~fixes:
            (fix "Move it with `own`." [ insert (read_span state value.id).start "own " ]
            ::
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert (read_span state value.id).stop ".copy()" ] ]
             else []))
          (Printf.sprintf
             "`%s` takes ownership of its argument. Move the place with `own`, or pass a copy." name)
  | Own, With_mode (Mut, _) ->
      report state Wrong_mode (read_span state value.id)
        (Printf.sprintf "`%s` takes ownership of its argument, so it is passed `own`, not `mut`."
           name)
  | (Mut | Own), With_mode (Read, _) -> ()

let check_lent_value state env (operand : expression) =
  let rec fields ~variant (value : expression) =
    match (value.kind, state.tables.calls.(value.id)) with
    | ( Call (_, arguments),
        Some { callee = Constructor { variant = constructed; _ }; arguments = checked; _ } ) ->
        let variant = if Option.is_some constructed then constructed else variant in
        List.iter
          (fun (argument : argument) ->
            match
              List.find_opt
                (fun (checked_argument : Tables.argument) ->
                  checked_argument.expression = argument.value.id)
                checked
            with
            | Some { mode = Read; _ } -> ()
            | Some { mode = Mut; _ } -> (
                match variant with
                | Some variant when runs env ->
                    state.diagnostics <-
                      Diagnostic.make ~code:(Ownership Lent_mut_in_variant)
                        (read_span state argument.value.id)
                        (Printf.sprintf
                           "This place is lent `mut` inside the variant `%s`. The caller could \
                            replace the variant, and the place would be left without a value. Lend \
                            the place itself, and give the caller another method that says whether \
                            the place is there."
                           variant)
                      :: state.diagnostics
                | _ -> ())
            | _ -> fields ~variant argument.value)
          arguments
    | _ -> ()
  in
  fields ~variant:None operand

let check_owned state env (value : expression) type_ =
  if runs env then
    defer state (fun () ->
        let type_ = normalize state type_ in
        if Types.contains_unsolved type_ then false
        else begin
          (match argument_form state value with
          | Place when not (plain state type_) ->
              let place = source state (read_span state value.id) in
              let copy =
                if copyable state type_ then
                  [ fix "Copy it." [ insert (read_span state value.id).stop ".copy()" ] ]
                else []
              in
              let fixes, message =
                if is_part_of_constant state value then
                  ( copy,
                    Printf.sprintf "An owned value is needed here, and `%s` is %s. Copy it." place
                      (match value.kind with
                      | Name _ -> "a constant"
                      | _ when is_member_constant state value -> "a constant"
                      | _ -> "part of a constant") )
                else
                  ( fix "Move it with `own`." [ insert (read_span state value.id).start "own " ]
                    :: copy,
                    Printf.sprintf
                      "An owned value is needed here, and `%s` is a place. Pass it `own` to move \
                       it, or copy it."
                      place )
              in
              state.diagnostics <-
                Diagnostic.make ~fixes ~code:(Ownership Needs_owned) (read_span state value.id)
                  message
                :: state.diagnostics
          | _ -> ());
          true
        end)
