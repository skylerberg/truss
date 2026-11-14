open Syntax
open State

(* Records that a call is a call of a lending method, with the mode it
   lends with. The result of such a call is a part of the receiver, lent
   for the rest of the caller's statement. It is not a temporary: it is
   never moved. *)
let note_lending state (value : expression) (output : Types.result) =
  match output with
  | Lends (mode, _) -> state.tables.lend_modes.(value.id) <- Some mode
  | Returns _ -> ()

(* The mode with which an expression is lent, if it is the result of a
   lending call, or a field or an element of one. A mode keyword before the
   expression belongs to the receiver of the lending call. *)
let rec lent state (value : expression) : Types.mode option =
  match value.kind with
  | Call _ -> state.tables.lend_modes.(value.id)
  | Member (base, _) | Parenthesized base -> lent state base
  | Bracket (base, _) when state.resolved.brackets.(value.id) <> Some Type_arguments ->
      lent state base
  | Mode (_, inner) when Option.is_some (call_with_mode_keyword state inner) -> lent state inner
  | _ -> None

(* Whether an expression is a slice, such as [items[1..3]]. A slice is
   written like an index, but it is a value: a view of part of its base. *)
let rec is_slice (value : expression) =
  match value.kind with
  | Bracket (_, [ Item { kind = Range _; _ } ]) -> true
  | Parenthesized inner | Mode (_, inner) -> is_slice inner
  | _ -> false

(* Whether a [let], [match], or [is] borrows the expression: it denotes a
   place, or a part that a lending call lends. The bindings then borrow
   parts of that place. A slice is a value, so it is not borrowed. *)
let borrowed state (value : expression) =
  (is_place state value || Option.is_some (lent state value)) && not (is_slice value)

(* The mode in which a pattern's bindings bind the parts of the scrutinee of
   a [match] or an [is]. A scrutinee written with [own] or [mut] has that
   mode. A place with no mode keyword, or a lent part, is borrowed, so the
   bindings are [Read]. Any other scrutinee is a value that the match
   consumes, so the bindings are [Own]. A mode keyword that belongs to the
   receiver of a method call, as in [mut cursor.next()], is not a mode
   keyword on the scrutinee. *)
let scrutinee_mode state (scrutinee : expression) : Types.mode =
  match scrutinee.kind with
  | Mode (Own, inner) when Option.is_none (call_with_mode_keyword state inner) -> Own
  | Mode (Mut, inner)
    when Option.is_none (call_with_mode_keyword state inner) && not (is_slice inner) ->
      Mut
  | _ -> if borrowed state scrutinee then Read else Own

(* Why a place cannot be mutated. *)
type immutable =
  | Read_only of string
      (** The place is, or is part of, a [let] binding, a parameter that is not [mut], a constant,
          or [self] in a method that does not take [mut self]. *)
  | Captured of string  (** Inside a lambda, the place belongs to the enclosing function. *)
  | Lent_read_only  (** The place is a part that a lending call lent read-only. *)
  | Not_a_place

(* Why a place cannot be mutated, or [None] if it can. Only a [var], a
   [mut] parameter, the variable of a [mut] loop, [mut self], a part of one
   of these, and a part that a call lends [mut] can be mutated. *)
let rec immutable state env (value : expression) : immutable option =
  match value.kind with
  | Name path -> (
      match target state path.last with
      | Some (Local id) -> (
          let captured =
            match (state.lambdas, Hashtbl.find_opt state.binding_spans id) with
            | (lambda : span) :: _, Some (binding : span) ->
                binding.start < lambda.start || binding.start >= lambda.stop
            | _ -> false
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

(* Records that a place is mutated: every index expression in the place
   is a call of [IndexMut.at], which lends its element [mut]. A collection
   whose type implements [Index] alone lends each element read-only, so an
   element of it cannot be mutated in place. That is reported with [code]
   where the place is otherwise one that can be mutated. *)
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
                          if argument.parameter_index = 0 then { argument with mode = Types.Mut }
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
                  report state code value.span
                    (Printf.sprintf
                       "An element of `%s` cannot be mutated in place: `%s` implements `Index`, \
                        which lends an element read-only, and not `IndexMut`.%s"
                       (show state self_type) (show state self_type)
                       (if assigns then " Assign the whole element with `=`." else "")))
                report_with)
      | _ -> ());
      use_mutable_indexes state ~report_with base
  | _ -> ()

type mutation =
  | Assignment
  | Passed_mut  (** The place is passed [mut], is a [mut] receiver, or is lent or yielded [mut]. *)

(* Checks that a place may be mutated, and records that it is. Every
   construct that mutates a place calls this. *)
let mutate state env ~(by : mutation) (value : expression) =
  let code : Diagnostic.Code.types =
    match by with Assignment -> Not_assignable | Passed_mut -> Wrong_mode
  in
  (match (immutable state env value, by) with
  | _ when is_formula env ->
      report state Not_in_specification value.span
        (Printf.sprintf
           "Nothing in a specification, a proof, or a quantifier's body can be %s: the prover \
            reads them as formulas, which mutate nothing."
           (match by with Assignment -> "assigned" | Passed_mut -> "passed `mut`"))
  | None, _ -> ()
  | Some (Captured name), _ ->
      report state code value.span
        (Printf.sprintf
           "A lambda cannot mutate its captures, and `%s` is from outside it. Return the new value \
            instead, or use a loop."
           name)
  | Some (Read_only name), _ ->
      report state code value.span
        (Printf.sprintf
           "`%s` cannot be mutated here: only a `var`, a `mut` parameter, or `mut self`, and their \
            parts, can be %s."
           name
           (match by with Assignment -> "assigned" | Passed_mut -> "passed `mut`"))
  | Some Lent_read_only, Assignment ->
      report state code value.span
        ~fixes:[ fix "Pass it `mut`." [ insert value.span.start "mut " ] ]
        "This part is lent read-only, so it cannot be mutated. Pass the place it is lent from \
         `mut`, so that it is lent `mut`."
  | Some Not_a_place, Assignment ->
      report state code value.span
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

(* The mode with which a field of a constructor that a lending method
   lends lends a place to the value that is built, or [None] if the field
   takes its value, as a field of any other constructor does. [type_] is
   the type of [value]. A method that lends read-only lends every place
   read-only, except a [Plain] place, which is copied. A method that lends
   [mut] lends the places that are passed [mut]. A slice is a value, so it
   is taken. *)
let lent_field state (value : expression) type_ : Types.mode option =
  match (Hashtbl.find_opt state.yielded value.id, argument_form state value) with
  | _ when is_slice value -> None
  | Some Read, With_mode (Mut, _) -> Some Read
  | Some Read, (Place | Lent _) when not (plain state type_) -> Some Read
  | Some Mut, With_mode (Mut, _) -> Some Mut
  | _ -> None

let mode_keyword_span (value : expression) (inner : expression) =
  Span.make value.span.start inner.span.start

let check_mode state env (value : expression) (parameter : Types.parameter_info) type_ =
  let name = parameter.name in
  match (parameter.mode, argument_form state value) with
  | Read, (Place | Temporary | Lent _) -> ()
  | Read, With_mode (_, inner) ->
      report state Redundant_mode value.span
        ~fixes:
          [
            fix "Remove the keyword."
              [ Diagnostic.delete (Span.make value.span.start inner.span.start) ];
          ]
        (Printf.sprintf "`%s` only reads its argument, so it takes no mode keyword." name)
  | Mut, With_mode (Mut, inner) -> mutate state env ~by:Passed_mut inner
  | Mut, Place ->
      report state Missing_mode value.span
        ~fixes:[ fix "Pass it `mut`." [ insert value.span.start "mut " ] ]
        (Printf.sprintf "`%s` may mutate its argument, so the call site passes it `mut`." name)
  | Mut, Lent Mut -> mutate state env ~by:Passed_mut value
  | Mut, Lent (Read | Own) ->
      report state Wrong_mode value.span
        (Printf.sprintf
           "`%s` may mutate its argument, and this part is lent read-only. Pass the place it is \
            lent from `mut`, so that it is lent `mut`."
           name)
  | Own, Lent _ ->
      if not (plain state type_) then
        report state Missing_mode value.span
          ~fixes:
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else [])
          (Printf.sprintf
             "`%s` takes ownership of its argument, and a part that is lent cannot be moved. Pass \
              a copy."
             name)
  | Mut, (Temporary | With_mode (Own, _)) ->
      report state Wrong_mode value.span
        (Printf.sprintf "`%s` mutates its argument in place, so it must be a place passed `mut`."
           name)
  | Own, With_mode (Own, inner) ->
      if plain state type_ then
        report state Redundant_mode value.span
          ~fixes:[ fix "Remove the keyword." [ Diagnostic.delete (mode_keyword_span value inner) ] ]
          (Printf.sprintf "`%s` copies implicitly, so it needs no `own`." (show state type_))
  | Own, Temporary -> ()
  | Own, Place when Hashtbl.find_opt state.yielded value.id = Some Mut ->
      if not (plain state type_) then
        report state Missing_mode value.span
          ~fixes:
            (fix "Lend it `mut`." [ insert value.span.start "mut " ]
            ::
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else []))
          (Printf.sprintf
             "`%s` is a field of a value that is lent `mut`. Pass the place `mut` to lend it too, \
              or pass a copy."
             name)
  | Own, Place when is_part_of_constant state value ->
      if not (plain state type_) then
        report state Missing_mode value.span
          ~fixes:
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else [])
          (Printf.sprintf
             "`%s` takes ownership of its argument, and a constant cannot be moved. Pass a copy."
             name)
  | Own, Place ->
      if not (plain state type_) then
        report state Missing_mode value.span
          ~fixes:
            (fix "Move it with `own`." [ insert value.span.start "own " ]
            ::
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else []))
          (Printf.sprintf
             "`%s` takes ownership of its argument. Move the place with `own`, or pass a copy." name)
  | Own, With_mode (Mut, _) ->
      report state Wrong_mode value.span
        (Printf.sprintf "`%s` takes ownership of its argument, so it is passed `own`, not `mut`."
           name)
  | (Mut | Own), With_mode (Read, _) -> ()

(* A place lent [mut] is not inside a variant's constructor at any depth.
   The caller could replace the variant, as [mut pair.maybe() = None] does,
   and the place would be left without a value: a use after free.
   [operand] is the part that the method lends. *)
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
                      Diagnostic.make ~code:(Ownership Lent_mut_in_variant) argument.value.span
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

(* Checks a value where an owned value is required and no parameter
   receives it: the initializer of a [var], the value of an assignment, an
   element of a collection literal, or a part of a tagged string. A place
   there must be passed [own] or copied, unless its type is [Plain]. This
   is a rule of ownership. The type checker reports it because only the
   syntax tree has the mode keywords. *)
let check_owned state env (value : expression) type_ =
  if runs env then
    defer state (fun () ->
        let type_ = normalize state type_ in
        if Types.contains_unsolved type_ then false
        else begin
          (match argument_form state value with
          | Place when not (plain state type_) ->
              let place = source state value.span in
              let copy =
                if copyable state type_ then [ fix "Copy it." [ insert value.span.stop ".copy()" ] ]
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
                  ( fix "Move it with `own`." [ insert value.span.start "own " ] :: copy,
                    Printf.sprintf
                      "An owned value is needed here, and `%s` is a place. Pass it `own` to move \
                       it, or copy it."
                      place )
              in
              state.diagnostics <-
                Diagnostic.make ~fixes ~code:(Ownership Needs_owned) value.span message
                :: state.diagnostics
          | _ -> ());
          true
        end)
