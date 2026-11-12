open Syntax
open State

(* Records that a call is a call of a lending method, with the mode it
   lends with. The result of such a call is a part of the receiver, lent
   for the rest of the caller's statement. It is not a temporary: it is
   never moved. *)
let note_lending state (value : expression) (output : Types.result) =
  match output with
  | Lends (mode, _) -> state.tables.lend_modes.(value.id) <- Some mode
  | Returns _ | Yields _ -> ()

(* The mode with which an expression is lent, if it is the result of a
   lending call, or a field or an element of one. A mark before the
   expression belongs to the receiver of the lending call. *)
let rec lent state (value : expression) : Types.mode option =
  match value.kind with
  | Call _ -> state.tables.lend_modes.(value.id)
  | Member (base, _) | Parenthesized base -> lent state base
  | Bracket (base, _) when state.resolved.brackets.(value.id) <> Some Type_arguments ->
      lent state base
  | Mode (_, inner) when Option.is_some (marked_call state inner) -> lent state inner
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
   a [match] or an [is]. A scrutinee marked [own] or [mut] has that mode. An
   unmarked place or lent part is borrowed, so the bindings are [Read]. Any
   other scrutinee is a value that the match consumes, so the bindings are
   [Own]. A mark that belongs to the receiver of a method call, as in [mut
   cursor.next()], is not a mark on the scrutinee. *)
let scrutinee_mode state (scrutinee : expression) : Types.mode =
  match scrutinee.kind with
  | Mode (Own, inner) when Option.is_none (marked_call state inner) -> Own
  | Mode (Mut, inner) when Option.is_none (marked_call state inner) && not (is_slice inner) -> Mut
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
  | Mode (Mut, inner) when Option.is_some (marked_call state inner) -> immutable state env inner
  | Call _ -> (
      match lent state value with
      | Some Types.Mut -> None
      | Some _ -> Some Lent_read_only
      | None -> Some Not_a_place)
  | _ -> Some Not_a_place

(* Records that a place is mutated: every index expression in the place
   uses the [mut self] version of [at], which lends its element [mut]. *)
let rec use_mutable_indexes state (value : expression) =
  match value.kind with
  | Member (base, _) | Parenthesized base | Mode (_, base) -> use_mutable_indexes state base
  | Bracket (base, _) ->
      (match state.tables.calls.(value.id) with
      | Some ({ callee = Trait_method ({ name = "at"; _ } as method_); arguments; _ } as call) ->
          state.tables.calls.(value.id) <-
            Some
              {
                call with
                callee = Trait_method { method_ with receiver = Mut };
                arguments =
                  List.map
                    (fun (argument : Tables.argument) ->
                      if argument.parameter_index = 0 then { argument with mode = Types.Mut }
                      else argument)
                    arguments;
              }
      | _ -> ());
      use_mutable_indexes state base
  | _ -> ()

type mutation =
  | Assignment
  | Mut_mark  (** The place is passed [mut], is a [mut] receiver, or is lent or yielded [mut]. *)

(* Checks that a place may be mutated, and records that it is. Every
   construct that mutates a place calls this. *)
let mutate state env ~(by : mutation) (value : expression) =
  let code : Diagnostic.Code.types =
    match by with Assignment -> Not_assignable | Mut_mark -> Wrong_mark
  in
  (match (immutable state env value, by) with
  | None, _ -> ()
  | Some (Captured name), _ ->
      report state code value.span
        (Printf.sprintf
           "A lambda cannot change what it captures, and `%s` is from outside it. Return the new \
            value instead, or use a loop."
           name)
  | Some (Read_only name), _ ->
      report state code value.span
        (Printf.sprintf
           "`%s` cannot change here: only a `var`, a `mut` parameter, or `mut self`, and their \
            parts, can be %s."
           name
           (match by with Assignment -> "assigned" | Mut_mark -> "marked `mut`"))
  | Some Lent_read_only, Assignment ->
      report state code value.span
        ~fixes:[ fix "Mark it `mut`." [ insert value.span.start "mut " ] ]
        "This part is lent read-only, so it cannot change. Mark the place it is lent from `mut`, \
         so that it is lent `mut`."
  | Some Not_a_place, Assignment ->
      report state code value.span
        "Only a place, such as a variable, a field, or an element, can be assigned."
  (* The check of the mark or of the receiver reports these. *)
  | Some (Lent_read_only | Not_a_place), Mut_mark -> ());
  use_mutable_indexes state value

let rec is_part_of_constant state (value : expression) =
  match value.kind with
  | Name path -> (
      match target state path.last with Some (Definition (Constant, _)) -> true | _ -> false)
  | Member (base, _) -> is_member_constant state value || is_part_of_constant state base
  | Bracket (base, _) | Parenthesized base -> is_part_of_constant state base
  | _ -> false

type argument_form = Marked of Types.mode * expression | Place | Lent of Types.mode | Temporary

let argument_form state (value : expression) =
  match value.kind with
  | Mode (mode, inner) when Option.is_none (marked_call state inner) ->
      Marked ((match mode with Mut -> Mut | Own -> Own), inner)
  | _ -> (
      match lent state value with
      | Some mode -> Lent mode
      | None -> if is_place state value then Place else Temporary)

(* The mode with which a field of a yielded constructor lends a place to
   the value that is built, or [None] if the field takes its value, as a
   field of any other constructor does. [type_] is the type of [value]. A
   method that yields read-only lends every place read-only, except a
   [Plain] place, which is copied. A method that yields [mut] lends the
   places that are marked [mut]. A slice is a value, so it is taken. *)
let lent_field state (value : expression) type_ : Types.mode option =
  match (Hashtbl.find_opt state.yielded value.id, argument_form state value) with
  | _ when is_slice value -> None
  | Some Read, Marked (Mut, _) -> Some Read
  | Some Read, (Place | Lent _) when not (plain state type_) -> Some Read
  | Some Mut, Marked (Mut, _) -> Some Mut
  | _ -> None

let mark_span (value : expression) (inner : expression) =
  Span.make value.span.start inner.span.start

let check_mode state env (value : expression) (parameter : Types.parameter_info) type_ =
  let name = parameter.name in
  match (parameter.mode, argument_form state value) with
  | Read, (Place | Temporary | Lent _) -> ()
  | Read, Marked (_, inner) ->
      report state Redundant_mark value.span
        ~fixes:
          [
            fix "Remove the mark."
              [ Diagnostic.delete (Span.make value.span.start inner.span.start) ];
          ]
        (Printf.sprintf "`%s` only reads its argument, so it takes no mark." name)
  | Mut, Marked (Mut, inner) -> mutate state env ~by:Mut_mark inner
  | Mut, Place ->
      report state Missing_mark value.span
        ~fixes:[ fix "Mark it `mut`." [ insert value.span.start "mut " ] ]
        (Printf.sprintf "`%s` may change its argument, so the call marks it `mut`." name)
  | Mut, Lent Mut -> mutate state env ~by:Mut_mark value
  | Mut, Lent (Read | Own) ->
      report state Wrong_mark value.span
        (Printf.sprintf
           "`%s` may change its argument, and this part is lent read-only. Mark the place it is \
            lent from `mut`, so that it is lent `mut`."
           name)
  | Own, Lent _ ->
      if not (plain state type_) then
        report state Missing_mark value.span
          ~fixes:
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else [])
          (Printf.sprintf
             "`%s` takes ownership of its argument, and a part that is lent cannot be given up. \
              Pass a copy."
             name)
  | Mut, (Temporary | Marked (Own, _)) ->
      report state Wrong_mark value.span
        (Printf.sprintf "`%s` changes its argument in place, so it must be a place marked `mut`."
           name)
  | Own, Marked (Own, inner) ->
      if plain state type_ then
        report state Redundant_mark value.span
          ~fixes:[ fix "Remove the mark." [ Diagnostic.delete (mark_span value inner) ] ]
          (Printf.sprintf "`%s` copies implicitly, so it needs no `own`." (show state type_))
  | Own, Temporary -> ()
  | Own, Place when Hashtbl.find_opt state.yielded value.id = Some Mut ->
      if not (plain state type_) then
        report state Missing_mark value.span
          ~fixes:
            (fix "Lend it `mut`." [ insert value.span.start "mut " ]
            ::
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else []))
          (Printf.sprintf
             "`%s` is a field of a value that is lent `mut`. Mark the place `mut` to lend it too, \
              or pass a copy."
             name)
  | Own, Place when is_part_of_constant state value ->
      if not (plain state type_) then
        report state Missing_mark value.span
          ~fixes:
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else [])
          (Printf.sprintf
             "`%s` takes ownership of its argument, and a constant cannot be given up. Pass a copy."
             name)
  | Own, Place ->
      if not (plain state type_) then
        report state Missing_mark value.span
          ~fixes:
            (fix "Give it up with `own`." [ insert value.span.start "own " ]
            ::
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else []))
          (Printf.sprintf
             "`%s` takes ownership of its argument. Give the place up with `own`, or pass a copy."
             name)
  | Own, Marked (Mut, _) ->
      report state Wrong_mark value.span
        (Printf.sprintf "`%s` takes ownership of its argument, so it is marked `own`, not `mut`."
           name)
  | (Mut | Own), Marked (Read, _) -> ()

(* A yielded constructor that lends a place owns nothing, so nothing drops
   it when the lend ends. Each of its other fields must then have nothing
   to drop: the field is a constructor too, or its type is [Plain].

   A place lent [mut] is not inside a variant's constructor at any depth.
   The caller could change the variant, as [mut pair.maybe() = None] does,
   and the place would be left without a value: a use after free.
   [operand] is the operand of the [yield]. *)
let check_lent_value state env (operand : expression) =
  let has_lent_field = ref false and owned_values = ref [] in
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
            | Some { mode = Read; _ } -> has_lent_field := true
            | Some { mode = Mut; _ } -> (
                has_lent_field := true;
                match variant with
                | Some variant when runs env ->
                    state.diagnostics <-
                      Diagnostic.make ~code:(Ownership Lent_mut_in_variant) argument.value.span
                        (Printf.sprintf
                           "This place is lent `mut` inside the variant `%s`. The caller could \
                            change the variant, and the place would be left without a value. Lend \
                            a local of the whole type instead, and store it back after the \
                            `yield`."
                           variant)
                      :: state.diagnostics
                | _ -> ())
            | _ -> fields ~variant argument.value)
          arguments
    | _ -> owned_values := value :: !owned_values
  in
  fields ~variant:None operand;
  if !has_lent_field && runs env then
    List.iter
      (fun (value : expression) ->
        defer state (fun () ->
            match Option.map (normalize state) state.tables.types.(value.id) with
            | None -> true
            | Some type_ when Types.contains_unsolved type_ -> false
            | Some type_ ->
                let fieldless_variant =
                  match (state.tables.resolutions.(value.id), type_) with
                  | Some (Variant_value _), Types.Function _ -> false
                  | Some (Variant_value _), _ -> true
                  | _ -> false
                in
                if not (plain state type_ || fieldless_variant) then
                  state.diagnostics <-
                    Diagnostic.make ~code:(Ownership Owned_beside_lent) value.span
                      "This value is owned, but the value that is yielded lends a place, so it \
                       owns nothing. Bind this value to a name first, and pass the name."
                    :: state.diagnostics;
                true))
      !owned_values

(* Checks a value where an owned value is required and no parameter
   receives it: the initializer of a [var], the value of an assignment, an
   element of a collection literal, or a part of a tagged string. A place
   there must be marked [own] or copied, unless its type is [Plain]. This
   is a rule of ownership. The type checker reports it because only the
   syntax tree has the marks. *)
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
                  ( fix "Give it up with `own`." [ insert value.span.start "own " ] :: copy,
                    Printf.sprintf
                      "An owned value is needed here, and `%s` is a place. Mark it `own` to give \
                       it up, or copy it."
                      place )
              in
              state.diagnostics <-
                Diagnostic.make ~fixes ~code:(Ownership Needs_owned) value.span message
                :: state.diagnostics
          | _ -> ());
          true
        end)
