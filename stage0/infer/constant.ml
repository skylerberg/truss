(* Checks constant expressions: the value of a constant, and a default. The
   compiler evaluates a constant expression, and every build gets the same
   value.

   A constant expression consists of literals, operators on built-in numbers
   and [Bool], other constants, and records, variants, and collections of
   these. It calls no function, so it uses no capability and always
   terminates, and it names only definitions. The check reads the checked
   tables, which give the callee of each call and the referent of each name,
   and not the spelling of the expression. *)

open Syntax
module T = Types
open State
open Pattern_typing

(* The first sub-expression that is not allowed in a constant expression. *)
let rec offending state (value : expression) : expression option =
  let first = List.find_map (offending state) in
  let built_in (operand : expression) =
    match state.tables.types.(operand.id) with
    | Some type_ ->
        T.is_integer_type type_ || T.is_float_type type_ || T.is_builtin Bool type_
        || T.is_error type_
    | None -> true
  in
  match value.kind with
  | Integer _ | Float _ | True | False | Todo | Expression_error -> None
  | String { rest = []; _ } -> None
  | String { rest = (interpolated, _) :: _; _ } -> Some interpolated
  | Parenthesized inner -> offending state inner
  | Prefix (_, inner) -> if built_in inner then offending state inner else Some value
  | Binary { left; right; _ } ->
      if built_in left && built_in right then first [ left; right ] else Some value
  | Name _ | Member _ | Bracket _ -> (
      match (state.tables.meanings.(value.id), value.kind) with
      | Some (Global _ | Variant_value _ | Type_name _), _ -> None
      | Some (Field_read _), Member (base, _) -> offending state base
      | _ -> Some value)
  | Call (_, arguments) -> (
      match state.tables.calls.(value.id) with
      | Some { callee = Constructor _; _ } ->
          first (List.map (fun (argument : argument) -> argument.value) arguments)
      | _ -> Some value)
  | List items -> first items
  | Map entries -> first (List.concat_map (fun (key, item) -> [ key; item ]) entries)
  | _ -> Some value

(* Integer arithmetic that the checker can evaluate must not overflow its
   type or divide by zero. An operation that would panic at run time is a
   compile-time error here. A negated literal is checked as a literal. *)
let rec check_arithmetic state (value : expression) =
  let worked_out part =
    Interface.Constants.expression state.database ~visiting:[] state.resolved part
  in
  (match (value.kind, state.tables.types.(value.id)) with
  | Prefix (Negate, { kind = Integer _; _ }), _ -> ()
  | (Prefix _ | Binary _), Some type_ -> (
      match (builtin_range ~usize_bits:(usize_bits state) type_, worked_out value, value.kind) with
      | Some (low, high), Some found, _ when Z.lt found low || Z.gt found high ->
          report state Constant_overflow value.span
            (Printf.sprintf "This is %s, which does not fit in `%s`, which holds %s to %s."
               (Z.to_string found) (T.show type_) (Z.to_string low) (Z.to_string high))
      | Some _, None, Binary { operator = Divide | Remainder; right; _ }
        when worked_out right = Some Z.zero ->
          report state Constant_overflow right.span "This divides by zero."
      | _ -> ())
  | _ -> ());
  Syntax_walk.expression_parts ~expression:(check_arithmetic state) ~statement:ignore value

(* Checks the value of a constant, or a default if [default] is true. The
   expression has already been checked against its type. *)
let check state ~default (value : expression) =
  (match offending state value with
  | Some part ->
      if default then
        report state Default_not_constant part.span
          "A default must be a constant expression: literals, arithmetic, constants, and records, \
           variants, and collections built from them. It cannot call a function or name a \
           parameter."
      else
        report state Not_constant part.span
          "A constant must be a constant expression: literals, arithmetic, other constants, and \
           records, variants, and collections built from them. It cannot call a function."
  | None -> ());
  check_arithmetic state value
