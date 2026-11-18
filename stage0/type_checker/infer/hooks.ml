let raise_not_set name _ = State.raise_bug "Hooks.%s was called before Expressions set it" name

let expression_hook :
    (State.state -> State.env -> ?expected:Types.ty -> Syntax.expression -> Types.ty) ref =
  ref (fun _ _ ?expected:_ -> raise_not_set "expression")

let check_hook : (State.state -> State.env -> Syntax.expression -> Types.ty -> unit) ref =
  ref (fun _ _ _ -> raise_not_set "check")

let check_expression state env ?expected value = !expression_hook state env ?expected value
let check state env value expected = !check_hook state env value expected

let check_integer state env (value : Syntax.expression) =
  let type_ = check_expression state env value in
  State.defer state (fun () ->
      match State.normalize state type_ with
      | Types.Integer | Literal (Integer_literal, _) | Never | Error _ -> true
      | resolved when State.is_integer_type state resolved -> true
      | Variable _ | Hole -> false
      | resolved ->
          State.report_mismatch state (State.read_span state value.id) ~expected:Types.Integer
            ~actual:resolved;
          true)
