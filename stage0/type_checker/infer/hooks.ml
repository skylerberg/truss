let raise_not_set name _ = State.raise_bug "Hooks.%s was called before Expressions set it" name

let expression_hook :
    (State.state -> State.env -> ?expected:Types.ty -> Syntax.expression -> Types.ty) ref =
  ref (fun _ _ ?expected:_ -> raise_not_set "expression")

let check_hook : (State.state -> State.env -> Syntax.expression -> Types.ty -> unit) ref =
  ref (fun _ _ _ -> raise_not_set "check")

let check_expression state env ?expected value = !expression_hook state env ?expected value
let check state env value expected = !check_hook state env value expected
