let build (mode : Types.mode) (node : Core.expression) : Core.operand =
  match (mode, node.kind) with
  | (Read | Mut), Use place -> Place place
  | Read, String _ -> Place (Temporary node)
  | _ -> Value node

let build_argument mode node : Core.argument = Passed { mode; value = build mode node }
