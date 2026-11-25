let build (mode : Language.Mode.t) (node : Core.expression) : Core.operand =
  match (mode, node.kind) with
  | (Read | Mut), Use place -> Place place
  | Read, Literal _ -> Place (Temporary node)
  | Mut, Parameter_default _ -> Place (Temporary node)
  | _ -> Value node

let build_argument mode node : Core.argument = { mode; value = build mode node }
