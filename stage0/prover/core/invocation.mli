type site = { origin : Core.origin; type_ : Types.ty }
type callee = unit Core.target
type t = { callee : callee; lends : Language.Mode.t option; uses : Types.capability_set }

type shape =
  | Named_function of { origin : Core.origin; path : Path.t }
  | Forwarded of Core.local
  | Lambda
  | Other
