type site = { id : Core.id; origin : Core.origin; type_ : Types.ty }
type callee = unit Core.target
type t = { callee : callee; lends : Types.mode option; uses : Types.capability_set }

type shape =
  | Named_function of { id : Core.id; origin : Core.origin; path : Path.t }
  | Forwarded of Core.local
  | Other
