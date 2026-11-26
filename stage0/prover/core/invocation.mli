type site = { origin : Core.origin; type_ : Types.ty }

type shape =
  | Named_function of { origin : Core.origin; path : Path.t }
  | Forwarded of Core.local
  | Lambda
  | Other
