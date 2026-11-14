type site = { id : Core.id; origin : Core.origin; type_ : Types.ty }
type callee = unit Core.target
type t = { callee : callee; lends : Types.mode option; uses : Types.capability_set }

let unit_callee : _ Core.target -> callee = function
  | Function { path; type_arguments } -> Function { path; type_arguments }
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } ->
      Trait_method { trait; name; receiver; self_type; type_arguments; evidence }
  | Capability_method { capability; name } -> Capability_method { capability; name }
  | Intrinsic { operation; type_arguments } -> Intrinsic { operation; type_arguments }
  | Indirect _ -> Indirect ()

let of_mir (call : Mir.call) ~lends = { callee = unit_callee call.callee; lends; uses = call.uses }

type shape =
  | Named_function of { id : Core.id; origin : Core.origin; path : Path.t }
  | Forwarded of Core.local
  | Other
