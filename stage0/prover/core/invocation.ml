type site = { id : Core.id; origin : Core.origin; type_ : Types.ty }

let site_of (node : Core.expression) = { id = node.id; origin = node.origin; type_ = node.type_ }

type callee = unit Core.target
type t = { callee : callee; lends : Types.mode option; uses : Types.capability_set }

(* A callee over nothing: what a call through a function value gives is the
   caller's. *)
let unit_callee callee =
  Option.value (Core_walk.traverse_indirect (fun _ -> Some ()) callee) ~default:(Core.Indirect ())

let of_core (call : Core.call) =
  { callee = unit_callee call.callee; lends = call.lends; uses = call.uses }

let of_mir (call : Mir.call) ~lends = { callee = unit_callee call.callee; lends; uses = call.uses }

type shape =
  | Named_function of { id : Core.id; origin : Core.origin; path : Path.t }
  | Forwarded of Core.local
  | Other
