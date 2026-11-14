type root = Local of Core.local | Temporary of Mir.local | Constant of Path.t | Environment
type step = Field of string | Element of { node : Core.id; origin : Core.origin }
type t = { root : root; steps : step list }
type overlap = Disjoint | Overlapping | Maybe_disjoint of Core.origin * Core.origin

val overlap : t -> t -> overlap
val is_slice_type : Types.ty -> bool
