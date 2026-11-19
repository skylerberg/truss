type root = Local of Core.local | Temporary of Mir.local | Constant of Path.t | Environment
type selection = { node : Core.id; origin : Core.origin }
type step = Field of string | Element of selection | Range of selection
type t = { root : root; steps : step list }
type overlap = Disjoint | Overlapping | Maybe_disjoint of Core.origin list * Core.origin list

val classify_overlap : t -> t -> overlap
val is_slice_type : Types.ty -> bool
val is_storage_type : Types.ty -> bool
