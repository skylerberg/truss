type root = Local of Core.local | Constant of Path.t | Environment
type step = Field of string | Element of { node : Core.id; origin : Core.origin }
type t = { root : root; steps : step list }
type overlap = Disjoint | Overlapping | Maybe_disjoint of Core.origin * Core.origin

val overlap : t -> t -> overlap
val is_prefix : t -> t -> bool
val storage_index : Core.expression -> Core.place option
val of_core : Core.place -> t option
val is_slice_type : Types.ty -> bool
val written_slice : whole:bool -> Core.place -> Core.place option
val of_slice : Core.expression -> t option
val is_lent_part : Core.place -> bool
