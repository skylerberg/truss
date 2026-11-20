type root = Local of Core.local | Temporary of Mir.local | Constant of Path.t | Environment
type step = Field of string | Element of Core.id | Range of Core.id
type t = { root : root; steps : step list }
type overlap = Disjoint | Overlapping | Maybe_disjoint of Core.id list * Core.id list

val classify_overlap : t -> t -> overlap
