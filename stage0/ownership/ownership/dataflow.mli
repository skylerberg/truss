type held_views = (Place.root * Actions.view list) list
type state = { views : held_views; loans : (Mir.loan * Actions.loan list) list }

val resolve : Context.context -> held_views -> Actions.view list -> Actions.view list
val forward : Context.context -> Actions.t -> state array array option array
