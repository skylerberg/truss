(** The rules on a [parallel for] and a [concurrent for]: an iteration that mutates its element is
    lent a place no other iteration is lent, which prevents a data race, and a task is given no view
    that the next pull of a cursor could leave dangling. *)

val check : Context.context -> Mir.t -> unit
