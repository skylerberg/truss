(** A span relative to its definition's base: [start] is included and [stop] is not. Spans are made
    only by {!make}, so [0 <= start <= stop]. *)

type t = private { start : int; stop : int }

val make : int -> int -> t
