(** A span relative to its definition's base: [start] is included and [stop] is not. Spans are made
    only by {!make}, so [0 <= start <= stop]. *)

type t = private { start : int; stop : int }

val make : int -> int -> t
val zero_width : int -> t

val to_source : base:int -> t -> Source.span
(** The span in its file's offsets, for the definition at [base]. *)

val of_source : base:int -> Source.span -> t
(** The span relative to [base]. Raises [Invalid_argument] if the span starts before [base]. *)
