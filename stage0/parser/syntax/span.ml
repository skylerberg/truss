type t = { start : int; stop : int }

let make start stop =
  if start < 0 || stop < start then invalid_arg (Printf.sprintf "Syntax.Span.make %d %d" start stop);
  { start; stop }

let zero_width position = make position position
let to_source ~base span = Source.span (base + span.start) (base + span.stop)
let of_source ~base (span : Source.span) = make (span.start - base) (span.stop - base)
