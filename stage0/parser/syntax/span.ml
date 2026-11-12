type t = { start : int; stop : int }

let make start stop =
  if start < 0 || stop < start then invalid_arg (Printf.sprintf "Syntax.Span.make %d %d" start stop);
  { start; stop }
