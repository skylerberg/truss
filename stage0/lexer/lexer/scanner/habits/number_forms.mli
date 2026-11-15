val scan_end : string -> int -> int
val check : string -> Numbers.checked
val trailing_point : Cursor.t -> start:int -> stop:int -> Numbers.checked -> Token.kind option
val report_trailing_point : Cursor.t -> start:int -> point:int -> unit
val leading_dot : Cursor.t -> Token.kind option
