type t = Cursor.t

val create : Source.t -> Diagnostic.Collector.t -> Cursor.t
val next : Cursor.t -> Layout.input
