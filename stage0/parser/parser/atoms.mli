val expression_node : Cursor.t -> int -> Syntax.expression_kind -> Syntax.expression
val type_node : Cursor.t -> int -> Syntax.type_kind -> Syntax.type_expression
val error_expression : Cursor.t -> int -> Syntax.expression
val begins_expression : Token.kind -> bool
val begins_statement : Token.kind -> bool
val mode : Cursor.t -> Syntax.mode option
val name : Cursor.t -> Token.t -> string -> Syntax.name
val lower : Cursor.t -> string -> Syntax.name
val upper : Cursor.t -> string -> Syntax.name
val module_prefix : Cursor.t -> Syntax.name list
val upper_path : Cursor.t -> string -> Syntax.path

val string_literal :
  Cursor.t ->
  start:int ->
  modules:Syntax.name list ->
  Token.string_literal ->
  interpolation:(Token.interpolation -> Syntax.expression) ->
  Syntax.string_literal
