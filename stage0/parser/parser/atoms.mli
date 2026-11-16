val make_expression_node : Cursor.t -> int -> Syntax.expression_kind -> Syntax.expression
val make_type_node : Cursor.t -> int -> Syntax.type_kind -> Syntax.type_expression
val make_error_expression : Cursor.t -> int -> Syntax.expression
val begins_expression : Token.kind -> bool
val begins_statement : Token.kind -> bool
val parse_mode : Cursor.t -> Syntax.mode option
val make_name : Cursor.t -> Token.t -> string -> Syntax.name
val lower_name : Cursor.t -> string -> Syntax.name
val parse_upper_name : Cursor.t -> string -> Syntax.name
val parse_module_prefix : Cursor.t -> Syntax.name list
val parse_upper_path : Cursor.t -> string -> Syntax.path

val make_string_literal :
  Cursor.t ->
  start:int ->
  modules:Syntax.name list ->
  Token.string_literal ->
  interpolation:(Token.interpolation -> Syntax.expression) ->
  Syntax.string_literal
