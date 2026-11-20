val is_clause_keyword : Token.kind -> bool
val rank_binary : Syntax.binary -> int
val find_angle_closer : Cursor.t -> int option
val parse_type_expression : Cursor.t -> Syntax.type_expression
val parse_path_type : Cursor.t -> Syntax.path_type
val parse_bounds : Cursor.t -> Syntax.path_type list
val parse_generics : Cursor.t -> Syntax.generic_parameter list
val parse_path_type_list : Cursor.t -> Syntax.path_type list
val parse_capability_list : Cursor.t -> Syntax.capability_reference list
val parse_capability_uses : Cursor.t -> Syntax.capability_use list
val parse_clause : Cursor.t -> Syntax.clause
val parse_expression : ?open_range:bool -> Cursor.t -> Syntax.expression

val parse_string_literal :
  Cursor.t -> start:int -> modules:Syntax.name list -> Token.string_literal -> Syntax.string_literal

val opens_body : Cursor.t -> bool
val expect_body_opening : Cursor.t -> unit
val parse_body : Cursor.t -> Syntax.block
val parse_statement_line : Cursor.t -> previous:Syntax.statement option -> Syntax.statement
