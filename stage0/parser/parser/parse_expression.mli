val is_clause_keyword : Token.kind -> bool

type operator = Binary_operator of Syntax.binary | Is_operator | Range_operator of bool

val angle_closer : Cursor.t -> int option
val type_expression : Cursor.t -> Syntax.type_expression
val path_type : Cursor.t -> Syntax.path_type
val bounds : Cursor.t -> Syntax.path_type list
val generics : Cursor.t -> Syntax.generic_parameter list
val path_type_list : Cursor.t -> Syntax.path_type list
val capability_list : Cursor.t -> Syntax.capability_reference list
val clause : Cursor.t -> Syntax.clause
val expression : ?open_range:bool -> Cursor.t -> Syntax.expression

val string_literal :
  Cursor.t -> start:int -> modules:Syntax.name list -> Token.string_literal -> Syntax.string_literal

val opens_body : Cursor.t -> bool
val body_opening : Cursor.t -> unit
val body : Cursor.t -> Syntax.block
val statement_line : Cursor.t -> previous:Syntax.statement option -> Syntax.statement
