val increment : Cursor.t -> target:Syntax.expression -> operator:Token.t -> unit
val double_negation : Cursor.t -> operator:Token.t -> operand:Syntax.expression -> unit
val match_arm_comma : Cursor.t -> comma:Token.t -> unit

val conditional :
  Cursor.t ->
  condition:Syntax.expression ->
  then_:Syntax.expression ->
  else_:Syntax.expression ->
  question:Token.t ->
  unit

val let_mut : Cursor.t -> let_token:Token.t -> mut_token:Token.t -> unit
val address_of : Cursor.t -> before:Token.t option -> ampersand:Token.t -> next:Token.t -> unit

val closure_bars :
  Cursor.t ->
  opening:Token.t ->
  closing:Token.t ->
  body:Syntax.expression ->
  before_else:bool ->
  unit

val brace_record :
  Cursor.t ->
  name_stop:int ->
  opening:Token.t ->
  first:Token.t ->
  last_stop:int ->
  closing:Token.t ->
  unit

val turbofish : Cursor.t -> colons:Token.t -> less:Token.t -> greater:Token.t -> unit
val angle_brackets : Cursor.t -> angles:Token.t list -> unit
val path_separator : Cursor.t -> separator:Token.t -> unit
val qualified_variant : Cursor.t -> qualifier_start:int -> variant:Token.t -> unit
val macro_call : Cursor.t -> name:Syntax.name -> bang:Token.t -> opening:Token.t -> unit
val keyword_macro : Cursor.t -> bang:Token.t -> closing:Token.t -> empty:bool -> unit
val tuple : Cursor.t -> opening:Token.t -> 'a
val tuple_field : Cursor.t -> field:Token.t -> 'a
val power_operator : Cursor.t -> operator:Token.t -> unit
val short_declaration : Cursor.t -> target:Syntax.expression -> operator:Token.t -> unit

val pipe_operator :
  Cursor.t -> value:Syntax.expression -> operator:Token.t -> callee:Syntax.expression -> unit

val lambda_annotation : Cursor.t -> from:int -> stop:int -> unit
val impl_parameters : Cursor.t -> opening:Token.t -> closing:Token.t -> plain:bool -> unit

val null_coalescing :
  Cursor.t ->
  value:Syntax.expression ->
  first:Token.t ->
  second:Token.t ->
  default:Syntax.expression ->
  unit

val parameter_name : Syntax.expression -> string

val trailing_lambda :
  Cursor.t ->
  callee:Syntax.expression ->
  parameter:string ->
  opening:Token.t ->
  closing:Token.t ->
  uses:Token.t list ->
  unit

val as_conversion :
  Cursor.t -> value:Syntax.expression -> as_token:Token.t -> target:Syntax.type_expression -> unit

val elif : Cursor.t -> previous_stop:int -> elif_token:Token.t -> unit
val loop : Cursor.t -> loop_token:Token.t -> unit
val constant_keyword : Cursor.t -> token:Token.t -> unit
