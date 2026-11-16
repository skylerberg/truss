val increment : Cursor.t -> target:Syntax.expression -> operator:Token.t -> unit
val report_double_negation : Cursor.t -> operator:Token.t -> operand:Syntax.expression -> unit
val match_arm_comma : Cursor.t -> comma:Token.t -> unit

val report_conditional :
  Cursor.t ->
  condition:Syntax.expression ->
  then_:Syntax.expression ->
  else_:Syntax.expression ->
  question:Token.t ->
  unit

val report_let_mut : Cursor.t -> let_token:Token.t -> mut_token:Token.t -> unit

val report_address_of :
  Cursor.t -> before:Token.t option -> ampersand:Token.t -> next:Token.t -> unit

val report_closure_bars :
  Cursor.t ->
  opening:Token.t ->
  closing:Token.t ->
  body:Syntax.expression ->
  is_before_else:bool ->
  unit

val report_brace_record :
  Cursor.t ->
  name_stop:int ->
  opening:Token.t ->
  first:Token.t ->
  last_stop:int ->
  closing:Token.t ->
  unit

val report_turbofish : Cursor.t -> colons:Token.t -> less:Token.t -> greater:Token.t -> unit
val report_angle_brackets : Cursor.t -> angles:Token.t list -> unit
val report_path_separator : Cursor.t -> separator:Token.t -> unit
val report_qualified_variant : Cursor.t -> qualifier_start:int -> variant:Syntax.name -> unit
val report_macro_call : Cursor.t -> name:Syntax.name -> bang:Token.t -> opening:Token.t -> unit
val report_keyword_macro : Cursor.t -> bang:Token.t -> closing:Token.t -> has_arguments:bool -> unit
val report_tuple : Cursor.t -> opening:Token.t -> 'a
val report_tuple_field : Cursor.t -> field:Token.t -> 'a
val report_power_operator : Cursor.t -> operator:Token.t -> unit
val report_short_declaration : Cursor.t -> target:Syntax.expression -> operator:Token.t -> unit

val pipe_operator :
  Cursor.t -> value:Syntax.expression -> operator:Token.t -> callee:Syntax.expression -> unit

val report_lambda_annotation : Cursor.t -> from:int -> stop:int -> unit

val report_impl_parameters :
  Cursor.t -> opening:Token.t -> closing:Token.t -> has_bounds:bool -> unit

val report_null_coalescing :
  Cursor.t ->
  value:Syntax.expression ->
  first:Token.t ->
  second:Token.t ->
  default:Syntax.expression ->
  unit

val derive_parameter_name : Syntax.expression -> string

val report_trailing_lambda :
  Cursor.t ->
  callee:Syntax.expression ->
  parameter:string ->
  opening:Token.t ->
  closing:Token.t ->
  uses:Token.t list ->
  unit

val report_as_conversion :
  Cursor.t -> value:Syntax.expression -> as_token:Token.t -> target:Syntax.type_expression -> unit

val report_elif : Cursor.t -> previous_stop:int -> elif_token:Token.t -> unit
val report_loop : Cursor.t -> loop_token:Token.t -> unit
val report_constant_keyword : Cursor.t -> token:Token.t -> reserved:Token.reserved -> unit

val report_let_condition :
  Cursor.t ->
  let_token:Token.t ->
  pattern:Syntax.pattern ->
  scrutinee:Syntax.expression ->
  is_condition:bool ->
  unit

val report_let_shorthand : Cursor.t -> let_token:Token.t -> name:Syntax.name -> unit
