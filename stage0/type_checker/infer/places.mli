val find_target : Resolve.resolved -> Syntax.name -> Resolve.target option
val is_member_constant : Tables.t -> Syntax.expression -> bool
val is_place : Resolve.resolved -> Tables.t -> Syntax.expression -> bool

val find_keyword_operation :
  Resolve.resolved -> Tables.t -> Syntax.expression -> (Syntax.id * Syntax.expression) option

val find_lent_mode : Resolve.resolved -> Tables.t -> Syntax.expression -> Language.Mode.t option
val is_slice : Syntax.expression -> bool
val is_plain_string_literal : Syntax.expression -> bool
val is_borrowed : Resolve.resolved -> Tables.t -> Syntax.expression -> bool
val classify_scrutinee_mode : Resolve.resolved -> Tables.t -> Syntax.expression -> Language.Mode.t
