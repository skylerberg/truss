(** Checking an [impl] against the trait it implements, and each method written inside it against
    the method the trait declares. *)

val check_impl :
  Checking.state ->
  Syntax.impl_member Syntax.line list ->
  Types.impl_interface ->
  Syntax.path_type ->
  unit

val check_impl_method :
  Checking.state ->
  Syntax.name ->
  Path.receiver ->
  Types.signature ->
  Types.impl_interface ->
  Syntax.path_type ->
  unit
