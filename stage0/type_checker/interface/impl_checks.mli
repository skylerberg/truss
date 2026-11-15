val check_impl :
  Checking.state ->
  Syntax.impl_member Syntax.node list ->
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
