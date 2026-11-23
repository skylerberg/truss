val show_signature : Types.signature -> string
val signatures_agree : Types.signature -> Types.signature -> bool
val has_default : Types.signature -> bool

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
  trait_span:Source.Definition_span.t ->
  Syntax.path_type ->
  unit
