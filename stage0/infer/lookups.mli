module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower

type version = Own_version of Path.t | Trait_version of Types.trait_reference * Types.trait_method

val marked_receiver : Syntax.expression -> Path.receiver

val coerce :
  State.state ->
  State.env ->
  ?argument:bool ->
  Syntax.expression ->
  actual:Types.ty ->
  expected:Types.ty ->
  unit

val literal_type : State.state -> expected:Types.ty option -> Types.literal_kind -> Types.ty
val named : State.state -> State.env -> Syntax.expression -> Resolve.head -> Types.ty
val field : State.state -> Syntax.expression -> Types.ty -> Syntax.name -> Types.ty
val static_member : State.state -> Syntax.expression -> Types.ty -> Syntax.name -> Types.ty

val explicit_type_arguments :
  ?head:int ->
  State.state ->
  Syntax.expression ->
  Instantiation.instance ->
  Syntax.bracket_item list ->
  unit

val finish_call :
  State.state ->
  Syntax.expression ->
  Tables.callee ->
  Instantiation.instance ->
  Tables.argument list ->
  string list ->
  Types.ty

val check_specification_call :
  State.state -> State.env -> Syntax.expression -> Types.signature -> unit

val trait_static_method :
  State.state ->
  Path.t ->
  State.Names.String_map.key ->
  Path.receiver ->
  (Types.trait_reference * Types.trait_method) list

val resolve_evidence : State.state -> Syntax.expression -> Types.ty -> Types.trait_reference -> unit

val versions :
  State.state ->
  Types.ty ->
  State.Names.String_map.key ->
  ((Path.receiver * version) list, Types.trait_reference list) Result.t

val impl_method_if_resolved : State.state -> Types.ty -> version -> version

val each_call :
  State.state -> Syntax.span -> Types.ty -> Types.mode -> (Tables.call * Types.ty) option
