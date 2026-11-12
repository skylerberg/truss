module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower

type version =
  | Own_version of Path.t
  | Trait_version of State.T.trait_reference * State.T.trait_method

val marked_receiver : Syntax.expression -> Path.receiver

val coerce :
  State.state ->
  State.env ->
  ?argument:bool ->
  Syntax.expression ->
  actual:Unify.T.ty ->
  expected:Unify.T.ty ->
  unit

val literal_type : State.state -> expected:Unify.T.ty option -> Unify.T.literal_kind -> Unify.T.ty
val named : State.state -> State.env -> Syntax.expression -> Resolve.head -> State.T.ty
val field : State.state -> Syntax.expression -> Unify.T.ty -> Syntax.name -> State.T.ty
val static_member : State.state -> Syntax.expression -> State.T.ty -> Syntax.name -> State.T.ty

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
  State.C.callee ->
  Instantiation.instance ->
  State.C.argument list ->
  string list ->
  State.T.ty

val check_specification_call :
  State.state -> State.env -> Syntax.expression -> State.T.signature -> unit

val trait_static_method :
  State.state ->
  Path.t ->
  State.Names.String_map.key ->
  Path.receiver ->
  (State.T.trait_reference * Members.T.trait_method) list

val resolve_evidence :
  State.state -> Syntax.expression -> Unify.T.ty -> State.T.trait_reference -> unit

val versions :
  State.state ->
  State.T.ty ->
  State.Names.String_map.key ->
  ((Path.receiver * version) list, State.T.trait_reference list) Result.t

val impl_method_if_resolved : State.state -> Unify.T.ty -> version -> version

val each_call :
  State.state -> Syntax.span -> State.T.ty -> State.T.mode -> (State.C.call * State.T.ty) option
