module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

val binding_pattern :
  State.state -> 'a -> Syntax.pattern -> Unify.T.ty -> is_var:bool -> mode:State.T.mode -> unit

val pattern : State.state -> 'a -> Syntax.pattern -> Unify.T.ty -> mode:State.T.mode -> unit
val check_literal_fits : State.state -> Syntax.expression -> Z.t -> Unify.T.ty -> unit
val usize_bits : State.state -> int
val builtin_range : ?usize_bits:int -> Unify.T.ty -> (Z.t * Z.t) option
val character_tag : State.state -> Syntax.string_literal -> Intrinsic.builtin option

val character_literal :
  State.state -> Syntax.id -> Syntax.string_literal -> Intrinsic.builtin -> State.T.ty
