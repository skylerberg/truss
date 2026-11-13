module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

val binding_pattern :
  State.state -> 'a -> Syntax.pattern -> Types.ty -> is_var:bool -> mode:Types.mode -> unit

val pattern : State.state -> 'a -> Syntax.pattern -> Types.ty -> mode:Types.mode -> unit
val check_literal_fits : State.state -> Syntax.expression -> Z.t -> Types.ty -> unit
val usize_bits : State.state -> int
val builtin_range : ?usize_bits:int -> Types.ty -> (Z.t * Z.t) option
val character_tag : State.state -> Syntax.string_literal -> Intrinsic.builtin option

val character_literal :
  State.state -> Syntax.id -> Syntax.string_literal -> Intrinsic.builtin -> Types.ty
