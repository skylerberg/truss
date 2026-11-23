type t

val create : unit -> t
val read : t -> Interface.Lookups.t -> Path.t -> Types.signature option

val read_of_method :
  t -> Interface.Lookups.t -> owner:Path.t -> Types.trait_method -> Types.signature

type declaration = {
  definition : Path.t;
  signature : Types.signature;
  substitution : Types.substitution;
}

val find_declaration : t -> Interface.Lookups.t -> 'indirect Core.target -> declaration option
