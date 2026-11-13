val apply : string -> Diagnostic.span Diagnostic.edit list -> string
val run : fix:bool -> proofs:bool -> int

module For_testing : sig
  val chosen : Diagnostic.t list -> Diagnostic.t list
end
