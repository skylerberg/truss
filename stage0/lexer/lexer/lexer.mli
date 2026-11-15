val lex : Source.t -> Token.t array * Diagnostic.t list

module Recovery : sig
  val to_original : Source.span Diagnostic.edit list -> Token.t array -> Token.t array

  val alters_neighbors :
    edits:Source.span Diagnostic.edit list -> written:Token.t array -> fixed:Token.t array -> bool

  val recover :
    stage:string ->
    path:string ->
    attempt:(Source.span Diagnostic.edit list -> unfixed:Diagnostic.t list -> 'fixed option) ->
    is_applied:(Diagnostic.t -> bool) ->
    Token.t array ->
    Diagnostic.t list ->
    Diagnostic.t list * 'fixed option
end

module For_testing : sig
  val can_end : Token.kind -> bool
  val can_begin : Token.kind -> bool
end
