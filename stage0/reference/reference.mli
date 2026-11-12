(** The reference parser: GRAMMAR.md's grammar, built by Menhir from grammar/truss.mly, which the
    tests and the fuzzer check the hand-written parser against. It is built only for them. *)

type entry
(** An entry point of the reference grammar. *)

val file : entry

val accepts : entry -> Token.t list -> bool
(** Whether the reference grammar accepts the tokens from the entry point. A string is one token, so
    the grammar does not see interpolations, which are ordinary expressions. A reserved word or a
    foreign sequence is rejected: no grammar rule accepts it. *)

(** The documents' examples, split into pieces the way a file is, each parsed by the kind of piece
    it starts like. *)
module Snippet : sig
  type kind = Use | Definition | Signature | Statement
  type item = { kind : kind; first : int; stop : int }

  val parse : Source.t -> Token.t array -> item list * Diagnostic.t list
  (** The pieces of an example, with the hand-written parser's diagnostics. *)

  val entry : kind -> entry
  (** The reference grammar's entry point for each kind of piece. *)
end
