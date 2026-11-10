(** The solver's logic: sorts, terms, and queries, and their canonical text in SMT-LIB.

    Symbols here are the prover's own names, chosen to be readable while a query is built. A query's
    canonical text never contains them: {!text} numbers every declared symbol by its first
    appearance, so two queries that differ only in names have the same text, and so the same hash.
*)

type sort =
  | Int  (** The mathematical integers, which every built-in integer type is a range of. *)
  | Bool
  | Float of int * int
      (** IEEE 754 binary floating point, with its exponent's and significand's widths in bits, the
          significand counting its hidden bit: [Float (11, 53)] is [Float64]. *)
  | Uninterpreted of string  (** A sort the solver knows nothing about, such as a type parameter. *)

type term =
  | Symbol of string  (** A declared constant, or a bound variable inside its quantifier. *)
  | Integer of Z.t
  | Boolean of bool
  | Bits of int * Z.t  (** A bit-vector literal: its width, and its value, at or above zero. *)
  | Apply of string * term list
      (** A built-in operation of SMT-LIB, such as ["+"] or ["ite"], or a declared function. *)
  | Forall of (string * sort) list * term
  | Exists of (string * sort) list * term

type declaration =
  | Constant of string * sort
  | Function of string * sort list * sort
  | Datatype of string * (string * (string * sort) list) list
      (** An algebraic datatype, the sort [Uninterpreted name]: its constructors, each with its
          fields' selectors and sorts. A constructor and a selector are applied by name, and
          {!tester} names the test of which constructor built a value. Constructors and fields are
          numbered in the order given, which the prover makes their names' order, so reordering a
          type's fields or variants changes no query. *)

val tester : string -> string
(** The function that tests whether a value was built by a constructor. *)

type query = {
  declarations : declaration list;
  facts : term list;  (** What may be assumed, in order. *)
  goal : term;  (** What must be shown; the query asks whether it can be false. *)
}

(** {1 Building terms} *)

val int : int -> term
val ( &&& ) : term -> term -> term
val ( ||| ) : term -> term -> term
val ( ==> ) : term -> term -> term
val not_ : term -> term
val equal : term -> term -> term
val ite : term -> term -> term -> term
val conjunction : term list -> term
val disjunction : term list -> term

val truncated_divide : term -> term -> term
(** Integer division rounding toward zero, as Truss's [/] does. SMT-LIB's [div] rounds so that the
    remainder is never negative. *)

val truncated_remainder : term -> term -> term
(** The remainder of {!truncated_divide}, with the sign of the left operand. *)

val mentions : string list -> term -> bool
(** Whether a term mentions any of the symbols, free. *)

val replace : from:term -> into:term -> term -> term
(** Each occurrence of [from] in a term replaced by [into], except under a quantifier that binds one
    of [from]'s symbols. *)

val prune : query -> query
(** The query with only the facts its goal can depend on: starting from the goal's declared symbols,
    each fact that mentions one of them is kept, with its symbols, until no more are added. A
    quantified fact is kept only once every symbol of one of its triggers is, an application of a
    declared function that names every bound variable, since only a term of such a shape can use it.
    Dropping a fact is always sound, and a fact about symbols the goal never reaches cannot help to
    prove it, so a change to such a fact leaves the query's text, and its cached result, as they
    were. *)

(** {1 Canonical text} *)

val text : query -> string
(** The query's canonical SMT-LIB text: declarations numbered by first appearance, then the facts,
    then the negated goal, then [(check-sat)]. Only symbols reached from the facts or the goal are
    declared. *)

val symbols : query -> (string * string) list
(** Each declared symbol the canonical text mentions, with its canonical name, for reading a model
    back. *)

val members : query -> (string * (string * string list)) list
(** Each datatype constructor the canonical text names, with the prover's name for it, for reading a
    model back. *)

val hash : string -> string
(** The hash of a query's text, in hexadecimal, with a prefix naming the format and the algorithm.
*)

val show_term : term -> string
(** A term as SMT-LIB, with the prover's own names, for tests and debugging. *)
