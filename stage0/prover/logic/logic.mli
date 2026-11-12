(** The solver's logic: sorts, terms, and queries, and their canonical text in SMT-LIB.

    Symbols here are the prover's own names: each is a {!symbol}, whose constructor gives its kind.
    A query's canonical text never contains them: {!text} numbers every declared symbol by its first
    appearance, so two queries that differ only in names have the same text, and so the same hash.
*)

type sort =
  | Int  (** The mathematical integers, which every built-in integer type is a range of. *)
  | Bool
  | Float of int * int
      (** IEEE 754 binary floating point, with its exponent's and significand's widths in bits, the
          significand counting its hidden bit: [Float (11, 53)] is [Float64]. *)
  | Uninterpreted of string
      (** A sort the solver knows nothing about, such as a type parameter, by its type's key. *)

(** The prover's symbols. A [type_key] names a type: the prover gives equal types equal keys. *)
module Symbol : sig
  (** The [O(...)] bound that a pair of cost constants belongs to. *)
  type cost_group =
    | Own_bound of { counter : int; inherited : bool }
        (** The definition's own bound on a counter, by the counter's number in the definition, or
            the bound it inherits from a trait's method. *)
    | Lambda_bound of { lambda : int; counter : int }  (** A lambda's bound, by its node. *)
    | Loop_bound of int  (** A loop's [cost] clause, by its origin. *)

  (** A symbol, over the terms it can hold. *)
  type 'term t =
    | Variable of { label : string; numbers : int list }
        (** A value the prover makes, or a bound variable: [label] names its purpose, and [numbers]
            tell it from others with the same label. *)
    | Function of { callee : Path.t; instance : string list }
        (** A pure callee as a function in the logic, at the keys of its type arguments. *)
    | Function_value of { callee : Path.t; instance : string list }
        (** A named function used as a value. *)
    | Constant of Path.t  (** A [const] definition's value. *)
    | Generic_value of { owner : Path.t; name : string }  (** A generic value parameter. *)
    | Literal of { type_key : string; text : string }  (** A text literal's value. *)
    | Argument of 'term  (** A term that holds a pure call, named by the term. *)
    | Lambda of { sorts : sort list; definition : 'term }
        (** A functional lambda, named by its parameters' sorts and its definition. *)
    | Over of 'term t
        (** A symbol made inside a lambda's body, as a function of the lambda's arguments. *)
    | Constructor of { type_key : string; type_name : string; variant : string option }
        (** A datatype's constructor: a variant's, or with [None], a record's. [type_name] is the
            type's own name, as a counterexample shows a record. *)
    | Field of { type_key : string; variant : string option; field : string }
        (** A datatype's selector. *)
    | Unit  (** The constructor of [Unit]. *)
    | Apply of sort list
        (** The application of a function value of the first sort to arguments of the others, whose
            result has the last. *)
    | Equal of string  (** A type's derived [==]. *)
    | Valid of string  (** Whether a value of a type whose invariant is hidden is valid. *)
    | Rank of string  (** A value's place in the order of parts. *)
    | Capacity of string  (** How many elements a storage has room for. *)
    | Model of string  (** The sequence a storage or a view holds. *)
    | Slack of string  (** A buffer's slack for growing. *)
    | Potential of string  (** A value's potential. *)
    | Potential_measure of string  (** A type's potential as a measure for a sum. *)
    | Cursor_yielded of string  (** A cursor's yielded parts. *)
    | Cursor_ended of string  (** Whether a cursor has ended. *)
    | Block_bytes of { type_key : string; variant : string option }
        (** The size of a variant's or a record's block. *)
    | Time of sort  (** The time of one call of a function value of the sort. *)
    | Method_time of { method_ : Path.t; self_type : string }
        (** The time of one call of a trait's method, for a type. *)
    | Opaque_operation of { operation : string; type_key : string; integer : (int * bool) option }
        (** An operation known only by its result's range, with the width and signedness of its
            integer type, if it has one. *)
    | Bit_count of { count : string; width : int }
        (** [leading_zeros] or [trailing_zeros] of an integer of a width. *)
    | System of string  (** Whether a program runs on an operating system or architecture. *)
    | Libc_number of string  (** A number the C library defines. *)
    | Handle_descriptor  (** The descriptor a handle holds. *)
    | Compare_bytes_order  (** The order [compare_bytes] gives. *)
    | Cost_factor of cost_group
    | Cost_addend of cost_group
    | Cost_most  (** The larger of two costs. *)
    | Cost_log  (** The base-2 logarithm, for cost bounds. *)
    | Cost_power  (** Exponentiation, for cost bounds. *)
    | Reached of int  (** Whether a counterexample reaches a decision, by its position. *)
    | Condition of int  (** Whether a decision's condition holds there. *)
end

type term =
  | Symbol of symbol  (** A declared constant, or a bound variable inside its quantifier. *)
  | Integer of Z.t
  | Boolean of bool
  | Bits of int * Z.t  (** A bit-vector literal: its width, and its value, at or above zero. *)
  | Apply of symbol * term list
      (** A declared function, or a datatype's constructor or selector, applied. *)
  | Is of symbol * term  (** SMT-LIB's [(_ is C)]: whether constructor [C] built the value. *)
  | Operation of string * term list
      (** A built-in operation of SMT-LIB, such as ["+"] or ["ite"], by its SMT-LIB name. *)
  | Forall of (symbol * sort) list * term
  | Exists of (symbol * sort) list * term

and symbol = term Symbol.t

type declaration =
  | Constant of symbol * sort
  | Function of symbol * sort list * sort
  | Datatype of string * (symbol * (symbol * sort) list) list
      (** An algebraic datatype, the sort [Uninterpreted name]: its constructors, each with its
          fields' selectors and sorts. A constructor and a selector are applied by name, and {!Is}
          tests which constructor built a value. Constructors and fields are numbered in the order
          given, which the prover makes their names' order, so reordering a type's fields or
          variants changes no query. *)

type query = {
  declarations : declaration list;
  facts : term list;  (** The assumptions, in order. *)
  goal : term;  (** The goal; the query asks whether it can be false. *)
}

val arguments : term -> term list
(** The arguments of an application, [Apply], [Operation], or [Is]; of any other term, none. *)

val map_arguments : (term -> term) -> term -> term
(** An application with each of its arguments mapped; any other term as it is. *)

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

val mentions : symbol list -> term -> bool
(** Whether a term mentions any of the symbols, free. *)

val free_symbols : term -> symbol list
(** The symbols a term mentions free, as constants, not as applied functions. *)

val quantified : term -> bool
(** Whether a term has a quantifier in it. *)

val replace : from:term -> into:term -> term -> term
(** Each occurrence of [from] in a term replaced by [into], except under a quantifier that binds one
    of [from]'s symbols. *)

val untriggered : query -> bool
(** Whether a quantified fact of the query has no trigger, so that the solver may not use it where a
    proof needs it. *)

val prune : query -> query
(** The query with only the facts its goal can depend on: starting from the goal's declared symbols,
    each fact that mentions one of them is kept, with its symbols, until no more are added. A
    quantified fact is kept only once every symbol of one of its triggers is, since only terms of
    their shapes can use it. Dropping a fact is always sound, and a fact about symbols the goal
    never reaches cannot help to prove it, so a change to such a fact leaves the query's text, and
    its cached result, as they were. *)

(** {1 Canonical text} *)

val text : query -> string
(** The query's canonical SMT-LIB text: declarations numbered by first appearance, then the facts,
    then the negated goal, then [(check-sat)]. Each quantifier states the triggers chosen for it.
    Only symbols reached from the facts or the goal are declared. *)

val term_text : query -> term -> string option
(** A term in the query's canonical names, for asking its value of a model, or [None] if it names a
    symbol the query's text does not. *)

val symbols : query -> (symbol * string) list
(** Each declared symbol the canonical text mentions, with its canonical name, for reading a model
    back. *)

val members : query -> (string * (symbol * symbol list)) list
(** Each datatype constructor the canonical text names, with the prover's name for it, for reading a
    model back. *)

val hash : string -> string
(** The hash of a query's text, in hexadecimal, with a prefix naming the format and the algorithm.
*)

val show_term : term -> string
(** A term as SMT-LIB, with the prover's own names, for tests and debugging. *)

val show_symbol : symbol -> string
(** A symbol as readable text, for tests and debugging. *)
