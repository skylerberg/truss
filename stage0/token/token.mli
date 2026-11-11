(** The tokens the lexer produces. *)

type span = Source.span = private { start : int; stop : int }

type keyword =
  | Any
  | Assert
  | Break
  | Capability
  | Concurrent
  | Continue
  | Cost
  | Decreases
  | Derives
  | Echo
  | Else
  | Ensures
  | Exists
  | False
  | Fn
  | For
  | Forall
  | If
  | Impl
  | In
  | Indirect
  | Internal
  | Invariant
  | Is
  | Law
  | Lends
  | Let
  | Match
  | Mut
  | Opaque
  | Own
  | Parallel
  | Proof
  | Provide
  | Public
  | Requires
  | Return
  | Self_value  (** [self] *)
  | Self_type  (** [Self] *)
  | Test
  | Theorem
  | Todo
  | Trait
  | Transparent
  | True
  | Type
  | Unreachable
  | Use
  | Uses
  | Var
  | While
  | With
  | Yield
  | Yields

(** Reserved for later use. The parser reports them, since a good fix depends on the construct
    around them. *)
type reserved =
  | As
  | Async
  | Await
  | Const
  | Defer
  | Extern
  | Loop
  | Macro
  | Static
  | Unsafe
  | Where

type bracket = Paren | Square | Curly

type punctuation =
  | Open of bracket
  | Close of bracket
  | Comma
  | Colon
  | Colon_colon
  | Dot
  | Dot_dot
  | Dot_dot_equal
  | Arrow
  | Fat_arrow
  | Question
  | Bar
  | Equal
  | Plus_equal
  | Minus_equal
  | Star_equal
  | Slash_equal
  | Percent_equal
  | Ampersand_equal
  | Bar_equal
  | Caret_equal
  | Shift_left_equal
  | Shift_right_equal
  | Plus
  | Minus
  | Star
  | Slash
  | Percent
  | Equal_equal
  | Not_equal
  | Less
  | Less_equal
  | Greater
  | Greater_equal
  | And_and
  | Or_or
  | Implies
  | Bang
  | Ampersand
  | Caret
  | Tilde
  | Shift_left
  | Shift_right

(** Sequences from other languages whose fix depends on the expression around them. No grammar rule
    accepts them, and the parser reports them. *)
type foreign = Plus_plus | Minus_minus

(** An exact decimal, significand × 10^exponent, with the trailing zeros of the significand removed,
    so that equal values are equal records. *)
module Decimal : sig
  type t = private { significand : Z.t; exponent : Z.t }

  val make : significand:Z.t -> exponent:Z.t -> t
end

type t = {
  kind : kind;
  span : span;
  line_break_before : bool;  (** A line break between this token and the one before. *)
  blank_line_before : bool;  (** A blank line between them. *)
}

and kind =
  | Upper of string
  | Lower of string
  | Underscore
  | Keyword of keyword
  | Reserved of reserved
  | Integer of Z.t
  | Float of Decimal.t
  | String of string_literal
  | Punctuation of punctuation
  | Foreign of foreign
  | Newline
  | End_of_file

and string_literal = {
  tag : (string * span) option;
  form : form;
  first : text;
  rest : (interpolation * text) array;
}
(** A string's texts alternate with its interpolations, starting and ending with a text, which is
    the shape of a Template: ["a${x}b"] has [first] ["a"] and [rest] [[(x, "b")]]. *)

and form = Ordinary | Raw of { quotes : int; dollars : int; multi_line : bool }
and text = { value : string; span : span }
and interpolation = { tokens : t array; span : span }

val equal_punctuation : punctuation -> punctuation -> bool
(** Equality on [punctuation] that compares constructors, without a structural comparison. *)

val texts : string_literal -> text array
val interpolations : string_literal -> interpolation array

(** {1 Spellings}

    Each list is the one place its items are spelled. A test checks them against GRAMMAR.md. *)

val keywords : (string * keyword) list
val reserved_words : (string * reserved) list
val punctuation : (string * punctuation) list
val foreign_sequences : (string * foreign) list

val word : string -> kind option
(** The keyword or reserved word with this spelling, if there is one. *)

val keyword_spelling : keyword -> string
val reserved_spelling : reserved -> string
val punctuation_spelling : punctuation -> string
val foreign_spelling : foreign -> string

(** {1 Definitions} *)

val definition_keywords : keyword list
(** The keywords that start a top-level definition. *)
