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
  | Self_value
  | Self_type
  | Test
  | Theorem
  | Todo
  | Trait
  | True
  | Type
  | Unreachable
  | Use
  | Uses
  | Var
  | While
  | With

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

type foreign = Plus_plus | Minus_minus | Star_star | Colon_equal | Pipe_greater

module Decimal : sig
  type t = private { significand : Z.t; exponent : Z.t }

  val normalized : significand:Z.t -> exponent:Z.t -> t
end

type t = {
  kind : kind;
  span : Source.span;
  line_break_before : bool;
  blank_line_before : bool;
  is_inserted_closer : bool;
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
  tag : (string * Source.span) option;
  form : form;
  first : text;
  rest : (interpolation * text) array;
}

and form = Ordinary | Raw of { quotes : int; dollars : int; multi_line : bool }
and text = { value : string; span : Source.span }
and interpolation = { tokens : t array; span : Source.span; is_closed : bool }

val equal_punctuation : punctuation -> punctuation -> bool
val texts : string_literal -> text array
val interpolations : string_literal -> interpolation array
val keywords : (string * keyword) list
val reserved_words : (string * reserved) list
val punctuation : (string * punctuation) list
val word : string -> kind option
val keyword_spelling : keyword -> string
val reserved_spelling : reserved -> string
val punctuation_spelling : punctuation -> string
val foreign_spelling : foreign -> string
val definition_keywords : keyword list
val spelling : ?insertions:(int * string) list -> t array -> string option
val can_end : kind -> bool
val can_begin : kind -> bool
val joins_neighbor : before:string -> after:string -> string -> bool
