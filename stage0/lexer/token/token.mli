type keyword =
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
  | Unless
  | Unreachable
  | Use
  | Uses
  | Var
  | When
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

type foreign = Plus_plus | Minus_minus | Star_star | Colon_equal | Colon_colon | Pipe_greater

module Decimal : sig
  type t = private { significand : Z.t; exponent : Z.t }

  val normalize : significand:Z.t -> exponent:Z.t -> t
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
val list_interpolations : string_literal -> interpolation array
val punctuation : (string * punctuation) list
val find_word : string -> kind option
val spell_keyword : keyword -> string
val spell_reserved : reserved -> string
val spell_punctuation : punctuation -> string
val spell_foreign : foreign -> string
val definition_keywords : keyword list
val spell_tokens : ?insertions:(int * string) list -> t array -> string option
val joins : char -> char -> bool
val can_end : kind -> bool
val can_begin : kind -> bool
val joins_neighbor : before:char option -> after:char option -> string -> bool

module For_testing : sig
  val list_texts : string_literal -> text array
  val keywords : (string * keyword) list
  val reserved_words : (string * reserved) list
end
