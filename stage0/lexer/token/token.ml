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
  | Modifies
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
  | View
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
end = struct
  type t = { significand : Z.t; exponent : Z.t }

  let ten = Z.of_int 10

  let normalize ~significand ~exponent =
    if Z.equal significand Z.zero then { significand = Z.zero; exponent = Z.zero }
    else
      let significand, zeros = Z.remove significand ten in
      { significand; exponent = Z.add exponent (Z.of_int zeros) }
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

let equal_punctuation (first : punctuation) (second : punctuation) =
  match (first, second) with
  | Open first, Open second | Close first, Close second -> first = second
  | (Open _ | Close _), _ | _, (Open _ | Close _) -> false
  | _ -> first == second

let list_interpolations literal = Array.map fst literal.rest

let keywords =
  [
    ("assert", Assert);
    ("break", Break);
    ("capability", Capability);
    ("concurrent", Concurrent);
    ("continue", Continue);
    ("cost", Cost);
    ("decreases", Decreases);
    ("derives", Derives);
    ("echo", Echo);
    ("else", Else);
    ("ensures", Ensures);
    ("exists", Exists);
    ("false", False);
    ("fn", Fn);
    ("for", For);
    ("forall", Forall);
    ("if", If);
    ("impl", Impl);
    ("in", In);
    ("indirect", Indirect);
    ("internal", Internal);
    ("invariant", Invariant);
    ("is", Is);
    ("law", Law);
    ("lends", Lends);
    ("let", Let);
    ("match", Match);
    ("modifies", Modifies);
    ("mut", Mut);
    ("opaque", Opaque);
    ("own", Own);
    ("parallel", Parallel);
    ("proof", Proof);
    ("provide", Provide);
    ("public", Public);
    ("requires", Requires);
    ("return", Return);
    ("self", Self_value);
    ("Self", Self_type);
    ("test", Test);
    ("theorem", Theorem);
    ("todo", Todo);
    ("trait", Trait);
    ("true", True);
    ("type", Type);
    ("unless", Unless);
    ("unreachable", Unreachable);
    ("use", Use);
    ("uses", Uses);
    ("var", Var);
    ("view", View);
    ("when", When);
    ("while", While);
    ("with", With);
  ]

let reserved_words =
  [
    ("as", As);
    ("async", Async);
    ("await", Await);
    ("const", Const);
    ("defer", Defer);
    ("extern", Extern);
    ("loop", Loop);
    ("macro", Macro);
    ("static", Static);
    ("unsafe", Unsafe);
    ("where", Where);
  ]

let punctuation =
  [
    ("(", Open Paren);
    (")", Close Paren);
    ("[", Open Square);
    ("]", Close Square);
    ("{", Open Curly);
    ("}", Close Curly);
    (",", Comma);
    (":", Colon);
    (".", Dot);
    ("..", Dot_dot);
    ("..=", Dot_dot_equal);
    ("->", Arrow);
    ("=>", Fat_arrow);
    ("?", Question);
    ("|", Bar);
    ("=", Equal);
    ("+=", Plus_equal);
    ("-=", Minus_equal);
    ("*=", Star_equal);
    ("/=", Slash_equal);
    ("%=", Percent_equal);
    ("&=", Ampersand_equal);
    ("|=", Bar_equal);
    ("^=", Caret_equal);
    ("<<=", Shift_left_equal);
    (">>=", Shift_right_equal);
    ("+", Plus);
    ("-", Minus);
    ("*", Star);
    ("/", Slash);
    ("%", Percent);
    ("==", Equal_equal);
    ("!=", Not_equal);
    ("<", Less);
    ("<=", Less_equal);
    (">", Greater);
    (">=", Greater_equal);
    ("&&", And_and);
    ("||", Or_or);
    ("==>", Implies);
    ("!", Bang);
    ("&", Ampersand);
    ("^", Caret);
    ("~", Tilde);
    ("<<", Shift_left);
    (">>", Shift_right);
  ]

let foreign_sequences =
  [
    ("++", Plus_plus);
    ("--", Minus_minus);
    ("**", Star_star);
    (":=", Colon_equal);
    ("::", Colon_colon);
    ("|>", Pipe_greater);
  ]

let definition_keywords =
  [ Fn; Type; Trait; Impl; Capability; Let; Test; Theorem; Proof; Use; Public; Internal ]

let words : (string, kind) Hashtbl.t =
  let table = Hashtbl.create 64 in
  List.iter (fun (spelling, keyword) -> Hashtbl.replace table spelling (Keyword keyword)) keywords;
  List.iter
    (fun (spelling, reserved) -> Hashtbl.replace table spelling (Reserved reserved))
    reserved_words;
  table

let find_word spelling = Hashtbl.find_opt words spelling
let lookup_spelling list value = fst (List.find (fun (_, candidate) -> candidate = value) list)
let spell_keyword = lookup_spelling keywords
let spell_reserved = lookup_spelling reserved_words
let spell_punctuation = lookup_spelling punctuation
let spell_foreign = lookup_spelling foreign_sequences

let joins left right =
  let is_name_byte character =
    (character >= 'a' && character <= 'z')
    || (character >= 'A' && character <= 'Z')
    || (character >= '0' && character <= '9')
    || character = '_'
    || Char.code character >= 0x80
  in
  let is_operator_byte character = String.contains "!%&*+-./:<=>^|" character in
  (is_name_byte left && (is_name_byte right || right = '"' || right = '\''))
  || (is_operator_byte left && is_operator_byte right)

let joins_neighbor ~before ~after code =
  match (code, before, after) with
  | "", Some left, Some right -> joins left right
  | "", _, _ -> false
  | _ ->
      Option.fold ~none:false ~some:(fun left -> joins left code.[0]) before
      || Option.fold ~none:false ~some:(joins code.[String.length code - 1]) after

let can_end = function
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ -> true
  | Punctuation (Close _ | Question) -> true
  | Keyword (True | False | Self_value | Self_type | Todo | Unreachable | Break | Continue | Return)
    ->
      true
  | Foreign (Plus_plus | Minus_minus) -> true
  | Foreign (Star_star | Colon_equal | Colon_colon | Pipe_greater) -> false
  | Keyword _ | Reserved _ | Punctuation _ | Newline | End_of_file -> false

let can_begin = function
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ | Reserved _ -> true
  | Foreign (Plus_plus | Minus_minus) -> true
  | Foreign (Star_star | Colon_equal | Colon_colon | Pipe_greater) -> false
  | Punctuation (Open _ | Minus | Bang | Tilde) -> true
  | Keyword
      ( Assert | Break | Capability | Concurrent | Continue | Echo | Exists | False | Fn | For
      | Forall | If | Impl | Internal | Law | Let | Match | Mut | Own | Parallel | Proof | Provide
      | Public | Return | Self_value | Self_type | Test | Theorem | Todo | Trait | True | Type
      | Unreachable | Use | Var | While ) ->
      true
  | Keyword
      ( Cost | Decreases | Derives | Else | Ensures | In | Indirect | Invariant | Is | Lends
      | Modifies | Opaque | Requires | Unless | Uses | View | When | With ) ->
      false
  | Punctuation _ | Newline | End_of_file -> false

module For_testing = struct
  let list_texts literal = Array.append [| literal.first |] (Array.map snd literal.rest)
  let keywords = keywords
  let reserved_words = reserved_words
end
