(* The tokens the lexer produces. Each list below is the single place its
   items are spelled; a test checks the lists against GRAMMAR.md. *)

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
  | Self_value (* self *)
  | Self_type (* Self *)
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

(* Reserved for later use. The parser reports them, since a good fix depends
   on the construct around them. *)
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

(* Sequences from other languages whose fix depends on the expression around
   them. No grammar rule accepts them, and the parser reports them. *)
type foreign = Plus_plus | Minus_minus

(* An exact decimal, significand × 10^exponent, with the trailing zeros of
   the significand removed, so that equal values are equal records. *)
module Decimal : sig
  type t = private { significand : Z.t; exponent : Z.t }

  val make : significand:Z.t -> exponent:Z.t -> t
end = struct
  type t = { significand : Z.t; exponent : Z.t }

  let ten = Z.of_int 10

  (* The zeros are counted in the decimal digits, in one pass. Dividing by
     ten once for each zero would take time quadratic in the number of
     digits, which a literal with many zeros would make the lexer pay. *)
  let make ~significand ~exponent =
    if Z.equal significand Z.zero then { significand = Z.zero; exponent = Z.zero }
    else
      let digits = Z.to_string significand in
      let rec trailing_zeros count =
        if digits.[String.length digits - 1 - count] = '0' then trailing_zeros (count + 1)
        else count
      in
      let zeros = trailing_zeros 0 in
      if zeros = 0 then { significand; exponent }
      else
        {
          significand = Z.divexact significand (Z.pow ten zeros);
          exponent = Z.add exponent (Z.of_int zeros);
        }
end

type t = {
  kind : kind;
  span : span;
  line_break_before : bool; (* a line break between this token and the one before *)
  blank_line_before : bool; (* a blank line between them *)
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

(* A string's texts alternate with its interpolations, starting and ending
   with a text, which is the shape of a Template: "a${x}b" has [first] "a"
   and [rest] [(x, "b")]. *)
and string_literal = {
  tag : (string * span) option;
  form : form;
  first : text;
  rest : (interpolation * text) array;
}

and form = Ordinary | Raw of { quotes : int; dollars : int; multi_line : bool }
and text = { value : string; span : span }
and interpolation = { tokens : t array; span : span }

let equal_punctuation (first : punctuation) (second : punctuation) =
  match (first, second) with
  | Open first, Open second | Close first, Close second -> first = second
  | (Open _ | Close _), _ | _, (Open _ | Close _) -> false
  | _ -> first == second

let texts literal = Array.append [| literal.first |] (Array.map snd literal.rest)
let interpolations literal = Array.map fst literal.rest

let keywords =
  [
    ("any", Any);
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
    ("transparent", Transparent);
    ("true", True);
    ("type", Type);
    ("unreachable", Unreachable);
    ("use", Use);
    ("uses", Uses);
    ("var", Var);
    ("while", While);
    ("with", With);
    ("yield", Yield);
    ("yields", Yields);
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
    ("::", Colon_colon);
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

let foreign_sequences = [ ("++", Plus_plus); ("--", Minus_minus) ]

(* The keywords that start a top-level definition. *)
let definition_keywords =
  [ Fn; Type; Trait; Impl; Capability; Let; Test; Theorem; Proof; Use; Public; Internal ]

let words : (string, kind) Hashtbl.t =
  let table = Hashtbl.create 64 in
  List.iter (fun (spelling, keyword) -> Hashtbl.replace table spelling (Keyword keyword)) keywords;
  List.iter
    (fun (spelling, reserved) -> Hashtbl.replace table spelling (Reserved reserved))
    reserved_words;
  table

let word spelling = Hashtbl.find_opt words spelling
let spelling_of list value = fst (List.find (fun (_, candidate) -> candidate = value) list)
let keyword_spelling = spelling_of keywords
let reserved_spelling = spelling_of reserved_words
let punctuation_spelling = spelling_of punctuation
let foreign_spelling = spelling_of foreign_sequences
