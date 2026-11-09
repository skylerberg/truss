(* The tokens the lexer produces. Each list below is the single place its
   items are spelled; a test checks the lists against GRAMMAR.md. *)

type span = Source.span = { start : int; stop : int }

type keyword =
  | Any | Assert | Break | Capability | Continue | Cost | Decreases | Derives
  | Echo | Else | Ensures | Exists | False | Fn | For | Forall | If | Impl | In
  | Internal | Invariant | Is | Law | Let | Match | Mut | Opaque | Own
  | Parallel | Proof | Provide | Public | Requires | Return
  | Self_value  (* self *)
  | Self_type  (* Self *)
  | Test | Theorem | Todo | Trait | True | Type | Unreachable | Use | Uses
  | Var | While | With | Yield | Yields

(* Reserved for later use. The parser reports them, since a good fix depends
   on the construct around them. *)
type reserved =
  | As | Async | Await | Const | Defer | Extern | Loop | Macro | Static
  | Unsafe | Where

type punctuation =
  | Left_paren | Right_paren | Left_bracket | Right_bracket | Left_brace
  | Right_brace | Comma | Colon | Colon_colon | Dot | Dot_dot | Dot_dot_equal
  | Arrow | Fat_arrow | Question | Bar
  | Equal | Plus_equal | Minus_equal | Star_equal | Slash_equal
  | Percent_equal | Ampersand_equal | Bar_equal | Caret_equal
  | Shift_left_equal | Shift_right_equal
  | Plus | Minus | Star | Slash | Percent | Equal_equal | Not_equal | Less
  | Less_equal | Greater | Greater_equal | And_and | Or_or | Implies | Bang | Ampersand
  | Caret | Tilde | Shift_left | Shift_right

(* Sequences from other languages whose fix depends on the expression around
   them. No grammar rule accepts them, and the parser reports them. *)
type foreign = Plus_plus | Minus_minus

type t = {
  kind : kind;
  span : span;
  line_break_before : bool;  (* a line break between this token and the one before *)
  blank_line_before : bool;  (* a blank line between them *)
}

and kind =
  | Upper of string
  | Lower of string
  | Underscore
  | Keyword of keyword
  | Reserved of reserved
  | Integer of Z.t
  | Float of { significand : Z.t; exponent : Z.t }  (* significand × 10^exponent, exactly *)
  | String of string_literal
  | Punctuation of punctuation
  | Foreign of foreign
  | Newline
  | End_of_file

and string_literal = {
  tag : (string * span) option;
  form : form;
  texts : text array;  (* always one more than interpolations *)
  interpolations : interpolation array;
}

and form = Ordinary | Raw of { quotes : int; dollars : int; multi_line : bool }
and text = { value : string; span : span }
and interpolation = { tokens : t array; span : span }

(* A token from the scanner, before layout. [first_line_break] is the first
   line break between this token and the one before, if there is one, which
   is where a NEWLINE token goes. *)
type raw = { token : t; first_line_break : span option }

let keywords =
  [
    ("any", Any); ("assert", Assert); ("break", Break); ("capability", Capability);
    ("continue", Continue); ("cost", Cost); ("decreases", Decreases); ("derives", Derives);
    ("echo", Echo); ("else", Else); ("ensures", Ensures); ("exists", Exists);
    ("false", False); ("fn", Fn); ("for", For); ("forall", Forall); ("if", If);
    ("impl", Impl); ("in", In); ("internal", Internal); ("invariant", Invariant);
    ("is", Is); ("law", Law); ("let", Let); ("match", Match); ("mut", Mut);
    ("opaque", Opaque); ("own", Own); ("parallel", Parallel); ("proof", Proof);
    ("provide", Provide); ("public", Public); ("requires", Requires); ("return", Return);
    ("self", Self_value); ("Self", Self_type); ("test", Test); ("theorem", Theorem);
    ("todo", Todo); ("trait", Trait); ("true", True); ("type", Type);
    ("unreachable", Unreachable); ("use", Use); ("uses", Uses); ("var", Var);
    ("while", While); ("with", With); ("yield", Yield); ("yields", Yields);
  ]

let reserved_words =
  [
    ("as", As); ("async", Async); ("await", Await); ("const", Const); ("defer", Defer);
    ("extern", Extern); ("loop", Loop); ("macro", Macro); ("static", Static);
    ("unsafe", Unsafe); ("where", Where);
  ]

let punctuation =
  [
    ("(", Left_paren); (")", Right_paren); ("[", Left_bracket); ("]", Right_bracket);
    ("{", Left_brace); ("}", Right_brace); (",", Comma); (":", Colon); ("::", Colon_colon);
    (".", Dot); ("..", Dot_dot); ("..=", Dot_dot_equal); ("->", Arrow); ("=>", Fat_arrow);
    ("?", Question); ("|", Bar);
    ("=", Equal); ("+=", Plus_equal); ("-=", Minus_equal); ("*=", Star_equal);
    ("/=", Slash_equal); ("%=", Percent_equal); ("&=", Ampersand_equal); ("|=", Bar_equal);
    ("^=", Caret_equal); ("<<=", Shift_left_equal); (">>=", Shift_right_equal);
    ("+", Plus); ("-", Minus); ("*", Star); ("/", Slash); ("%", Percent);
    ("==", Equal_equal); ("!=", Not_equal); ("<", Less); ("<=", Less_equal);
    (">", Greater); (">=", Greater_equal); ("&&", And_and); ("||", Or_or); ("==>", Implies); ("!", Bang);
    ("&", Ampersand); ("^", Caret); ("~", Tilde); ("<<", Shift_left); (">>", Shift_right);
  ]

let foreign_sequences = [ ("++", Plus_plus); ("--", Minus_minus) ]

(* The keywords that start a top-level definition. A line that starts with one
   in column 0 ends whatever came before it, when the lexer recovers from an
   unclosed bracket or an unterminated raw string. *)
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

let spelling_of list value =
  fst (List.find (fun (_, candidate) -> candidate = value) list)

let keyword_spelling = spelling_of keywords
let reserved_spelling = spelling_of reserved_words
let punctuation_spelling = spelling_of punctuation
let foreign_spelling = spelling_of foreign_sequences

let closer_of = function
  | Left_paren -> Some Right_paren
  | Left_bracket -> Some Right_bracket
  | Left_brace -> Some Right_brace
  | _ -> None

let opener_of = function
  | Right_paren -> Some Left_paren
  | Right_bracket -> Some Left_bracket
  | Right_brace -> Some Left_brace
  | _ -> None
