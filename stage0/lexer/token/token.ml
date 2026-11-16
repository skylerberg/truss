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
end = struct
  type t = { significand : Z.t; exponent : Z.t }

  let ten = Z.of_int 10

  let normalized ~significand ~exponent =
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
    ("true", True);
    ("type", Type);
    ("unreachable", Unreachable);
    ("use", Use);
    ("uses", Uses);
    ("var", Var);
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

let foreign_sequences =
  [
    ("++", Plus_plus);
    ("--", Minus_minus);
    ("**", Star_star);
    (":=", Colon_equal);
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

let word spelling = Hashtbl.find_opt words spelling
let spelling_of list value = fst (List.find (fun (_, candidate) -> candidate = value) list)
let keyword_spelling = spelling_of keywords
let reserved_spelling = spelling_of reserved_words
let punctuation_spelling = spelling_of punctuation
let foreign_spelling = spelling_of foreign_sequences

let escaped text =
  let buffer = Buffer.create (String.length text) in
  String.iteri
    (fun index character ->
      match character with
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\t' -> Buffer.add_string buffer "\\t"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\000' -> Buffer.add_string buffer "\\0"
      | '$' when index + 1 < String.length text && text.[index + 1] = '{' ->
          Buffer.add_string buffer "\\$"
      | character when Char.code character < 0x20 || Char.code character = 0x7f ->
          Buffer.add_string buffer (Printf.sprintf "\\u{%x}" (Char.code character))
      | character -> Buffer.add_char buffer character)
    text;
  Buffer.contents buffer

let rec spelling ?(insertions = []) (tokens : t array) =
  let inserted offset =
    String.concat ""
      (List.filter_map (fun (at, text) -> if at = offset then Some text else None) insertions)
  in
  let buffer = Buffer.create 64 in
  let rec spell index previous_stop =
    if index = Array.length tokens then begin
      Option.iter (fun stop -> Buffer.add_string buffer (inserted stop)) previous_stop;
      true
    end
    else
      let token = tokens.(index) in
      match token.kind with
      | End_of_file -> spell (index + 1) previous_stop
      | kind -> (
          match if token.is_inserted_closer then None else kind_spelling kind with
          | None -> false
          | Some text ->
              (match previous_stop with
              | Some stop ->
                  Buffer.add_string buffer (inserted stop);
                  if stop < token.span.start then begin
                    Buffer.add_char buffer ' ';
                    Buffer.add_string buffer (inserted token.span.start)
                  end
              | None -> Buffer.add_string buffer (inserted token.span.start));
              Buffer.add_string buffer text;
              spell (index + 1) (Some token.span.stop))
  in
  if spell 0 None then Some (Buffer.contents buffer) else None

and kind_spelling = function
  | Upper name | Lower name -> Some name
  | Underscore -> Some "_"
  | Keyword keyword -> Some (keyword_spelling keyword)
  | Reserved reserved -> Some (reserved_spelling reserved)
  | Integer value -> Some (Z.to_string value)
  | Float { Decimal.significand; exponent } ->
      Some (Z.to_string significand ^ "e" ^ Z.to_string exponent)
  | String literal -> string_spelling literal
  | Punctuation punctuation -> Some (punctuation_spelling punctuation)
  | Foreign foreign -> Some (foreign_spelling foreign)
  | Newline | End_of_file -> None

and string_spelling literal =
  let pieces =
    Array.to_list
      (Array.map
         (fun ((interpolation : interpolation), (text : text)) ->
           if interpolation.is_closed then
             Option.map
               (fun inner -> "${" ^ inner ^ "}" ^ escaped text.value)
               (spelling interpolation.tokens)
           else None)
         literal.rest)
  in
  if List.mem None pieces then None
  else
    let tag = match literal.tag with Some (tag, _) -> tag | None -> "" in
    Some
      (tag ^ "\"" ^ escaped literal.first.value
      ^ String.concat "" (List.filter_map Fun.id pieces)
      ^ "\"")

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
  | Foreign (Star_star | Colon_equal | Pipe_greater) -> false
  | Keyword _ | Reserved _ | Punctuation _ | Newline | End_of_file -> false

let can_begin = function
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ | Reserved _ -> true
  | Foreign (Plus_plus | Minus_minus) -> true
  | Foreign (Star_star | Colon_equal | Pipe_greater) -> false
  | Punctuation (Open _ | Minus | Bang | Tilde) -> true
  | Keyword
      ( Any | Assert | Break | Capability | Concurrent | Continue | Echo | Exists | False | Fn | For
      | Forall | If | Impl | Internal | Law | Let | Match | Mut | Own | Parallel | Proof | Provide
      | Public | Return | Self_value | Self_type | Test | Theorem | Todo | Trait | True | Type
      | Unreachable | Use | Var | While ) ->
      true
  | Keyword
      ( Cost | Decreases | Derives | Else | Ensures | In | Indirect | Invariant | Is | Lends
      | Opaque | Requires | Uses | With ) ->
      false
  | Punctuation _ | Newline | End_of_file -> false
