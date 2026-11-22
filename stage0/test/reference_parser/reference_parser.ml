type entry = (Lexing.lexbuf -> Truss.token) -> Lexing.lexbuf -> unit

let token_of_kind (kind : Token.kind) : Truss.token option =
  match kind with
  | Upper _ -> Some UPPER
  | Lower _ -> Some LOWER
  | Underscore -> Some UNDERSCORE
  | Integer _ -> Some INTEGER
  | Float _ -> Some FLOAT
  | String { tag = None; _ } -> Some STRING
  | String { tag = Some _; _ } -> Some TAGGED
  | Newline -> Some NEWLINE
  | End_of_file -> Some EOF
  | Reserved _ | Foreign _ -> None
  | Keyword keyword ->
      Some
        (match keyword with
        | Any -> ANY
        | Assert -> ASSERT
        | Break -> BREAK
        | Capability -> CAPABILITY
        | Concurrent -> CONCURRENT
        | Continue -> CONTINUE
        | Cost -> COST
        | Decreases -> DECREASES
        | Derives -> DERIVES
        | Echo -> ECHO
        | Else -> ELSE
        | Ensures -> ENSURES
        | Exists -> EXISTS
        | False -> FALSE
        | Fn -> FN
        | For -> FOR
        | Forall -> FORALL
        | If -> IF
        | Impl -> IMPL
        | In -> IN
        | Indirect -> INDIRECT
        | Internal -> INTERNAL
        | Invariant -> INVARIANT
        | Is -> IS
        | Law -> LAW
        | Lends -> LENDS
        | Let -> LET
        | Match -> MATCH
        | Mut -> MUT
        | Opaque -> OPAQUE
        | Own -> OWN
        | Parallel -> PARALLEL
        | Proof -> PROOF
        | Provide -> PROVIDE
        | Public -> PUBLIC
        | Requires -> REQUIRES
        | Return -> RETURN
        | Self_value -> SELF
        | Self_type -> SELF_TYPE
        | Test -> TEST
        | Theorem -> THEOREM
        | Todo -> TODO
        | Trait -> TRAIT
        | True -> TRUE
        | Type -> TYPE
        | Unless -> UNLESS
        | Unreachable -> UNREACHABLE
        | Use -> USE
        | Uses -> USES
        | Var -> VAR
        | When -> WHEN
        | While -> WHILE
        | With -> WITH)
  | Punctuation punctuation ->
      Some
        (match punctuation with
        | Open Paren -> LPAREN
        | Close Paren -> RPAREN
        | Open Square -> LBRACKET
        | Close Square -> RBRACKET
        | Open Curly -> LBRACE
        | Close Curly -> RBRACE
        | Comma -> COMMA
        | Colon -> COLON
        | Dot -> DOT
        | Dot_dot -> DOTDOT
        | Dot_dot_equal -> DOTDOTEQ
        | Arrow -> ARROW
        | Fat_arrow -> FATARROW
        | Question -> QUESTION
        | Bar -> BAR
        | Equal -> EQ
        | Plus_equal -> PLUSEQ
        | Minus_equal -> MINUSEQ
        | Star_equal -> STAREQ
        | Slash_equal -> SLASHEQ
        | Percent_equal -> PERCENTEQ
        | Ampersand_equal -> AMPEQ
        | Bar_equal -> BAREQ
        | Caret_equal -> CARETEQ
        | Shift_left_equal -> SHLEQ
        | Shift_right_equal -> SHREQ
        | Plus -> PLUS
        | Minus -> MINUS
        | Star -> STAR
        | Slash -> SLASH
        | Percent -> PERCENT
        | Equal_equal -> EQEQ
        | Not_equal -> NEQ
        | Less -> LT
        | Less_equal -> LE
        | Greater -> GT
        | Greater_equal -> GE
        | And_and -> ANDAND
        | Or_or -> OROR
        | Implies -> IMPLIES
        | Bang -> BANG
        | Ampersand -> AMP
        | Caret -> CARET
        | Tilde -> TILDE
        | Shift_left -> SHL
        | Shift_right -> SHR)

let accepts parse_entry (tokens : Token.t list) =
  let converted = List.filter_map (fun (written : Token.t) -> token_of_kind written.kind) tokens in
  if List.compare_lengths converted tokens <> 0 then false
  else
    let remaining = ref converted in
    let read_next_token _ =
      match !remaining with
      | token :: rest ->
          remaining := rest;
          token
      | [] -> Truss.EOF
    in
    match parse_entry read_next_token (Lexing.from_string "") with
    | () -> true
    | exception Truss.Error -> false

let parse_file = Truss.file

let conflicts_resolved_by_precedence =
  List.fold_left
    (fun count line ->
      if String.ends_with ~suffix:"silently solved." line then count + Scanf.sscanf line "%d" Fun.id
      else count)
    0
    (String.split_on_char '\n' Menhir_log.text)

module Snippet = struct
  type kind = Use | Definition | Signature | Statement
  type item = { kind : kind; first : int; stop : int }

  let starts_definition (tokens : Token.t array) (piece : Parser.For_testing.piece) =
    let read_kind offset =
      if piece.first + offset < piece.stop then tokens.(piece.first + offset).kind else End_of_file
    in
    match (read_kind 0, read_kind 1) with
    | Keyword (Public | Internal | Type | Trait | Impl | Capability | Test | Theorem), _ -> true
    | Keyword Fn, (Lower _ | Upper _) -> true
    | Lower "tuple", Keyword Type -> true
    | Keyword Proof, Upper _ -> true
    | Keyword Let, Upper _ -> (
        match read_kind 2 with Punctuation (Dot | Open Square) -> true | _ -> false)
    | _ -> false

  let parse tokens =
    let pieces =
      List.map
        (fun (piece : Parser.For_testing.piece) ->
          let kind, diagnostics =
            if Parser.For_testing.is_use tokens piece then
              (Use, snd (Parser.For_testing.parse_use_line tokens piece))
            else if starts_definition tokens piece then
              match Parser.For_testing.parse_example_definition tokens piece with
              | Example_definition, diagnostics -> (Definition, diagnostics)
              | Example_signature, diagnostics -> (Signature, diagnostics)
            else (Statement, Parser.For_testing.parse_example_statement tokens piece)
          in
          ({ kind; first = piece.first; stop = piece.stop }, diagnostics))
        (Parser.For_testing.split tokens)
    in
    (List.map fst pieces, List.concat_map snd pieces)

  let select_entry = function
    | Use -> Truss.snippet_use
    | Definition -> Truss.snippet_definition
    | Signature -> Truss.snippet_signature
    | Statement -> Truss.snippet_statement
end
