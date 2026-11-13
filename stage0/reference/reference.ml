open Token

type entry = (Lexing.lexbuf -> Truss.token) -> Lexing.lexbuf -> unit

(* The token Menhir's grammar reads for each of the lexer's. Reserved
   words and foreign sequences have none. *)
let token (kind : Token.kind) : Truss.token option =
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
        | Unreachable -> UNREACHABLE
        | Use -> USE
        | Uses -> USES
        | Var -> VAR
        | While -> WHILE
        | With -> WITH
        | Yield -> YIELD
        | Yields -> YIELDS)
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
        | Colon_colon -> COLONCOLON
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

let accepts entry (tokens : Token.t list) =
  let converted = List.filter_map (fun (written : Token.t) -> token written.kind) tokens in
  if List.compare_lengths converted tokens <> 0 then false
  else
    let remaining = ref converted in
    let next _ =
      match !remaining with
      | token :: rest ->
          remaining := rest;
          token
      | [] -> Truss.EOF
    in
    match entry next (Lexing.from_string "") with () -> true | exception Truss.Error -> false

let file = Truss.file

module Snippet = struct
  type kind = Use | Definition | Signature | Statement
  type item = { kind : kind; first : int; stop : int }

  (* Whether a piece starts like a definition rather than a statement. A
     [let] starts a constant only before a name under a type, as in
     [let UInt8.maximum]; otherwise it starts a statement. *)
  let starts_definition (tokens : Token.t array) (piece : Parser.piece) =
    let kind offset =
      if piece.first + offset < piece.stop then tokens.(piece.first + offset).kind else End_of_file
    in
    match (kind 0, kind 1) with
    | Keyword (Public | Internal | Type | Trait | Impl | Capability | Test | Theorem), _ -> true
    | Keyword Fn, (Lower _ | Upper _) -> true
    | Keyword Proof, Upper _ -> true
    | Keyword Let, Upper _ -> (
        match kind 2 with Punctuation (Dot | Open Square) -> true | _ -> false)
    | _ -> false

  let parse source tokens =
    let pieces =
      List.map
        (fun (piece : Parser.piece) ->
          let kind, diagnostics =
            if Parser.is_use tokens piece then
              let parsed = Parser.use_line source tokens piece in
              (Use, Parser.diagnostics_in_file parsed)
            else if starts_definition tokens piece then
              match Parser.example_definition source tokens piece with
              | Example_definition, diagnostics -> (Definition, diagnostics)
              | Example_signature, diagnostics -> (Signature, diagnostics)
            else (Statement, Parser.example_statement source tokens piece)
          in
          ({ kind; first = piece.first; stop = piece.stop }, diagnostics))
        (Parser.split tokens)
    in
    (List.map fst pieces, List.concat_map snd pieces)

  let entry = function
    | Use -> Truss.snippet_use
    | Definition -> Truss.snippet_definition
    | Signature -> Truss.snippet_signature
    | Statement -> Truss.snippet_statement
end
