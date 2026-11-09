(* The reference parser: GRAMMAR.md's grammar, built by Menhir from
   grammar/truss.mly, which the tests and the fuzzer check the hand-written
   parser against. See PARSER.md, "Testing". It is built only for them. *)

open Token

(* The token Menhir's grammar reads for each of the lexer's. A string is one
   token, so the grammar does not see interpolations, which are ordinary
   expressions. Reserved words and foreign sequences have none: no grammar
   rule accepts them. *)
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

(* Whether the reference grammar accepts [tokens] from [entry]. *)
let accepts entry (tokens : Token.t list) =
  match List.map (fun (written : Token.t) -> token written.kind) tokens with
  | converted when List.mem None converted -> false
  | converted -> (
      let remaining = ref (List.map Option.get converted) in
      let next _ =
        match !remaining with
        | token :: rest ->
            remaining := rest;
            token
        | [] -> Truss.EOF
      in
      match entry next (Lexing.from_string "") with () -> true | exception Truss.Error -> false)

let entry : Parser.Snippet.kind -> _ = function
  | Use -> Truss.snippet_use
  | Definition -> Truss.snippet_definition
  | Signature -> Truss.snippet_signature
  | Statement -> Truss.snippet_statement

let file = Truss.file
