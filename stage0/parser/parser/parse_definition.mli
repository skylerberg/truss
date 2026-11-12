type written_visibility = {
  visibility : Syntax.visibility;
  tokens : Token.t list;
  modifier : (Token.t * Token.t) option;
}

type container = In_trait | In_impl | In_capability

val method_ : Cursor.t -> container:container -> visibility:Syntax.visibility -> Syntax.definition
val header : Cursor.t -> Token.keyword option * Syntax.definition_name option

type empty = |

val definition : Cursor.t -> Syntax.definition

type example =
  | Whole of Syntax.definition
  | Signature_alone of Syntax.visibility * Syntax.signature

val example : Cursor.t -> example
