type container = In_trait | In_impl | In_capability

val parse_method : Cursor.t -> container:container -> Syntax.definition
val parse_definition : Cursor.t -> Syntax.definition * Split.piece list

type example =
  | Whole of Syntax.definition * Split.piece list
  | Signature_alone of Syntax.visibility * Syntax.signature

val parse_example : Cursor.t -> example
