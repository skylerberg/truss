type container = In_trait | In_impl | In_capability

val method_ : Cursor.t -> container:container -> visibility:Syntax.visibility -> Syntax.definition
val definition : Cursor.t -> Syntax.definition

type example =
  | Whole of Syntax.definition
  | Signature_alone of Syntax.visibility * Syntax.signature

val example : Cursor.t -> example
