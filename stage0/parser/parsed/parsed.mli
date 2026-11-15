type file = {
  uses : Syntax.path Syntax.item list;
  definitions : Syntax.definition Syntax.item list;
  diagnostics : Diagnostic.t list;
}

val parse : Source.t -> file
