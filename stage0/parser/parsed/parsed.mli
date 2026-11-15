type file = {
  uses : Syntax.path Syntax.item list;
  definitions : Syntax.definition Syntax.item list;
  diagnostics : Diagnostic.t list;
  text : string;
}

val parse : Source.t -> file
