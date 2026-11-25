type kind = Upper | Lower

type checked = {
  kind : kind;
  name : string;
  problem : Syntax_catalog.Lexing.name_problem option;
  fix : string option;
}

val check : string -> checked
