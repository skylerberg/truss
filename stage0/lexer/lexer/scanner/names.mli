type kind = Upper | Lower

type checked = {
  kind : kind;
  name : string;
  problem : (Diagnostic.Code.lexer * string) option;
  fix : string option;
}

val check : string -> checked
