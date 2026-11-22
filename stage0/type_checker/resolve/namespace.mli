type declared_definition = {
  declaration : Names.declaration;
  file : Path.file;
  position : int;
  container : Names.key option;
  item : Syntax.definition Syntax.item;
}

type module_declarations = {
  definitions : declared_definition list;
  imports : (Path.file * (string * Path.module_) list) list;
  impls : ((Path.t * Path.t) * Path.t) list;
  law_proofs : (Names.law_proof_name * Names.key) list;
}

val builtin_entries : Names.entry list
val list_entries : Syntax.file -> Names.entry list
val declare : Names.lookups -> (Path.file * Syntax.file * string) list -> module_declarations
val compare_key : Names.key -> Names.key -> int
