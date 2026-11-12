module Names = Resolve.Names

type what = Definition of Path.t | Module of Path.module_

type plan = {
  edits : (Path.module_ * Diagnostic.span Diagnostic.edit list) list;
  moved : (Path.module_ * Path.module_) option;
}

val run : directory:string -> from_:string -> to_:string -> json:bool -> int
