val key : (Path.t, Resolve.Names.key option) Query.query
val definition : Query.context -> Path.t -> (Resolve.Names.key * Syntax.definition) option

type generic_kind = Type_kind | Value_kind | Capability_kind

val generics_of : (Path.t, (string * generic_kind) list option) Query.query

type trait_header = {
  associated : string list;
  capabilities : string list;
  required : Path.t list;
  laws : string list;
}

val trait_header : (Path.t, trait_header option) Query.query
val trait_closure : Query.context -> ?seen:Path.t list -> Path.t -> Path.t list
val kind_of : Query.context -> Path.t -> Resolve.Names.named option
