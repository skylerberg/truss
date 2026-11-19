type t

val build :
  Names.lookups ->
  Path.package ->
  (Path.module_ * (Path.file * Syntax.file * string) list) list ->
  t

val empty : t

type change =
  | Entry of Path.module_ * string
  | Entries of Path.module_
  | Imports of Names.key
  | Declaration of Names.key
  | Tree of Names.key
  | Positions of Names.key
  | Text of Names.key
  | Place of Names.key
  | Container of Names.key
  | Contained of Names.key
  | Module_declarations of Path.module_
  | File_declarations of Path.file
  | Package_declarations
  | Members of Path.t * string
  | Traits_declaring of string
  | Impl_index
  | Impls_of_type of Path.t
  | Impls_of_trait of Path.t
  | Law_proofs of Names.law_proof_name

val list_changes : t -> t -> change list

val make_lookups :
  read_namespace:(Path.package -> t) ->
  split_module:(string list -> Path.module_ option) ->
  list_dependency_names:(Path.package -> Path.package list) ->
  Names.lookups
