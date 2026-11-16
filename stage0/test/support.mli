val parse_module : string -> Path.module_
val make_top_path : string -> string -> Path.t
val parse_file : string -> Path.file
val locate_occurrence : sub:string -> occurrence:int -> string -> int
val setup : ?dependencies:(string * string) list -> (string * string) list -> Project.package list

val with_dependencies :
  Project.package list -> Path.package -> Manifest.dependency list -> Project.package list

val read_source : Project.package list -> Path.file -> Source.t
val parse_errors : Project.package list -> Path.file -> string list
val make_database : Project.package list -> Database.t
val make_names : Project.package list -> Path.package -> Resolve.Names.lookups
val list_declarations : Project.package list -> Path.module_ -> Resolve.Names.declaration list
val list_diagnostics : Database.t -> Path.file -> Diagnostic.t list
val list_codes : Diagnostic.t list -> string list

type core_nodes = {
  expressions : Core.expression list;
  statements : Core.statement list;
  patterns : Core.pattern list;
}

val collect_core_nodes : Project.package list -> Resolve.Names.key -> core_nodes
val collect_first_core_nodes : string -> core_nodes

val expect_no_diagnostics :
  check:(Project.package list -> Path.file -> Diagnostic.t list) -> (string * string) list -> unit

val expect_one_diagnostic :
  check:(Project.package list -> Path.file -> Diagnostic.t list) ->
  ?setup:((string * string) list -> Project.package list) ->
  ?file:string ->
  ?others:(string * string) list ->
  ?fixed:string ->
  ?says:string ->
  ?at:string * int ->
  string ->
  string ->
  unit

val prove : Database.t -> Path.file -> Database.proofs
val list_proof_diagnostics : Database.t -> Path.file -> Diagnostic.t list
val list_proof_states : Database.t -> Path.file -> Source.span Prover.state list
val read_proofs : Database.t -> Path.file -> Resolve.Names.key -> Prover.proof
