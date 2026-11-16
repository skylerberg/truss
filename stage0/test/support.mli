val module_of : string -> Path.module_
val top : string -> string -> Path.t
val file_of : string -> Path.file
val setup : ?dependencies:(string * string) list -> (string * string) list -> Project.package list

val with_dependencies :
  Project.package list -> Path.package -> Manifest.dependency list -> Project.package list

val source : Project.package list -> Path.file -> Source.t
val parse_errors : Project.package list -> Path.file -> string list
val database : Project.package list -> Database.t
val names : Project.package list -> Path.package -> Resolve.Names.lookups
val declarations : Project.package list -> Path.module_ -> Resolve.Names.declaration list
val diagnostics : Database.t -> Path.file -> Diagnostic.t list
val codes : Diagnostic.t list -> string list

type core_nodes = {
  expressions : Core.expression list;
  statements : Core.statement list;
  patterns : Core.pattern list;
}

val core_nodes : Project.package list -> Resolve.Names.key -> core_nodes
val first_core_nodes : string -> core_nodes

val no_diagnostics :
  check:(Project.package list -> Path.file -> Diagnostic.t list) -> (string * string) list -> unit

val one_diagnostic :
  check:(Project.package list -> Path.file -> Diagnostic.t list) ->
  ?setup:((string * string) list -> Project.package list) ->
  ?file:string ->
  ?others:(string * string) list ->
  ?fixed:string ->
  ?says:string ->
  string ->
  string ->
  unit

val proven : Database.t -> Path.file -> Database.proofs
val proof_diagnostics : Database.t -> Path.file -> Diagnostic.t list
val proof_states : Database.t -> Path.file -> Source.span Prover.state list
val proofs : Database.t -> Path.file -> Resolve.Names.key -> Prover.proof
