val module_of : string -> Path.module_
val file_of : string -> Path.file
val top_key : string -> string -> Resolve.Names.key
val setup : ?dependencies:(string * string) list -> (string * string) list -> Query.context
val parse_errors : Query.context -> Path.file -> string list
val codes : Diagnostic.t list -> string list

type core_nodes = {
  expressions : Core.expression list;
  statements : Core.statement list;
  patterns : Core.pattern list;
}

val core_nodes : Query.context -> Resolve.Names.key -> core_nodes
val first_core_nodes : string -> core_nodes

val no_diagnostics :
  check:(Query.context -> Path.file -> Diagnostic.t list) -> (string * string) list -> unit

val one_diagnostic :
  check:(Query.context -> Path.file -> Diagnostic.t list) ->
  ?setup:((string * string) list -> Query.context) ->
  ?file:string ->
  ?others:(string * string) list ->
  ?fixed:string ->
  ?says:string ->
  string ->
  string ->
  unit

val solver : Solver.t Lazy.t
val record : Query.context -> (string * Prover.oracle_response) list -> unit
