(** Setting up a workspace with the real standard library, for the type checker's tests, and
    asserting one diagnostic with its fix. *)

val module_of : string -> Path.module_
(** ["app::main"] is the module [main] of the package [app]. *)

val file_of : string -> Path.file
(** ["app::shapes/circle"] is the file [circle] of the module [app::shapes], and ["app::shapes"] is
    the file named after its module, [shapes], or [main] in a package's root module. *)

val top_key : string -> string -> Resolve.Names.key
(** The key of a top-level definition, by its module and name: [top_key "app::main" "caller"]. *)

val setup : ?dependencies:(string * string) list -> (string * string) list -> Query.context
(** A database with the standard library and the given files, each named as {!file_of} reads it,
    with its text. Each pair of [dependencies], such as [("app", "lib")], makes the first package
    depend on the second; each manifest grants nothing. The standard library is a fixed base that
    every test shares, so it is checked once per run. *)

val standard : Engine.t Lazy.t
(** That base. *)

val parse_errors : Query.context -> Path.file -> string list
val codes : Diagnostic.t list -> string list

val check_core_invariants : Query.context -> Resolve.Names.key -> Core.t -> unit
(** Fails the running test if a definition's core form breaks an invariant of the core form: node
    ids are unique, every type is fully inferred, no generic parameter of a callee appears, every
    [Lent] place is a call of a lending method, and every argument fits its parameter's mode. *)

val check_file_core_invariants : Query.context -> Path.file -> int
(** Runs {!check_core_invariants} on every definition of a file that has a core form. Returns the
    number of such definitions. *)

type core_nodes = {
  expressions : Core.expression list;
  statements : Core.statement list;
  patterns : Core.pattern list;
}

val core_nodes : Query.context -> Resolve.Names.key -> core_nodes
(** Every node of a definition's core form, at any depth. Raises [Failure] if the definition has no
    core form. *)

val first_core_nodes : string -> core_nodes
(** {!core_nodes} of the first definition of [app::main], with the given text. *)

val no_diagnostics :
  check:(Query.context -> Path.file -> Diagnostic.t list) -> (string * string) list -> unit
(** Fails the running test if a given module does not parse, has a diagnostic, or has a definition
    whose core form fails {!check_core_invariants}. *)

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
(** [one_diagnostic ~check text code]: [file], [app::main] unless given, with [text], has exactly
    one diagnostic, with [code]. With [~fixed], its first fix gives that text, which then has no
    diagnostic. With [~says], its message contains that text. [setup] makes the database, {!setup}
    by default. *)

val solver : Solver.t Lazy.t
(** The solver, without a cache. Without a solver the tests cannot run, so the executable exits. *)

val record : Query.context -> (string * Prover.oracle_response) list -> unit
(** Records the oracles' responses in the context's engine, as the database does for a session. *)
