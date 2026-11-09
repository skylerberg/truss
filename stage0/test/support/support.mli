(** Setting up a workspace with the real standard library, for the type checker's tests, and
    asserting one diagnostic with its fix. *)

val module_of : string -> Path.module_
(** ["app::main"] is the module [main] of the package [app]. *)

val setup : (string * string) list -> Query.database
(** A database with the standard library and the given modules, each a module path and its text.
    Each package's manifest grants nothing and lists no dependencies. *)

val parse_errors : Query.database -> Path.module_ -> string list
val codes : Diagnostic.t list -> string list

val no_diagnostics :
  check:(Query.database -> Path.module_ -> Diagnostic.t list) -> (string * string) list -> unit
(** Fails the running test if any given module has a diagnostic, or does not parse. *)

val one_diagnostic :
  check:(Query.database -> Path.module_ -> Diagnostic.t list) ->
  ?others:(string * string) list ->
  ?fixed:string ->
  string ->
  string ->
  unit
(** [one_diagnostic ~check text code]: [app::main], with [text], has exactly one diagnostic, with
    [code]. With [~fixed], its first fix gives that text, which then has no diagnostic. *)
