(** Setting up a workspace with the real standard library, for the type checker's tests, and
    asserting one diagnostic with its fix. *)

val module_of : string -> Path.module_
(** ["app::main"] is the module [main] of the package [app]. *)

val setup : (string * string) list -> Query.context
(** A database with the standard library and the given modules, each a module path and its text.
    Each package's manifest grants nothing and lists no dependencies. The standard library is a
    fixed base that every test shares. *)

val standard : Engine.t Lazy.t
(** That base. *)

val parse_errors : Query.context -> Path.module_ -> string list
val codes : Diagnostic.t list -> string list

val form_holds : Query.context -> Resolve.Names.key -> Core.t -> unit
(** Fails the running test if a definition's core form breaks what every core form promises its
    readers: an id of its own for each node, every type decided, no generic parameter of another
    definition, places that are what they say, and arguments that fit their parameters' modes. *)

val forms_hold : Query.context -> Path.module_ -> int
(** {!form_holds} for every definition of a module that has a core form, and how many do. *)

val no_diagnostics :
  check:(Query.context -> Path.module_ -> Diagnostic.t list) -> (string * string) list -> unit
(** Fails the running test if any given module has a diagnostic, or does not parse, or has a
    definition whose core form does not hold to what {!form_holds} checks. *)

val one_diagnostic :
  check:(Query.context -> Path.module_ -> Diagnostic.t list) ->
  ?others:(string * string) list ->
  ?fixed:string ->
  string ->
  string ->
  unit
(** [one_diagnostic ~check text code]: [app::main], with [text], has exactly one diagnostic, with
    [code]. With [~fixed], its first fix gives that text, which then has no diagnostic. *)
