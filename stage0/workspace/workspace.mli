(** The inputs of a build, and the queries that parse them. See TYPECHECKER.md, "One definition at a
    time, through queries".

    The driver sets each package, with its manifest and the modules it has, and the text of each
    module's file. Everything else is a query, so changing one file re-parses that file alone, and a
    definition whose tree comes out the same, as one that only moved does, changes nothing that
    reads it. *)

type dependency = { package : string; capabilities : string list }
(** A dependency from the manifest, with the capabilities it is granted. *)

type package = { name : string; dependencies : dependency list; modules : Path.module_ list }

val packages : (string, package) Query.input
val file_text : (Path.module_, string) Query.input

val file_path : Path.module_ -> string
(** [weather/forecast/hourly.truss], as in diagnostics. *)

type file = {
  source : Source.t;
  tokens : Token.t array;
  uses : Syntax.path Syntax.item list;
  definitions : Syntax.definition Syntax.item list;
  diagnostics : Diagnostic.t list;  (** The lexer's and the parser's, in the file's offsets. *)
}

val file : (Path.module_, file) Query.query
(** A module's file, lexed and parsed. Raises [Not_found] if the module has no text. *)

val package : Query.database -> string -> package option
(** A package, or [None] if there is no such package. *)

val module_exists : (Path.module_, bool) Query.query
(** Whether a package has the module, which a [use] line or a full path asks. *)
