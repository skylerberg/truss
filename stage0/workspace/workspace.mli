(** The inputs of a build, and the queries that parse them.

    The driver sets each package, with its manifest and its files, and the text of each file. A
    module is a directory of a package, and its files share one namespace. Everything else is a
    query, so changing one file re-parses that file alone, and a definition whose tree comes out the
    same, as one that only moved does, changes nothing that reads it. *)

type file = {
  source : Source.t;
  tokens : Token.t array;
  uses : Syntax.path Syntax.item list;
  definitions : Syntax.definition Syntax.item list;
  diagnostics : Diagnostic.t list;  (** The lexer's and the parser's, in the file's offsets. *)
}

val file : (Path.file, file) Query.query
(** A file, lexed and parsed. Raises [Not_found] if it has no text. *)

val modules : (Path.package, Path.module_ list) Query.query
(** A package's modules, and none for a package there is not. *)

val files : (Path.module_, Path.file list) Query.query
(** A module's files, in order. *)

val dependencies : (Path.package, Manifest.dependency list) Query.query
(** A package's dependencies, each with its grants. *)

val usize_bits : (Path.package, int) Query.query
(** The width of [USize] a package's code must hold for. *)

val exists : (Path.package, bool) Query.query
(** Whether there is a package of that name. *)

val split_module : Query.context -> string list -> Path.module_ option
(** The module that the names of a full path start with, whose package is two of them when it has an
    owner; [None] when they start with no package's name. *)

val module_exists : (Path.module_, bool) Query.query
(** Whether a package has the module, which a [use] line or a full path asks. *)
