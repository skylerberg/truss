(** The inputs of a build, and the queries that parse them.

    The driver sets each package, with its manifest and the modules it has, and the text of each
    module's file. Everything else is a query, so changing one file re-parses that file alone, and a
    definition whose tree comes out the same, as one that only moved does, changes nothing that
    reads it. *)

type dependency = Manifest.dependency = { package : string; capabilities : string list }
(** A dependency from the manifest, with the capabilities it is granted. *)

type package = Project.package = {
  name : string;
  dependencies : dependency list;
  modules : Path.module_ list;
  usize_bits : int;
      (** 64 when the manifest says the package runs only on 64-bit targets, and 32 otherwise, so
          that its code holds for both widths of [USize]. *)
}

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

val package : Query.context -> string -> package option
(** A package, or [None] if there is no such package. Reading it reads the whole of what the
    manifest says, so a result that needs one thing of it asks for that thing below. *)

val modules : (string, Path.module_ list) Query.query
(** A package's modules, and none for a package there is not. *)

val dependencies : (string, dependency list) Query.query
(** A package's dependencies, each with what it is granted. *)

val usize_bits : (string, int) Query.query
(** The width of [USize] a package's code must hold for. *)

val exists : (string, bool) Query.query
(** Whether there is a package of that name. *)

val split_path : Query.context -> string list -> (string * string list) option
(** The package that the names of a full path start with, which is two of them when it has an owner,
    and the names after it; [None] when they start with no package's name. *)

val module_exists : (Path.module_, bool) Query.query
(** Whether a package has the module, which a [use] line or a full path asks. *)
