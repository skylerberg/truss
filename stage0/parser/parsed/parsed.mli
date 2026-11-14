(** Each file of a build, lexed and parsed, as a query. Changing one file parses that file alone,
    and a definition whose tree comes out the same, as one that only moved does, changes nothing
    that reads it. *)

type file = {
  uses : Syntax.path Syntax.item list;
  definitions : Syntax.definition Syntax.item list;
  diagnostics : Diagnostic.t list;  (** The lexer's and the parser's, in the file's offsets. *)
}

val file : (Path.file, file) Query.query
(** A file's [use] lines and definitions. Raises [Not_found] if it has no text. *)
