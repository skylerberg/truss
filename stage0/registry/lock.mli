(** A lock file, [truss.lock]: the version and content of each registry package a project's packages
    use, as SYNTAX.md's "The lock file" writes it. A published package's lock file is the record of
    what it was published with, and has no [holds]. *)

type entry = {
  name : string;
  version : Version.t;
  hash : string;  (** Of the package's files, as {!Content.hash} gives it *)
  holds : string list;  (** The capabilities its users in the build grant it, as grants name them *)
}

type t = entry list
(** In order of name. *)

exception Malformed of int * string
(** The line, counting from 1, and what is wrong there, as whole sentences. *)

val parse : string -> t
(** Raises {!Malformed}. A text with nothing in it is a lock file with no package. *)

val print : t -> string
(** The one way a lock file is written, which {!parse} reads back as the same entries. *)

val find : t -> string -> entry option
