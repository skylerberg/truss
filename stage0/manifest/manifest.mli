(** Reading a manifest, [truss.toml], in the part of TOML a manifest is written in. *)

type dependency = { package : string; capabilities : string list }
(** A dependency, with the capabilities it is granted. *)

type package = {
  name : string;  (** One name, or an owner and a name joined by [::] *)
  truss : string option;  (** The version of Truss the package is written for *)
  dependencies : dependency list;  (** Each dependency's name and the capabilities it is granted *)
  usize_bits : int;  (** 64 when [[package]] says [usize_bits = 64], and 32 otherwise *)
}

type t = {
  package : package option;  (** What [[package]] and [[dependencies]] say, if there is one *)
  project : bool;  (** Whether the manifest has a [[project]] table *)
  time_limit : int option;  (** [[test]]'s [time_limit], in seconds, if it is written *)
}
(** A manifest has a package, a project, or both. *)

val default_time_limit : int

exception Malformed of int * string
(** The line, counting from 1, and what is wrong there, as whole sentences. *)

val parse : string -> t
(** Raises {!Malformed}. A manifest is read strictly: a table or a key it does not have is
    malformed, and so is what a manifest of another language would hold, such as a version. *)

val has_project_table : string -> bool
(** Whether a manifest's text has a [[project]] table, whatever else is in it. *)

val with_dependency : string -> string -> string
(** A manifest's text with an entry for a dependency that grants it nothing, after its other
    entries, and the same text if it has one. Raises {!Malformed}. *)

val without_dependency : string -> string -> string
(** A manifest's text without the entry of a dependency, by its name, and the same text if it has
    none. Raises {!Malformed}. *)

val valid_name : string -> bool
(** Whether a text is a package's name: a [lower_snake_case] name, or two joined by [::]. *)

val name_parts : string -> string list option
(** A package's name as its parts, an owner and a name or a name alone. *)

val truss_version : string
(** The version of Truss this toolchain is. *)

val toolchain_builds : string -> bool
(** Whether this toolchain builds a package written for a version of Truss: one no newer than its
    own. *)
