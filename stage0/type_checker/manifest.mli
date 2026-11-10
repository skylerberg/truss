(** Reading a manifest, [truss.toml], in the part of TOML a manifest is written in. *)

type t = {
  name : string;  (** One name, or an owner and a name joined by [::] *)
  truss : string option;  (** The version of Truss the package is written for *)
  dependencies : Workspace.dependency list;
      (** Each dependency's name and the capabilities it is granted *)
  usize_bits : int;  (** 64 when [[package]] says [usize_bits = 64], and 32 otherwise *)
  time_limit : int;  (** Each test's, in seconds: [[test]]'s [time_limit], or 10 *)
  project : bool;  (** Whether the manifest has a [[project]] table *)
}

val default_time_limit : int

exception Malformed of int * string
(** The line, counting from 1, and what is wrong there, as whole sentences. *)

val parse : string -> t
(** Raises {!Malformed}. A manifest is read strictly: a table or a key it does not have is
    malformed, and so is what a manifest of another language would hold, such as a version. *)

val valid_name : string -> bool
(** Whether a text is a package's name: a [lower_snake_case] name, or two joined by [::]. *)

val name_parts : string -> string list option
(** A package's name as its parts, an owner and a name or a name alone. *)
