(** Reading a package's [truss.toml]: the subset of TOML a manifest uses. See SYNTAX.md, "Package
    manifest". *)

type t = {
  name : string;
  dependencies : Workspace.dependency list;
  usize_bits : int;  (** 64 when [[package]] says [usize_bits = 64], and 32 otherwise *)
  time_limit : int;  (** Each test's, in seconds: [[test]]'s [time_limit], or 10 *)
}

val default_time_limit : int

exception Malformed of int * string
(** The line, counting from 1, and what was expected there. *)

val parse : string -> t
(** Raises {!Malformed}. Comments, sections other than [[package]], [[dependencies]], and [[test]],
    keys of [[package]] other than [name] and [usize_bits], such as [version], keys of a dependency
    other than [capabilities], and keys of [[test]] other than [time_limit] are read past. *)
