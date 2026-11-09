(** Reading a package's [truss.toml]: the subset of TOML a manifest uses. See SYNTAX.md, "Package
    manifest". *)

type t = { name : string; dependencies : Workspace.dependency list; usize_bits : int }
(** [usize_bits] is 64 when [[package]] says [usize_bits = 64], and 32 otherwise. *)

exception Malformed of int * string
(** The line, counting from 1, and what was expected there. *)

val parse : string -> t
(** Raises {!Malformed}. Comments, sections other than [[package]] and [[dependencies]], keys of
    [[package]] other than [name] and [usize_bits], such as [version], and keys of a dependency
    other than [capabilities] are read past. *)
