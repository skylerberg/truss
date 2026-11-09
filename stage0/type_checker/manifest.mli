(** Reading a package's [truss.toml]: the subset of TOML a manifest uses. See SYNTAX.md, "Package
    manifest". *)

type t = { name : string; dependencies : Workspace.dependency list }

exception Malformed of int * string
(** The line, counting from 1, and what was expected there. *)

val parse : string -> t
(** Raises {!Malformed}. Keys of [[package]] other than [name], such as [version], and keys of a
    dependency other than [capabilities] are read past. *)
