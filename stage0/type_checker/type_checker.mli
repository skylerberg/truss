(** The type checker's entry point: loading a build's packages and gathering every stage's
    diagnostics. See TYPECHECKER.md, "Structure". *)

module Manifest = Manifest

val diagnostics : Query.database -> Path.module_ -> Diagnostic.t list
(** Every diagnostic of a file, from the lexer to the package checks, in its offsets and in order.
*)

val load_package :
  Query.database ->
  name:string ->
  dependencies:Workspace.dependency list ->
  (Path.module_ * string) list ->
  unit
(** Sets a package's modules, with their text, and its manifest as inputs. *)

val load_standard : Query.database -> unit
(** Sets the [standard] package, built into the compiler. *)
