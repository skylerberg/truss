module Part = Part

type t
type package_database

val create : ?loaded:package_database list -> ?checks:bool -> Project.package list -> t
val copy : t -> t
val read_package_database : t -> Path.package -> package_database
val list_package_diagnostics : package_database -> (Source.t * Diagnostic.t list) list
val update : t -> (Path.file * string option) list -> unit
val relayout : t -> loaded:package_database list -> Project.package list -> unit
val propagate : ?on_bug:(Compiler_bug.t -> unit) -> t -> unit
val list_unsaved : t -> (string * string option) list
val mark_saved : t -> unit

val restore :
  loaded:package_database list ->
  find_text:(Path.file -> string option) ->
  (string * string) list ->
  t

val check : t -> Path.package list -> unit
val list_file_diagnostics : t -> Path.file -> Diagnostic.t list
val list_dependency_diagnostics : t -> Path.package -> (Source.t * Diagnostic.t list) list

type manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
  | Unused_dependency of Path.package

val list_manifest_problems : t -> Path.package -> manifest_problem list
val find_code_packages : t -> Path.package -> Path.package list option
val read_checked_body : t -> Resolve.Names.key -> Infer.checked option
val read_parsed : t -> Path.file -> Syntax.file
val make_name_lookups : t -> Path.package list -> Resolve.Names.lookups
val read_resolved : t -> Resolve.Names.key -> Resolve.resolved option
val make_interface_lookups : t -> Path.package list -> Interface.Lookups.t
val make_lowering_requests : t -> Path.package list -> Backend.requests
val find_main : t -> Path.package -> Path.t option

type read = { dependent : Part.t; dependency : Part.t }

val list_dependencies : t -> Path.t list -> read list
val list_dependents : t -> Path.t list -> read list
val list_changes : t -> t -> Part.t list

type 'a part = Value of 'a | Failed of Diagnostic.in_definition list | Blocked
type proofs

val prove : t -> Path.file list -> proofs
val list_holes : proofs -> Path.t -> (Path.file * int) list
val list_template_checks : proofs -> Prover.State.template_check list
val list_proofs : proofs -> (Resolve.Names.key * Prover.proof) list
val make_proof_lookups : t -> Prover.Lookups.t

type counts = {
  kind : string;
  computed : int;
  unchanged : int;
  writes : int;
  reads : int;
  distinct_reads : int;
}

val count : (unit -> 'a) -> 'a * counts list

module For_testing : sig
  type checker = Resolve | Interface | Infer | Patterns | Usage | Ownership | Package_checks

  val list_diagnostics : checker list -> t -> Path.file -> Diagnostic.t list
  val read_derived_form : t -> Path.t -> Core.t option
  val read_core : t -> Path.t -> (Core.t * Types.substitution) option
  val make_mir_lookups : t -> Path.package -> Mir.lookups
  val read_ownership : t -> Resolve.Names.key -> (Core.origin list * Core.origin list) list part
  val find_proof : proofs -> Resolve.Names.key -> Prover.proof part option
  val list_reads : t -> string -> string list
  val list_unread_parts : t -> Path.package list -> Part.any list
  val list_differences : t -> t -> string list

  type observed = { recomputed : string list; collected : string list }

  val observe : (unit -> unit) -> observed
  val add_root : t -> Instance.key -> unit
end
