module Part = Part

type t
type state

val create : ?loaded:state list -> ?checks:bool -> Project.package list -> t
val copy : t -> t
val state : t -> Path.package -> state
val update : t -> (Path.file * string option) list -> unit
val relayout : t -> loaded:state list -> Project.package list -> unit
val propagate : ?on_bug:(Compiler_bug.t -> unit) -> t -> unit
val unsaved : t -> (string * string option) list
val mark_saved : t -> unit
val restore : loaded:state list -> texts:(Path.file -> string option) -> (string * string) list -> t
val check : t -> Path.package list -> unit
val file_diagnostics : t -> Path.file -> Diagnostic.t list
val manifest_problems : t -> Path.package -> Package_checks.manifest_problem list
val code_packages : t -> Path.package -> Path.package list option
val read_checked_body : t -> Resolve.Names.key -> Infer.checked option
val parsed : t -> Path.file -> Parsed.t
val names : t -> Path.package list -> Resolve.Names.lookups
val resolved : t -> Resolve.Names.key -> Resolve.resolved option
val interface_lookups : t -> Path.package list -> Interface.Lookups.t
val lowering_requests : t -> Path.package list -> Compile.requests
val main : t -> Path.package -> Path.t option
val callers : t -> viewer:Path.package -> Path.t -> Path.t list

type read = { dependent : Part.t; dependency : Part.t }

val dependencies : t -> Path.t list -> read list
val dependents : t -> Path.t list -> read list
val changes : t -> t -> Part.t list

type 'a part = Value of 'a | Failed of Diagnostic.in_definition list | Blocked
type proofs

val prove : t -> Path.file list -> proofs
val holes : proofs -> Path.t -> (Path.file * int) list
val template_checks : proofs -> Prover.State.template_check list

val run_template_checks :
  Compile.t ->
  Prover.State.template_check list ->
  (Prover.State.template_check * (bool list, string) result) list

type verdicts

val decide :
  runs:(Prover.State.template_check * (bool list, string) result) list ->
  Solver.t ->
  proofs ->
  verdicts

val states : verdicts -> Path.file -> Source.span Prover.state list
val diagnostics : verdicts -> Path.file -> Diagnostic.t list

module For_testing : sig
  type stage = Resolve | Interface | Infer | Patterns | Usage | Ownership | Package_checks

  val diagnostics : stage list -> t -> Path.file -> Diagnostic.t list
  val derived : t -> Path.t -> Core.t option
  val core_of_path : t -> Path.t -> (Core.t * Types.substitution) option
  val proof_lookups : t -> Prover.Lookups.t
  val mir : t -> Path.package -> Mir.lookups
  val ownership : t -> Resolve.Names.key -> (Core.origin * Core.origin) list part
  val proof : proofs -> Resolve.Names.key -> Prover.proof part option
  val reads : t -> string -> string list
  val differences : t -> t -> string list

  type observed = { recomputed : string list; collected : string list }

  val observe : t -> (unit -> unit) -> observed
  val root : t -> Instance.key -> unit
end
