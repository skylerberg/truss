type t
type state

val create : ?loaded:state list -> Project.package list -> t
val state : t -> Path.package -> state
val check : t -> Path.package list -> unit
val file_diagnostics : t -> Path.file -> Diagnostic.t list
val manifest_problems : t -> Path.package -> Package_checks.manifest_problem list
val code_packages : t -> Path.package -> Path.package list option
val tables : t -> Resolve.Names.key -> Infer.tables option
val parsed : t -> Path.file -> Parsed.file
val names : t -> Path.package list -> Resolve.Names.lookups
val resolved : t -> Resolve.Names.key -> Resolve.resolved option
val interface_lookups : t -> Path.package list -> Interface.Lookups.t
val lowering_lookups : t -> Path.package list -> Compile.Lookups.t

type 'a part = Value of 'a | Failed of Syntax.diagnostic list | Blocked
type proofs

val prove : t -> Path.file list -> proofs
val proof : proofs -> Resolve.Names.key -> Prover.proof part option
val holes : proofs -> Path.t -> (Path.file * int) list

type verdicts

val decide : ?evaluator:Prover.evaluator -> Solver.t -> proofs -> verdicts
val states : verdicts -> Path.file -> Diagnostic.span Prover.state list
val diagnostics : verdicts -> Path.file -> Diagnostic.t list

module For_testing : sig
  type stage = Resolve | Interface | Infer | Patterns | Usage | Ownership | Package_checks

  val diagnostics : stage list -> t -> Path.file -> Diagnostic.t list
  val checked_body : t -> Resolve.Names.key -> Infer.checked option
  val derived : t -> Path.t -> Core.t option
  val core_of_path : t -> Path.t -> (Core.t * Types.substitution) option
  val proof_lookups : t -> Prover.Lookups.t
  val mir : t -> Path.package -> Mir.lookups
  val ownership : t -> Resolve.Names.key -> (Core.origin * Core.origin) list part
end
