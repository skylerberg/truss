val add_requires : State.frame -> Catalog.Prover.required list -> Catalog.Prover.fix list
val find_goal_code : State.frame -> Logic.term -> Catalog.Code.t option
val make_uses_fix : State.environment -> Types.capability -> Catalog.Prover.fix list
val find_parameter_code : State.frame -> Logic.term -> Catalog.Code.t option
val make_comparison : Catalog.Code.t -> Language.Comparison.t -> Catalog.Code.t -> Catalog.Code.t
val make_range_fix : State.frame -> Types.ty -> Logic.term -> Catalog.Prover.fix list

val make_overflow_fix :
  State.frame ->
  Types.ty ->
  Intrinsic.scalar ->
  Logic.term ->
  Logic.term ->
  Logic.term ->
  Catalog.Prover.fix list

val make_division_overflow_fix :
  State.frame -> Types.ty -> Logic.term -> Logic.term -> Catalog.Prover.fix list

val make_negation_fix : State.frame -> Types.ty -> Logic.term -> Catalog.Prover.fix list
val list_type_names : Types.substitution -> (string * Types.ty) list

val list_required_fixes :
  State.frame ->
  State.clauses ->
  Mir.requirement ->
  Logic.term ->
  State.passed list ->
  type_names:(string * Types.ty) list ->
  Catalog.Prover.fix list
