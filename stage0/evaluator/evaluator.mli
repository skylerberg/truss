(** The prover's evaluator, through code generation: it runs a tagged template's check, and a call
    whose arguments are known. The prover does not depend on code generation, so a driver gives it
    this. *)

val of_compiler : Compile.t Lazy.t -> Prover.evaluator
(** With the compiler, made only when something is run or keyed. A run past the compiler's
    evaluation time limit times out. *)
