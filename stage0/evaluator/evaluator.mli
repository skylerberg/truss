(** The prover's evaluator, through code generation: it runs a tagged template's check, and a call
    whose arguments are known. The prover does not depend on code generation, so a driver gives it
    this. *)

val of_compiler :
  ?results:Compile.results -> ?time_limit:int -> Compile.t Lazy.t -> Prover.evaluator
(** With the compiler, made only when something is run or keyed; [results] keeps each run's results
    under the key of the code that ran, and a run past [time_limit], in milliseconds, times out. *)
