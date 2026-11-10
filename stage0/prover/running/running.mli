(** Running compiled code for the prover, through code generation: a tagged template's check, and a
    call whose arguments are known. The prover does not depend on code generation, so a driver gives
    it this. *)

val through : ?results:Compile.results -> ?time_limit:int -> Compile.t Lazy.t -> Prover.running
(** With the compiler, made only when something is run; [results] keeps each run's results under the
    key of the code that ran, and a run past [time_limit], in milliseconds, 10 seconds unless given,
    is stopped. What cannot be built is left to the solver. *)
