val render_runtime : tests:bool -> string
val render_tests_start : time_limit_ms:int -> runner:string -> string list -> string
val render_evaluator_start : string -> string
val render_program_start : string -> string

module For_testing : sig
  val main_calling : string -> string
end
