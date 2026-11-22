val todo_status : int
val render_runtime : tests:bool -> string
val render_tests_start : time_limit_ms:int -> runner:string -> string list -> string
val render_evaluator_start : cpu_time_limit_ms:int -> string -> string
val render_program_start : string -> string

module For_testing : sig
  val render_main_start : string -> string
end
