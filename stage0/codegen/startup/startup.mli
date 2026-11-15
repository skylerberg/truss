val runtime : tests:bool -> in_order:bool -> string
val tests_calling : time_limit_ms:int -> runner:string -> string list -> string
val evaluator_calling : string -> string
val program_calling : string -> string

module For_testing : sig
  val main_calling : string -> string
end
