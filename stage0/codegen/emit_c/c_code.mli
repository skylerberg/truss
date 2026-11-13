(* A function's header, with no linkage, and its body. *)
val function_c : C_types.context -> Instance.key -> string -> Lir.function_ -> string * string
