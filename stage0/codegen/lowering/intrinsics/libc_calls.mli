val make_number_constant : Context.t -> Libc.number -> Lowered.operand
val load_text_at : Context.t -> Lowered.local -> is_present:Lowered.place -> unit
val lower : Context.t -> Libc.function_ -> unit
