open State

val variable : ?numbers:int list -> string -> 'a Symbol.t

exception Unsupported of span * string
exception Foreign_unsupported of string

val unsupported : span -> ('a, unit, string, 'b) format4 -> 'a
val bug : ('a, unit, string, 'b) format4 -> 'a
val is_in_recursion_group : context -> Path.t -> bool
val clauses : Mir.requirement list -> Mir.formula list
val declare : context -> Logic.declaration -> unit
val add_fact : context -> Logic.term -> unit
val value_symbol : context -> frame -> Logic.symbol -> Logic.sort -> Logic.term
val fresh_name : context -> string -> 'a Symbol.t
val fresh : context -> frame -> string -> Logic.sort -> Logic.term
val mentions_fresh_after : context -> int -> Logic.term -> bool
val closed_over_binders : frame -> Logic.term -> Logic.term option
val fact : context -> frame -> Logic.term -> unit
val assume : context -> frame -> Logic.term -> unit
val add_requires : context -> frame -> message -> fix list

val oblige :
  ?template_clause:template_clause ->
  ?cited:Names.key * Core.origin ->
  ?fixes:fix list ->
  context ->
  frame ->
  Code.prover ->
  span ->
  message ->
  Logic.term ->
  unit

val obligation_at :
  ?template_clause:template_clause ->
  context ->
  frame ->
  Code.prover ->
  span ->
  message ->
  Logic.term ->
  obligation option

val make_obligation :
  ?template_clause:template_clause ->
  context ->
  frame ->
  Code.prover ->
  span ->
  message ->
  Logic.term ->
  obligation

val span_of : source -> int -> span
val quote : source -> int -> piece
val quoted : string -> span -> string
val text_of : source -> int -> string
val builtin : Types.ty -> Intrinsic.builtin option
val bounds : Types.ty -> (Z.t * Z.t) option
val float_format : Types.ty -> (int * int) option
val constructor_name : Types.ty -> string option -> 'a Symbol.t
val selector_name : Types.ty -> string option -> string -> 'a Symbol.t
val is_standard_equal : Path.t -> bool
val equal_trait : Path.t
val visible_type : context -> Types.ty -> (Types.type_interface * Types.substitution) option
val constructors : context -> Types.ty -> (string option * (string * Types.ty) list) list option
val sort_of : context -> Types.ty -> Logic.sort
val structural : context -> ?seen:Types.ty list -> Types.ty -> bool
val in_range : Types.ty -> Logic.term -> Logic.term
val once : context -> stated -> (unit -> unit) -> unit
val arrive : context -> frame -> string -> Types.ty -> Logic.term
val bind : frame -> Locals.key -> Types.ty -> Logic.term -> frame
val substituted : context -> frame -> Types.ty -> Types.ty
val local_type : context -> frame -> Locals.key -> Types.ty option
val mentions_potential : Logic.term -> bool
val restrict : frame -> Logic.term -> frame
val path_condition : context -> frame -> Logic.term -> Logic.term

val merge :
  context ->
  ?value_type:Types.ty ->
  condition:Logic.term ->
  (Logic.term * frame * Logic.term option) list ->
  frame * Logic.term option

val join :
  context ->
  ?value_type:Types.ty ->
  (frame * Logic.term option) list ->
  (frame * Logic.term option) option

val join_frames : context -> frame list -> frame option
