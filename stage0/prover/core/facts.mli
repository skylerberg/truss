(** The operations on the state of a proof: declarations, facts, fresh symbols, obligations, the
    logic's sorts for types, and the join of paths. *)

open State

val variable : ?numbers:int list -> string -> 'a Symbol.t

exception Unsupported of span * string
exception Foreign_unsupported of string

val unsupported : span -> ('a, unit, string, 'b) format4 -> 'a
val bug : ('a, unit, string, 'b) format4 -> 'a
val home : source -> Names.key
val clauses : Mir.requirement list -> Mir.formula list
val reading_package : context -> Path.package option
val declare : context -> Logic.declaration -> unit
val add_fact : context -> Logic.term -> unit
val value_symbol : context -> frame -> Logic.symbol -> Logic.sort -> Logic.term
val fresh_name : context -> string -> 'a Symbol.t
val fresh : context -> frame -> string -> Logic.sort -> Logic.term
val mentions_fresh_after : context -> int -> Logic.term -> bool
val closed_over_binders : frame -> Logic.term -> Logic.term option
val fact : context -> frame -> Logic.term -> unit
val assume : context -> frame -> Logic.term -> unit
val add_requires : context -> frame -> string -> Syntax.Span.t Diagnostic.fix list
val exactly : Logic.query -> Logic.query

val oblige :
  ?evaluation:evaluation ->
  ?cited:Names.key * span ->
  ?fixes:span Diagnostic.fix list ->
  context ->
  frame ->
  Code.prover ->
  span ->
  string ->
  Logic.term ->
  unit

val obligation_at :
  ?evaluation:evaluation ->
  context ->
  frame ->
  Code.prover ->
  span ->
  string ->
  Logic.term ->
  obligation option

val make_obligation :
  ?evaluation:evaluation ->
  context ->
  frame ->
  Code.prover ->
  span ->
  string ->
  Logic.term ->
  obligation

val span_of : source -> int -> span
val quote : source -> int -> string
val builtin : Types.ty -> Intrinsic.builtin option
val bounds : Types.ty -> (Z.t * Z.t) option
val width : Types.ty -> int option
val is_numeric : Types.ty -> bool
val float_format : Types.ty -> (int * int) option
val float_literal : int * int -> float -> Logic.term
val float_operation : string -> Logic.term -> Logic.term -> Logic.term
val is_nan : Logic.term -> Logic.term
val truncated : Logic.term -> Logic.term
val float_equal : Logic.term -> Logic.term -> Logic.term
val float_less : Logic.term -> Logic.term -> Logic.term
val is_bool : Types.ty -> bool
val type_key : Types.ty -> string
val argument_key : Types.argument -> string
val constructor_name : Types.ty -> string option -> 'a Symbol.t
val selector_name : Types.ty -> string option -> string -> 'a Symbol.t
val is_standard_equal : Path.t -> bool
val equal_trait : Path.t
val end_scope : outer:frame -> frame -> frame

val callee_substitution :
  frame -> Types.signature -> Types.argument list -> (Types.parameter * Types.argument) list

val visible_type : context -> Types.ty -> (Types.type_interface * Types.substitution) option
val constructors : context -> Types.ty -> (string option * (string * Types.ty) list) list option
val declared_fields : context -> Types.ty -> string option -> (string * Types.ty) list option
val sort_of : context -> Types.ty -> Logic.sort
val structural : context -> ?seen:Types.ty list -> Types.ty -> bool
val scalar_bytes : Types.ty -> int option
val in_range : Types.ty -> Logic.term -> Logic.term
val once : context -> stated -> (unit -> unit) -> unit
val canonical_binders : Logic.term -> Logic.term
val arrive : context -> frame -> string -> Types.ty -> Logic.term
val bind : frame -> Locals.key -> Types.ty -> Logic.term -> frame
val substituted : context -> frame -> Types.ty -> Types.ty
val local_type : context -> frame -> Locals.key -> Types.ty option
val mentions_potential : Logic.term -> bool
val restrict : frame -> Logic.term -> frame

val join :
  context ->
  ?value_type:Types.ty ->
  (frame * Logic.term option) list ->
  (frame * Logic.term option) option

val join_frames : context -> frame list -> frame option
