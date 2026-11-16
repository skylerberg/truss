type local = { type_ : Types.ty; is_var : bool; mode : Types.mode }

type env = {
  output : Types.result option;
  specification : bool;
  self : Types.ty option;
  self_mode : Types.mode;
  loop_element : Types.ty option;
  compile_time : bool;
  in_quantifier : bool;
}

val runs : env -> bool

type subset_constraint = {
  subset : Types.capability_set;
  superset : Types.capability_set;
  report_missing : Types.capability_set -> unit;
}

type frame = {
  first_variable : int;
  mutable recorded_expressions : int list;
  mutable bindings : int list;
  mutable declared : int list;
  mutable deferred_checks : (unit -> bool) list;
  mutable reported_unmet_bounds : (Types.ty * Types.trait_reference) list;
  mutable compiled_expressions : int list;
  mutable compiled_bindings : int list;
  mutable specification_only_report : Diagnostic.reported option;
  frame_specification : bool;
  span : Source.Definition_span.t;
}

type undecided_literal = {
  index : int;
  kind : Types.literal_kind;
  local : Syntax.id;
  owner : frame;
}

type literal_decision = {
  decided_local : Syntax.id;
  decided_type : Types.ty;
  decided_at : Source.Definition_span.t;
  is_default : bool;
  mutable decision_report : Diagnostic.reported option;
}

type form = {
  expression_builders : (unit -> Core.expression) option array;
  statement_builders : (unit -> Core.statement) option array;
  pattern_builders : (unit -> Core.pattern) option array;
  mutable definition_builder : (holds_body:bool -> Core.definition) option;
  mutable next_node_id : int;
  mutable next_synthetic_local : int;
  mutable tables_with_holes : Tables.t option;
}

type state = {
  lookups : Lookups.t;
  key : Resolve.Names.key;
  package : Path.package;
  definition : Syntax.definition;
  resolved : Resolve.resolved;
  context : Interface.Elaborator.t;
  text : string Lazy.t;
  mutable tables : Tables.t;
  form : form;
  mutable diagnostics : Diagnostic.in_definition list;
  unifier : Unify.t;
  locals : (Syntax.id, local) Hashtbl.t;
  mutable law_parameters : (string * Types.ty) list;
  mutable frames : frame list;
  mutable locals_read : Syntax.id list;
  mutable receiver_modes : (Syntax.id * Types.mode) list;
  yielded : (Syntax.id, Types.mode) Hashtbl.t;
  lent_tails : (Syntax.id, unit) Hashtbl.t;
  mutable lambdas : Source.Definition_span.t list;
  mutable unsolved : Diagnostic.reported option;
  mutable capability_constraints : subset_constraint list;
  mutable capability_solution : (int, Types.capability_set) Hashtbl.t option;
  mutable evidence_packages : Path.package list;
  mutable undecided : undecided_literal list;
  decisions : (int, literal_decision) Hashtbl.t;
  annotatable : (Syntax.id, unit) Hashtbl.t;
}

val report :
  state ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Source.Definition_span.t ->
  string ->
  unit

val is_formula : env -> bool
val reject_in_formula : state -> env -> Source.Definition_span.t -> string -> unit
val read_span : state -> Syntax.id -> Source.Definition_span.t
val bug : ('a, unit, string, 'b) format4 -> 'a

val make_error_type :
  state ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Source.Definition_span.t ->
  string ->
  Types.ty

val quote_span : state -> Source.Definition_span.t -> string
val allocate_node_id : state -> int

val make_synthetic_expression :
  state -> origin:Core.origin -> Types.ty -> Core.kind -> Core.expression

val register_expression : state -> Syntax.expression -> (unit -> Core.kind) -> unit
val was_hole : state -> (Tables.t -> Types.ty option array) -> Syntax.id -> bool
val build_expression : state -> Syntax.expression -> Core.expression
val register_statement : state -> Syntax.statement -> (unit -> Core.statement_kind) -> unit
val build_statement : state -> Syntax.statement -> Core.statement
val register_pattern : state -> Syntax.pattern -> (unit -> Core.pattern_kind) -> unit
val build_pattern : state -> Syntax.pattern -> Core.pattern
val alias_expression : state -> Syntax.expression -> Syntax.expression -> unit
val mark_lent_tails : state -> Syntax.expression -> unit
val make_place : Core.expression -> Core.place
val allocate_synthetic_local : state -> Core.local

val fix :
  string -> Source.Definition_span.t Diagnostic.edit list -> Source.Definition_span.t Diagnostic.fix

val replace : Source.Definition_span.t -> string -> Source.Definition_span.t Diagnostic.edit
val insert : int -> string -> Source.Definition_span.t Diagnostic.edit
val find_current_frame : state -> frame option
val record : state -> Syntax.expression -> Types.ty -> unit
val note_compiled_expression : state -> env -> Syntax.expression -> unit
val report_specification_only : state -> Source.Definition_span.t -> string -> Diagnostic.reported
val defer : state -> (unit -> bool) -> unit
val resolve : state -> Types.ty -> Types.ty
val zonk : state -> Types.ty -> Types.ty
val make_fresh_type : state -> Types.ty
val is_integer_type : state -> Types.ty -> bool
val is_signed_type : state -> Types.ty -> bool
val lookup_bounds : state -> Types.parameter -> Types.trait_reference list
val normalize : state -> Types.ty -> Types.ty
val finalize_type : state -> Types.ty -> Types.ty
val finalize_capabilities : state -> Types.capability_set -> Types.capability_set
val finalize_argument : state -> Types.argument -> Types.argument
val unify : state -> Types.ty -> Types.ty -> bool
val unify_as_hint : state -> Types.ty -> Types.ty -> unit
val implements : state -> Types.ty -> Types.trait_reference -> Interface.Impls.evidence option
val is_plain : state -> Types.ty -> bool
val is_view : state -> Types.ty -> bool
val is_copyable : state -> Types.ty -> bool

val resolve_associated_type :
  state -> Types.ty -> Types.trait_reference -> string -> at:Source.Definition_span.t -> Types.ty

val convert_evidence : Interface.Impls.evidence -> Tables.evidence
val make_trait_reference : ?arguments:Types.argument list -> Path.t -> Types.trait_reference
val string_type : Types.ty
val in_statement : state -> env -> Source.Definition_span.t -> (unit -> 'a) -> 'a
val diverges : is_never:(Syntax.expression -> bool) -> Syntax.statement -> bool
val statement_diverges : state -> Syntax.statement -> bool
val build_block : state -> Syntax.block -> Core.block
val declare : state -> Syntax.name -> Types.ty -> is_var:bool -> mode:Types.mode -> unit

val declare_compiled :
  state -> env -> Syntax.name -> Types.ty -> is_var:bool -> mode:Types.mode -> unit

val find_target : state -> Syntax.name -> Resolve.target option
val decide_default_literal : state -> at:Source.Definition_span.t -> Types.ty -> Types.ty
val find_head : state -> Syntax.expression -> Resolve.head option
val is_variant_name : Syntax.name -> bool
val is_member_constant : state -> Syntax.expression -> bool
val show : state -> Types.ty -> string

val add_mismatch_diagnostic :
  state ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Source.Definition_span.t ->
  sides:(Types.ty * Types.ty) list ->
  string ->
  Diagnostic.reported

val add_mismatch :
  state -> Source.Definition_span.t -> expected:Types.ty -> actual:Types.ty -> Diagnostic.reported

val report_mismatch :
  state -> Source.Definition_span.t -> expected:Types.ty -> actual:Types.ty -> unit

val is_place : state -> Syntax.expression -> bool
val find_call_with_mode_keyword : state -> Syntax.expression -> Syntax.id option
val check_resource : state -> Syntax.resource -> unit

val make_slice :
  state ->
  origin:Core.origin ->
  Core.place ->
  start:Core.expression option ->
  stop:Core.expression option ->
  inclusive:bool ->
  Core.kind

type conversion = From_never | Owned_to_view | Function_widening | To_integer | From_integer

val convert :
  state ->
  env ->
  ?argument:Types.mode ->
  ?expression:Core.origin ->
  Source.Definition_span.t ->
  actual:Types.ty ->
  expected:Types.ty ->
  unit
