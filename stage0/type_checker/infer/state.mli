type binding = Parameter | Var | Let
type local = { name : string; type_ : Types.ty; binding : binding; mode : Language.Mode.t }

type env = {
  output : Types.result option;
  specification : bool;
  self : Types.ty option;
  self_mode : Language.Mode.t;
  loop_element : Types.ty option;
  compile_time : bool;
  in_quantifier : bool;
}

val runs : env -> bool

type subset_constraint = {
  subset : Types.capability_set;
  restriction : Types.capability_set option;
  superset : Types.capability_set;
  report_missing : Types.capability_set -> unit;
}

type requirement = Implements of Types.trait_reference | Within of Language.Builtin_type.t list

type cause =
  | Bound of { at : Source.Definition_span.t; of_type : Types.ty option }
  | Operator of Source.Definition_span.t
  | Method_call of Source.Definition_span.t
  | Loop of Source.Definition_span.t
  | Any_conversion of { at : Source.Definition_span.t; any_type : Types.ty }
  | Excluded of (Types.ty -> Diagnostic.reported)

type goal = {
  subject : Types.ty;
  requirement : requirement;
  outputs : (string * Types.ty) list;
  cause : cause;
  is_specification : bool;
}

type frame = {
  first_variable : int;
  mutable recorded_expressions : int list;
  mutable bindings : int list;
  mutable declared : int list;
  mutable goals : goal list;
  mutable reported_unmet_bounds : (Types.ty * Types.trait_reference * Diagnostic.reported) list;
  mutable compiled_expressions : int list;
  mutable compiled_bindings : int list;
  mutable specification_only_report : Diagnostic.reported option;
  frame_specification : bool;
  span : Source.Definition_span.t;
}

type undecided_literal = { index : int; local : Syntax.id; owner : frame }

type narrowing = {
  narrowed : Types.ty;
  allowed : Language.Builtin_type.t list;
  report_excluded : Types.ty -> Diagnostic.reported;
}

type default_site = Method_lookup | Actual_head

type literal_decision = {
  decided_local : Syntax.id;
  decided_type : Types.ty;
  decided_at : Source.Definition_span.t;
  default_site : default_site option;
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
  mutable keyword_modes : (Syntax.id * Language.Mode.t) list;
  mutable places_without_keyword : (Syntax.id * Language.Mode.t) list;
  mutable mode_keywords : Core.mode_keyword list;
  yielded : (Syntax.id, Language.Mode.t) Hashtbl.t;
  lent_tails : (Syntax.id, unit) Hashtbl.t;
  mutable lambdas : Source.Definition_span.t list;
  mutable unsolved : Diagnostic.reported option;
  mutable capability_constraints : subset_constraint list;
  mutable capability_solution : (int, Types.capability_set) Hashtbl.t option;
  mutable evidence_packages : Path.package list;
  mutable final_type_checks : (unit -> unit) list;
  mutable undecided : undecided_literal list;
  decisions : (int, literal_decision) Hashtbl.t;
  annotatable : (Syntax.id, unit) Hashtbl.t;
  mutable narrowings : narrowing list;
}

val add_diagnostic :
  state ->
  ?notes:(Source.Definition_span.t * string) list ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Source.Definition_span.t ->
  string ->
  Diagnostic.reported

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
val raise_bug : ('a, unit, string, 'b) format4 -> 'a

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
val build_scrutinee_pattern : state -> Syntax.pattern -> Core.pattern
val alias_expression : state -> Syntax.expression -> Syntax.expression -> unit
val mark_lent_tails : state -> Syntax.expression -> unit
val make_place : Core.expression -> Core.place
val allocate_synthetic_local : state -> Core.local

val fix :
  string -> Source.Definition_span.t Diagnostic.edit list -> Source.Definition_span.t Diagnostic.fix

val replace : Source.Definition_span.t -> string -> Source.Definition_span.t Diagnostic.edit
val insert : int -> string -> Source.Definition_span.t Diagnostic.edit
val read_current_frame : state -> frame
val record : state -> Syntax.expression -> Types.ty -> unit
val record_loop : state -> loop:Syntax.id -> Tables.loop -> unit
val note_compiled_expression : state -> env -> Syntax.expression -> unit
val report_specification_only : state -> Source.Definition_span.t -> string -> Diagnostic.reported
val check_when_final : state -> (unit -> unit) -> unit
val resolve : state -> Types.ty -> Types.ty
val zonk : state -> Types.ty -> Types.ty
val make_fresh_type : state -> Types.ty
val make_fresh_generic_arguments : state -> Types.generic list -> Types.argument list
val lookup_bounds : state -> Types.parameter -> Types.trait_reference list
val normalize : state -> Types.ty -> Types.ty
val find_domain : state -> Types.ty -> Language.Builtin_type.t list option
val is_within : state -> Types.ty -> Language.Builtin_type.t list -> bool
val read_integer_range : state -> Types.ty -> Z.t * Z.t

val make_literal_type :
  state ->
  Language.Builtin_type.t list ->
  report_excluded:(Types.ty -> Diagnostic.reported) ->
  Types.ty

val finalize_type : state -> Types.ty -> Types.ty
val finalize_capabilities : state -> Types.capability_set -> Types.capability_set
val finalize_argument : state -> Types.argument -> Types.argument
val finalize_instantiation : state -> Types.instantiation -> Types.instantiation
val unify : state -> Types.ty -> Types.ty -> bool
val unify_as_hint : state -> Types.ty -> Types.ty -> unit
val normalize_trait : state -> Types.trait_reference -> Types.trait_reference
val find_evidence : state -> Types.ty -> Types.trait_reference -> Interface.Impls.evidence option

val decide_property :
  state -> Interface.Properties.property -> Types.ty -> Interface.Properties.decision

val is_plain : state -> Types.ty -> bool
val is_view : state -> Types.ty -> bool
val decide_binding_mode : state -> Language.Mode.t -> Types.ty -> Language.Mode.t

val resolve_associated_type :
  state ->
  Types.ty ->
  Types.trait_reference ->
  Well_known.associated ->
  at:Source.Definition_span.t ->
  Types.ty

val make_callee : state -> Core.operand Core.target -> Core.callee

val make_call :
  state ->
  callee:Core.operand Core.target ->
  arguments:Core.argument list ->
  lends:Language.Mode.t option ->
  Core.call

val make_trait_reference : arguments:Types.argument list -> Path.t -> Types.trait_reference
val string_type : Types.ty

val run_in_statement :
  state -> env -> Source.Definition_span.t -> solve:(frame -> unit) -> (unit -> 'a) -> 'a

val diverges : is_never:(Syntax.expression -> bool) -> Syntax.statement -> bool
val build_block : state -> Syntax.block -> Core.block
val declare : state -> Syntax.name -> Types.ty -> binding:binding -> mode:Language.Mode.t -> unit

val declare_compiled :
  state -> env -> Syntax.name -> Types.ty -> binding:binding -> mode:Language.Mode.t -> unit

val find_target : state -> Syntax.name -> Resolve.target option

val decide_default_literal :
  state -> at:Source.Definition_span.t -> site:default_site -> Types.ty -> Types.ty

val report_decided_in_specification :
  state -> Source.Definition_span.t -> int -> Diagnostic.reported

val find_head : state -> Syntax.expression -> Resolve.head option
val show : state -> Types.ty -> string
val describe : state -> Types.ty -> string

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
val find_keyword_operation : state -> Syntax.expression -> (Syntax.id * Syntax.expression) option
val note_mode_keyword : state -> Syntax.expression -> Syntax.mode -> Syntax.expression -> unit
val find_local_type : state -> Syntax.name -> Types.ty option
val find_sequence_element : Types.ty -> Types.ty option

val make_range :
  state ->
  origin:Core.origin ->
  Core.place ->
  start:Core.expression option ->
  stop:Core.expression option ->
  inclusive:bool ->
  Core.kind
