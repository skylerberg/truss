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
  | Operator of {
      at : Source.Definition_span.t;
      operands : (Source.Definition_span.t * Source.Definition_span.t) option;
    }
  | Method_call of Source.Definition_span.t
  | Loop of Source.Definition_span.t
  | Any_conversion of { at : Source.Definition_span.t; any_type : Types.ty }
  | Excluded of (Types.ty -> Diagnostic.reported)

type goal = {
  subject : Types.ty;
  requirement : requirement;
  outputs : (string * Types.ty) list;
  cause : cause;
  mode : Unify.mode;
  depth : int;
  needed_by : goal option;
}

type frame = {
  first_variable : int;
  mutable recorded_expressions : int list;
  mutable bindings : int list;
  mutable reported_unmet_bounds : (Types.ty * Types.trait_reference * Diagnostic.reported) list;
  mutable compiled_expressions : int list;
  mutable compiled_bindings : int list;
  mutable specification_only_report : Diagnostic.reported option;
  span : Source.Definition_span.t;
}

type decision_site = Use | Statement_end | Actual_head | Method_call

type entry =
  | Literal of {
      allowed : Language.Builtin_type.t list;
      report_excluded : Types.ty -> Diagnostic.reported;
      literal : Syntax.id;
    }
  | Narrowing of {
      allowed : Language.Builtin_type.t list;
      report_excluded : Types.ty -> Diagnostic.reported;
    }
  | Local of Syntax.id
  | Decided of {
      site : decision_site;
      decided_type : Types.ty;
      decided_at : Source.Definition_span.t;
    }

type logged = { member : int; entry : entry }

type state = {
  lookups : Lookups.t;
  key : Resolve.Names.key;
  package : Path.package;
  definition : Syntax.definition;
  resolved : Resolve.resolved;
  text : string Lazy.t;
  tables : Tables.t;
  mutable diagnostics : Diagnostic.in_definition list;
  unifier : Unify.t;
  locals : (Syntax.id, local) Hashtbl.t;
  law_parameters : (string * Types.ty) list;
  mutable frames : frame list;
  mutable goals : goal list;
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
  mutable log : logged list;
  annotatable : (Syntax.id, unit) Hashtbl.t;
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
val mark_lent_tails : state -> Syntax.expression -> unit

val fix :
  string -> Source.Definition_span.t Diagnostic.edit list -> Source.Definition_span.t Diagnostic.fix

val replace : Source.Definition_span.t -> string -> Source.Definition_span.t Diagnostic.edit
val insert : int -> string -> Source.Definition_span.t Diagnostic.edit
val read_current_frame : state -> frame
val record : state -> Syntax.expression -> Types.ty -> unit
val note_compiled_expression : state -> env -> Syntax.expression -> unit
val report_specification_only : state -> Source.Definition_span.t -> string -> Diagnostic.reported
val check_compiled_binding : state -> Syntax.id -> unit
val check_compiled_expression : state -> Syntax.id -> unit
val reduce_condition : state -> Types.condition -> Types.condition option
val record_condition : state -> Syntax.id -> Syntax.condition option -> Types.condition option
val with_mode : state -> Unify.mode -> (unit -> 'a) -> 'a
val with_added_condition : state -> Types.condition -> (unit -> 'a) -> 'a
val read_context : state -> Interface.Elaborator.t
val check_when_final : state -> (unit -> unit) -> unit
val resolve : state -> Types.ty -> Types.ty
val zonk : state -> Types.ty -> Types.ty
val make_fresh_type : state -> Types.ty
val make_fresh_generic_arguments : state -> Types.generic list -> Types.argument list
val lookup_bounds : state -> Types.parameter -> Types.trait_reference list
val normalize : state -> Types.ty -> Types.ty
val find_domain : state -> Types.ty -> Language.Builtin_type.t list option
val is_float_domain : Language.Builtin_type.t list -> bool
val is_within : state -> Types.ty -> Language.Builtin_type.t list -> bool
val read_integer_range : state -> Types.ty -> Z.t * Z.t

val make_literal_type :
  state ->
  Syntax.expression ->
  Language.Builtin_type.t list ->
  report_excluded:(Types.ty -> Diagnostic.reported) ->
  Types.ty

val record_narrowing :
  state ->
  int ->
  allowed:Language.Builtin_type.t list ->
  report_excluded:(Types.ty -> Diagnostic.reported) ->
  unit

val record_decided :
  state -> int -> site:decision_site -> decided_type:Types.ty -> at:Source.Definition_span.t -> unit

val resolve_capabilities : state -> Types.capability_set -> Types.capability_set
val finalize_type : state -> Types.ty -> Types.ty
val finalize_capabilities : state -> Types.capability_set -> Types.capability_set
val finalize_argument : state -> Types.argument -> Types.argument
val unify : state -> Types.ty -> Types.ty -> bool
val unify_as_hint : state -> Types.ty -> Types.ty -> unit
val normalize_trait : state -> Types.trait_reference -> Types.trait_reference
val find_evidence : state -> Types.ty -> Types.trait_reference -> Interface.Impls.evidence option

val decide_property :
  state -> Interface.Properties.property -> Types.ty -> Interface.Properties.decision

val diverges : is_never:(Syntax.expression -> bool) -> Syntax.statement -> bool
val declare : state -> Syntax.name -> Types.ty -> binding:binding -> mode:Language.Mode.t -> unit

val declare_compiled :
  state -> env -> Syntax.name -> Types.ty -> binding:binding -> mode:Language.Mode.t -> unit

val find_target : state -> Syntax.name -> Resolve.target option
val find_head : state -> Syntax.expression -> Resolve.head option
val show : state -> Types.ty -> string
val describe : state -> Types.ty -> string
val note_mode_keyword : state -> Syntax.expression -> Syntax.mode -> Syntax.expression -> unit
val find_local_type : state -> Syntax.name -> Types.ty option
