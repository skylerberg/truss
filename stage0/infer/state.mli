module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

type local = { type_ : Types.ty; is_var : bool; mode : Types.mode }
type enclosing = Loop | Task of Core.task
type exit = Return_exit | Break_exit | Continue_exit

val tasks_exited_by : exit -> enclosing list -> Core.task list

type env = {
  output : Types.result option;
  specification : bool;
  self : Types.ty option;
  self_mode : Types.mode;
  loop_element : Types.ty option;
  compile_time : bool;
  enclosing : enclosing list;
}

val runs : env -> bool

type subset_constraint = {
  subset : Types.capability_set;
  superset : Types.capability_set;
  report_missing : Types.capability_set -> unit;
}

type frame = {
  start : int;
  mutable nodes : int list;
  mutable bindings : int list;
  mutable patterns : int list;
  mutable pending : (unit -> bool) list;
  mutable unmet : (Types.ty * Types.trait_reference) list;
  frame_specification : bool;
  span : Syntax.span;
}

type form = {
  expression_builders : (unit -> Core.expression) option array;
  statement_builders : (unit -> Core.statement) option array;
  pattern_builders : (unit -> Core.pattern) option array;
  mutable definition_builder : (unit -> Core.definition) option;
  mutable next_node_id : int;
  mutable next_synthetic_local : int;
  mutable tables_with_holes : Tables.t option;
}

type state = {
  database : Query.context;
  key : Names.key;
  package : Path.package;
  definition : Syntax.definition;
  resolved : Resolve.resolved;
  context : Lower.context;
  text : string;
  mutable tables : Tables.t;
  form : form;
  mutable diagnostics : Syntax.diagnostic list;
  unifier : Unify.t;
  locals : (Syntax.id, local) Hashtbl.t;
  mutable law_parameters : (string * Types.ty) list;
  mutable frames : frame list;
  mutable references : Syntax.id list;
  mutable receiver_modes : (Syntax.id * Types.mode) list;
  yielded : (Syntax.id, Types.mode) Hashtbl.t;
  binding_spans : (Syntax.id, Syntax.span) Hashtbl.t;
  mutable lambdas : Syntax.span list;
  mutable unsolved : Diagnostic.reported option;
  mutable capability_constraints : subset_constraint list;
  mutable capability_solution : (int, Types.capability_set) Hashtbl.t option;
  mutable evidence : Path.package list;
}

val reported :
  state ->
  ?fixes:Syntax.span Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Syntax.span ->
  string ->
  Diagnostic.reported

val report :
  state ->
  ?fixes:Syntax.span Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Syntax.span ->
  string ->
  unit

val bug : ('a, unit, string, 'b) format4 -> 'a

val error :
  state ->
  ?fixes:Syntax.span Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Syntax.span ->
  string ->
  Types.ty

val source : state -> Syntax.span -> string
val fresh_node_id : state -> int
val synthetic_expression : state -> origin:Core.origin -> Types.ty -> Core.kind -> Core.expression
val register_expression : state -> Syntax.expression -> (unit -> Core.kind) -> unit
val was_hole : state -> (Tables.t -> Types.ty option array) -> Syntax.id -> bool
val build_expression : state -> Syntax.expression -> Core.expression
val register_statement : state -> Syntax.statement -> (unit -> Core.statement_kind) -> unit
val build_statement : state -> Syntax.statement -> Core.statement
val register_pattern : state -> Syntax.pattern -> (unit -> Core.pattern_kind) -> unit
val build_pattern : state -> Syntax.pattern -> Core.pattern
val alias_expression : state -> Syntax.expression -> Syntax.expression -> unit
val place_of : Core.expression -> Core.place
val fresh_synthetic_local : state -> Core.local
val fix : string -> Syntax.span Diagnostic.edit list -> Syntax.span Diagnostic.fix
val replace : Syntax.span -> string -> Syntax.span Diagnostic.edit
val insert : int -> string -> Syntax.span Diagnostic.edit
val current_frame : state -> frame option
val record : state -> Syntax.expression -> Types.ty -> unit
val defer : state -> (unit -> bool) -> unit
val resolve : state -> Types.ty -> Types.ty
val zonk : state -> Types.ty -> Types.ty
val fresh : state -> Types.ty

val integer_type : state -> Types.ty -> bool
(** Whether a type is a built-in integer type, or a type parameter that an integer trait bounds. *)

val signed_type : state -> Types.ty -> bool
(** Whether a type is a signed integer type, a built-in one or a parameter that [SignedInteger]
    bounds. *)

val bounds : state -> Types.parameter -> Types.trait_reference list
val normalize : state -> Types.ty -> Types.ty
val final_type : state -> Types.ty -> Types.ty
val final_capabilities : state -> Types.capability_set -> Types.capability_set
val final_argument : state -> Types.argument -> Types.argument
val unify : state -> Types.ty -> Types.ty -> bool
val unify_as_hint : state -> Types.ty -> Types.ty -> unit
val implements : state -> Types.ty -> Types.trait_reference -> Impls.evidence option
val plain : state -> Types.ty -> bool
val copyable : state -> Types.ty -> bool
val associated : state -> Types.ty -> Types.trait_reference -> string -> at:Syntax.span -> Types.ty
val evidence_of : Impls.evidence -> Tables.evidence
val trait_reference : ?arguments:Types.argument list -> Path.t -> Types.trait_reference
val string_type : Types.ty
val in_statement : state -> env -> Syntax.span -> (unit -> 'a) -> 'a
val statement_diverges : state -> Syntax.statement -> bool
val build_block : state -> Syntax.block -> Core.block
val declare : state -> Syntax.name -> Types.ty -> is_var:bool -> mode:Types.mode -> unit
val target : state -> Syntax.name -> Resolve.target option
val default_literal : state -> Types.ty -> Types.ty
val head : state -> Syntax.expression -> Resolve.head option
val names_variant : Syntax.name -> bool
val is_member_constant : state -> Syntax.expression -> bool
val show : state -> Types.ty -> string
val mismatched : state -> Syntax.span -> expected:Types.ty -> actual:Types.ty -> Diagnostic.reported
val mismatch : state -> Syntax.span -> expected:Types.ty -> actual:Types.ty -> unit
val is_place : state -> Syntax.expression -> bool
val marked_call : state -> Syntax.expression -> Syntax.id option
val called : Syntax.expression -> Syntax.expression option
val check_resource : state -> Syntax.resource -> unit

type conversion = From_never | Owned_to_view | Function_widening | To_integer | From_integer

val convert :
  state ->
  env ->
  ?argument:bool ->
  ?expression:Core.origin ->
  Syntax.span ->
  actual:Types.ty ->
  expected:Types.ty ->
  unit
