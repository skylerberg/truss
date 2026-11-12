module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

type local = { type_ : T.ty; mutable_ : bool; mode : T.mode }
type enclosing = Loop | Task of Core.task
type exit = Return_exit | Break_exit | Continue_exit

val tasks_exited_by : exit -> enclosing list -> Core.task list

type env = {
  output : T.result option;
  specification : bool;
  self : T.ty option;
  self_mode : T.mode;
  loop_element : T.ty option;
  compile_time : bool;
  enclosing : enclosing list;
}

val runs : env -> bool

type subset_constraint = {
  subset : T.capability list;
  superset : T.capability list;
  report_missing : T.capability list -> unit;
}

type frame = {
  start : int;
  mutable nodes : int list;
  mutable bindings : int list;
  mutable patterns : int list;
  mutable pending : (unit -> bool) list;
  mutable unmet : (T.ty * T.trait_reference) list;
  frame_specification : bool;
  span : Syntax.span;
}

type form = {
  expression_builders : (unit -> Core.expression) option array;
  statement_builders : (unit -> Core.statement) option array;
  pattern_builders : (unit -> Core.pattern) option array;
  mutable definition_builder : (unit -> Core.definition) option;
  mutable next_node_id : int;
  mutable synthetic_local_count : int;
  mutable tables_with_holes : C.t option;
}

type state = {
  database : Query.context;
  key : Names.key;
  package : Path.package;
  definition : Syntax.definition;
  resolved : Resolve.resolved;
  context : Lower.context;
  text : string;
  mutable tables : C.t;
  form : form;
  mutable diagnostics : Diagnostic.t list;
  unifier : Unify.t;
  locals : (Syntax.id, local) Hashtbl.t;
  mutable law_parameters : (string * T.ty) list;
  mutable frames : frame list;
  mutable references : Syntax.id list;
  mutable receiver_modes : (Syntax.id * T.mode) list;
  yielded : (Syntax.id, T.mode) Hashtbl.t;
  binding_spans : (Syntax.id, Syntax.span) Hashtbl.t;
  mutable lambdas : Syntax.span list;
  mutable unsolved : Diagnostic.reported option;
  mutable capability_constraints : subset_constraint list;
  mutable capability_solution : (int, T.capability list) Hashtbl.t option;
  mutable evidence : Path.package list;
}

val reported :
  state ->
  ?fixes:Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Syntax.span ->
  string ->
  Diagnostic.reported

val report :
  state -> ?fixes:Diagnostic.fix list -> Diagnostic.Code.types -> Syntax.span -> string -> unit

val bug : ('a, unit, string, 'b) format4 -> 'a

val error :
  state -> ?fixes:Diagnostic.fix list -> Diagnostic.Code.types -> Syntax.span -> string -> T.ty

val source : state -> Syntax.span -> string
val fresh_node_id : state -> int
val synthetic_expression : state -> origin:Core.origin -> Types.ty -> Core.kind -> Core.expression
val register_expression : state -> Syntax.expression -> (unit -> Core.kind) -> unit
val was_hole : state -> (C.t -> T.ty option array) -> Syntax.id -> bool
val build_expression : state -> Syntax.expression -> Core.expression
val register_statement : state -> Syntax.statement -> (unit -> Core.statement_kind) -> unit
val build_statement : state -> Syntax.statement -> Core.statement
val register_pattern : state -> Syntax.pattern -> (unit -> Core.pattern_kind) -> unit
val build_pattern : state -> Syntax.pattern -> Core.pattern
val alias_expression : state -> Syntax.expression -> Syntax.expression -> unit
val place_of : Core.expression -> Core.place
val fresh_synthetic_local : state -> Core.local
val fix : string -> Diagnostic.edit list -> Diagnostic.fix
val replace : Syntax.span -> string -> Diagnostic.edit
val insert : int -> string -> Diagnostic.edit
val current_frame : state -> frame option
val record : state -> Syntax.expression -> Types.ty -> unit
val defer : state -> (unit -> bool) -> unit
val resolve : state -> Unify.T.ty -> Unify.T.ty
val zonk : state -> Unify.T.ty -> Unify.T.ty
val fresh : state -> Unify.T.ty
val bounds : state -> Types.parameter -> Types.trait_reference list
val normalize : state -> Unify.T.ty -> Types.ty
val final : state -> Unify.T.ty -> T.ty
val final_capabilities : state -> T.capability list -> T.capability list
val final_argument : state -> T.argument -> T.argument
val unify : state -> Unify.T.ty -> Unify.T.ty -> bool
val unify_as_hint : state -> Unify.T.ty -> Unify.T.ty -> unit
val implements : state -> Unify.T.ty -> T.trait_reference -> Impls.evidence option
val plain : state -> Unify.T.ty -> bool
val associated : state -> Unify.T.ty -> T.trait_reference -> string -> at:Syntax.span -> T.ty
val evidence_of : Impls.evidence -> C.evidence
val trait_reference : ?arguments:T.argument list -> Path.t -> T.trait_reference
val string_type : T.ty
val in_statement : state -> env -> Syntax.span -> (unit -> 'a) -> 'a
val statement_never : state -> Syntax.statement -> bool
val build_block : state -> Syntax.block -> Core.block
val declare : state -> Syntax.name -> T.ty -> mutable_:bool -> mode:T.mode -> unit
val target : state -> Syntax.name -> Resolve.target option
val default_literal : state -> Unify.T.ty -> Unify.T.ty
val head : state -> Syntax.expression -> Resolve.head option
val names_variant : Syntax.name -> bool
val show : state -> Unify.T.ty -> string

val mismatched :
  state -> Syntax.span -> expected:Unify.T.ty -> found:Unify.T.ty -> Diagnostic.reported

val mismatch : state -> Syntax.span -> expected:Unify.T.ty -> found:Unify.T.ty -> unit
val is_place : state -> Syntax.expression -> bool
val marked_call : state -> Syntax.expression -> Syntax.id option
val called : Syntax.expression -> Syntax.expression option
val check_resource : state -> Syntax.resource -> unit

type static_ =
  | Static_type of T.ty
  | Static_trait of Path.t * T.argument list option
  | Static_capability of Path.t

type conversion = From_never | Owned_to_view | Function_widening | To_integer | From_integer

val convert :
  state ->
  env ->
  ?argument:bool ->
  ?expression:Core.origin ->
  Syntax.span ->
  found:Unify.T.ty ->
  expected:Unify.T.ty ->
  unit

val require :
  state ->
  at:Syntax.span ->
  Unify.T.ty ->
  T.trait_reference ->
  unmet:(Types.ty -> (string * Types.ty) option -> unit) ->
  unit

val fresh_arguments : state -> Path.t -> T.argument list
val instantiate_type : state -> Syntax.span -> Path.t -> T.argument list
val static_ : state -> Syntax.expression -> static_ option
val named_type : state -> Syntax.expression -> Path.t -> Syntax.bracket_item list option -> T.ty
val type_argument_of_expression : state -> Syntax.expression -> T.argument

type instance = {
  signature : T.signature;
  substitution : T.substitution;
  type_arguments : T.argument list;
}

val instantiate :
  state -> Syntax.span -> ?extra:(T.parameter * T.argument) list -> T.signature -> instance

val output_type : T.result -> T.ty
val function_signature : state -> Path.t -> (Types.signature, Diagnostic.reported) result option
val note_lending : state -> Syntax.expression -> T.result -> unit
val lent : state -> Syntax.expression -> T.mode option
val borrowed : state -> Syntax.expression -> bool
val scrutinee_mode : state -> Syntax.expression -> T.mode

type immutable = Read_only of string | Captured of string | Lent_read_only | Not_a_place
type mutation = Assignment | Mut_mark

val mutate : state -> env -> by:mutation -> Syntax.expression -> unit

type argument_form = Marked of T.mode * Syntax.expression | Place | Lent of T.mode | Temporary

val lent_field : state -> Syntax.expression -> Unify.T.ty -> T.mode option
val check_mode : state -> env -> Syntax.expression -> T.parameter_info -> Unify.T.ty -> unit
val check_lent_value : state -> env -> Syntax.expression -> unit
val check_owned : state -> env -> Syntax.expression -> Unify.T.ty -> unit
