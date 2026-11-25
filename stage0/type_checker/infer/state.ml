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
  binds_view : bool;
}

let runs (env : env) = not (env.specification || env.compile_time)
let is_compiled (env : env) = not env.specification

type subset_constraint = {
  subset : Types.capability_set;
  restriction : Types.capability_set option;
  superset : Types.capability_set;
  report_missing : Types.capability_set -> unit;
}

type requirement = Implements of Types.trait_reference | Within of Language.Builtin_type.t list

type cause =
  | Bound of { at : Core.origin; of_type : Types.ty option }
  | Operator of { at : Core.origin; operands : (Core.origin * Core.origin) option }
  | Method_call of Core.origin
  | Loop of Core.origin
  | Quantifier of Core.origin
  | Excluded of (Types.ty -> Catalog.reported)

type origin =
  | List_literal of Syntax.id
  | Map_literal of Syntax.id
  | Generic_argument of { written : Syntax.id; parameter : Types.generic; declared_on : Path.t }

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
  mutable reported_unmet_bounds : (Types.ty * Types.trait_reference * Catalog.reported) list;
  mutable compiled_expressions : int list;
  mutable compiled_bindings : int list;
  mutable specification_only_report : Catalog.reported option;
  origin : Core.origin;
}

type decision_site = Catalog.Inference.decision_site =
  | Use
  | Statement_end
  | Actual_head
  | Method_call

type entry =
  | Literal of {
      allowed : Language.Builtin_type.t list;
      report_excluded : Types.ty -> Catalog.reported;
      literal : Syntax.id;
    }
  | Narrowing of {
      allowed : Language.Builtin_type.t list;
      report_excluded : Types.ty -> Catalog.reported;
    }
  | Local of Syntax.id
  | Origin of origin
  | Decided of { site : decision_site; decided_type : Types.ty; decided_at : Core.origin }

type logged = { member : int; entry : entry }

type state = {
  lookups : Lookups.t;
  key : Resolve.Names.key;
  package : Path.package;
  definition : Syntax.definition;
  resolved : Resolve.resolved;
  order : Source.Node_order.t;
  signatures : Signatures.t;
  visible_packages : Path.package list Lazy.t;
  tables : Tables.t;
  mutable diagnostics : Catalog.diagnostic list;
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
  mutable lambdas : Syntax.id list;
  mutable unsolved : Catalog.reported option;
  mutable capability_constraints : subset_constraint list;
  mutable capability_solution : (int, Types.capability_set) Hashtbl.t option;
  mutable evidence_packages : Path.package list;
  mutable final_type_checks : (unit -> unit) list;
  mutable log : logged list;
  annotatable : (Syntax.id, unit) Hashtbl.t;
}

let record_diagnostic state (diagnostic : Catalog.diagnostic) =
  state.diagnostics <- diagnostic :: state.diagnostics;
  Catalog.make_reported diagnostic

let add_diagnostic state diagnostic = record_diagnostic state (Catalog.Inference diagnostic)
let report state diagnostic = ignore (add_diagnostic state diagnostic)
let is_formula env = env.specification || env.in_quantifier

let reject_in_formula state env at construct =
  if is_formula env then report state (Runs_in_formula { at; construct })

let read_context state = state.unifier.mode.context
let contains state ~outer ~inner = Source.Node_order.contains state.order ~outer ~inner
let compare_in_source_order state left right = Source.Node_order.compare state.order left right
let raise_bug format = Compiler_bug.raise_bug ~stage:"Infer" format
let make_error_type state diagnostic = Types.Error (add_diagnostic state diagnostic)

let rec mark_lent_tails state (value : Syntax.expression) =
  match value.kind with
  | Parenthesized inner -> mark_lent_tails state inner
  | If { then_; else_ = Some else_; _ } -> (
      mark_lent_block state then_;
      match else_ with
      | Else block -> mark_lent_block state block
      | Else_if nested -> mark_lent_tails state nested)
  | Match { arms; _ } ->
      List.iter
        (fun (arm : Syntax.arm) ->
          match arm.body.kind with Expression body -> mark_lent_tails state body | _ -> ())
        arms
  | Block body -> mark_lent_block state body
  | Return _ | Todo | Unreachable -> ()
  | _ -> Hashtbl.replace state.lent_tails value.id ()

and mark_lent_block state (body : Syntax.block) =
  match List.rev body.statements with
  | { kind = Expression value; _ } :: _ -> mark_lent_tails state value
  | _ -> ()

let read_current_frame state =
  match state.frames with frame :: _ -> frame | [] -> raise_bug "a check runs outside every frame"

let record state (value : Syntax.expression) type_ =
  state.tables.types.(value.id) <- Some type_;
  let frame = read_current_frame state in
  frame.recorded_expressions <- value.id :: frame.recorded_expressions

let note_compiled_expression state env (value : Syntax.expression) =
  if is_compiled env then
    let frame = read_current_frame state in
    frame.compiled_expressions <- value.id :: frame.compiled_expressions

let report_specification_only state diagnostic =
  let frame = read_current_frame state in
  match frame.specification_only_report with
  | Some report -> report
  | None ->
      let report = add_diagnostic state diagnostic in
      frame.specification_only_report <- Some report;
      report

let reject_specification_only_type state ~subject at type_ =
  Option.map
    (fun specification_type ->
      report_specification_only state
        (Specification_only_type { at; subject; type_; specification_type }))
    (Types.find_specification_only_type type_)

let with_mode (state : state) mode run =
  let enclosing = state.unifier.mode in
  state.unifier.mode <- mode;
  Fun.protect ~finally:(fun () -> state.unifier.mode <- enclosing) run

let with_added_condition (state : state) condition run =
  let mode = state.unifier.mode in
  with_mode state
    { mode with context = Interface.Elaborator.add_condition mode.context condition }
    run

let keep_mode (state : state) run =
  let mode = state.unifier.mode in
  fun argument -> with_mode state mode (fun () -> run argument)

let check_when_final state check =
  state.final_type_checks <- keep_mode state check :: state.final_type_checks

let resolve state type_ = Unify.resolve state.unifier type_
let zonk state type_ = Unify.zonk state.unifier type_
let record_in_log state member entry = state.log <- { member; entry } :: state.log

let list_class_log state index =
  let root = Unify.read_root state.unifier index in
  List.rev
    (List.filter
       (fun (logged : logged) -> Unify.read_root state.unifier logged.member = root)
       state.log)

let find_class_origin state index =
  List.find_map
    (function { member; entry = Origin origin } -> Some (member, origin) | _ -> None)
    (list_class_log state index)

let make_fresh_type state origin =
  let fresh = Unify.make_fresh_type state.unifier in
  record_in_log state state.unifier.next (Origin origin);
  fresh

let make_fresh_generic_arguments state generics (origin_of : Types.generic -> origin) =
  List.map
    (fun generic ->
      let argument = Unify.make_fresh_argument state.unifier generic in
      record_in_log state state.unifier.next (Origin (origin_of generic));
      argument)
    generics

let lookup_bounds state = Interface.Elaborator.list_known_bounds (read_context state)

let reduce_condition state (condition : Types.condition) =
  Interface.Impls.decide_condition state.lookups.interface ~list_bounds:(lookup_bounds state)
    condition

let record_condition state id (written : Syntax.condition option) =
  let condition =
    reduce_condition state
      (Option.fold ~none:[]
         ~some:(Interface.Elaborator.elaborate_condition (read_context state))
         written)
  in
  state.tables.conditions.(id) <- condition;
  condition

let normalize state type_ =
  let zonked = zonk state type_ in
  if
    Types.exists
      (function
        | Types.Projection _ as projection -> Unify.list_unknowns state.unifier projection <> []
        | _ -> false)
      zonked
  then raise_bug "`%s` holds a projection of an unknown" (Types.show zonked);
  Interface.Impls.normalize state.lookups.interface ~list_bounds:(lookup_bounds state) zonked

let check_compiled_binding state (id : Syntax.id) =
  match state.tables.local_types.(id) with
  | Some type_ -> (
      match
        reject_specification_only_type state ~subject:(Binding_subject (Written id)) (Written id)
          (normalize state type_)
      with
      | Some report ->
          let poisoned = Types.Error report in
          state.tables.local_types.(id) <- Some poisoned;
          Option.iter
            (fun local -> Hashtbl.replace state.locals id { local with type_ = poisoned })
            (Hashtbl.find_opt state.locals id)
      | None -> ())
  | None -> ()

let check_compiled_expression state (id : Syntax.id) =
  Option.iter
    (fun type_ ->
      ignore
        (reject_specification_only_type state ~subject:Value_subject (Written id)
           (normalize state type_)))
    state.tables.types.(id)

let find_domain state type_ =
  match resolve state type_ with
  | Types.Variable index -> Unify.find_domain state.unifier index
  | _ -> None

let is_float_domain domain = List.exists (fun member -> List.mem member Types.float_types) domain
let is_within state type_ set = Unify.is_within state.unifier (normalize state type_) set

let read_integer_range state type_ =
  match
    List.filter_map
      (fun member -> Types.find_integer_range (Types.make_builtin member))
      (Unify.list_possible_members state.unifier (normalize state type_))
  with
  | [] -> raise_bug "`%s` may be no integer type" (Types.show (zonk state type_))
  | first :: rest ->
      List.fold_left
        (fun (low, high) (other_low, other_high) -> (Z.max low other_low, Z.min high other_high))
        first rest

let make_literal_type state (value : Syntax.expression) allowed ~report_excluded =
  let literal = Unify.make_fresh_number state.unifier allowed in
  record_in_log state state.unifier.next
    (Literal { allowed; report_excluded = keep_mode state report_excluded; literal = value.id });
  literal

let record_narrowing state member ~allowed ~report_excluded =
  record_in_log state member
    (Narrowing { allowed; report_excluded = keep_mode state report_excluded })

let record_decided state member ~site ~decided_type ~at =
  record_in_log state member (Decided { site; decided_type; decided_at = at })

let read_unsolved_report state =
  match state.unsolved with
  | Some report -> report
  | None -> raise_bug "an unknown value outlived its statement, and no statement reported it"

let resolve_capabilities state (capabilities : Types.capability_set) =
  match state.capability_solution with
  | Some solution when Types.contains_capability_variable capabilities ->
      Types.replace_capabilities
        (function
          | Types.Capability_variable variable ->
              Some
                (Option.value ~default:Types.no_capabilities (Hashtbl.find_opt solution variable))
          | _ -> None)
        capabilities
  | _ -> capabilities

let rec finalize_type state type_ =
  Types.map ~map_capabilities:(finalize_capabilities state)
    (function
      | Types.Variable _ -> raise_bug "an unknown type outlived the statement that reported it"
      | _ -> None)
    (normalize state type_)

and finalize_capabilities state capabilities =
  resolve_capabilities state
    (Interface.Impls.normalize_capabilities state.lookups.interface
       ~list_bounds:(lookup_bounds state)
       (Types.map_capability_types (finalize_type state) (finalize_trait state) capabilities))

and finalize_trait state (trait : Types.trait_reference) : Types.trait_reference =
  {
    trait with
    trait_arguments = List.map (finalize_argument state) trait.trait_arguments;
    associated = List.map (fun (name, type_) -> (name, finalize_type state type_)) trait.associated;
  }

and finalize_argument state = function
  | Types.Type type_ -> Types.Type (finalize_type state type_)
  | Types.Value value -> (
      match Unify.resolve_value state.unifier value with
      | Types.Value_variable _ -> Types.Value (Types.Value_error (read_unsolved_report state))
      | value -> Types.Value value)

let unify ?modulo_views state left right =
  Unify.unify ?modulo_views state.unifier (normalize state left) (normalize state right)

let unify_as_hint state actual expected =
  let is_output index =
    List.exists
      (fun goal ->
        List.exists (fun (_, output) -> resolve state output = Variable index) goal.outputs)
      state.goals
  in
  let skip_outputs type_ =
    Types.map
      (function
        | Types.Variable index when is_output index -> Some (Unify.make_fresh_type state.unifier)
        | _ -> None)
      (zonk state type_)
  in
  let deferred_capability_equalities = state.unifier.deferred_capability_equalities in
  ignore (unify state (skip_outputs actual) (skip_outputs expected));
  state.unifier.deferred_capability_equalities <- deferred_capability_equalities

let normalize_trait state trait =
  Types.map_trait (normalize state) (Unify.zonk_trait state.unifier trait)

let find_evidence state type_ trait =
  Interface.Impls.find_evidence state.lookups.interface ~list_bounds:(lookup_bounds state)
    (normalize state type_) (normalize_trait state trait)

let elaborate state id elaboration = state.tables.elaborations.(id) <- Some elaboration

let decide_property state property type_ =
  Interface.Impls.decide_property property state.lookups.interface
    ~list_bounds:(lookup_bounds state) (zonk state type_)

let rec diverges ~is_never (written : Syntax.statement) =
  match written.kind with
  | Expression value | Let { value; _ } | Assignment { value; _ } -> is_never value
  | While { condition = { kind = True; _ }; body; _ } -> not (Syntax_walk.contains_break body)
  | Parallel body | Concurrent body -> List.exists (diverges ~is_never) body.statements
  | _ -> false

let declare state (name : Syntax.name) type_ ~binding ~mode =
  Hashtbl.replace state.locals name.id { name = name.text; type_; binding; mode };
  state.tables.local_types.(name.id) <- Some type_;
  let frame = read_current_frame state in
  frame.bindings <- name.id :: frame.bindings;
  match resolve state type_ with
  | Types.Variable index when Option.is_some (Unify.find_domain state.unifier index) ->
      record_in_log state index (Local name.id)
  | _ -> ()

let declare_compiled state env (name : Syntax.name) type_ ~binding ~mode =
  declare state name type_ ~binding ~mode;
  if is_compiled env then begin
    let frame = read_current_frame state in
    frame.compiled_bindings <- name.id :: frame.compiled_bindings;
    check_compiled_binding state name.id
  end

let find_target state (name : Syntax.name) = state.resolved.names.(name.id)
let find_head state (value : Syntax.expression) = Resolve.find_head state.resolved value

let make_shown state type_ : Catalog.Inference.shown =
  match find_domain state type_ with
  | Some domain -> if is_float_domain domain then Some_float else Some_integer
  | None -> Exactly (zonk state type_)

let note_mode_keyword state (written : Syntax.expression) (mode : Syntax.mode)
    (operand : Syntax.expression) =
  let rec strip_parentheses (value : Syntax.expression) =
    match value.kind with Parenthesized inner -> strip_parentheses inner | _ -> value
  in
  let place =
    match Places.find_keyword_operation state.resolved state.tables operand with
    | Some (_, receiver) -> receiver
    | None -> operand
  in
  state.mode_keywords <-
    {
      mode = (match mode with Mut -> Mut | Own -> Own);
      written = written.id;
      operand = operand.id;
      place = (strip_parentheses place).id;
    }
    :: state.mode_keywords

let find_local state (name : Syntax.name) =
  match find_target state name with
  | Some (Local id) -> Hashtbl.find_opt state.locals id
  | _ -> None

let find_local_type state (name : Syntax.name) =
  Option.map (fun (local : local) -> resolve state local.type_) (find_local state name)
