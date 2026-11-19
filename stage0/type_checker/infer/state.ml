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
  is_specification : bool;
}

type frame = {
  first_variable : int;
  mutable recorded_expressions : int list;
  mutable bindings : int list;
  mutable goals : goal list;
  mutable reported_unmet_bounds : (Types.ty * Types.trait_reference * Diagnostic.reported) list;
  mutable compiled_expressions : int list;
  mutable compiled_bindings : int list;
  mutable specification_only_report : Diagnostic.reported option;
  frame_specification : bool;
  span : Source.Definition_span.t;
}

type default_site = Statement_end | Actual_head | Method_call | Definition_end

type decision = {
  decided_type : Types.ty;
  decided_at : Source.Definition_span.t;
  mutable decision_report : Diagnostic.reported option;
}

type entry =
  | Literal of {
      allowed : Language.Builtin_type.t list;
      report_excluded : Types.ty -> Diagnostic.reported;
      literal_at : Source.Definition_span.t;
    }
  | Narrowing of {
      allowed : Language.Builtin_type.t list;
      report_excluded : Types.ty -> Diagnostic.reported;
    }
  | Local of Syntax.id
  | Decision of decision
  | Default of { site : default_site; decision : decision; waiting : goal list }

type logged = { member : int; entry : entry }

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
  mutable log : logged list;
  annotatable : (Syntax.id, unit) Hashtbl.t;
}

let add_diagnostic state ?notes ?(fixes = []) code (span : Source.Definition_span.t) message =
  let diagnostic = Diagnostic.make ?notes ~fixes ~code:(Types code) span message in
  state.diagnostics <- diagnostic :: state.diagnostics;
  Diagnostic.make_reported diagnostic

let report state ?fixes code span message = ignore (add_diagnostic state ?fixes code span message)
let is_formula env = env.specification || env.in_quantifier

let reject_in_formula state env span what =
  if is_formula env then
    report state Not_in_specification span
      (Printf.sprintf
         "%s runs, so it cannot be part of a specification, a proof, or a quantifier's body, which \
          the prover reads as formulas: they are built from `let`, `if`, `match`, and calls."
         what)

let read_span state id = Interface.Elaborator.read_span state.context id
let raise_bug format = Compiler_bug.raise_bug ~stage:"Infer" format

let make_error_type state ?fixes code span message =
  Types.Error (add_diagnostic state ?fixes code span message)

let quote_span state span = Source.Definition_span.quote (Lazy.force state.text) span

let allocate_node_id state =
  let id = state.form.next_node_id in
  state.form.next_node_id <- id + 1;
  id

let make_synthetic_expression state ~origin type_ kind : Core.expression =
  { id = allocate_node_id state; origin; type_; kind }

let register_expression state (value : Syntax.expression) make_kind =
  state.form.expression_builders.(value.id) <-
    Some
      (fun () ->
        let id = allocate_node_id state in
        match state.tables.types.(value.id) with
        | Some type_ -> { Core.id; origin = value.id; type_; kind = make_kind () }
        | None ->
            raise_bug "`%s` has a node and no type" (quote_span state (read_span state value.id)))

let was_hole state (select_table : Tables.t -> Types.ty option array) (id : Syntax.id) =
  match state.form.tables_with_holes with
  | Some tables -> (select_table tables).(id) = Some Types.Hole
  | None -> false

let rec list_operands state (value : Syntax.expression) : Syntax.expression list =
  let list_checked (part : Syntax.expression) =
    if Option.is_some state.form.expression_builders.(part.id) then [ part ]
    else list_operands state part
  in
  match value.kind with
  | Match { scrutinees; _ } -> List.concat_map list_checked scrutinees
  | Quantified { binder = Binder_in (_, collection); _ } -> list_checked collection
  | Quantified { binder = Binder_type _; _ } -> []
  | If _ | Parenthesized _ | Mode _ -> []
  | _ ->
      let checked_parts = ref [] in
      Syntax_walk.visit_expression_parts ~on_statement:ignore value ~on_expression:(fun part ->
          checked_parts := list_checked part :: !checked_parts);
      List.concat (List.rev !checked_parts)

let rec build_expression state (value : Syntax.expression) : Core.expression =
  let evaluated =
    if Option.is_some state.form.tables_with_holes then list_operands state value else []
  in
  if
    List.exists
      (fun (operand : Syntax.expression) -> was_hole state (fun tables -> tables.types) operand.id)
      evaluated
  then begin
    let evaluate (operand : Syntax.expression) : Core.statement option =
      match operand.kind with
      | Lambda _ -> None
      | _ ->
          let node = build_expression state operand in
          Some
            {
              id = allocate_node_id state;
              origin = operand.id;
              kind =
                Let
                  {
                    pattern =
                      {
                        id = allocate_node_id state;
                        origin = operand.id;
                        type_ = node.type_;
                        kind = Wildcard;
                      };
                    value = Operands.build Read node;
                    else_ = None;
                  };
            }
    in
    let statements = List.filter_map evaluate evaluated in
    let todo = make_synthetic_expression state ~origin:value.id Types.Never Todo in
    make_synthetic_expression state ~origin:value.id Types.Never
      (Block { statements; value = Some todo })
  end
  else
    match state.form.expression_builders.(value.id) with
    | Some build -> build ()
    | None ->
        raise_bug "`%s` has no node in the core form" (quote_span state (read_span state value.id))

let register_statement state (written : Syntax.statement) make_kind =
  state.form.statement_builders.(written.id) <-
    Some (fun () -> { Core.id = allocate_node_id state; origin = written.id; kind = make_kind () })

let build_statement state (written : Syntax.statement) : Core.statement =
  let rec strip_mode_keyword (value : Syntax.expression) =
    match value.kind with
    | Mode (_, inner) | Parenthesized inner -> strip_mode_keyword inner
    | _ -> value
  in
  let find_hole (value : Syntax.expression) =
    let value = strip_mode_keyword value in
    if was_hole state (fun tables -> tables.types) value.id then Some value else None
  in
  match
    match written.kind with
    | For { iterable; _ } -> find_hole iterable
    | Assignment { target; _ } -> find_hole target
    | _ -> None
  with
  | Some value ->
      {
        id = allocate_node_id state;
        origin = written.id;
        kind = Evaluate (build_expression state value);
      }
  | None -> (
      match state.form.statement_builders.(written.id) with
      | Some build -> build ()
      | None ->
          raise_bug "`%s` has no node in the core form"
            (quote_span state (read_span state written.id)))

let register_pattern state (written : Syntax.pattern) make_kind =
  state.form.pattern_builders.(written.id) <-
    Some
      (fun () ->
        let id = allocate_node_id state in
        match state.tables.scrutinee_types.(written.id) with
        | Some type_ -> { Core.id; origin = written.id; type_; kind = make_kind () }
        | None ->
            raise_bug "`%s` has a node and no type" (quote_span state (read_span state written.id)))

let build_pattern state (written : Syntax.pattern) : Core.pattern =
  if was_hole state (fun tables -> tables.scrutinee_types) written.id then
    { id = allocate_node_id state; origin = written.id; type_ = Types.Never; kind = Wildcard }
  else
    match state.form.pattern_builders.(written.id) with
    | Some build -> build ()
    | None ->
        raise_bug "`%s` has no node in the core form"
          (quote_span state (read_span state written.id))

let alias_expression state (value : Syntax.expression) (inner : Syntax.expression) =
  state.form.expression_builders.(value.id) <- Some (fun () -> build_expression state inner)

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

let make_place (node : Core.expression) : Core.place =
  match node.kind with Use place -> place | _ -> Temporary node

let allocate_synthetic_local state : Core.local =
  let number = state.form.next_synthetic_local in
  state.form.next_synthetic_local <- number + 1;
  Synthetic number

let fix title edits = Diagnostic.fix title edits
let replace = Diagnostic.replace
let insert position text = Diagnostic.insert (Source.Definition_span.make_zero_width position) text

let read_current_frame state =
  match state.frames with frame :: _ -> frame | [] -> raise_bug "a check runs outside every frame"

let record state (value : Syntax.expression) type_ =
  state.tables.types.(value.id) <- Some type_;
  let frame = read_current_frame state in
  frame.recorded_expressions <- value.id :: frame.recorded_expressions

let record_loop state ~loop record = state.tables.loops.(loop) <- Some record

let note_compiled_expression state env (value : Syntax.expression) =
  if is_compiled env then
    let frame = read_current_frame state in
    frame.compiled_expressions <- value.id :: frame.compiled_expressions

let report_specification_only state span message =
  let frame = read_current_frame state in
  match frame.specification_only_report with
  | Some report -> report
  | None ->
      let report = add_diagnostic state Specification_only span message in
      frame.specification_only_report <- Some report;
      report

let reject_specification_only_type state ~subject span type_ =
  Option.map
    (fun specification_type ->
      report_specification_only state span
        (if Types.equal type_ specification_type then
           Printf.sprintf
             "%s has the type `%s`, which exists only in specifications and has no representation \
              in code that runs."
             subject (Types.show type_)
         else
           Printf.sprintf
             "%s has the type `%s`, which holds `%s`. `%s` exists only in specifications and has \
              no representation in code that runs."
             subject (Types.show type_) (Types.show specification_type)
             (Types.show specification_type)))
    (Types.find_specification_only_type type_)

let check_compiled_binding state (id : Syntax.id) =
  match state.tables.local_types.(id) with
  | Some type_ -> (
      let span = read_span state id in
      match
        reject_specification_only_type state
          ~subject:(Printf.sprintf "`%s`" (quote_span state span))
          span (Unify.zonk state.unifier type_)
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
      ignore (reject_specification_only_type state ~subject:"This value" (read_span state id) type_))
    state.tables.types.(id)

let compare_in_source_order state left right =
  let left : Source.Definition_span.t = read_span state left
  and right : Source.Definition_span.t = read_span state right in
  compare (left.start, -left.stop) (right.start, -right.stop)

let check_when_final state check = state.final_type_checks <- check :: state.final_type_checks
let resolve state type_ = Unify.resolve state.unifier type_
let zonk state type_ = Unify.zonk state.unifier type_
let make_fresh_type state = Unify.make_fresh_type state.unifier

let make_fresh_generic_arguments state (generics : Types.generic list) =
  List.map
    (fun (generic : Types.generic) ->
      match generic.kind with
      | Value_generic -> Types.Value (Unify.make_fresh_value state.unifier)
      | Type_generic _ -> Types.Type (make_fresh_type state))
    generics

let lookup_bounds state parameter = Interface.Elaborator.list_bounds state.context parameter

let normalize state type_ =
  Interface.Impls.normalize state.lookups.interface ~list_bounds:(lookup_bounds state)
    (zonk state type_)

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

let record_in_log state member entry = state.log <- { member; entry } :: state.log

let make_literal_type state ~at allowed ~report_excluded =
  let literal = Unify.make_fresh_number state.unifier allowed in
  record_in_log state state.unifier.next (Literal { allowed; report_excluded; literal_at = at });
  literal

let make_unsolved_type state =
  match state.unsolved with
  | Some report -> Types.Error report
  | None ->
      let report =
        add_diagnostic state Cannot_infer
          (Source.Definition_span.make (read_span state state.definition.id).start
             (read_span state state.definition.id).start)
          "A type in this definition cannot be inferred. Give the `let` a type, or the call type \
           arguments."
      in
      state.unsolved <- Some report;
      Types.Error report

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
      | Types.Variable _ -> Some (make_unsolved_type state)
      | Types.Hole when Option.is_some state.form.tables_with_holes -> Some Types.Never
      | _ -> None)
    (normalize state type_)

and finalize_capabilities state capabilities =
  resolve_capabilities state
    (Interface.Impls.normalize_capabilities state.lookups.interface
       ~list_bounds:(lookup_bounds state)
       (Types.replace_capabilities
          (function
            | Types.Capability_projection { base; trait; name } ->
                Some
                  (Types.make_capability_set
                     [
                       Types.Capability_projection { base = finalize_type state base; trait; name };
                     ])
            | _ -> None)
          capabilities))

and finalize_argument state = function
  | Types.Type type_ -> Types.Type (finalize_type state type_)
  | Types.Value value -> (
      match Unify.resolve_value state.unifier value with
      | Types.Value_variable _ -> Types.Type (make_unsolved_type state)
      | value -> Types.Value value)

let finalize_instantiation state (instantiation : Types.instantiation) : Types.instantiation =
  {
    type_arguments = List.map (finalize_argument state) instantiation.type_arguments;
    capability_arguments =
      List.map
        (fun (name, argument) -> (name, finalize_capabilities state argument))
        instantiation.capability_arguments;
  }

let unify state left right =
  let normalize type_ =
    Interface.Impls.normalize state.lookups.interface ~list_bounds:(lookup_bounds state)
      (Unify.zonk state.unifier type_)
  in
  Unify.unify state.unifier (normalize left) (normalize right)

let unify_as_hint state actual expected =
  let deferred_capability_equalities = state.unifier.deferred_capability_equalities in
  ignore (unify state actual expected);
  state.unifier.deferred_capability_equalities <- deferred_capability_equalities

let normalize_trait state (trait : Types.trait_reference) : Types.trait_reference =
  {
    trait with
    trait_arguments =
      List.map
        (function Types.Type type_ -> Types.Type (normalize state type_) | other -> other)
        (Unify.zonk_trait state.unifier trait).trait_arguments;
    associated = List.map (fun (name, type_) -> (name, normalize state type_)) trait.associated;
  }

let find_evidence state type_ trait =
  Interface.Impls.find_evidence state.lookups.interface ~list_bounds:(lookup_bounds state)
    (normalize state type_) (normalize_trait state trait)

let decide_property state property type_ =
  Interface.Impls.decide_property property state.lookups.interface
    ~list_bounds:(lookup_bounds state) (zonk state type_)

let is_plain state type_ =
  Interface.Impls.is_plain state.lookups.interface ~list_bounds:(lookup_bounds state)
    (zonk state type_)

let is_view state type_ =
  Interface.Impls.is_view state.lookups.interface ~list_bounds:(lookup_bounds state)
    (zonk state type_)

let decide_binding_mode state (mode : Language.Mode.t) type_ : Language.Mode.t =
  match mode with Read when is_plain state type_ -> Own | Read | Mut | Own -> mode

let rec copy_plain_bindings state (pattern : Core.pattern) : Core.pattern =
  let copy_fields = List.map (fun (field, inner) -> (field, copy_plain_bindings state inner)) in
  match pattern.kind with
  | Bind bound ->
      let mode = decide_binding_mode state bound.mode pattern.type_ in
      { pattern with kind = Bind { bound with mode } }
  | Variant { variant; fields } ->
      { pattern with kind = Variant { variant; fields = copy_fields fields } }
  | Record fields -> { pattern with kind = Record (copy_fields fields) }
  | Alternatives alternatives ->
      { pattern with kind = Alternatives (List.map (copy_plain_bindings state) alternatives) }
  | Wildcard | Literal _ | Range _ | Equal_to _ -> pattern

let build_scrutinee_pattern state written = copy_plain_bindings state (build_pattern state written)

let resolve_associated_type state type_ (trait : Types.trait_reference) associated
    ~(at : Source.Definition_span.t) =
  let type_ = normalize state type_ and trait = normalize_trait state trait in
  let name = Well_known.show_associated associated in
  match
    Interface.Impls.project_associated_type state.lookups.interface
      ~list_bounds:(lookup_bounds state) type_ trait name
  with
  | Some associated_type -> associated_type
  | None ->
      make_error_type state Unknown_associated_type at
        (Printf.sprintf "`%s` gives no `%s` as a `%s`." (Types.show type_) name
           (Types.show_trait trait))

let make_callee state (target : Core.operand Core.target) =
  Callee_uses.make_callee state.lookups.interface ~list_bounds:(lookup_bounds state) target

let make_call state ~callee ~arguments ~lends =
  Callee_uses.make_call state.lookups.interface ~list_bounds:(lookup_bounds state) ~callee
    ~arguments ~lends

let make_trait_reference ~arguments trait : Types.trait_reference =
  { trait; trait_arguments = arguments; associated = [] }

let string_type = Types.Named { path = Well_known.make_path String; arguments = [] }

let make_default_type domain =
  match
    List.filter
      (fun default -> List.mem default domain)
      [ Language.Builtin_type.Integer; Int64; UInt64; Float64 ]
  with
  | Integer :: _ -> Types.Integer
  | default :: _ -> Types.make_builtin default
  | [] -> raise_bug "a number has no default type"

let holds_class state root type_ =
  List.exists
    (function Unify.Unknown_type index | Unknown_value index -> index = root)
    (Unify.list_unknowns state.unifier type_)

let find_refused_class state ~sides =
  Option.bind state.unifier.refused_code_unknown (fun root ->
      if List.exists (fun (side, _) -> holds_class state root side) sides then Some root else None)

let report_decided_in_specification state span root =
  let message =
    match
      Array.find_index
        (Option.fold ~none:false ~some:(holds_class state root))
        state.tables.local_types
    with
    | Some local ->
        let name = quote_span state (read_span state local) in
        Printf.sprintf "A specification cannot decide the type of `%s`. Declare `%s` with a type."
          name name
    | None ->
        "A specification cannot decide a type that code computes with. Give the call its type \
         arguments."
  in
  let report = add_diagnostic state Decided_in_specification span message in
  Hashtbl.replace state.unifier.type_solutions root (Types.Error report);
  report

let list_goal_inputs state goal =
  match goal.requirement with
  | Implements trait ->
      List.concat_map
        (Unify.list_argument_unknowns state.unifier)
        (Types.Type goal.subject :: trait.trait_arguments)
  | Within _ -> Unify.list_unknowns state.unifier goal.subject

let decide_default state ~site ~at type_ =
  match (resolve state type_, find_domain state type_) with
  | Types.Variable root, Some domain -> (
      let default = make_default_type domain in
      let waiting =
        List.filter
          (fun goal -> List.mem (Unify.Unknown_type root) (list_goal_inputs state goal))
          (List.concat_map (fun frame -> frame.goals) state.frames)
      in
      ignore (Unify.unify state.unifier type_ default);
      match find_refused_class state ~sides:[ (type_, default) ] with
      | Some refused -> Types.Error (report_decided_in_specification state at refused)
      | None ->
          let decision = { decided_type = default; decided_at = at; decision_report = None } in
          record_in_log state root (Default { site; decision; waiting });
          default)
  | _ -> type_

let record_narrowing state member ~allowed ~report_excluded =
  record_in_log state member (Narrowing { allowed; report_excluded })

let record_failure state goal report =
  List.iter
    (function
      | { entry = Default { decision; waiting; _ }; _ }
        when List.memq goal waiting && Option.is_none decision.decision_report ->
          decision.decision_report <- Some report
      | _ -> ())
    state.log

let gives state index goal =
  List.exists (fun (_, output) -> resolve state output = Types.Variable index) goal.outputs

let default_inputs state ~site ~at goals =
  let frame = read_current_frame state in
  let rec force visited = function
    | Unify.Unknown_type index when not (List.mem index visited) -> (
        match List.filter (gives state index) frame.goals with
        | [] ->
            if Unify.may_decide state.unifier index then
              ignore (decide_default state ~site ~at (Types.Variable index));
            index :: visited
        | givers ->
            List.fold_left force (index :: visited)
              (List.concat_map (list_goal_inputs state) givers))
    | _ -> visited
  in
  ignore (List.fold_left force [] (List.concat_map (list_goal_inputs state) goals))

let record_decisions state ~at =
  let decided = Hashtbl.create 8 in
  List.iter
    (fun { member; entry } ->
      let root = Unify.read_root state.unifier member in
      match (entry, resolve state (Types.Variable root)) with
      | (Decision _ | Default _), _ -> Hashtbl.replace decided root ()
      | Literal _, Types.Variable _ | (Narrowing _ | Local _), _ -> ()
      | Literal _, decided_type ->
          if not (Hashtbl.mem decided root) then begin
            Hashtbl.replace decided root ();
            record_in_log state root
              (Decision
                 { decided_type = zonk state decided_type; decided_at = at; decision_report = None })
          end)
    state.log

let settle state frame ~solve =
  List.iter
    (fun (left, right) ->
      let report_missing _ =
        report state Mismatch frame.span
          (Printf.sprintf
             "Two function types here must use the same capabilities, and one uses `%s` where the \
              other uses `%s`."
             (Types.show_capabilities (resolve_capabilities state left))
             (Types.show_capabilities (resolve_capabilities state right)))
      in
      state.capability_constraints <-
        { subset = left; restriction = None; superset = right; report_missing }
        :: { subset = right; restriction = None; superset = left; report_missing }
        :: state.capability_constraints)
    state.unifier.deferred_capability_equalities;
  state.unifier.deferred_capability_equalities <- [];
  solve frame;
  let parent = match state.frames with _ :: parent :: _ -> Some parent | _ -> None in
  let is_owned = function
    | Unify.Unknown_type index | Unknown_value index ->
        index >= frame.first_variable && Option.is_none (Unify.find_domain state.unifier index)
  in
  (match parent with
  | Some _ ->
      default_inputs state ~site:Statement_end ~at:frame.span
        (List.filter
           (fun goal ->
             List.exists
               (fun (_, output) -> List.exists is_owned (Unify.list_unknowns state.unifier output))
               goal.outputs)
           frame.goals)
  | None ->
      let rec default_goal_inputs () =
        let before = state.log in
        default_inputs state ~site:Definition_end ~at:frame.span frame.goals;
        if state.log != before then begin
          solve frame;
          default_goal_inputs ()
        end
      in
      default_goal_inputs ();
      List.iter
        (function
          | { member; entry = Literal _ } ->
              ignore
                (decide_default state ~site:Definition_end ~at:frame.span (Types.Variable member))
          | _ -> ())
        state.log);
  solve frame;
  let list_types ids table = List.filter_map (fun id -> table.(id)) ids in
  let list_all_types () =
    list_types frame.recorded_expressions state.tables.types
    @ list_types frame.bindings state.tables.local_types
  in
  let list_call_arguments () =
    List.concat_map
      (fun id ->
        match state.tables.calls.(id) with
        | Some { callee = Trait_method { trait; instantiation; _ }; _ } ->
            trait.trait_arguments @ instantiation.type_arguments
        | Some
            {
              callee =
                ( Function { instantiation = { type_arguments; _ }; _ }
                | Constructor { type_arguments; _ }
                | Intrinsic { type_arguments; _ } );
              _;
            } ->
            type_arguments
        | _ -> [])
      frame.recorded_expressions
  in
  let list_goal_unknowns goal =
    list_goal_inputs state goal
    @ List.concat_map (fun (_, output) -> Unify.list_unknowns state.unifier output) goal.outputs
  in
  let list_unknowns () =
    List.concat_map (Unify.list_unknowns state.unifier) (list_all_types ())
    @ List.concat_map (Unify.list_argument_unknowns state.unifier) (list_call_arguments ())
    @ List.concat_map list_goal_unknowns frame.goals
  in
  let unsolved = List.filter is_owned (list_unknowns ()) in
  if unsolved <> [] then begin
    let list_trait_unknowns (trait : Types.trait_reference) =
      List.concat_map (Unify.list_argument_unknowns state.unifier) trait.trait_arguments
    in
    let undetermined =
      List.filter_map
        (fun goal ->
          match (goal.cause, goal.requirement) with
          | ((Method_call at | Loop at) as cause), Implements trait
            when (not (Types.contains_unsolved (zonk state goal.subject)))
                 && List.exists
                      (fun unknown -> List.mem unknown unsolved)
                      (list_trait_unknowns trait) ->
              Some
                ( add_diagnostic state Cannot_infer at
                    (Printf.sprintf
                       (match cause with
                       | Loop _ ->
                           "This loop does not determine the arguments of `%s`, whose methods give \
                            its elements."
                       | _ ->
                           "This call does not determine the arguments of `%s`. Write the call in \
                            full with them.")
                       (match trait.trait with Top { name; _ } -> name | path -> Path.show path)),
                  list_trait_unknowns trait )
          | _ -> None)
        frame.goals
    in
    let explained = List.concat_map snd undetermined in
    let report =
      match undetermined with
      | (first, _) :: _ when List.for_all (fun unknown -> List.mem unknown explained) unsolved ->
          first
      | _ ->
          add_diagnostic state Cannot_infer frame.span
            "The types in this statement cannot be inferred from it alone. Give the `let` a type, \
             or the call type arguments, such as `var names: List[String] = []`."
    in
    if Option.is_none state.unsolved then state.unsolved <- Some report;
    List.iter
      (function
        | Unify.Unknown_type index ->
            Hashtbl.replace state.unifier.type_solutions index (Types.Error report)
        | Unknown_value _ -> ())
      unsolved;
    solve frame;
    frame.goals <-
      List.filter
        (fun goal ->
          not (List.exists (fun unknown -> List.mem unknown unsolved) (list_goal_unknowns goal)))
        frame.goals
  end;
  record_decisions state ~at:frame.span;
  let is_open unknown = not (is_owned unknown) in
  let finish table ids keep =
    List.iter
      (fun id ->
        match table.(id) with
        | Some type_ -> (
            let type_ =
              Interface.Impls.normalize state.lookups.interface ~list_bounds:(lookup_bounds state)
                (zonk state type_)
            in
            table.(id) <- Some type_;
            if List.exists is_open (Unify.list_unknowns state.unifier type_) then
              match parent with Some parent -> keep parent id | None -> ())
        | None -> ())
      ids
  in
  finish state.tables.types frame.recorded_expressions (fun parent id ->
      parent.recorded_expressions <- id :: parent.recorded_expressions);
  finish state.tables.local_types frame.bindings (fun parent id ->
      parent.bindings <- id :: parent.bindings);
  let is_settled table id =
    match table.(id) with
    | Some type_ -> not (List.exists is_open (Unify.list_unknowns state.unifier type_))
    | None -> true
  in
  let settled_bindings, open_bindings =
    List.partition (is_settled state.tables.local_types) (List.rev frame.compiled_bindings)
  in
  let settled_expressions, open_expressions =
    List.partition (is_settled state.tables.types) (List.rev frame.compiled_expressions)
  in
  Option.iter
    (fun parent ->
      parent.compiled_bindings <- List.rev_append open_bindings parent.compiled_bindings;
      parent.compiled_expressions <- List.rev_append open_expressions parent.compiled_expressions)
    parent;
  List.iter (check_compiled_binding state) settled_bindings;
  List.iter (check_compiled_expression state)
    (List.sort (compare_in_source_order state) settled_expressions);
  match (parent, frame.goals) with
  | Some parent, _ -> parent.goals <- frame.goals @ parent.goals
  | None, [] -> ()
  | None, _ :: _ -> raise_bug "a goal is pending at the end of the definition"

let run_in_statement state env (span : Source.Definition_span.t) ~solve body =
  let frame =
    {
      first_variable = state.unifier.next + 1;
      recorded_expressions = [];
      bindings = [];
      goals = [];
      reported_unmet_bounds = [];
      compiled_expressions = [];
      compiled_bindings = [];
      specification_only_report = None;
      frame_specification = env.specification;
      span;
    }
  in
  let enclosing_checks_specification = state.unifier.checks_specification in
  state.frames <- frame :: state.frames;
  state.unifier.checks_specification <- frame.frame_specification;
  let result = body () in
  settle state frame ~solve;
  state.frames <- List.tl state.frames;
  state.unifier.checks_specification <- enclosing_checks_specification;
  result

let rec diverges ~is_never (written : Syntax.statement) =
  match written.kind with
  | Expression value | Let { value; _ } | Assignment { value; _ } -> is_never value
  | While { condition = { kind = True; _ }; body; _ } -> not (Syntax_walk.contains_break body)
  | Parallel body | Concurrent body -> List.exists (diverges ~is_never) body.statements
  | _ -> false

let build_block state (written : Syntax.block) : Core.block =
  let rec build_statements (statements : Syntax.statement list) =
    match statements with
    | [] -> ([], None)
    | [ ({ kind = Expression value; _ } as last) ]
      when Option.is_none state.form.statement_builders.(last.id) ->
        ([], Some (build_expression state value))
    | first :: rest ->
        let first = build_statement state first in
        let rest, value = build_statements rest in
        (first :: rest, value)
  in
  let statements, value = build_statements written.statements in
  { statements; value }

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
let show state type_ = Types.show (zonk state type_)

let describe state type_ =
  match find_domain state type_ with
  | Some domain -> if is_float_domain domain then "a float" else "an integer"
  | None -> "`" ^ show state type_ ^ "`"

let list_class_entries state type_ =
  match type_ with
  | Types.Variable index ->
      let root = Unify.read_root state.unifier index in
      List.rev
        (List.filter_map
           (fun { member; entry } ->
             if Unify.read_root state.unifier member = root then Some entry else None)
           state.log)
  | _ -> []

let find_integer_literals state (side, wanted) =
  let entries = list_class_entries state side in
  match
    List.filter_map
      (function
        | Literal { allowed; literal_at; _ } when not (is_float_domain allowed) -> Some literal_at
        | _ -> None)
      entries
  with
  | _ :: _ as literals
    when is_within state wanted Types.float_types
         && not (List.exists (function Decision _ -> true | _ -> false) entries) ->
      Some (literals, wanted)
  | _ -> None

let find_explanation entry ~local ~decided =
  let took where = Printf.sprintf "%s took its default type, `%s`, %s." local decided where in
  match entry with
  | Decision _ ->
      Some
        ( Printf.sprintf "An earlier statement decided that the type of %s is `%s`." local decided,
          Printf.sprintf "This statement decides that the type of %s is `%s`." local decided )
  | Default { site = Statement_end; _ } ->
      Some
        ( took "at an earlier statement",
          Printf.sprintf
            "This statement needs the type of %s, so %s takes its default type `%s` here." local
            local decided )
  | Default { site = Actual_head; _ } ->
      Some
        ( took "where the type of an earlier value was needed",
          Printf.sprintf "The type of this value is needed here, so %s takes its default type `%s`."
            local decided )
  | Default { site = Method_call; _ } ->
      Some
        ( took "at an earlier method call",
          Printf.sprintf
            "Method lookup needs the type of %s, so %s takes its default type `%s` here." local
            local decided )
  | Default { site = Definition_end; _ } | Literal _ | Narrowing _ | Local _ -> None

let meets_goal state ~root candidate goal =
  let rec substitute type_ =
    Types.map
      (function
        | Types.Variable index when Unify.read_root state.unifier index = root -> Some candidate
        | Types.Variable _ as variable when resolve state variable <> variable ->
            Some (substitute (resolve state variable))
        | _ -> None)
      type_
  in
  let substitute_argument = function
    | Types.Type type_ -> Types.Type (substitute type_)
    | value -> value
  in
  match goal.requirement with
  | Within set -> is_within state (substitute goal.subject) set
  | Implements trait ->
      Option.is_some
        (find_evidence state (substitute goal.subject)
           {
             trait with
             trait_arguments = List.map substitute_argument trait.trait_arguments;
             associated =
               List.map
                 (fun (name, type_) -> (name, substitute type_))
                 (trait.associated @ goal.outputs);
           })

let find_log_report state ~fixes code span message (side, wanted) =
  let entries = list_class_entries state side in
  let is_same_kind =
    is_within state wanted
      (if
         List.exists
           (function Literal { allowed; _ } -> is_float_domain allowed | _ -> false)
           entries
       then Types.float_types
       else Integer :: Types.integer_types)
  in
  let wanted_type = normalize state wanted in
  match
    List.find_opt
      (function
        | Literal { allowed; _ } | Narrowing { allowed; _ } ->
            is_same_kind && not (is_within state wanted allowed)
        | Decision decision | Default { decision; _ } ->
            not (Types.equal decision.decided_type wanted_type)
        | Local _ -> false)
      entries
  with
  | Some (Literal { report_excluded; _ } | Narrowing { report_excluded; _ }) ->
      Some (report_excluded wanted)
  | Some ((Decision decision | Default { decision; _ }) as entry) -> (
      match
        ( decision.decision_report,
          List.find_map (function Local local -> Some local | _ -> None) entries )
      with
      | Some report, _ -> Some report
      | None, None -> None
      | None, Some local ->
          let name = read_span state local in
          let text = quote_span state name in
          let wanted = zonk state wanted in
          Option.map
            (fun (explanation, note) ->
              let fixes =
                match (entry, side) with
                | Default { waiting; _ }, Types.Variable index
                  when Hashtbl.mem state.annotatable local
                       && (not (Types.contains_unsolved wanted || Types.is_error wanted))
                       && List.for_all
                            (meets_goal state ~root:(Unify.read_root state.unifier index) wanted)
                            waiting ->
                    fix
                      (Printf.sprintf "Declare `%s` as a `%s`." text (Types.show wanted))
                      [ insert name.stop (": " ^ Types.show wanted) ]
                    :: fixes
                | _ -> fixes
              in
              let report =
                add_diagnostic state code span
                  ~notes:[ (decision.decided_at, note) ]
                  ~fixes
                  (message ^ " " ^ explanation)
              in
              decision.decision_report <- Some report;
              report)
            (find_explanation entry ~local:(Printf.sprintf "`%s`" text)
               ~decided:(Types.show decision.decided_type)))
  | Some (Local _) | None -> None

let add_mismatch_diagnostic state ?(fixes = []) code (span : Source.Definition_span.t)
    ~(sides : (Types.ty * Types.ty) list) message =
  match find_refused_class state ~sides with
  | Some root -> report_decided_in_specification state span root
  | None -> (
      match List.find_map (find_integer_literals state) sides with
      | Some (literals, wanted) ->
          add_diagnostic state Integer_for_float span
            ~fixes:
              [
                fix "Write it as a float."
                  (List.map (fun (at : Source.Definition_span.t) -> insert at.stop ".0") literals);
              ]
            (Printf.sprintf "An integer literal is never a float, and %s is expected here."
               (describe state wanted))
      | None -> (
          match List.find_map (find_log_report state ~fixes code span message) sides with
          | Some report -> report
          | None -> add_diagnostic state ~fixes code span message))

let add_mismatch state (span : Source.Definition_span.t) ~expected ~actual =
  add_mismatch_diagnostic state Mismatch span
    ~sides:[ (actual, expected); (expected, actual) ]
    (Printf.sprintf "Expected %s, found %s." (describe state expected) (describe state actual))

let add_operand_mismatch state ~(at : Source.Definition_span.t)
    ~left:((left_span : Source.Definition_span.t), left)
    ~right:((right_span : Source.Definition_span.t), right) =
  let left_type = normalize state left and right_type = normalize state right in
  if is_within state left_type Types.integer_types && is_within state right_type Types.integer_types
  then begin
    let is_within narrower wider =
      match (Types.find_integer_range narrower, Types.find_integer_range wider) with
      | Some (low, high), Some (wider_low, wider_high) ->
          Z.geq low wider_low && Z.leq high wider_high
      | _ -> false
    in
    let make_widening_fix side (operand : Source.Definition_span.t) target =
      fix
        (Printf.sprintf "Convert the %s side to `%s`." side (Types.show target))
        [
          replace operand
            (Printf.sprintf "%s.from_integer(%s)" (Types.show target) (quote_span state operand));
        ]
    in
    let fixes =
      if is_within right_type left_type then [ make_widening_fix "right" right_span left_type ]
      else if is_within left_type right_type then [ make_widening_fix "left" left_span right_type ]
      else []
    in
    add_mismatch_diagnostic state Mismatched_integers at
      ~sides:[ (left, right); (right, left) ]
      ~fixes
      (Printf.sprintf
         "Integer types never convert implicitly: this compares or combines `%s` with `%s`."
         (Types.show left_type) (Types.show right_type))
  end
  else add_mismatch state right_span ~expected:left ~actual:right

let report_mismatch state span ~expected ~actual =
  ignore (add_mismatch state span ~expected ~actual)

let is_member_constant state (value : Syntax.expression) =
  match state.tables.resolutions.(value.id) with
  | Some (Global { path = Member_constant _; _ }) -> true
  | _ -> false

let rec is_place state (value : Syntax.expression) =
  match value.kind with
  | Name path -> (
      match find_target state path.last with
      | Some (Local _ | Law_parameter _ | Field _ | Definition (Constant, _)) -> true
      | _ -> false)
  | Self_value -> true
  | Member (base, _) -> is_place state base || is_member_constant state value
  | Bracket (base, _) -> (
      match state.resolved.brackets.(value.id) with
      | Some Index -> is_place state base
      | Some Method_bracket -> (
          match base.kind with Member _ -> is_place state base | _ -> false)
      | _ -> false)
  | Parenthesized inner -> is_place state inner
  | _ -> false

let rec find_keyword_operation state (value : Syntax.expression) =
  match value.kind with
  | Call ({ kind = Member (base, _); _ }, _)
  | Call ({ kind = Bracket ({ kind = Member (base, _); _ }, _); _ }, _)
  | With (base, _) ->
      if is_place state base then Some (value.id, base) else find_keyword_operation state base
  | Member (base, _) | Bracket (base, _) | Try base -> find_keyword_operation state base
  | _ -> None

let note_mode_keyword state (written : Syntax.expression) (mode : Syntax.mode)
    (operand : Syntax.expression) =
  let rec strip_parentheses (value : Syntax.expression) =
    match value.kind with Parenthesized inner -> strip_parentheses inner | _ -> value
  in
  let place =
    match find_keyword_operation state operand with
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

let find_local_type state (name : Syntax.name) =
  match find_target state name with
  | Some (Local id) ->
      Option.map
        (fun (local : local) -> resolve state local.type_)
        (Hashtbl.find_opt state.locals id)
  | _ -> None

let find_sequence_element (sequence : Types.ty) =
  match sequence with
  | Types.Named { path; arguments = Types.Type element :: _ }
    when Well_known.is_buffer_sequence path || Well_known.find_builtin_type path = Some Array ->
      Some element
  | _ -> None

let make_range state ~origin (base : Core.place) ~start ~stop ~inclusive : Core.kind =
  let make = make_synthetic_expression state ~origin in
  let uint64 = Types.make_builtin UInt64 in
  let element =
    match Core_walk.compute_place_type base with
    | Types.Named { arguments = Types.Type element :: _; _ } -> element
    | type_ -> raise_bug "a range of `%s`" (Types.show type_)
  in
  let stop =
    Option.map
      (fun stop ->
        if inclusive then
          make uint64
            (Operator { operation = Add; arguments = [ stop; make uint64 (Integer Z.one) ] })
        else stop)
      stop
  in
  Use
    (Range
       {
         base;
         start = (match start with Some start -> start | None -> make uint64 (Integer Z.zero));
         stop;
         type_ =
           Types.Named { path = Well_known.make_path Slice; arguments = [ Types.Type element ] };
         origin;
       })
