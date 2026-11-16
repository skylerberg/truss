open Syntax
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

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

let runs (env : env) = not (env.specification || env.compile_time)
let is_compiled (env : env) = not env.specification

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

type undecided_literal = { index : int; kind : Types.literal_kind; local : id; owner : frame }

type literal_decision = {
  decided_local : id;
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
  key : Names.key;
  package : Path.package;
  definition : definition;
  resolved : Resolve.resolved;
  context : Lower.context;
  text : string Lazy.t;
  mutable tables : Tables.t;
  form : form;
  mutable diagnostics : Diagnostic.in_definition list;
  unifier : Unify.t;
  locals : (id, local) Hashtbl.t;
  mutable law_parameters : (string * Types.ty) list;
  mutable frames : frame list;
  mutable locals_read : id list;
  mutable receiver_modes : (id * Types.mode) list;
  yielded : (id, Types.mode) Hashtbl.t;
  lent_tails : (id, unit) Hashtbl.t;
  mutable lambdas : Source.Definition_span.t list;
  mutable unsolved : Diagnostic.reported option;
  mutable capability_constraints : subset_constraint list;
  mutable capability_solution : (int, Types.capability_set) Hashtbl.t option;
  mutable evidence_packages : Path.package list;
  mutable undecided : undecided_literal list;
  decisions : (int, literal_decision) Hashtbl.t;
  annotatable : (id, unit) Hashtbl.t;
}

let reported state ?notes ?(fixes = []) code (span : Source.Definition_span.t) message =
  let diagnostic = Diagnostic.make ?notes ~fixes ~code:(Types code) span message in
  state.diagnostics <- diagnostic :: state.diagnostics;
  Diagnostic.reported diagnostic

let report state ?fixes code span message = ignore (reported state ?fixes code span message)
let is_formula env = env.specification || env.in_quantifier

let reject_in_formula state env span what =
  if is_formula env then
    report state Not_in_specification span
      (Printf.sprintf
         "%s runs, so it cannot be part of a specification, a proof, or a quantifier's body, which \
          the prover reads as formulas: they are built from `let`, `if`, `match`, and calls."
         what)

let read_span state id = state.context.spans.(id)
let bug format = Compiler_bug.bug ~stage:"Infer" format
let error state ?fixes code span message = Types.Error (reported state ?fixes code span message)
let source state span = Source.Definition_span.quote (Lazy.force state.text) span

let fresh_node_id state =
  let id = state.form.next_node_id in
  state.form.next_node_id <- id + 1;
  id

let synthetic_expression state ~origin type_ kind : Core.expression =
  { id = fresh_node_id state; origin; type_; kind }

let register_expression state (value : expression) kind =
  state.form.expression_builders.(value.id) <-
    Some
      (fun () ->
        let id = fresh_node_id state in
        match state.tables.types.(value.id) with
        | Some type_ -> { Core.id; origin = value.id; type_; kind = kind () }
        | None -> bug "`%s` has a node and no type" (source state (read_span state value.id)))

let was_hole state (table : Tables.t -> Types.ty option array) (id : id) =
  match state.form.tables_with_holes with
  | Some tables -> (table tables).(id) = Some Types.Hole
  | None -> false

let rec operands state (value : expression) : expression list =
  let checked (part : expression) =
    if Option.is_some state.form.expression_builders.(part.id) then [ part ]
    else operands state part
  in
  match value.kind with
  | Match { scrutinees; _ } -> List.concat_map checked scrutinees
  | Quantified { binder = Binder_in (_, collection); _ } -> checked collection
  | Quantified { binder = Binder_type _; _ } -> []
  | If _ | Parenthesized _ | Mode _ -> []
  | _ ->
      let checked_parts = ref [] in
      Syntax_walk.expression_parts ~statement:ignore value ~expression:(fun part ->
          checked_parts := checked part :: !checked_parts);
      List.concat (List.rev !checked_parts)

let rec build_expression state (value : expression) : Core.expression =
  let evaluated =
    if Option.is_some state.form.tables_with_holes then operands state value else []
  in
  if
    List.exists
      (fun (operand : expression) -> was_hole state (fun tables -> tables.types) operand.id)
      evaluated
  then begin
    let evaluate (operand : expression) : Core.statement option =
      match operand.kind with
      | Lambda _ -> None
      | _ ->
          let node = build_expression state operand in
          Some
            {
              id = fresh_node_id state;
              origin = operand.id;
              kind =
                Let
                  {
                    pattern =
                      {
                        id = fresh_node_id state;
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
    let todo = synthetic_expression state ~origin:value.id Types.Never Todo in
    synthetic_expression state ~origin:value.id Types.Never
      (Block { statements; value = Some todo })
  end
  else
    match state.form.expression_builders.(value.id) with
    | Some build -> build ()
    | None -> bug "`%s` has no node in the core form" (source state (read_span state value.id))

let register_statement state (written : statement) kind =
  state.form.statement_builders.(written.id) <-
    Some (fun () -> { Core.id = fresh_node_id state; origin = written.id; kind = kind () })

let build_statement state (written : statement) : Core.statement =
  let rec without_mode_keyword (value : expression) =
    match value.kind with
    | Mode (_, inner) | Parenthesized inner -> without_mode_keyword inner
    | _ -> value
  in
  let hole (value : expression) =
    let value = without_mode_keyword value in
    if was_hole state (fun tables -> tables.types) value.id then Some value else None
  in
  match
    match written.kind with
    | For { iterable; _ } -> hole iterable
    | Assignment { target; _ } -> hole target
    | _ -> None
  with
  | Some value ->
      {
        id = fresh_node_id state;
        origin = written.id;
        kind = Evaluate (build_expression state value);
      }
  | None -> (
      match state.form.statement_builders.(written.id) with
      | Some build -> build ()
      | None -> bug "`%s` has no node in the core form" (source state (read_span state written.id)))

let register_pattern state (written : pattern) kind =
  state.form.pattern_builders.(written.id) <-
    Some
      (fun () ->
        let id = fresh_node_id state in
        match state.tables.scrutinee_types.(written.id) with
        | Some type_ -> { Core.id; origin = written.id; type_; kind = kind () }
        | None -> bug "`%s` has a node and no type" (source state (read_span state written.id)))

let build_pattern state (written : pattern) : Core.pattern =
  if was_hole state (fun tables -> tables.scrutinee_types) written.id then
    { id = fresh_node_id state; origin = written.id; type_ = Types.Never; kind = Wildcard }
  else
    match state.form.pattern_builders.(written.id) with
    | Some build -> build ()
    | None -> bug "`%s` has no node in the core form" (source state (read_span state written.id))

let alias_expression state (value : expression) (inner : expression) =
  state.form.expression_builders.(value.id) <- Some (fun () -> build_expression state inner)

let rec mark_lent_tails state (value : expression) =
  match value.kind with
  | Parenthesized inner -> mark_lent_tails state inner
  | If { then_; else_ = Some else_; _ } -> (
      mark_lent_block state then_;
      match else_ with
      | Else block -> mark_lent_block state block
      | Else_if nested -> mark_lent_tails state nested)
  | Match { arms; _ } ->
      List.iter
        (fun (arm : arm) ->
          match arm.body.kind with Expression body -> mark_lent_tails state body | _ -> ())
        arms
  | Block body -> mark_lent_block state body
  | Return _ | Todo | Unreachable -> ()
  | _ -> Hashtbl.replace state.lent_tails value.id ()

and mark_lent_block state (body : block) =
  match List.rev body.statements with
  | { kind = Expression value; _ } :: _ -> mark_lent_tails state value
  | _ -> ()

let place_of (node : Core.expression) : Core.place =
  match node.kind with Use place -> place | _ -> Temporary node

let fresh_synthetic_local state : Core.local =
  let number = state.form.next_synthetic_local in
  state.form.next_synthetic_local <- number + 1;
  Synthetic number

let fix title edits = Diagnostic.fix title edits
let replace = Diagnostic.replace
let insert position text = Diagnostic.insert (Source.Definition_span.zero_width position) text
let current_frame state = match state.frames with frame :: _ -> Some frame | [] -> None

let record state (value : expression) type_ =
  state.tables.types.(value.id) <- Some type_;
  match current_frame state with
  | Some frame -> frame.recorded_expressions <- value.id :: frame.recorded_expressions
  | None -> ()

let note_compiled_expression state env (value : expression) =
  match current_frame state with
  | Some frame when is_compiled env ->
      frame.compiled_expressions <- value.id :: frame.compiled_expressions
  | _ -> ()

let report_specification_only state span message =
  match current_frame state with
  | Some { specification_only_report = Some report; _ } -> report
  | frame ->
      let report = reported state Specification_only span message in
      Option.iter (fun frame -> frame.specification_only_report <- Some report) frame;
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

let check_compiled_binding state (id : id) =
  match state.tables.local_types.(id) with
  | Some type_ -> (
      let span = read_span state id in
      match
        reject_specification_only_type state
          ~subject:(Printf.sprintf "`%s`" (source state span))
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

let check_compiled_expression state (id : id) =
  Option.iter
    (fun type_ ->
      ignore (reject_specification_only_type state ~subject:"This value" (read_span state id) type_))
    state.tables.types.(id)

let compare_in_source_order state left right =
  let left : Source.Definition_span.t = read_span state left
  and right : Source.Definition_span.t = read_span state right in
  compare (left.start, -left.stop) (right.start, -right.stop)

let defer state check =
  match current_frame state with
  | Some frame -> if not (check ()) then frame.deferred_checks <- check :: frame.deferred_checks
  | None -> ignore (check ())

let resolve state type_ = Unify.resolve state.unifier type_
let zonk state type_ = Unify.zonk state.unifier type_
let fresh state = Unify.fresh state.unifier

let integer_type state (type_ : Types.ty) =
  Types.is_integer_type type_
  ||
  match type_ with
  | Parameter _ | Projection _ -> state.unifier.integer_range type_ <> None
  | _ -> false

let signed_type state (type_ : Types.ty) =
  Types.is_signed type_
  ||
  match type_ with
  | Parameter _ | Projection _ -> (
      match state.unifier.integer_range type_ with Some (low, _) -> Z.sign low < 0 | None -> false)
  | _ -> false

let bounds state parameter =
  Option.value ~default:[] (Hashtbl.find_opt state.context.bounds parameter)

let normalize state type_ =
  Interface.Impls.normalize state.lookups.interface ~bounds:(bounds state) (zonk state type_)

let unsolved state =
  match state.unsolved with
  | Some report -> Types.Error report
  | None ->
      let report =
        reported state Cannot_infer
          (Source.Definition_span.make (read_span state state.definition.id).start
             (read_span state state.definition.id).start)
          "A type in this definition cannot be inferred. Give the `let` a type, or the call type \
           arguments."
      in
      state.unsolved <- Some report;
      Types.Error report

let resolve_capabilities state (capabilities : Types.capability_set) =
  match state.capability_solution with
  | Some solution when Types.has_capability_variable capabilities ->
      Types.flat_map_capabilities
        (function
          | Types.Capability_variable variable ->
              (Option.value ~default:Types.no_capabilities (Hashtbl.find_opt solution variable)
                :> Types.capability list)
          | capability -> [ capability ])
        capabilities
  | _ -> capabilities

let rec final_type state type_ =
  Types.map ~capabilities:(final_capabilities state)
    (function
      | Types.Variable _ | Types.Literal _ -> Some (unsolved state)
      | Types.Hole when Option.is_some state.form.tables_with_holes -> Some Types.Never
      | _ -> None)
    (normalize state type_)

and final_capabilities state capabilities =
  resolve_capabilities state
    (Interface.Impls.normalize_capabilities state.lookups.interface ~bounds:(bounds state)
       (Types.flat_map_capabilities
          (function
            | Types.Capability_projection { base; trait; name } ->
                [ Types.Capability_projection { base = final_type state base; trait; name } ]
            | capability -> [ capability ])
          capabilities))

let final_argument state = function
  | Types.Type type_ -> Types.Type (final_type state type_)
  | Types.Value value -> (
      match Unify.resolve_value state.unifier value with
      | Types.Value_variable _ -> Types.Type (unsolved state)
      | value -> Types.Value value)
  | Types.Capabilities capabilities -> Types.Capabilities (final_capabilities state capabilities)

let unify state left right =
  let normalize type_ =
    Interface.Impls.normalize state.lookups.interface ~bounds:(bounds state)
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

let implements state type_ trait =
  Interface.Impls.implements state.lookups.interface ~bounds:(bounds state) (normalize state type_)
    (normalize_trait state trait)

let copyable state type_ =
  Interface.Impls.copyable state.lookups.interface ~bounds:(bounds state) (zonk state type_)

let plain state type_ =
  Interface.Impls.plain state.lookups.interface ~bounds:(bounds state) (zonk state type_)

let is_view state type_ =
  Interface.Impls.is_view state.lookups.interface ~bounds:(bounds state) (zonk state type_)

let associated state type_ (trait : Types.trait_reference) name ~(at : Source.Definition_span.t) =
  let type_ = normalize state type_ and trait = normalize_trait state trait in
  match
    Interface.Impls.associated_type state.lookups.interface ~bounds:(bounds state) type_ trait name
  with
  | Some associated_type -> associated_type
  | None ->
      error state Unknown_associated_type at
        (Printf.sprintf "`%s` gives no `%s` as a `%s`." (Types.show type_) name
           (Types.show_trait trait))

let evidence_of = function
  | Impls.From_impl { impl; substitution } -> Tables.Impl { impl; arguments = substitution }
  | Impls.From_bound -> Tables.Bound
  | Impls.From_any -> Tables.Dynamic
  | Impls.Built_in | Impls.Accepted _ -> Tables.Built_in

let trait_reference ?(arguments = []) trait : Types.trait_reference =
  { trait; trait_arguments = arguments; associated = [] }

let string_type = Types.Named { path = Well_known.path String; arguments = [] }
let undecided_type (undecided : undecided_literal) = Types.Literal (undecided.kind, undecided.index)

let decide_literals state ~(at : Source.Definition_span.t) ~is_default =
  state.undecided <-
    List.filter
      (fun (undecided : undecided_literal) ->
        match Unify.resolve state.unifier (undecided_type undecided) with
        | Types.Literal _ -> true
        | _ ->
            Hashtbl.replace state.decisions undecided.index
              {
                decided_local = undecided.local;
                decided_type = Unify.zonk state.unifier (undecided_type undecided);
                decided_at = at;
                is_default;
                decision_report = None;
              };
            false)
      state.undecided

let settle state frame =
  List.iter
    (fun (left, right) ->
      let report_missing _ =
        report state Mismatch frame.span
          (Printf.sprintf
             "Two function types here must use the same capabilities, and one uses `%s` where the \
              other uses `%s`."
             (Types.show_argument (Types.Capabilities (resolve_capabilities state left)))
             (Types.show_argument (Types.Capabilities (resolve_capabilities state right))))
      in
      state.capability_constraints <-
        { subset = left; superset = right; report_missing }
        :: { subset = right; superset = left; report_missing }
        :: state.capability_constraints)
    state.unifier.deferred_capability_equalities;
  state.unifier.deferred_capability_equalities <- [];
  let run_pending () =
    let rec loop pending =
      let left = List.filter (fun check -> not (check ())) pending in
      if List.length left < List.length pending then loop left else left
    in
    frame.deferred_checks <- loop frame.deferred_checks
  in
  run_pending ();
  let parent = match state.frames with _ :: parent :: _ -> Some parent | _ -> None in
  decide_literals state ~at:frame.span ~is_default:false;
  let types_of ids table = List.filter_map (fun id -> table.(id)) ids in
  let all_types () =
    types_of frame.recorded_expressions state.tables.types
    @ types_of frame.bindings state.tables.local_types
  in
  let call_arguments () =
    List.concat_map
      (fun id ->
        match state.tables.calls.(id) with
        | Some
            {
              callee =
                ( Function { type_arguments; _ }
                | Trait_method { type_arguments; _ }
                | Constructor { type_arguments; _ }
                | Intrinsic { type_arguments; _ } );
              _;
            } ->
            type_arguments
        | _ -> [])
      frame.recorded_expressions
  in
  let unknowns () =
    List.concat_map (Unify.unknowns state.unifier) (all_types ())
    @ List.concat_map (Unify.argument_unknowns state.unifier) (call_arguments ())
  in
  (match parent with
  | Some parent when parent.frame_specification = frame.frame_specification ->
      List.iter
        (fun local ->
          match state.tables.local_types.(local) with
          | Some type_ ->
              List.iter
                (function
                  | Unify.Unknown_literal (kind, index) when index >= frame.first_variable ->
                      if not frame.frame_specification then
                        Hashtbl.replace state.unifier.code_literals index ();
                      state.undecided <- { index; kind; local; owner = parent } :: state.undecided
                  | _ -> ())
                (Unify.unknowns state.unifier type_)
          | None -> ())
        frame.declared
  | _ -> ());
  let undecided =
    List.filter_map
      (fun (undecided : undecided_literal) ->
        if undecided.owner == frame then None
        else
          match Unify.resolve state.unifier (undecided_type undecided) with
          | Types.Literal (_, root) -> Some root
          | _ -> None)
      state.undecided
  in
  let is_undecided index = List.mem index undecided in
  List.iter
    (function
      | Unify.Unknown_literal (kind, index)
        when index >= frame.first_variable && not (is_undecided index) ->
          Hashtbl.replace state.unifier.type_solutions index
            (match kind with
            | Integer_literal ->
                if frame.frame_specification then Types.Integer else Types.builtin Int64
            | Float_literal -> Types.builtin Float64)
      | _ -> ())
    (unknowns ());
  run_pending ();
  let unsolved =
    List.filter
      (function
        | Unify.Unknown_type index | Unknown_value index -> index >= frame.first_variable
        | Unknown_literal (_, index) -> index >= frame.first_variable && not (is_undecided index))
      (unknowns ())
  in
  state.undecided <-
    List.filter (fun (undecided : undecided_literal) -> undecided.owner != frame) state.undecided;
  if unsolved <> [] then begin
    let report =
      reported state Cannot_infer frame.span
        "The types in this statement cannot be inferred from it alone. Give the `let` a type, or \
         the call type arguments, such as `var names: List[String] = []`."
    in
    if Option.is_none state.unsolved then state.unsolved <- Some report;
    List.iter
      (function
        | Unify.Unknown_type index | Unknown_literal (_, index) ->
            Hashtbl.replace state.unifier.type_solutions index (Types.Error report)
        | Unknown_value _ -> ())
      unsolved;
    frame.deferred_checks <- []
  end;
  let is_open = function
    | Unify.Unknown_type index | Unknown_value index -> index < frame.first_variable
    | Unknown_literal (_, index) -> index < frame.first_variable || is_undecided index
  in
  let finish table ids keep =
    List.iter
      (fun id ->
        match table.(id) with
        | Some type_ -> (
            let type_ =
              Interface.Impls.normalize state.lookups.interface ~bounds:(bounds state)
                (zonk state type_)
            in
            table.(id) <- Some type_;
            if List.exists is_open (Unify.unknowns state.unifier type_) then
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
    | Some type_ -> not (List.exists is_open (Unify.unknowns state.unifier type_))
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
  match parent with
  | Some parent -> parent.deferred_checks <- frame.deferred_checks @ parent.deferred_checks
  | None -> ()

let in_statement state env (span : Source.Definition_span.t) body =
  let frame =
    {
      first_variable = state.unifier.next + 1;
      recorded_expressions = [];
      bindings = [];
      declared = [];
      deferred_checks = [];
      reported_unmet_bounds = [];
      compiled_expressions = [];
      compiled_bindings = [];
      specification_only_report = None;
      frame_specification = env.specification;
      span;
    }
  in
  state.frames <- frame :: state.frames;
  let result = body () in
  settle state frame;
  state.frames <- List.tl state.frames;
  result

let rec diverges ~is_never (written : statement) =
  match written.kind with
  | Expression value | Let { value; _ } | Assignment { value; _ } -> is_never value
  | While { condition = { kind = True; _ }; body; _ } -> not (Syntax_walk.contains_break body)
  | Parallel body | Concurrent body -> List.exists (diverges ~is_never) body.statements
  | _ -> false

let statement_diverges state =
  diverges ~is_never:(fun (value : expression) ->
      match state.tables.types.(value.id) with
      | Some type_ -> resolve state type_ = Types.Never
      | None -> false)

let build_block state (written : block) : Core.block =
  let rec build_statements (statements : statement list) =
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

let declare state (name : name) type_ ~is_var ~mode =
  Hashtbl.replace state.locals name.id { type_; is_var; mode };
  state.tables.local_types.(name.id) <- Some type_;
  match current_frame state with
  | Some frame ->
      frame.bindings <- name.id :: frame.bindings;
      frame.declared <- name.id :: frame.declared
  | None -> ()

let declare_compiled state env (name : name) type_ ~is_var ~mode =
  declare state name type_ ~is_var ~mode;
  match current_frame state with
  | Some frame when is_compiled env ->
      frame.compiled_bindings <- name.id :: frame.compiled_bindings;
      check_compiled_binding state name.id
  | _ -> ()

let target state (name : name) = state.resolved.names.(name.id)

let default_literal state ~at type_ =
  let decide default =
    (match current_frame state with
    | Some frame -> decide_literals state ~at:frame.span ~is_default:false
    | None -> ());
    ignore (Unify.unify state.unifier type_ default);
    decide_literals state ~at ~is_default:true;
    default
  in
  match Unify.resolve state.unifier type_ with
  | Types.Literal (Integer_literal, _) -> decide (Types.builtin Int64)
  | Types.Literal (Float_literal, _) -> decide (Types.builtin Float64)
  | _ -> type_

let head state (value : expression) = Resolve.head state.resolved value

let names_variant (member : name) =
  member.text <> "" && member.text.[0] >= 'A' && member.text.[0] <= 'Z'

let show state type_ = Types.show (zonk state type_)

let literal_decision state type_ =
  let rec follow (type_ : Types.ty) =
    match type_ with
    | Literal (_, index) | Variable index -> (
        match Hashtbl.find_opt state.decisions index with
        | Some decision -> Some decision
        | None -> Option.bind (Hashtbl.find_opt state.unifier.type_solutions index) follow)
    | _ -> None
  in
  follow type_

let reported_mismatch state ?(fixes = []) code (span : Source.Definition_span.t)
    ~(sides : (Types.ty * Types.ty) list) message =
  let other_fixes = fixes in
  match
    List.find_map
      (fun (decided, wanted) ->
        Option.map (fun decision -> (decision, wanted)) (literal_decision state decided))
      sides
  with
  | None -> reported state ~fixes code span message
  | Some ({ decision_report = Some report; _ }, _) -> report
  | Some (decision, wanted) ->
      let name = read_span state decision.decided_local in
      let text = source state name in
      let local = Printf.sprintf "`%s`" text in
      let decided = Types.show decision.decided_type and wanted = zonk state wanted in
      let explanation, note =
        if decision.is_default then
          ( Printf.sprintf "%s took its default type, `%s`, at an earlier method call." local decided,
            Printf.sprintf
              "Method lookup needs the type of %s, so %s takes its default type `%s` here." local
              local decided )
        else
          ( Printf.sprintf "An earlier statement decided that the type of %s is `%s`." local decided,
            Printf.sprintf "This statement decides that the type of %s is `%s`." local decided )
      in
      let fixes =
        if
          decision.is_default
          && Hashtbl.mem state.annotatable decision.decided_local
          && not (Types.contains_unsolved wanted || Types.is_error wanted)
        then
          fix
            (Printf.sprintf "Declare `%s` as a `%s`." text (Types.show wanted))
            [ insert name.stop (": " ^ Types.show wanted) ]
          :: other_fixes
        else other_fixes
      in
      let report =
        reported state code span
          ~notes:[ (decision.decided_at, note) ]
          ~fixes
          (message ^ " " ^ explanation)
      in
      decision.decision_report <- Some report;
      report

let mismatched state (span : Source.Definition_span.t) ~expected ~actual =
  let sides = [ (actual, expected); (expected, actual) ] in
  let expected = zonk state expected and actual = zonk state actual in
  match (resolve state actual, expected) with
  | Types.Literal (Integer_literal, _), _ when Types.is_float_type expected ->
      reported state Integer_for_float span
        ~fixes:[ fix "Write it as a float." [ insert span.stop ".0" ] ]
        (Printf.sprintf "An integer literal is never a float, and `%s` is expected here."
           (Types.show expected))
  | _ ->
      reported_mismatch state Mismatch span ~sides
        (Printf.sprintf "Expected `%s`, found `%s`." (Types.show expected) (Types.show actual))

let mismatch state span ~expected ~actual = ignore (mismatched state span ~expected ~actual)

let is_member_constant state (value : expression) =
  match state.tables.resolutions.(value.id) with
  | Some (Global { path = Member_constant _; _ }) -> true
  | _ -> false

let rec is_place state (value : expression) =
  match value.kind with
  | Name path -> (
      match target state path.last with
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

let rec call_with_mode_keyword state (value : expression) =
  match value.kind with
  | Call ({ kind = Member (base, _); _ }, _)
  | Call ({ kind = Bracket ({ kind = Member (base, _); _ }, _); _ }, _) ->
      if is_place state base then Some value.id else call_with_mode_keyword state base
  | Member (base, _) | Bracket (base, _) | Try base -> call_with_mode_keyword state base
  | _ -> None

let check_resource state (resource : Syntax.resource) =
  let capability (path : path_type) (method_ : name option) =
    let shown = Interface.Lower.show_path path.path in
    match target state path.path.last with
    | Some (Definition (Capability, capability)) -> (
        match method_ with
        | Some method_ when state.lookups.interface.names.members capability method_.text = [] ->
            report state Unknown_member (read_span state method_.id)
              (Printf.sprintf "`%s` has no method `%s`." shown method_.text)
        | _ -> ())
    | Some (Unknown _) -> ()
    | _ ->
        report state Not_a_capability (read_span state path.id)
          (Printf.sprintf "`calls` counts the calls of a capability, and `%s` is not one." shown)
  in
  match resource with
  | Time | Allocations | Allocated_bytes -> ()
  | Calls (Call_capability path) -> capability path None
  | Calls (Call_method (path, method_)) -> capability path (Some method_)
  | Calls (Call_parameter name) -> (
      match target state name with
      | Some (Local id) -> (
          match
            Option.map
              (fun (local : local) -> resolve state local.type_)
              (Hashtbl.find_opt state.locals id)
          with
          | Some (Types.Function _ | Types.Error _ | Types.Hole) | None -> ()
          | Some other ->
              report state Not_callable (read_span state name.id)
                (Printf.sprintf "`calls` counts the calls through a function, and `%s` is a `%s`."
                   name.text (Types.show other)))
      | Some (Unknown _) -> ()
      | _ ->
          report state Not_callable (read_span state name.id)
            (Printf.sprintf
               "`calls` counts the calls through a parameter that is a function, or of a \
                capability, and `%s` is neither."
               name.text))

let slice state ~origin (base : Core.place) ~start ~stop ~inclusive : Core.kind =
  let make = synthetic_expression state ~origin in
  let uint64 = Types.builtin UInt64 in
  let path, type_arguments =
    match Core_walk.place_type base with
    | Types.Named { path; arguments } -> (path, arguments)
    | type_ -> bug "a slice of `%s`" (Types.show type_)
  in
  let callee name : Core.callee =
    Function { path = Method { owner = path; name; receiver = Read }; type_arguments }
  in
  let bound = Operands.build_argument Read in
  let start = match start with Some start -> start | None -> make uint64 (Integer Z.zero) in
  match stop with
  | None -> Slice { base; callee = callee "slice_from"; bounds = [ bound start ] }
  | Some stop ->
      let stop =
        if inclusive then
          make uint64
            (Operator { operation = Add; arguments = [ stop; make uint64 (Integer Z.one) ] })
        else stop
      in
      Slice { base; callee = callee "slice_range"; bounds = [ bound start; bound stop ] }

type conversion = From_never | Owned_to_view | Function_widening | To_integer | From_integer

let convert state env ?argument ?expression (span : Source.Definition_span.t) ~actual ~expected =
  let is_argument = Option.is_some argument in
  let converted (conversion : conversion option) =
    match (conversion, expression) with
    | Some conversion, Some id ->
        let before = state.form.expression_builders.(id) in
        state.form.expression_builders.(id) <-
          Option.map
            (fun build () ->
              let inner : Core.expression = build () in
              let expected = final_type state expected in
              let convert conversion =
                synthetic_expression state ~origin:id expected
                  (Convert { conversion; value = inner })
              in
              match conversion with
              | From_never -> inner
              | Function_widening ->
                  if Types.equal inner.type_ expected then inner else convert Widen
              | To_integer -> convert To_integer
              | From_integer -> convert From_integer
              | Owned_to_view when argument = Some Types.Mut && Types.is_well_known List inner.type_
                ->
                  let base : Core.place =
                    match inner.kind with Use place -> place | _ -> Temporary inner
                  in
                  synthetic_expression state ~origin:id expected
                    (slice state ~origin:id base ~start:None ~stop:None ~inclusive:false)
              | Owned_to_view -> (
                  match inner.type_ with
                  | Types.Named { path; arguments } ->
                      synthetic_expression state ~origin:id expected
                        (Call
                           {
                             callee =
                               Function
                                 {
                                   path = Method { owner = path; name = "slice"; receiver = Read };
                                   type_arguments = arguments;
                                 };
                             arguments = [ Operands.build_argument Read inner ];
                             lends = None;
                             uses = Types.no_capabilities;
                           })
                  | other -> bug "`%s` is viewed and has no view" (Types.show other)))
            before
    | _ -> ()
  in
  converted
  @@
  let actual_type = normalize state actual and wanted = normalize state expected in
  let refused () =
    mismatch state span ~expected ~actual;
    None
  in
  match (actual_type, wanted, expression) with
  | Types.Never, _, _ -> Some From_never
  | Types.Named actual_named, Types.Named wanted_named, _
    when is_argument
         && List.exists
              (fun (owned, view) ->
                Path.equal actual_named.path owned && Path.equal wanted_named.path view)
              [
                (Well_known.path List, Well_known.path Slice);
                (Well_known.path String, Well_known.path String_slice);
              ] ->
      if not (Unify.unify_arguments state.unifier wanted_named.arguments actual_named.arguments)
      then mismatch state span ~expected ~actual;
      Some Owned_to_view
  | Types.Integer, _, Some _ when is_argument && env.specification && integer_type state wanted ->
      Some From_integer
  | Types.Literal (Integer_literal, index), Types.Integer, _
    when env.specification && Hashtbl.mem state.unifier.code_literals index ->
      Some To_integer
  | _, Types.Integer, _ when env.specification && integer_type state actual_type -> Some To_integer
  | Types.Function actual_function, Types.Function wanted_function, _
    when not (Types.same_clauses actual_function wanted_function) ->
      let unlisted = Types.capability_difference actual_function.uses wanted_function.uses in
      let unknown =
        Types.capabilities_unsolved actual_function.uses
        || Types.capabilities_unsolved wanted_function.uses
      in
      let proven =
        Types.costs_imply ~provided:actual_function.costs ~required:wanted_function.costs
      in
      if
        Unify.unify state.unifier wanted
          (Types.Function
             { actual_function with uses = wanted_function.uses; costs = wanted_function.costs })
        && (unlisted = Types.no_capabilities || unknown)
        && (proven || is_argument || Option.is_some expression)
      then begin
        if unlisted <> Types.no_capabilities then
          state.capability_constraints <-
            {
              subset = actual_function.uses;
              superset = wanted_function.uses;
              report_missing =
                (fun _ ->
                  mismatch state span ~expected:(final_type state expected)
                    ~actual:(final_type state actual));
            }
            :: state.capability_constraints;
        Some Function_widening
      end
      else refused ()
  | _ -> if Unify.unify state.unifier wanted actual_type then None else refused ()
