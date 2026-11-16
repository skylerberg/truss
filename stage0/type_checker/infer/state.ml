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
let find_current_frame state = match state.frames with frame :: _ -> Some frame | [] -> None

let record state (value : Syntax.expression) type_ =
  state.tables.types.(value.id) <- Some type_;
  match find_current_frame state with
  | Some frame -> frame.recorded_expressions <- value.id :: frame.recorded_expressions
  | None -> ()

let note_compiled_expression state env (value : Syntax.expression) =
  match find_current_frame state with
  | Some frame when is_compiled env ->
      frame.compiled_expressions <- value.id :: frame.compiled_expressions
  | _ -> ()

let report_specification_only state span message =
  match find_current_frame state with
  | Some { specification_only_report = Some report; _ } -> report
  | frame ->
      let report = add_diagnostic state Specification_only span message in
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

let defer state check =
  match find_current_frame state with
  | Some frame -> if not (check ()) then frame.deferred_checks <- check :: frame.deferred_checks
  | None -> ignore (check ())

let resolve state type_ = Unify.resolve state.unifier type_
let zonk state type_ = Unify.zonk state.unifier type_
let make_fresh_type state = Unify.make_fresh_type state.unifier

let is_integer_type state (type_ : Types.ty) =
  Types.is_integer_type type_
  ||
  match type_ with
  | Parameter _ | Projection _ -> state.unifier.find_integer_range type_ <> None
  | _ -> false

let is_signed_type state (type_ : Types.ty) =
  Types.is_signed type_
  ||
  match type_ with
  | Parameter _ | Projection _ -> (
      match state.unifier.find_integer_range type_ with
      | Some (low, _) -> Z.sign low < 0
      | None -> false)
  | _ -> false

let lookup_bounds state parameter = Interface.Elaborator.list_bounds state.context parameter

let normalize state type_ =
  Interface.Impls.normalize state.lookups.interface ~list_bounds:(lookup_bounds state)
    (zonk state type_)

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
  | Some solution when Types.has_capability_variable capabilities ->
      Types.flat_map_capabilities
        (function
          | Types.Capability_variable variable ->
              (Option.value ~default:Types.no_capabilities (Hashtbl.find_opt solution variable)
                :> Types.capability list)
          | capability -> [ capability ])
        capabilities
  | _ -> capabilities

let rec finalize_type state type_ =
  Types.map ~map_capabilities:(finalize_capabilities state)
    (function
      | Types.Variable _ | Types.Literal _ -> Some (make_unsolved_type state)
      | Types.Hole when Option.is_some state.form.tables_with_holes -> Some Types.Never
      | _ -> None)
    (normalize state type_)

and finalize_capabilities state capabilities =
  resolve_capabilities state
    (Interface.Impls.normalize_capabilities state.lookups.interface
       ~list_bounds:(lookup_bounds state)
       (Types.flat_map_capabilities
          (function
            | Types.Capability_projection { base; trait; name } ->
                [ Types.Capability_projection { base = finalize_type state base; trait; name } ]
            | capability -> [ capability ])
          capabilities))

let finalize_argument state = function
  | Types.Type type_ -> Types.Type (finalize_type state type_)
  | Types.Value value -> (
      match Unify.resolve_value state.unifier value with
      | Types.Value_variable _ -> Types.Type (make_unsolved_type state)
      | value -> Types.Value value)
  | Types.Capabilities capabilities -> Types.Capabilities (finalize_capabilities state capabilities)

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

let solve_trait_arguments state type_ (trait : Types.trait_reference) =
  let trait = Unify.zonk_trait state.unifier trait in
  match normalize state type_ with
  | (Parameter _ | Projection _ | Any _) as bounded
    when List.exists Types.is_unsolved_argument trait.trait_arguments -> (
      let normalized = normalize_trait state trait in
      match
        List.sort_uniq compare
          (List.map
             (fun (bound : Types.trait_reference) -> bound.trait_arguments)
             (Interface.Impls.list_matching_bounds state.lookups.interface
                ~list_bounds:(lookup_bounds state) bounded normalized))
      with
      | [ arguments ] ->
          if Unify.unify_arguments state.unifier normalized.trait_arguments arguments then
            Unify.zonk_trait state.unifier trait
          else
            raise_bug "`%s` has one bound of `%s`, and its arguments do not unify with the trait's"
              (Types.show bounded) (Types.show_trait trait)
      | _ -> trait)
  | _ -> trait

let decide_property state property type_ =
  Interface.Impls.decide_property property state.lookups.interface
    ~list_bounds:(lookup_bounds state) (zonk state type_)

let is_plain state type_ =
  Interface.Impls.is_plain state.lookups.interface ~list_bounds:(lookup_bounds state)
    (zonk state type_)

let is_view state type_ =
  Interface.Impls.is_view state.lookups.interface ~list_bounds:(lookup_bounds state)
    (zonk state type_)

let resolve_associated_type state type_ (trait : Types.trait_reference) name
    ~(at : Source.Definition_span.t) =
  let type_ = normalize state type_ and trait = normalize_trait state trait in
  match
    Interface.Impls.project_associated_type state.lookups.interface
      ~list_bounds:(lookup_bounds state) type_ trait name
  with
  | Some associated_type -> associated_type
  | None ->
      make_error_type state Unknown_associated_type at
        (Printf.sprintf "`%s` gives no `%s` as a `%s`." (Types.show type_) name
           (Types.show_trait trait))

let convert_evidence = function
  | Interface.Impls.From_impl { impl; substitution } ->
      Tables.Impl { impl; arguments = substitution }
  | Interface.Impls.From_bound -> Tables.Bound
  | Interface.Impls.From_any -> Tables.Dynamic
  | Interface.Impls.Built_in | Interface.Impls.Accepted _ -> Tables.Built_in

let make_trait_reference ~arguments trait : Types.trait_reference =
  { trait; trait_arguments = arguments; associated = [] }

let string_type = Types.Named { path = Well_known.make_path String; arguments = [] }

let make_undecided_type (undecided : undecided_literal) =
  Types.Literal (undecided.kind, undecided.index)

let decide_literals state ~(at : Source.Definition_span.t) ~is_default =
  state.undecided <-
    List.filter
      (fun (undecided : undecided_literal) ->
        match Unify.resolve state.unifier (make_undecided_type undecided) with
        | Types.Literal _ -> true
        | _ ->
            Hashtbl.replace state.decisions undecided.index
              {
                decided_local = undecided.local;
                decided_type = Unify.zonk state.unifier (make_undecided_type undecided);
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
  let list_types ids table = List.filter_map (fun id -> table.(id)) ids in
  let list_all_types () =
    list_types frame.recorded_expressions state.tables.types
    @ list_types frame.bindings state.tables.local_types
  in
  let list_call_arguments () =
    List.concat_map
      (fun id ->
        match state.tables.calls.(id) with
        | Some { callee = Trait_method { trait; type_arguments; _ }; _ } ->
            trait.trait_arguments @ type_arguments
        | Some
            {
              callee =
                ( Function { type_arguments; _ }
                | Constructor { type_arguments; _ }
                | Intrinsic { type_arguments; _ } );
              _;
            } ->
            type_arguments
        | _ -> [])
      frame.recorded_expressions
  in
  let list_unknowns () =
    List.concat_map (Unify.list_unknowns state.unifier) (list_all_types ())
    @ List.concat_map (Unify.list_argument_unknowns state.unifier) (list_call_arguments ())
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
                (Unify.list_unknowns state.unifier type_)
          | None -> ())
        frame.declared
  | _ -> ());
  let undecided =
    List.filter_map
      (fun (undecided : undecided_literal) ->
        if undecided.owner == frame then None
        else
          match Unify.resolve state.unifier (make_undecided_type undecided) with
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
                if frame.frame_specification then Types.Integer else Types.make_builtin Int64
            | Float_literal -> Types.make_builtin Float64)
      | _ -> ())
    (list_unknowns ());
  run_pending ();
  let unsolved =
    List.filter
      (function
        | Unify.Unknown_type index | Unknown_value index -> index >= frame.first_variable
        | Unknown_literal (_, index) -> index >= frame.first_variable && not (is_undecided index))
      (list_unknowns ())
  in
  state.undecided <-
    List.filter (fun (undecided : undecided_literal) -> undecided.owner != frame) state.undecided;
  if unsolved <> [] then begin
    let list_trait_unknowns (trait : Types.trait_reference) =
      List.concat_map (Unify.list_argument_unknowns state.unifier) trait.trait_arguments
    in
    let undetermined_traits =
      List.filter_map
        (fun id ->
          match state.tables.calls.(id) with
          | Some { callee = Trait_method { trait; self_type; _ }; _ }
            when (not (Types.contains_unsolved (zonk state self_type)))
                 && List.exists
                      (fun unknown -> List.mem unknown unsolved)
                      (list_trait_unknowns trait) ->
              Some (id, trait)
          | _ -> None)
        frame.recorded_expressions
    in
    let call_reports =
      List.map
        (fun (id, (trait : Types.trait_reference)) ->
          add_diagnostic state Cannot_infer (read_span state id)
            (Printf.sprintf
               "This call does not determine the arguments of `%s`. Write the call in full with \
                them."
               (match trait.trait with Top { name; _ } -> name | path -> Path.show path)))
        undetermined_traits
    in
    let explained =
      List.concat_map (fun (_, trait) -> list_trait_unknowns trait) undetermined_traits
    in
    let report =
      match call_reports with
      | first :: _ when List.for_all (fun unknown -> List.mem unknown explained) unsolved -> first
      | _ ->
          add_diagnostic state Cannot_infer frame.span
            "The types in this statement cannot be inferred from it alone. Give the `let` a type, \
             or the call type arguments, such as `var names: List[String] = []`."
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
  match parent with
  | Some parent -> parent.deferred_checks <- frame.deferred_checks @ parent.deferred_checks
  | None -> ()

let run_in_statement state env (span : Source.Definition_span.t) body =
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

let rec diverges ~is_never (written : Syntax.statement) =
  match written.kind with
  | Expression value | Let { value; _ } | Assignment { value; _ } -> is_never value
  | While { condition = { kind = True; _ }; body; _ } -> not (Syntax_walk.contains_break body)
  | Parallel body | Concurrent body -> List.exists (diverges ~is_never) body.statements
  | _ -> false

let statement_diverges state =
  diverges ~is_never:(fun (value : Syntax.expression) ->
      match state.tables.types.(value.id) with
      | Some type_ -> resolve state type_ = Types.Never
      | None -> false)

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

let declare state (name : Syntax.name) type_ ~is_var ~mode =
  Hashtbl.replace state.locals name.id { type_; is_var; mode };
  state.tables.local_types.(name.id) <- Some type_;
  match find_current_frame state with
  | Some frame ->
      frame.bindings <- name.id :: frame.bindings;
      frame.declared <- name.id :: frame.declared
  | None -> ()

let declare_compiled state env (name : Syntax.name) type_ ~is_var ~mode =
  declare state name type_ ~is_var ~mode;
  match find_current_frame state with
  | Some frame when is_compiled env ->
      frame.compiled_bindings <- name.id :: frame.compiled_bindings;
      check_compiled_binding state name.id
  | _ -> ()

let find_target state (name : Syntax.name) = state.resolved.names.(name.id)

let decide_default_literal state ~at type_ =
  let decide default =
    (match find_current_frame state with
    | Some frame -> decide_literals state ~at:frame.span ~is_default:false
    | None -> ());
    ignore (Unify.unify state.unifier type_ default);
    decide_literals state ~at ~is_default:true;
    default
  in
  match Unify.resolve state.unifier type_ with
  | Types.Literal (Integer_literal, _) -> decide (Types.make_builtin Int64)
  | Types.Literal (Float_literal, _) -> decide (Types.make_builtin Float64)
  | _ -> type_

let find_head state (value : Syntax.expression) = Resolve.find_head state.resolved value

let is_variant_name (member : Syntax.name) =
  member.text <> "" && member.text.[0] >= 'A' && member.text.[0] <= 'Z'

let show state type_ = Types.show (zonk state type_)

let find_literal_decision state type_ =
  let rec follow (type_ : Types.ty) =
    match type_ with
    | Literal (_, index) | Variable index -> (
        match Hashtbl.find_opt state.decisions index with
        | Some decision -> Some decision
        | None -> Option.bind (Hashtbl.find_opt state.unifier.type_solutions index) follow)
    | _ -> None
  in
  follow type_

let add_mismatch_diagnostic state ?(fixes = []) code (span : Source.Definition_span.t)
    ~(sides : (Types.ty * Types.ty) list) message =
  let other_fixes = fixes in
  match
    List.find_map
      (fun (decided, wanted) ->
        Option.map (fun decision -> (decision, wanted)) (find_literal_decision state decided))
      sides
  with
  | None -> add_diagnostic state ~fixes code span message
  | Some ({ decision_report = Some report; _ }, _) -> report
  | Some (decision, wanted) ->
      let name = read_span state decision.decided_local in
      let text = quote_span state name in
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
        add_diagnostic state code span
          ~notes:[ (decision.decided_at, note) ]
          ~fixes
          (message ^ " " ^ explanation)
      in
      decision.decision_report <- Some report;
      report

let add_mismatch state (span : Source.Definition_span.t) ~expected ~actual =
  let sides = [ (actual, expected); (expected, actual) ] in
  let expected = zonk state expected and actual = zonk state actual in
  match (resolve state actual, expected) with
  | Types.Literal (Integer_literal, _), _ when Types.is_float_type expected ->
      add_diagnostic state Integer_for_float span
        ~fixes:[ fix "Write it as a float." [ insert span.stop ".0" ] ]
        (Printf.sprintf "An integer literal is never a float, and `%s` is expected here."
           (Types.show expected))
  | _ ->
      add_mismatch_diagnostic state Mismatch span ~sides
        (Printf.sprintf "Expected `%s`, found `%s`." (Types.show expected) (Types.show actual))

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

let rec find_call_with_mode_keyword state (value : Syntax.expression) =
  match value.kind with
  | Call ({ kind = Member (base, _); _ }, _)
  | Call ({ kind = Bracket ({ kind = Member (base, _); _ }, _); _ }, _) ->
      if is_place state base then Some value.id else find_call_with_mode_keyword state base
  | Member (base, _) | Bracket (base, _) | Try base -> find_call_with_mode_keyword state base
  | _ -> None

let check_resource state (resource : Syntax.resource) =
  let check_capability (path : Syntax.path_type) (method_ : Syntax.name option) =
    let shown = Interface.Elaborator.show_path path.path in
    match find_target state path.path.last with
    | Some (Definition (Capability, capability)) -> (
        match method_ with
        | Some method_ when state.lookups.interface.names.list_members capability method_.text = []
          ->
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
  | Calls (Call_capability path) -> check_capability path None
  | Calls (Call_method (path, method_)) -> check_capability path (Some method_)
  | Calls (Call_parameter name) -> (
      match find_target state name with
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

let make_slice state ~origin (base : Core.place) ~start ~stop ~inclusive : Core.kind =
  let make = make_synthetic_expression state ~origin in
  let uint64 = Types.make_builtin UInt64 in
  let path, type_arguments =
    match Core_walk.compute_place_type base with
    | Types.Named { path; arguments } -> (path, arguments)
    | type_ -> raise_bug "a slice of `%s`" (Types.show type_)
  in
  let make_callee name : Core.callee =
    Function { path = Method { owner = path; name; receiver = Read }; type_arguments }
  in
  let build_read_argument = Operands.build_argument Read in
  let start = match start with Some start -> start | None -> make uint64 (Integer Z.zero) in
  match stop with
  | None ->
      Slice { base; callee = make_callee "slice_from"; bounds = [ build_read_argument start ] }
  | Some stop ->
      let stop =
        if inclusive then
          make uint64
            (Operator { operation = Add; arguments = [ stop; make uint64 (Integer Z.one) ] })
        else stop
      in
      Slice
        {
          base;
          callee = make_callee "slice_range";
          bounds = [ build_read_argument start; build_read_argument stop ];
        }

type conversion = From_never | Owned_to_view | Function_widening | To_integer | From_integer

let convert state env ?argument ?expression (span : Source.Definition_span.t) ~actual ~expected =
  let is_argument = Option.is_some argument in
  let record_conversion (conversion : conversion option) =
    match (conversion, expression) with
    | Some conversion, Some id ->
        let before = state.form.expression_builders.(id) in
        state.form.expression_builders.(id) <-
          Option.map
            (fun build () ->
              let inner : Core.expression = build () in
              let expected = finalize_type state expected in
              let convert conversion =
                make_synthetic_expression state ~origin:id expected
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
                  make_synthetic_expression state ~origin:id expected
                    (make_slice state ~origin:id base ~start:None ~stop:None ~inclusive:false)
              | Owned_to_view -> (
                  match inner.type_ with
                  | Types.Named { path; arguments } ->
                      make_synthetic_expression state ~origin:id expected
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
                  | other -> raise_bug "`%s` is viewed and has no view" (Types.show other)))
            before
    | _ -> ()
  in
  record_conversion
  @@
  let actual_type = normalize state actual and wanted = normalize state expected in
  let refuse () =
    report_mismatch state span ~expected ~actual;
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
                (Well_known.make_path List, Well_known.make_path Slice);
                (Well_known.make_path String, Well_known.make_path String_slice);
              ] ->
      if not (Unify.unify_arguments state.unifier wanted_named.arguments actual_named.arguments)
      then report_mismatch state span ~expected ~actual;
      Some Owned_to_view
  | Types.Integer, _, Some _ when is_argument && env.specification && is_integer_type state wanted
    ->
      Some From_integer
  | Types.Literal (Integer_literal, index), Types.Integer, _
    when env.specification && Hashtbl.mem state.unifier.code_literals index ->
      Some To_integer
  | _, Types.Integer, _ when env.specification && is_integer_type state actual_type ->
      Some To_integer
  | Types.Function actual_function, Types.Function wanted_function, _
    when not (Types.has_same_clauses actual_function wanted_function) ->
      let unlisted =
        Types.compute_missing_capabilities ~required:actual_function.uses
          ~available:wanted_function.uses
      in
      let unknown =
        Types.has_unsolved_capabilities actual_function.uses
        || Types.has_unsolved_capabilities wanted_function.uses
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
                  report_mismatch state span ~expected:(finalize_type state expected)
                    ~actual:(finalize_type state actual));
            }
            :: state.capability_constraints;
        Some Function_widening
      end
      else refuse ()
  | _ -> if Unify.unify state.unifier wanted actual_type then None else refuse ()
