type local = { name : string; type_ : Types.ty; is_var : bool; mode : Types.mode }

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
  restriction : Types.capability_set option;
  superset : Types.capability_set;
  report_missing : Types.capability_set -> unit;
}

type narrowing_reason =
  | Integer_literal of Z.t
  | Float_literal
  | Negation
  | Shift_amount
  | Integer_operand of string
  | Range_element of string
  | Range_pattern
  | Sealed_bound of Path.t
  | Method_receiver of string

type narrowing = {
  variable : int;
  narrowed_at : Source.Definition_span.t;
  members : Scalar_set.t;
  reason : narrowing_reason;
}

type requirement =
  | Implements of {
      trait : Types.trait_reference;
      span : Source.Definition_span.t;
      on_met : Interface.Impls.evidence -> unit;
      on_unmet : Types.ty -> (string * Types.ty) option -> Diagnostic.reported;
    }
  | Within of {
      members : Scalar_set.t;
      reason : narrowing_reason;
      span : Source.Definition_span.t;
      on_met : Types.ty -> unit;
    }
  | When_solved of (Types.ty -> unit)

type obligation = { subject : Types.ty; requirement : requirement }

type frame = {
  level : int;
  mutable recorded_expressions : int list;
  mutable recorded_loops : (Syntax.id * Syntax.id) list;
  mutable bindings : int list;
  mutable declared : int list;
  mutable obligations : obligation list;
  mutable reported_unmet_bounds : (Types.ty * Types.trait_reference * Diagnostic.reported) list;
  mutable compiled_expressions : int list;
  mutable compiled_bindings : int list;
  mutable specification_only_report : Diagnostic.reported option;
  frame_specification : bool;
  span : Source.Definition_span.t;
}

type undecided_literal = { index : int; local : Syntax.id }
type default_site = At_method_call | At_statement

type literal_decision = {
  decided_local : Syntax.id;
  decided_type : Types.ty;
  decided_at : Source.Definition_span.t;
  default : default_site option;
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
  mutable keyword_modes : (Syntax.id * Types.mode) list;
  mutable places_without_keyword : (Syntax.id * Types.mode) list;
  mutable mode_keywords : Core.mode_keyword list;
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
  mutable unmet_impls : (Types.ty * Types.trait_reference * Diagnostic.reported) list;
  mutable narrowings : narrowing list;
  mutable associated_outputs : (Types.ty * Types.ty) list;
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

let record_loop state ~loop ~(iterable : Syntax.expression) record =
  state.tables.loops.(loop) <- Some record;
  match find_current_frame state with
  | Some frame -> frame.recorded_loops <- (loop, iterable.id) :: frame.recorded_loops
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

let resolve state type_ = Unify.resolve state.unifier type_
let zonk state type_ = Unify.zonk state.unifier type_
let make_fresh_type state = Unify.make_fresh_type state.unifier
let show state type_ = Types.show (zonk state type_)

let is_within state members type_ =
  match Unify.list_possible_members state.unifier type_ with
  | Some possible -> Scalar_set.is_subset possible ~of_:members
  | None -> false

let is_integer_type state type_ =
  match resolve state type_ with
  | Types.Number_variable _ -> false
  | resolved -> is_within state Scalar_set.fixed_width_integers resolved

let record_narrowing state ~variable ~(span : Source.Definition_span.t) ~members reason =
  state.narrowings <- { variable; narrowed_at = span; members; reason } :: state.narrowings

let describe state type_ =
  match resolve state type_ with
  | Types.Number_variable index -> Scalar_set.describe (Unify.read_domain state.unifier index)
  | resolved -> Types.describe (zonk state resolved)

let explain_narrowing state reason ~found =
  let shown = describe state found in
  let possible = Unify.list_possible_members state.unifier found in
  let is_number_variable =
    match resolve state found with Types.Number_variable _ -> true | _ -> false
  in
  let is_subset members =
    match possible with
    | Some possible -> Scalar_set.is_subset possible ~of_:members
    | None -> false
  in
  let may_be members =
    match possible with
    | Some possible -> not (Scalar_set.is_empty (Scalar_set.inter possible members))
    | None -> false
  in
  let explain_negation () : Diagnostic.Code.types * string =
    if is_number_variable then
      (Negated_unsigned, Printf.sprintf "This value is %s, so it cannot be negated." shown)
    else if is_subset Scalar_set.unsigned_integers then
      (Negated_unsigned, Printf.sprintf "%s is unsigned, so it cannot be negated." shown)
    else if may_be Scalar_set.unsigned_integers then
      (Negated_unsigned, Printf.sprintf "%s may be unsigned, so it cannot be negated." shown)
    else (No_impl, Printf.sprintf "%s cannot be negated." shown)
  in
  match reason with
  | Integer_literal value -> (
      if Z.sign value < 0 && is_subset Scalar_set.unsigned_integers then Some (explain_negation ())
      else
        match Option.bind possible Scalar_set.find_common_range with
        | Some (low, high) ->
            Some
              ( Literal_out_of_range,
                Printf.sprintf "`%s` does not fit in %s, which holds %s to %s." (Z.to_string value)
                  shown (Z.to_string low) (Z.to_string high) )
        | None -> None)
  | Float_literal ->
      if is_subset Scalar_set.floats then
        Some
          ( Literal_out_of_range,
            Printf.sprintf "This literal is too large for %s; it would round to infinity." shown )
      else None
  | Negation -> Some (explain_negation ())
  | Shift_amount ->
      Some (Mismatch, Printf.sprintf "A shift amount is an unsigned integer, not %s." shown)
  | Integer_operand operation ->
      Some (No_impl, Printf.sprintf "%s on built-in integers, not %s." operation shown)
  | Range_element described ->
      Some (Not_indexable, Printf.sprintf "%s range is of integers, not %s." described shown)
  | Range_pattern ->
      Some
        ( Mismatch,
          Printf.sprintf "A range pattern matches an integer or a `Character`, not %s." shown )
  | Sealed_bound _ | Method_receiver _ -> None

let find_excluding_narrowing state root wanted =
  match Unify.list_possible_members state.unifier wanted with
  | None -> None
  | Some possible ->
      List.find_opt
        (fun narrowing ->
          resolve state (Types.Number_variable narrowing.variable) = Types.Number_variable root
          && not (Scalar_set.is_subset possible ~of_:narrowing.members))
        (List.rev state.narrowings)

let lookup_bounds state parameter = Interface.Elaborator.list_bounds state.context parameter

let find_unmet_impl state subject (trait : Types.trait_reference) =
  List.find_map
    (fun (unmet_subject, unmet_trait, report) ->
      if Types.equal unmet_subject subject && unmet_trait = { trait with associated = [] } then
        Some report
      else None)
    state.unmet_impls

let describe_associated_type state base (trait : Types.trait_reference) name =
  Printf.sprintf "the `%s` of `%s` under `%s`" name (show state base)
    (Types.show_trait { (Unify.zonk_trait state.unifier trait) with associated = [] })

let describe_compared_type state type_ =
  match zonk state type_ with
  | Projection { base; trait; name } -> describe_associated_type state base trait name
  | zonked -> Printf.sprintf "`%s`" (Types.show zonked)

let describe_projection_mismatch state base trait name ~actual ~wanted =
  let associated_type = describe_associated_type state base trait name in
  if
    Types.equal (zonk state actual)
      (zonk state (Types.Projection { base; trait = { trait with associated = [] }; name }))
  then
    Printf.sprintf "%s may differ from %s."
      (String.capitalize_ascii associated_type)
      (describe_compared_type state wanted)
  else
    Printf.sprintf "%s is %s, and %s is expected."
      (String.capitalize_ascii associated_type)
      (describe_compared_type state actual)
      (describe_compared_type state wanted)

let find_associated_output state projection =
  let zonked = zonk state projection in
  List.find_map
    (fun (original, output) ->
      if Types.equal (zonk state original) zonked then Some output else None)
    state.associated_outputs

let make_associated_output state (frame : frame) base (trait : Types.trait_reference) name =
  let output = make_fresh_type state in
  let projection = Types.Projection { base; trait; name } in
  state.associated_outputs <- (projection, output) :: state.associated_outputs;
  Option.iter
    (fun level -> Unify.lower state.unifier ~level output)
    (Unify.find_lowest_level state.unifier
       (List.filter
          (function Unify.Unknown_number _ -> false | _ -> true)
          (Unify.list_unknowns state.unifier projection)));
  let report base mismatch =
    match mismatch with
    | Some (_, actual) ->
        add_diagnostic state Mismatch frame.span
          (describe_projection_mismatch state base trait name ~actual ~wanted:output)
    | None -> (
        match find_unmet_impl state base { trait with associated = [] } with
        | Some report -> report
        | None ->
            add_diagnostic state No_impl frame.span
              (Printf.sprintf "`%s` does not implement `%s`, so it has no `%s`." (show state base)
                 (Types.show_trait { (Unify.zonk_trait state.unifier trait) with associated = [] })
                 name))
  in
  frame.obligations <-
    {
      subject = base;
      requirement =
        Implements
          {
            trait = { trait with associated = [ (name, output) ] };
            span = frame.span;
            on_met = ignore;
            on_unmet = report;
          };
    }
    :: frame.obligations;
  output

let record_associated_output state projection output =
  state.associated_outputs <- (projection, output) :: state.associated_outputs

let rec flatten_associated_types state type_ =
  Types.map
    (function
      | Types.Projection { base; trait; name } ->
          let base = flatten_associated_types state base in
          let trait =
            {
              trait with
              trait_arguments =
                List.map
                  (function
                    | Types.Type argument -> Types.Type (flatten_associated_types state argument)
                    | value -> value)
                  trait.trait_arguments;
            }
          in
          let projection = Types.Projection { base; trait; name } in
          let has_unknowns = Unify.list_unknowns state.unifier projection <> [] in
          Some
            (match (find_associated_output state projection, find_current_frame state) with
            | Some output, _ when has_unknowns -> output
            | Some output, _ -> (
                match resolve state output with Types.Error _ as error -> error | _ -> projection)
            | None, Some frame when has_unknowns ->
                make_associated_output state frame base trait name
            | None, _ -> projection)
      | _ -> None)
    type_

let normalize state type_ =
  flatten_associated_types state
    (Interface.Impls.normalize state.lookups.interface ~list_bounds:(lookup_bounds state)
       (zonk state type_))

let solve_hook : (state -> Types.ty -> unit) ref = ref (fun _ _ -> ())

let is_associated_output state type_ =
  match resolve state type_ with
  | Types.Variable index ->
      List.exists
        (fun (_, output) -> resolve state output = Types.Variable index)
        state.associated_outputs
  | _ -> false

let read_head state type_ =
  let normalized = normalize state type_ in
  if is_associated_output state normalized then begin
    !solve_hook state normalized;
    normalize state type_
  end
  else normalized

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
      | Types.Variable _ | Types.Number_variable _ -> Some (make_unsolved_type state)
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
  Unify.unify state.unifier (normalize state left) (normalize state right)

let unify_as_hint state actual expected =
  let deferred_capability_equalities = state.unifier.deferred_capability_equalities in
  let frozen = state.unifier.frozen in
  let actual = normalize state actual and expected = normalize state expected in
  state.unifier.frozen <-
    List.filter_map
      (fun (_, output) ->
        match resolve state output with Types.Variable index -> Some index | _ -> None)
      state.associated_outputs;
  ignore (Unify.unify state.unifier actual expected);
  state.unifier.frozen <- frozen;
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

let decide_binding_mode state (mode : Types.mode) type_ : Types.mode =
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

let make_callee state (target : Core.operand Core.target) =
  Callee_uses.make_callee state.lookups.interface ~list_bounds:(lookup_bounds state) target

let make_call state ~callee ~arguments ~lends =
  Callee_uses.make_call state.lookups.interface ~list_bounds:(lookup_bounds state) ~callee
    ~arguments ~lends

let convert_evidence = function
  | Interface.Impls.From_impl { impl; substitution } -> Tables.Impl { impl; substitution }
  | Interface.Impls.From_bound -> Tables.Bound
  | Interface.Impls.From_any -> Tables.Dynamic
  | Interface.Impls.Built_in | Undetermined | Absorbed _ -> Tables.Built_in

let make_trait_reference ~arguments trait : Types.trait_reference =
  { trait; trait_arguments = arguments; associated = [] }

let string_type = Types.Named { path = Well_known.make_path String; arguments = [] }

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
  Hashtbl.replace state.locals name.id { name = name.text; type_; is_var; mode };
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
let find_head state (value : Syntax.expression) = Resolve.find_head state.resolved value

let is_variant_name (member : Syntax.name) =
  member.text <> "" && member.text.[0] >= 'A' && member.text.[0] <= 'Z'

let find_literal_decision state type_ =
  let rec follow (type_ : Types.ty) =
    match type_ with
    | Number_variable index | Variable index -> (
        match Hashtbl.find_opt state.decisions index with
        | Some decision -> Some decision
        | None -> Option.bind (Hashtbl.find_opt state.unifier.type_solutions index) follow)
    | _ -> None
  in
  follow type_

let add_mismatch_diagnostic state ?(fixes = []) code (span : Source.Definition_span.t)
    ~(sides : (Types.ty * Types.ty) list) message =
  let other_fixes = fixes in
  let narrowed =
    List.find_map
      (fun (decided, wanted) ->
        match resolve state decided with
        | Types.Number_variable root ->
            Option.map
              (fun narrowing -> (narrowing, wanted))
              (find_excluding_narrowing state root wanted)
        | _ -> None)
      sides
  in
  match narrowed with
  | Some (narrowing, wanted) -> (
      let use_note = (span, Printf.sprintf "It is used as %s here." (describe state wanted)) in
      match explain_narrowing state narrowing.reason ~found:wanted with
      | Some (narrowing_code, explanation) ->
          add_diagnostic state ~notes:[ use_note ] narrowing_code narrowing.narrowed_at explanation
      | None ->
          add_diagnostic state ~fixes
            ~notes:
              [
                ( narrowing.narrowed_at,
                  Printf.sprintf "Here it becomes %s." (Scalar_set.describe narrowing.members) );
              ]
            code span message)
  | None -> (
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
            match decision.default with
            | Some At_method_call ->
                ( Printf.sprintf
                    "%s took its default type, `%s`, at a method call that needs its type." local
                    decided,
                  Printf.sprintf
                    "This call needs the type of %s, so %s takes its default type `%s` here." local
                    local decided )
            | Some At_statement ->
                ( Printf.sprintf
                    "%s took its default type, `%s`, at a statement whose types depend on it." local
                    decided,
                  Printf.sprintf
                    "A type in this statement depends on the type of %s, so %s takes its default \
                     type `%s` here."
                    local local decided )
            | None ->
                ( Printf.sprintf "An earlier statement decided that the type of %s is `%s`." local
                    decided,
                  Printf.sprintf "This statement decides that the type of %s is `%s`." local decided
                )
          in
          let fixes =
            if
              Option.is_some decision.default
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
          report)

let add_mismatch state (span : Source.Definition_span.t) ~expected ~actual =
  let sides = [ (actual, expected); (expected, actual) ] in
  let expected = normalize state expected and actual = normalize state actual in
  match (resolve state actual, expected) with
  | Types.Number_variable index, _
    when Types.is_float_type expected
         && Scalar_set.is_subset
              (Unify.read_domain state.unifier index)
              ~of_:(Scalar_set.union Scalar_set.fixed_width_integers (Scalar_set.make [ Integer ]))
    ->
      add_diagnostic state Integer_for_float span
        ~fixes:[ fix "Write it as a float." [ insert span.stop ".0" ] ]
        (Printf.sprintf "An integer literal is never a float, and `%s` is expected here."
           (Types.show expected))
  | _ ->
      add_mismatch_diagnostic state Mismatch span ~sides
        (Printf.sprintf "Expected %s, found %s." (describe state expected) (describe state actual))

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

let check_resource state (resource : Syntax.resource) =
  let check_capability (path : Syntax.path_type) (method_ : Syntax.name option) =
    let shown = Interface.Elaborator.show_path path.path in
    match find_target state path.path.last with
    | Some (Definition (Capability, capability)) -> (
        match method_ with
        | Some method_
          when Option.is_none
                 (state.lookups.interface.names.find_key
                    (Path.make_capability_method capability method_.text)) ->
            report state Unknown_member (read_span state method_.id)
              (Printf.sprintf "`%s` has no method `%s`." shown method_.text)
        | _ -> ())
    | Some (Unknown _) -> ()
    | _ ->
        report state Not_a_capability (read_span state path.id)
          (Printf.sprintf "`calls` counts the calls of a capability, and `%s` is not one." shown)
  in
  match resource with
  | Metric _ -> ()
  | Calls (Call_capability path) -> check_capability path None
  | Calls (Call_method (path, method_)) -> check_capability path (Some method_)
  | Calls (Call_parameter name) -> (
      match (find_target state name, find_local_type state name) with
      | Some (Local _), (Some (Types.Function _ | Types.Error _ | Types.Hole) | None) -> ()
      | Some (Local _), Some other ->
          report state Not_callable (read_span state name.id)
            (Printf.sprintf "`calls` counts the calls through a function, and `%s` is a `%s`."
               name.text (Types.show other))
      | Some (Unknown _), _ -> ()
      | _ ->
          report state Not_callable (read_span state name.id)
            (Printf.sprintf
               "`calls` counts the calls through a parameter that is a function, or of a \
                capability, and `%s` is neither."
               name.text))

let check_operand_clause state (cost : Syntax.cost) (operand : Interface.Elaborator.cost_operand) =
  let span = read_span state operand.written.id in
  let cost_function = operand.cost_function.text in
  let callee =
    match operand.callee with
    | Function_parameter name -> name.text
    | Bound_method { type_; method_ } -> (
        match Interface.Elaborator.find_bounded_type state.context type_ with
        | Some self_type -> Printf.sprintf "%s.%s" (Types.show self_type) method_.text
        | None -> "...")
    | Not_a_callee -> "..."
  in
  let shown = Printf.sprintf "%s(%s)" cost_function callee in
  (match cost.resource with
  | Metric bounded when bounded = operand.metric -> ()
  | Metric bounded ->
      let bounded = Metric.show bounded in
      report state Cost_of_other_resource span
        ~fixes:
          [
            fix
              (Printf.sprintf "Write `%s`." bounded)
              [ replace (read_span state operand.cost_function.id) bounded ];
          ]
        (Printf.sprintf
           "`%s` bounds the `%s` of one call, not its `%s`, which this clause bounds. Write \
            `%s(%s)`."
           shown cost_function bounded bounded callee)
  | Calls _ ->
      report state Cost_of_other_resource span
        (Printf.sprintf
           "`%s` bounds the `%s` of one call, not the calls it makes, which this clause counts."
           shown cost_function));
  match cost.bound with
  | Exactly _ ->
      report state Upper_bound_in_exact_bound span
        (Printf.sprintf
           "`%s` is an upper bound on one call, and a call may spend less, so an exact amount that \
            names it would be false for that call. State this bound with `<=` or `O(...)`."
           shown)
  | Big_o _ | At_most _ -> ()

let check_cost state (cost : Syntax.cost) =
  check_resource state cost.resource;
  match cost.bound with
  | Big_o value | At_most value | Exactly value ->
      List.iter (check_operand_clause state cost)
        (Interface.Elaborator.list_cost_operands state.context value)

let make_slice state ~origin (base : Core.place) ~start ~stop ~inclusive : Core.kind =
  let make = make_synthetic_expression state ~origin in
  let uint64 = Types.make_builtin UInt64 in
  let path, type_arguments =
    match Core_walk.compute_place_type base with
    | Types.Named { path; arguments } -> (path, arguments)
    | type_ -> raise_bug "a slice of `%s`" (Types.show type_)
  in
  let make_method_callee name =
    make_callee state
      (Function
         {
           path = Method { owner = path; name; receiver = Read };
           instantiation = { Types.no_instantiation with type_arguments };
         })
  in
  let build_read_argument = Operands.build_argument Read in
  let start = match start with Some start -> start | None -> make uint64 (Integer Z.zero) in
  match stop with
  | None ->
      Slice
        { base; callee = make_method_callee "slice_from"; bounds = [ build_read_argument start ] }
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
          callee = make_method_callee "slice_range";
          bounds = [ build_read_argument start; build_read_argument stop ];
        }

type conversion =
  | From_never
  | Owned_to_view
  | View_to_owned
  | Function_widening
  | To_integer
  | From_integer

let find_view_as state ~owned ~view =
  match (Types.find_view (normalize state owned), normalize state view) with
  | Some (Types.Named found as found_view), Types.Named wanted
    when Path.equal found.path wanted.path ->
      Some found_view
  | _ -> None

let find_owner_as state ~view ~owner =
  match normalize state owner with
  | Types.Named { path; _ } as owner when Well_known.is List path || Well_known.is String path ->
      find_view_as state ~owned:owner ~view
  | _ -> None

let convert state env ?argument ?(takes_view_as_owner = false) ?expression
    (span : Source.Definition_span.t) ~actual ~expected =
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
              | View_to_owned -> convert View_to_owned
              | Owned_to_view
                when argument = Some Types.Mut
                     && (Types.is_well_known List inner.type_ || Types.is_builtin Array inner.type_)
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
                           (make_call state
                              ~callee:
                                (Function
                                   {
                                     path = Method { owner = path; name = "slice"; receiver = Read };
                                     instantiation =
                                       { Types.no_instantiation with type_arguments = arguments };
                                   })
                              ~arguments:[ Operands.build_argument Read inner ]
                              ~lends:None))
                  | other -> raise_bug "`%s` is viewed and has no view" (Types.show other)))
            before
    | _ -> ()
  in
  record_conversion
  @@
  let actual_type = read_head state actual and wanted = read_head state expected in
  let refuse () =
    report_mismatch state span ~expected ~actual;
    None
  in
  let between_owner_and_view =
    match if is_argument then find_view_as state ~owned:actual ~view:expected else None with
    | Some view -> Some (Owned_to_view, wanted, view)
    | None when takes_view_as_owner ->
        Option.map
          (fun view -> (View_to_owned, actual_type, view))
          (find_owner_as state ~view:actual ~owner:expected)
    | None -> None
  in
  match between_owner_and_view with
  | Some (conversion, written_view, view) ->
      if not (Unify.unify state.unifier written_view view) then
        report_mismatch state span ~expected ~actual;
      Some conversion
  | None -> (
      match (actual_type, wanted, expression) with
      | Types.Never, _, _ -> Some From_never
      | Types.Integer, _, Some _
        when is_argument && env.specification && is_integer_type state wanted ->
          Some From_integer
      | Types.Number_variable index, Types.Integer, _
        when env.specification
             && not (Scalar_set.mem Integer (Unify.read_domain state.unifier index)) ->
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
            && proven
          then begin
            if unlisted <> Types.no_capabilities then
              state.capability_constraints <-
                {
                  subset = actual_function.uses;
                  restriction = None;
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
      | _ -> if Unify.unify state.unifier wanted actual_type then None else refuse ())
