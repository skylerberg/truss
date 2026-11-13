(* The state of the type checker while it checks one definition, and the
   helpers that every part of the checker uses: reporting diagnostics,
   recording types, unification, and places. *)

open Syntax
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

type local = { type_ : Types.ty; is_var : bool; mode : Types.mode }

(* The context of the code that is being checked. *)
type env = {
  output : Types.result option;
      (** The result of the enclosing function or lambda. [return] and [yield] are checked against
          it. *)
  specification : bool;
      (** The code is a specification: a contract, a [proof] block, or the body of a function for
          specifications only. *)
  self : Types.ty option;  (** The type of [self]. *)
  self_mode : Types.mode;  (** The mode of [self]. Only [mut self] can be mutated. *)
  loop_element : Types.ty option;
      (** In the clauses of a [for] loop: the type of the loop's elements. [yielded] is a sequence
          of them. *)
  compile_time : bool;
      (** The expression is a constant expression, which the compiler evaluates: the value of a
          constant, or a default. *)
  in_quantifier : bool;
      (** In a quantifier's body, which the prover reads as a formula in code as in a specification.
      *)
}

(* Whether an expression runs in the compiled program. A specification
   does not run, and the compiler evaluates a constant expression. Only
   code that runs moves values, so only there must a value be owned. *)
let runs (env : env) = not (env.specification || env.compile_time)

(* A constraint between two capability sets: every capability in [subset]
   must be in [superset]. Either set may contain capability variables.

   Constraints are collected while a definition is checked and solved at
   the end. Solving grows each variable in a
   [superset] until the constraint holds. If a constraint still fails after
   solving (because its [superset] has no variable to grow), the solver
   calls [report_missing] with the capabilities that [superset] lacks. *)
type subset_constraint = {
  subset : Types.capability_set;
  superset : Types.capability_set;
  report_missing : Types.capability_set -> unit;
}

(* The state of the check of one statement. Types are inferred one
   statement at a time. *)
type frame = {
  start : int;  (** The first inference variable created for the statement. *)
  mutable nodes : int list;  (** The expressions whose types were recorded for the statement. *)
  mutable bindings : int list;
      (** The locals whose types the statement finishes: those it declares, and those of inner
          statements whose types were not solved there. *)
  mutable declared : int list;  (** The locals that the statement itself declares. *)
  mutable pending : (unit -> bool) list;
      (** Deferred checks that need a type that is not inferred yet. Each returns whether it is
          done. *)
  mutable unmet : (Types.ty * Types.trait_reference) list;
      (** The trait bounds already reported as not satisfied, with their types, so that each is
          reported once per statement. *)
  frame_specification : bool;
  span : span;
}

(* A literal type in the type of a local that the local's declaration left
   undecided, as in [let limit = 10]. It is undecided past the declaration,
   so a later statement may decide it, as in [count < limit] with a [UInt8]
   count. The enclosing statement of the declaration owns it, and gives it
   its default type if no statement in between decides it. *)
type undecided_literal = {
  index : int;  (** The index of the [Literal] variable. *)
  kind : Types.literal_kind;
  local : id;
  owner : frame;
}

(* How a statement after a local's declaration decided the literal type of
   the local. *)
type literal_decision = {
  decided_local : id;
  decided_type : Types.ty;
  decided_at : span;  (** The statement that decided it. *)
  is_default : bool;
      (** A method call on the local gave it its default type, because method lookup needs the type
          of the receiver. *)
  mutable decision_report : Diagnostic.reported option;
      (** The mismatch reported for the decision. Every later mismatch of the local reuses it. *)
}

(* The core form under construction. Each array is indexed by syntax id
   and holds a function that builds the core node for that syntax node.
   The checker registers a builder when it checks the syntax node. The
   builders run after the whole definition is checked, when every type is
   final. *)
type form = {
  expression_builders : (unit -> Core.expression) option array;
  statement_builders : (unit -> Core.statement) option array;
  pattern_builders : (unit -> Core.pattern) option array;
  mutable definition_builder : (unit -> Core.definition) option;
  mutable next_node_id : int;
  mutable next_synthetic_local : int;
  mutable tables_with_holes : Tables.t option;
      (** Set while the builders run, if a type in the definition is a hole. The core form has no
          hole type: a [todo] whose type is not inferred has the type [Never] there. So while the
          builders run, [state.tables] is a copy in which every hole is [Never], and this field
          holds the tables as the checker recorded them. *)
}

type state = {
  database : Query.context;
  key : Names.key;
  package : Path.package;
  definition : definition;
  resolved : Resolve.resolved;
  context : Lower.context;
  text : string;  (** The definition's source text, for fixes. *)
  mutable tables : Tables.t;
  form : form;
  mutable diagnostics : Syntax.diagnostic list;
  unifier : Unify.t;
  locals : (id, local) Hashtbl.t;
  mutable law_parameters : (string * Types.ty) list;
      (** In a law's proof, the law's parameters, with [Self] and the trait's parameters replaced by
          the proof's type and trait arguments. *)
  mutable frames : frame list;
  mutable references : id list;  (** Locals read, newest first, for lambdas' captures. *)
  mutable receiver_modes : (id * Types.mode) list;
      (** Method calls whose receiver a mark covers. *)
  yielded : (id, Types.mode) Hashtbl.t;
      (** The operand of each [yield], and each field of a constructor that is in this table, with
          the mode of the [yield]. A field in this table that is a place is lent to the yielded
          value instead of moved into it. *)
  binding_spans : (id, span) Hashtbl.t;
      (** Where each name of the definition is, for lambdas' captures. *)
  mutable lambdas : span list;  (** The lambdas being checked, innermost first. *)
  mutable unsolved : Diagnostic.reported option;
      (** The report of the first statement whose types could not be inferred. *)
  mutable capability_constraints : subset_constraint list;
  mutable capability_solution : (int, Types.capability_set) Hashtbl.t option;
      (** The set each capability variable was solved to. [None] until the constraints are solved. A
          variable with no entry is the empty set. *)
  mutable evidence : Path.package list;  (** The packages whose [impl]s met a bound here. *)
  mutable undecided : undecided_literal list;
  decisions : (int, literal_decision) Hashtbl.t;
      (** Keyed by the [index] of the [undecided_literal]. *)
  annotatable : (id, unit) Hashtbl.t;
      (** The locals that an unannotated [let] or [for] declares by a plain name, where a fix can
          add a type after the name. *)
}

let reported state ?notes ?(fixes = []) code (span : span) message =
  let diagnostic = Diagnostic.make ?notes ~fixes ~code:(Types code) span message in
  state.diagnostics <- diagnostic :: state.diagnostics;
  Diagnostic.reported diagnostic

let report state ?fixes code span message = ignore (reported state ?fixes code span message)

(* Whether the code is read as a formula: a specification, a proof, the
   body of a function for specifications only, or a quantifier's body. A
   formula states a fact, so it holds no loop, [var], or early exit, and
   changes nothing, which would have no meaning in the prover's logic. *)
let is_formula env = env.specification || env.in_quantifier

let reject_in_formula state env span what =
  if is_formula env then
    report state Not_in_specification span
      (Printf.sprintf
         "%s runs, so it cannot be part of a specification, a proof, or a quantifier's body, which \
          the prover reads as formulas: they are built from `let`, `if`, `match`, and calls."
         what)

(* Raises a compiler bug. Used where an earlier stage guarantees that a
   case cannot happen. *)
let bug format = Compiler_bug.bug ~stage:"Infer" format

(* Reports a diagnostic and returns the error type that carries the
   report. Every operation on an error type is accepted, so one mistake is
   reported once. *)
let error state ?fixes code span message = Types.Error (reported state ?fixes code span message)

let source state (span : span) =
  if span.stop <= String.length state.text then
    String.sub state.text span.start (span.stop - span.start)
  else ""

let fresh_node_id state =
  let id = state.form.next_node_id in
  state.form.next_node_id <- id + 1;
  id

(* A core expression that desugaring introduces. It has no syntax node, so
   the caller supplies its origin and type. *)
let synthetic_expression state ~origin type_ kind : Core.expression =
  { id = fresh_node_id state; origin; type_; kind }

(* Registers the builder for an expression's core node. [kind] computes
   the node's kind. The node's type is the type the checker recorded for
   the expression. *)
let register_expression state (value : expression) kind =
  state.form.expression_builders.(value.id) <-
    Some
      (fun () ->
        let id = fresh_node_id state in
        match state.tables.types.(value.id) with
        | Some type_ -> { Core.id; origin = value.id; type_; kind = kind () }
        | None -> bug "`%s` has a node and no type" (source state value.span))

(* Holes

   A [todo] with no expected type has a hole type, and so does everything
   computed from it. The checker accepts any operation on a hole without
   resolving it. Evaluating a hole never returns, because the [todo] it
   comes from stops the program. The core form uses that:

   - a hole type is [Never];
   - a use of a local whose type is a hole is a [Todo];
   - a pattern that matches a hole is a [Wildcard];
   - an expression with an operand whose type is a hole is a block that
     evaluates the operands in order and ends in a [Todo];
   - a [for] loop over a hole, or an assignment to one, only evaluates the
     hole.

   So the form holds no operation that the checker did not resolve. *)

(* Whether the checker recorded a hole as the type of an entry of one of
   its tables. *)
let was_hole state (table : Tables.t -> Types.ty option array) (id : id) =
  match state.form.tables_with_holes with
  | Some tables -> (table tables).(id) = Some Types.Hole
  | None -> false

(* The sub-expressions that an expression evaluates before it does
   anything else. A part that has no core node of its own, such as the
   [receiver.name] of a method call or the range of a slice, is replaced
   by its own operands. *)
let rec operands state (value : expression) : expression list =
  let checked (part : expression) =
    if Option.is_some state.form.expression_builders.(part.id) then [ part ]
    else operands state part
  in
  match value.kind with
  (* The guards and bodies run after the patterns bind their names. *)
  | Match { scrutinees; _ } -> List.concat_map checked scrutinees
  | Quantified { binder = Binder_in (_, collection); _ } -> checked collection
  | Quantified { binder = Binder_type _; _ } -> []
  (* A branch runs only if the condition holds, and the condition is a
     [Bool]. An alias evaluates nothing itself. *)
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
      (* Creating a closure has no effect, and the checker did not resolve
         the parameters of a lambda that is passed to a hole. *)
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
                    value = (match node.kind with Use place -> Place place | _ -> Value node);
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
    | None -> bug "`%s` has no node in the core form" (source state value.span)

let register_statement state (written : statement) kind =
  state.form.statement_builders.(written.id) <-
    Some (fun () -> { Core.id = fresh_node_id state; origin = written.id; kind = kind () })

let build_statement state (written : statement) : Core.statement =
  let rec unmarked (value : expression) =
    match value.kind with Mode (_, inner) | Parenthesized inner -> unmarked inner | _ -> value
  in
  let hole (value : expression) =
    let value = unmarked value in
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
      | None -> bug "`%s` has no node in the core form" (source state written.span))

(* Registers the builder for a pattern's core node. The node's type is
   the type of the value the pattern matches. *)
let register_pattern state (written : pattern) kind =
  state.form.pattern_builders.(written.id) <-
    Some
      (fun () ->
        let id = fresh_node_id state in
        match state.tables.scrutinee_types.(written.id) with
        | Some type_ -> { Core.id; origin = written.id; type_; kind = kind () }
        | None -> bug "`%s` has a node and no type" (source state written.span))

let build_pattern state (written : pattern) : Core.pattern =
  if was_hole state (fun tables -> tables.scrutinee_types) written.id then
    { id = fresh_node_id state; origin = written.id; type_ = Types.Never; kind = Wildcard }
  else
    match state.form.pattern_builders.(written.id) with
    | Some build -> build ()
    | None -> bug "`%s` has no node in the core form" (source state written.span)

(* Makes an expression's core node the core node of [inner]. Used for
   parentheses and for a mode marker such as [mut value]. *)
let alias_expression state (value : expression) (inner : expression) =
  state.form.expression_builders.(value.id) <- Some (fun () -> build_expression state inner)

(* The place a core expression denotes. A [Use] denotes the place it
   reads. Any other expression is a value, which is stored in a
   [Temporary]. *)
let place_of (node : Core.expression) : Core.place =
  match node.kind with Use place -> place | _ -> Temporary node

let fresh_synthetic_local state : Core.local =
  let number = state.form.next_synthetic_local in
  state.form.next_synthetic_local <- number + 1;
  Synthetic number

let fix title edits = Diagnostic.fix title edits
let replace = Diagnostic.replace
let insert position text = Diagnostic.insert (Span.zero_width position) text
let current_frame state = match state.frames with frame :: _ -> Some frame | [] -> None

let record state (value : expression) type_ =
  state.tables.types.(value.id) <- Some type_;
  match current_frame state with Some frame -> frame.nodes <- value.id :: frame.nodes | None -> ()

let defer state check =
  match current_frame state with
  | Some frame -> if not (check ()) then frame.pending <- check :: frame.pending
  | None -> ignore (check ())

let resolve state type_ = Unify.resolve state.unifier type_
let zonk state type_ = Unify.zonk state.unifier type_
let fresh state = Unify.fresh state.unifier

(* Whether a type is a built-in integer type, or a type parameter that an
   integer trait bounds, which only those types implement. *)
let integer_type state (type_ : Types.ty) =
  Types.is_integer_type type_
  ||
  match type_ with
  | Parameter _ | Projection _ -> state.unifier.integer_range type_ <> None
  | _ -> false

(* Whether a type is a signed integer type, a built-in one or a parameter
   that [SignedInteger] bounds. *)
let signed_type state (type_ : Types.ty) =
  Types.is_signed type_
  ||
  match type_ with
  | Parameter _ | Projection _ -> (
      match state.unifier.integer_range type_ with Some (low, _) -> Z.sign low < 0 | None -> false)
  | _ -> false

let bounds state parameter =
  Option.value ~default:[] (Hashtbl.find_opt state.context.bounds parameter)

let normalize state type_ = Impls.normalize state.database ~bounds:(bounds state) (zonk state type_)

(* The error type for an inference variable that no statement solved. The
   first unsolved variable is reported, and later ones reuse that report,
   so an unsolved type is never stored without a diagnostic. *)
let unsolved state =
  match state.unsolved with
  | Some report -> Types.Error report
  | None ->
      let report =
        reported state Cannot_infer
          (Span.make state.definition.span.start state.definition.span.start)
          "A type in this definition cannot be inferred. Give the `let` a type, or the call type \
           arguments."
      in
      state.unsolved <- Some report;
      Types.Error report

(* Replaces each capability variable in a set by its solution. Returns
   the set unchanged if the variables are not solved yet. *)
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

(* The final form of a type: inference variables replaced by their
   solutions, projections normalized, and capability variables replaced
   by their solutions. An unsolved inference variable becomes an error.
   While the core form is built, a hole becomes [Never]. *)
let rec final_type state type_ =
  Types.map ~capabilities:(final_capabilities state)
    (function
      | Types.Variable _ | Types.Literal _ -> Some (unsolved state)
      | Types.Hole when Option.is_some state.form.tables_with_holes -> Some Types.Never
      | _ -> None)
    (normalize state type_)

(* The final form of a set of capabilities: each associated capability set
   replaced by the capabilities that the [impl] of its type defines, and
   each capability variable replaced by its solution. *)
and final_capabilities state capabilities =
  resolve_capabilities state
    (Impls.normalize_capabilities state.database ~bounds:(bounds state)
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

(* Unifies two types. Projections are normalized first, so [Tables.Key] unifies
   with the type that the [impl] assigns to [Key]. *)
let unify state left right =
  let normalize type_ =
    Impls.normalize state.database ~bounds:(bounds state) (Unify.zonk state.unifier type_)
  in
  Unify.unify state.unifier (normalize left) (normalize right)

(* Unifies a call's result type with the expected type before the call's
   arguments are checked, so that the type arguments inferred here are known
   while the arguments are checked. Capability sets are excluded: a function
   value may be widened to a type with more [uses], and [convert] compares
   the capability sets when it checks the value. *)
let unify_as_hint state actual expected =
  let deferred_capability_equalities = state.unifier.deferred_capability_equalities in
  ignore (unify state actual expected);
  state.unifier.deferred_capability_equalities <- deferred_capability_equalities

(* Normalizes the type arguments and the associated types of a trait
   reference, as [normalize] does for a type. *)
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
  Impls.implements state.database ~bounds:(bounds state) (normalize state type_)
    (normalize_trait state trait)

let copyable state type_ = Impls.copyable state.database ~bounds:(bounds state) (zonk state type_)
let plain state type_ = Impls.plain state.database ~bounds:(bounds state) (zonk state type_)
let is_view state type_ = Impls.is_view state.database ~bounds:(bounds state) (zonk state type_)

(* The associated type [name] of a trait for a type. If the [impl] does
   not define it, the [impl] already has a diagnostic, and this returns an
   error type that carries that report. *)
let associated state type_ (trait : Types.trait_reference) name ~(at : span) =
  let type_ = normalize state type_ and trait = normalize_trait state trait in
  match Impls.associated_type state.database ~bounds:(bounds state) type_ trait name with
  | Some associated_type -> associated_type
  | None -> (
      let of_impl =
        match implements state type_ trait with
        | Some (Impls.From_impl { impl; _ }) -> Interface.Check.reported state.database impl
        | _ -> None
      in
      match of_impl with
      | Some report -> Types.Error report
      | None ->
          error state Unknown_associated_type at
            (Printf.sprintf "`%s` gives no `%s` as a `%s`." (Types.show type_) name
               (Types.show_trait trait)))

let evidence_of = function
  | Impls.From_impl { impl; substitution } -> Tables.Impl { impl; arguments = substitution }
  | Impls.From_bound -> Tables.Bound
  | Impls.From_any -> Tables.Dynamic
  | Impls.Built_in | Impls.Accepted _ -> Tables.Built_in

let trait_reference ?(arguments = []) trait : Types.trait_reference =
  { trait; trait_arguments = arguments; associated = [] }

let string_type = Types.Named { path = Well_known.path String; arguments = [] }
let undecided_type (undecided : undecided_literal) = Types.Literal (undecided.kind, undecided.index)

(* Records the decision of each undecided literal that a statement, or a
   method call at [at], has decided since the last check. *)
let decide_literals state ~(at : span) ~is_default =
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

(* Finishes the inference of a statement. An unsolved literal variable
   takes its default type, except one in the type of a local that the
   statement declares: that one is left for later statements to decide, and
   the enclosing statement gives it its default type. Any other unsolved
   variable that the statement created is an error. A type that mentions a
   variable of an enclosing statement is left for that statement. *)
let settle state frame =
  (* Unification deferred these equalities between capability sets because
     one side had a capability variable. An equality is two subset
     constraints. *)
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
    frame.pending <- loop frame.pending
  in
  run_pending ();
  let parent = match state.frames with _ :: parent :: _ -> Some parent | _ -> None in
  decide_literals state ~at:frame.span ~is_default:false;
  let types_of ids table = List.filter_map (fun id -> table.(id)) ids in
  let all_types () =
    types_of frame.nodes state.tables.types @ types_of frame.bindings state.tables.local_types
  in
  (* The type arguments of each call are checked too. A type argument that
     no parameter or result mentions is in no expression's type. *)
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
      frame.nodes
  in
  let unknowns () =
    List.concat_map (Unify.unknowns state.unifier) (all_types ())
    @ List.concat_map (Unify.argument_unknowns state.unifier) (call_arguments ())
  in
  (* A literal variable in the type of a local that the statement declares
     stays undecided, for a later statement to decide. A specification
     defaults a literal to [Integer] and code to [Int64], so a literal stays
     undecided only within one or the other. *)
  (match parent with
  | Some parent when parent.frame_specification = frame.frame_specification ->
      List.iter
        (fun local ->
          match state.tables.local_types.(local) with
          | Some type_ ->
              List.iter
                (function
                  | Unify.Unknown_literal (kind, index) when index >= frame.start ->
                      if not frame.frame_specification then
                        Hashtbl.replace state.unifier.code_literals index ();
                      state.undecided <- { index; kind; local; owner = parent } :: state.undecided
                  | _ -> ())
                (Unify.unknowns state.unifier type_)
          | None -> ())
        frame.declared
  | _ -> ());
  (* The literal variables that an enclosing statement owns. *)
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
  (* Any other unsolved literal variable of the statement takes its default
     type: [Int64] or [Float64], or [Integer] in a specification. *)
  List.iter
    (function
      | Unify.Unknown_literal (kind, index) when index >= frame.start && not (is_undecided index) ->
          Hashtbl.replace state.unifier.types index
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
        | Unify.Unknown_type index | Unknown_value index -> index >= frame.start
        | Unknown_literal (_, index) -> index >= frame.start && not (is_undecided index))
      (unknowns ())
  in
  (* The literals that the statement owns now have their types. *)
  state.undecided <-
    List.filter (fun (undecided : undecided_literal) -> undecided.owner != frame) state.undecided;
  if unsolved <> [] then begin
    let report =
      reported state Cannot_infer frame.span
        "The types in this statement cannot be inferred from it alone. Give the `let` a type, or \
         the call type arguments, such as `var names: List[String] = []`."
    in
    if Option.is_none state.unsolved then state.unsolved <- Some report;
    (* Each unsolved variable is bound to the error type, so it is reported
       once. *)
    List.iter
      (function
        | Unify.Unknown_type index | Unknown_literal (_, index) ->
            Hashtbl.replace state.unifier.types index (Types.Error report)
        | Unknown_value _ -> ())
      unsolved;
    (* The deferred checks wait on types that are now errors, so they are
       dropped. *)
    frame.pending <- []
  end;
  (* A type that mentions a variable of an enclosing statement, or an
     undecided literal, is finished again by the enclosing statement. *)
  let is_open = function
    | Unify.Unknown_type index | Unknown_value index -> index < frame.start
    | Unknown_literal (_, index) -> index < frame.start || is_undecided index
  in
  let finish table ids keep =
    List.iter
      (fun id ->
        match table.(id) with
        | Some type_ -> (
            let type_ = Impls.normalize state.database ~bounds:(bounds state) (zonk state type_) in
            table.(id) <- Some type_;
            if List.exists is_open (Unify.unknowns state.unifier type_) then
              match parent with Some parent -> keep parent id | None -> ())
        | None -> ())
      ids
  in
  finish state.tables.types frame.nodes (fun parent id -> parent.nodes <- id :: parent.nodes);
  finish state.tables.local_types frame.bindings (fun parent id ->
      parent.bindings <- id :: parent.bindings);
  match parent with Some parent -> parent.pending <- frame.pending @ parent.pending | None -> ()

let in_statement state env (span : span) body =
  let frame =
    {
      start = state.unifier.next + 1;
      nodes = [];
      bindings = [];
      declared = [];
      pending = [];
      unmet = [];
      frame_specification = env.specification;
      span;
    }
  in
  state.frames <- frame :: state.frames;
  let result = body () in
  settle state frame;
  state.frames <- List.tl state.frames;
  result

(* Whether a statement diverges: its expression has type [Never], or it
   is a [while true] loop with no [break]. *)
let rec statement_diverges state (written : statement) =
  match written.kind with
  | Expression value -> (
      match state.tables.types.(value.id) with
      | Some type_ -> resolve state type_ = Types.Never
      | None -> false)
  | While { condition = { kind = True; _ }; body; _ } -> not (Syntax_walk.contains_break body)
  (* A [parallel] or [concurrent] block ends only when every branch does. *)
  | Parallel body | Concurrent body -> List.exists (statement_diverges state) body.statements
  | _ -> false

(* Builds the core node of a block. The last expression is the block's
   value if the checker checked it as a value and not as a statement. *)
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

let target state (name : name) = state.resolved.names.(name.id)

(* A literal used as a receiver takes its default type, as in
   [5.wrapping_add(3)], because the method lookup needs the receiver's
   type. So does a local whose type is an undecided literal, and the
   method call at [at] decides it. The literals that the statement decided
   before the call are recorded first, as decided by their uses. *)
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

(* The referent of a name expression, as name resolution decided. *)
let head state (value : expression) = Resolve.head state.resolved value

(* A member name that starts with a capital letter is a variant. *)
let names_variant (member : name) =
  member.text <> "" && member.text.[0] >= 'A' && member.text.[0] <= 'Z'

let show state type_ = Types.show (zonk state type_)

(* The decision of the literal type of a local that a type is, if an
   earlier statement decided it. The type is the local's type as declared,
   before it is resolved. *)
let literal_decision state type_ =
  let rec follow (type_ : Types.ty) =
    match type_ with
    | Literal (_, index) | Variable index -> (
        match Hashtbl.find_opt state.decisions index with
        | Some decision -> Some decision
        | None -> Option.bind (Hashtbl.find_opt state.unifier.types index) follow)
    | _ -> None
  in
  follow type_

(* Reports a mismatch. If one side, [decided], is a local whose literal type
   an earlier statement decided, the report names that statement, because
   the mistake is the decision rather than this use. Each later mismatch of
   the local reuses the report, so one decision is one error. [wanted] is
   the type that the other side needs, which a fix can give the local. *)
let reported_mismatch state ?(fixes = []) code (span : span) ~(sides : (Types.ty * Types.ty) list)
    message =
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
      let name =
        match Hashtbl.find_opt state.binding_spans decision.decided_local with
        | Some name -> Some (name, source state name)
        | None -> None
      in
      let local = match name with Some (_, text) -> Printf.sprintf "`%s`" text | None -> "it" in
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
        match name with
        | Some (name, text)
          when decision.is_default
               && Hashtbl.mem state.annotatable decision.decided_local
               && not (Types.contains_unsolved wanted || Types.is_error wanted) ->
            [
              fix
                (Printf.sprintf "Declare `%s` as a `%s`." text (Types.show wanted))
                [ insert name.stop (": " ^ Types.show wanted) ];
            ]
            @ other_fixes
        | _ -> other_fixes
      in
      let report =
        reported state code span
          ~notes:[ (decision.decided_at, note) ]
          ~fixes
          (message ^ " " ^ explanation)
      in
      decision.decision_report <- Some report;
      report

let mismatched state (span : span) ~expected ~actual =
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

(* Whether an expression is a constant that a type declares, such as
   [UInt8.maximum]. *)
let is_member_constant state (value : expression) =
  match state.tables.resolutions.(value.id) with
  | Some (Global { path = Member_constant _; _ }) -> true
  | _ -> false

(* Whether an expression is a place: a local, a parameter, [self], or a
   constant, followed by fields and indexes. *)
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

(* In a marked expression such as [mut config.servers.sort()], the mark
   applies to the receiver of the first method call whose receiver is a
   place. Returns the id of that call. *)
let rec marked_call state (value : expression) =
  match value.kind with
  | Call ({ kind = Member (base, _); _ }, _)
  | Call ({ kind = Bracket ({ kind = Member (base, _); _ }, _); _ }, _) ->
      if is_place state base then Some value.id else marked_call state base
  | Member (base, _) | Bracket (base, _) | Try base -> marked_call state base
  | _ -> None

(* The call inside an expression, looking through marks and parentheses. *)
let rec called (value : expression) =
  match value.kind with
  | Call _ -> Some value
  | Mode (_, inner) | Parenthesized inner -> called inner
  | _ -> None

(* Checks the target of a [calls] clause: a function-typed parameter, a
   capability, or a method of a capability. *)
let check_resource state (resource : Syntax.resource) =
  let capability (path : path_type) (method_ : name option) =
    let shown = Names.spell_path path.path in
    match target state path.path.last with
    | Some (Definition (Capability, capability)) -> (
        match method_ with
        | Some method_
          when Query.demand state.database Names.members (capability, method_.text) = [] ->
            report state Unknown_member method_.span
              (Printf.sprintf "`%s` has no method `%s`." shown method_.text)
        | _ -> ())
    | Some (Unknown _) -> ()
    | _ ->
        report state Not_a_capability path.span
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
              report state Not_callable name.span
                (Printf.sprintf "`calls` counts the calls through a function, and `%s` is a `%s`."
                   name.text (Types.show other)))
      | Some (Unknown _) -> ()
      | _ ->
          report state Not_callable name.span
            (Printf.sprintf
               "`calls` counts the calls through a parameter that is a function, or of a \
                capability, and `%s` is neither."
               name.text))

type conversion = From_never | Owned_to_view | Function_widening | To_integer | From_integer

(* Checks a value of type [found] where [expected] is expected, and wraps
   the expression's core node in the implicit conversion, if one applies.
   This is the only place where a type converts to another:

   - [Never] converts to any type.
   - A function value converts to a function type with more [uses] or
     weaker costs (widening). The expected type may lack a capability that
     the value uses only if the expected type has a capability variable,
     which the capability check solves. If the constants in the two types
     do not show that the costs are weaker, the prover must show it: at the
     call, for an argument, and as an obligation on [expression] otherwise.
   - An argument that is an owned collection converts to its view. In a
     specification, an argument that is a built-in integer converts to
     [Integer], and an [Integer] converts to a built-in integer that it
     fits.

   In every other case, [actual] must unify with [expected]. *)
let convert state env ?(argument = false) ?expression (span : span) ~actual ~expected =
  (* Wraps the expression's core node in the conversion. The wrapped node
     has the expected type. *)
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
              (* If the value's type equals the expected type after the
                 capability variables are solved, there is no widening. *)
              | Function_widening ->
                  if Types.equal inner.type_ expected then inner else convert Widen
              | To_integer -> convert To_integer
              | From_integer -> convert From_integer
              (* An owned collection converts to its view by a call of its
                 [slice], which borrows the collection. *)
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
                             arguments =
                               [
                                 Passed
                                   {
                                     mode = Read;
                                     value =
                                       (match inner.kind with
                                       | Use place -> Place place
                                       | _ -> Value inner);
                                     mark = None;
                                   };
                               ];
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
    when argument
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
  | Types.Integer, _, Some _ when argument && env.specification && integer_type state wanted ->
      Some From_integer
  (* A local of code whose literal type is undecided converts to [Integer]
     as a built-in integer does. *)
  | Types.Literal (Integer_literal, index), Types.Integer, _
    when env.specification && Hashtbl.mem state.unifier.code_literals index ->
      Some To_integer
  (* In a specification, a built-in integer converts to [Integer]. *)
  | _, Types.Integer, _ when env.specification && integer_type state actual_type -> Some To_integer
  | Types.Function actual_function, Types.Function wanted_function, _
    when not (Types.same_clauses actual_function wanted_function) ->
      let unlisted = Types.capability_difference actual_function.uses wanted_function.uses in
      (* If either set is not known yet, the check waits until the
         definition is checked: a subset constraint requires the value's
         [uses] to be within the expected type's. *)
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
        && (proven || argument || Option.is_some expression)
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
