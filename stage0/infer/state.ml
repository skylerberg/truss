(* The state of the type checker while it checks one definition, and the
   helpers that every part of the checker uses: reporting diagnostics,
   recording types, unification, places, instantiation of signatures, and
   argument modes. [Expressions]
   describes the checking algorithm. *)

open Syntax
module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower

(* State *)

type local = { type_ : T.ty; mutable_ : bool; mode : T.mode }

(* The context of the code that is being checked. *)
(* An enclosing construct that an early exit can leave: a loop, or a task
   of [concurrent] code. An iteration of a [concurrent for] is both. *)
type enclosing = Loop | Task of Core.task
type exit = Return_exit | Break_exit | Continue_exit

(* The tasks that an early exit terminates, innermost first, given the
   enclosing constructs. A [return] terminates every enclosing task. A
   [break] or a [continue] terminates the tasks between it and its loop. A
   [break] in a [concurrent for] also terminates the task of its own
   iteration. A [continue] in one does not: the iteration ends normally. *)
let tasks_exited_by (exit : exit) (enclosing : enclosing list) : Core.task list =
  match exit with
  | Return_exit -> List.filter_map (function Task task -> Some task | Loop -> None) enclosing
  | Break_exit | Continue_exit ->
      let rec within_loop = function
        | [] | Loop :: _ -> []
        | Task (Iteration _ as task) :: _ -> if exit = Break_exit then [ task ] else []
        | Task (Branch _ as task) :: rest -> task :: within_loop rest
      in
      within_loop enclosing

type env = {
  output : T.result option;
      (** The result of the enclosing function or lambda. [return] and [yield] are checked against
          it. *)
  specification : bool;
      (** The code is a specification: a contract, a [proof] block, or the body of a function for
          specifications only. *)
  self : T.ty option;  (** The type of [self]. *)
  self_mode : T.mode;  (** The mode of [self]. Only [mut self] can be mutated. *)
  loop_element : T.ty option;
      (** In the clauses of a [for] loop: the type of the loop's elements. [yielded] is a sequence
          of them. *)
  compile_time : bool;
      (** The expression is a constant expression, which the compiler evaluates: the value of a
          constant, or a default. *)
  enclosing : enclosing list;
      (** The enclosing loops and [concurrent] tasks, innermost first, up to the enclosing function
          or lambda. *)
}

(* Whether an expression runs in the compiled program. A specification
   does not run, and the compiler evaluates a constant expression. Only
   code that runs moves values, so only there must a value be owned. *)
let runs (env : env) = not (env.specification || env.compile_time)

(* A constraint between two capability sets: every capability in [subset]
   must be in [superset]. Either set may contain capability variables.

   Constraints are collected while a definition is checked and solved at
   the end ([Capabilities.solve]). Solving grows each variable in a
   [superset] until the constraint holds. If a constraint still fails after
   solving (because its [superset] has no variable to grow), the solver
   calls [report_missing] with the capabilities that [superset] lacks. *)
type subset_constraint = {
  subset : T.capability list;
  superset : T.capability list;
  report_missing : T.capability list -> unit;
}

(* The state of the check of one statement. Types are inferred one
   statement at a time. *)
type frame = {
  start : int;  (** The first inference variable created for the statement. *)
  mutable nodes : int list;  (** The expressions whose types were recorded for the statement. *)
  mutable bindings : int list;  (** The locals that the statement binds. *)
  mutable patterns : int list;  (** The patterns whose types were recorded for the statement. *)
  mutable pending : (unit -> bool) list;
      (** Deferred checks that need a type that is not inferred yet. Each returns whether it is
          done. *)
  mutable unmet : (T.ty * T.trait_reference) list;
      (** The trait bounds already reported as not satisfied, with their types, so that each is
          reported once per statement. *)
  frame_specification : bool;
  span : span;
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
  mutable synthetic_local_count : int;
  mutable tables_with_holes : C.t option;
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
  mutable tables : C.t;
  form : form;
  mutable diagnostics : Syntax.diagnostic list;
  unifier : Unify.t;
  locals : (id, local) Hashtbl.t;
  mutable law_parameters : (string * T.ty) list;
      (** In a law's proof, the law's parameters, with [Self] and the trait's parameters replaced by
          the proof's type and trait arguments. *)
  mutable frames : frame list;
  mutable references : id list;  (** Locals read, newest first, for lambdas' captures. *)
  mutable receiver_modes : (id * T.mode) list;  (** Method calls whose receiver a mark covers. *)
  yielded : (id, T.mode) Hashtbl.t;
      (** The operand of each [yield], and each field of a constructor that is in this table, with
          the mode of the [yield]. A field in this table that is a place is lent to the yielded
          value instead of moved into it. *)
  binding_spans : (id, span) Hashtbl.t;
      (** Where each name of the definition is, for lambdas' captures. *)
  mutable lambdas : span list;  (** The lambdas being checked, innermost first. *)
  mutable unsolved : Diagnostic.reported option;
      (** The report of the first statement whose types could not be inferred. *)
  mutable capability_constraints : subset_constraint list;
  mutable capability_solution : (int, T.capability list) Hashtbl.t option;
      (** The set each capability variable was solved to. [None] until the constraints are solved. A
          variable with no entry is the empty set. *)
  mutable evidence : Path.package list;  (** The packages whose [impl]s met a bound here. *)
}

let reported state ?(fixes = []) code (span : span) message =
  let diagnostic = Diagnostic.make ~fixes ~code:(Types code) span message in
  state.diagnostics <- diagnostic :: state.diagnostics;
  Diagnostic.reported diagnostic

let report state ?fixes code span message = ignore (reported state ?fixes code span message)

(* Raises a compiler bug. Used where an earlier stage guarantees that a
   case cannot happen. *)
let bug format = Compiler_bug.bug ~stage:"Infer" format

(* Reports a diagnostic and returns the error type that carries the
   report. Every operation on an error type is accepted, so one mistake is
   reported once. *)
let error state ?fixes code span message = T.Error (reported state ?fixes code span message)

let source state (span : span) =
  if span.stop <= String.length state.text then
    String.sub state.text span.start (span.stop - span.start)
  else ""

(* The core form *)

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
let was_hole state (table : C.t -> T.ty option array) (id : id) =
  match state.form.tables_with_holes with
  | Some tables -> (table tables).(id) = Some T.Hole
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
      let found = ref [] in
      Syntax_walk.expression_parts ~statement:ignore value ~expression:(fun part ->
          found := checked part :: !found);
      List.concat (List.rev !found)

let rec build_expression state (value : expression) : Core.expression =
  let evaluated =
    if Option.is_some state.form.tables_with_holes then operands state value else []
  in
  if
    List.exists
      (fun (operand : expression) -> was_hole state (fun t -> t.types) operand.id)
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
    let todo = synthetic_expression state ~origin:value.id T.Never Todo in
    synthetic_expression state ~origin:value.id T.Never
      (Block { statements; value = Some todo; diverges = true })
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
    if was_hole state (fun t -> t.types) value.id then Some value else None
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
  if was_hole state (fun t -> t.scrutinee_types) written.id then
    { id = fresh_node_id state; origin = written.id; type_ = T.Never; kind = Wildcard }
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
  let number = state.form.synthetic_local_count in
  state.form.synthetic_local_count <- number + 1;
  Synthetic number

let fix title edits = Diagnostic.fix title edits
let replace = Diagnostic.replace
let insert position text = Diagnostic.replace (Span.zero_width position) text
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

let bounds state parameter =
  Option.value ~default:[] (Hashtbl.find_opt state.context.bounds parameter)

let normalize state type_ = Impls.normalize state.database ~bounds:(bounds state) (zonk state type_)

(* The error type for an inference variable that no statement solved. The
   first unsolved variable is reported, and later ones reuse that report,
   so an unsolved type is never stored without a diagnostic. *)
let unsolved state =
  match state.unsolved with
  | Some report -> T.Error report
  | None ->
      let report =
        reported state Cannot_infer
          (Span.make state.definition.span.start state.definition.span.start)
          "A type in this definition cannot be worked out. Give the `let` a type, or the call type \
           arguments."
      in
      state.unsolved <- Some report;
      T.Error report

(* Replaces each capability variable in a set by its solution. Returns
   the set unchanged if the variables are not solved yet. *)
let resolve_capabilities state (capabilities : T.capability list) =
  match state.capability_solution with
  | Some solution when T.has_capability_variable capabilities ->
      List.sort_uniq compare
        (List.concat_map
           (function
             | T.Capability_variable variable ->
                 Option.value ~default:[] (Hashtbl.find_opt solution variable)
             | capability -> [ capability ])
           capabilities)
  | _ -> capabilities

(* The final form of a type: inference variables replaced by their
   solutions, projections normalized, and capability variables replaced
   by their solutions. An unsolved inference variable becomes an error.
   While the core form is built, a hole becomes [Never]. *)
let rec final state type_ =
  T.map ~capabilities:(final_capabilities state)
    (function
      | T.Variable _ | T.Literal _ -> Some (unsolved state)
      | T.Hole when Option.is_some state.form.tables_with_holes -> Some T.Never
      | _ -> None)
    (normalize state type_)

(* The final form of a set of capabilities: each associated capability set
   replaced by the capabilities that the [impl] of its type defines, and
   each capability variable replaced by its solution. *)
and final_capabilities state capabilities =
  resolve_capabilities state
    (Impls.normalize_capabilities state.database ~bounds:(bounds state)
       (List.map
          (function
            | T.Capability_projection { base; trait; name } ->
                T.Capability_projection { base = final state base; trait; name }
            | capability -> capability)
          capabilities))

let final_argument state = function
  | T.Type type_ -> T.Type (final state type_)
  | T.Value value -> (
      match Unify.resolve_value state.unifier value with
      | T.Value_variable _ -> T.Type (unsolved state)
      | value -> T.Value value)
  | T.Capabilities capabilities -> T.Capabilities (final_capabilities state capabilities)

(* Unifies two types. Projections are normalized first, so [C.Key] unifies
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
let unify_as_hint state found expected =
  let deferred_capability_equalities = state.unifier.deferred_capability_equalities in
  ignore (unify state found expected);
  state.unifier.deferred_capability_equalities <- deferred_capability_equalities

(* Normalizes the type arguments and the associated types of a trait
   reference, as [normalize] does for a type. *)
let normalize_trait state (trait : T.trait_reference) : T.trait_reference =
  {
    trait with
    trait_arguments =
      List.map
        (function T.Type type_ -> T.Type (normalize state type_) | other -> other)
        (Unify.zonk_trait state.unifier trait).trait_arguments;
    associated = List.map (fun (name, type_) -> (name, normalize state type_)) trait.associated;
  }

let implements state type_ trait =
  Impls.implements state.database ~bounds:(bounds state) (normalize state type_)
    (normalize_trait state trait)

(* A bound that an [impl] satisfies makes this definition depend on the
   [impl]'s code. Checks that the capabilities the [impl] uses are granted
   to its package, and records the package. *)
let check_evidence_grants state (span : span) evidence =
  let impls = Interface.Grants.evidence_uses state.database ~bounds:(bounds state) evidence in
  state.evidence <- List.map (fun (impl, _, _) -> Path.package impl) impls @ state.evidence;
  List.iter
    (fun message ->
      state.diagnostics <-
        Diagnostic.make ~code:(Capabilities Not_granted) span message :: state.diagnostics)
    (Interface.Grants.messages state.database ~package:state.package impls)

let copyable state type_ = Impls.copyable state.database ~bounds:(bounds state) (zonk state type_)
let plain state type_ = Impls.plain state.database ~bounds:(bounds state) (zonk state type_)

(* The associated type [name] of a trait for a type. If the [impl] does
   not define it, the [impl] already has a diagnostic, and this returns an
   error type that carries that report. *)
let associated state type_ (trait : T.trait_reference) name ~(at : span) =
  let type_ = normalize state type_ and trait = normalize_trait state trait in
  match Impls.associated_type state.database ~bounds:(bounds state) type_ trait name with
  | Some found -> found
  | None -> (
      let of_impl =
        match implements state type_ trait with
        | Some (Impls.From_impl { impl; _ }) -> Interface.Check.reported state.database impl
        | _ -> None
      in
      match of_impl with
      | Some report -> T.Error report
      | None ->
          error state Unknown_associated_type at
            (Printf.sprintf "`%s` gives no `%s` as a `%s`." (T.show type_) name (T.show_trait trait))
      )

let evidence_of = function
  | Impls.From_impl { impl; substitution } -> C.Impl { impl; arguments = substitution }
  | Impls.From_bound -> C.Bound
  | Impls.From_any -> C.Dynamic
  | Impls.Built_in | Impls.Accepted _ -> C.Built_in

let trait_reference ?(arguments = []) trait : T.trait_reference =
  { trait; trait_arguments = arguments; associated = [] }

let string_type = T.Named { path = Well_known.path String; arguments = [] }

(* Statements *)

(* Finishes the inference of a statement. An unsolved literal variable
   takes its default type. Any other unsolved variable that the statement
   created is an error. A type that mentions a variable of an enclosing
   statement is left for that statement. *)
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
             (T.show_argument (T.Capabilities (resolve_capabilities state left)))
             (T.show_argument (T.Capabilities (resolve_capabilities state right))))
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
  (* An unsolved literal variable of the statement takes its default type:
     [Int64] or [Float64], or [Integer] in a specification. *)
  List.iter
    (function
      | Unify.Unknown_literal (kind, index) when index >= frame.start ->
          Hashtbl.replace state.unifier.types index
            (match kind with
            | Integer_literal -> if frame.frame_specification then T.Integer else T.builtin Int64
            | Float_literal -> T.builtin Float64)
      | _ -> ())
    (unknowns ());
  run_pending ();
  let unsolved =
    List.filter
      (function
        | Unify.Unknown_type index | Unknown_value index | Unknown_literal (_, index) ->
            index >= frame.start)
      (unknowns ())
  in
  if unsolved <> [] then begin
    let report =
      reported state Cannot_infer frame.span
        "The types in this statement cannot be worked out from it alone. Give the `let` a type, or \
         the call type arguments, such as `var names: List[String] = []`."
    in
    if Option.is_none state.unsolved then state.unsolved <- Some report;
    (* Each unsolved variable is bound to the error type, so it is reported
       once. *)
    List.iter
      (function
        | Unify.Unknown_type index | Unknown_literal (_, index) ->
            Hashtbl.replace state.unifier.types index (T.Error report)
        | Unknown_value _ -> ())
      unsolved;
    (* The deferred checks wait on types that are now errors, so they are
       dropped. *)
    frame.pending <- []
  end;
  let parent = match state.frames with _ :: parent :: _ -> Some parent | _ -> None in
  let finish table ids keep =
    List.iter
      (fun id ->
        match table.(id) with
        | Some type_ -> (
            let type_ = Impls.normalize state.database ~bounds:(bounds state) (zonk state type_) in
            table.(id) <- Some type_;
            if T.contains_unsolved type_ then
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
      patterns = [];
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
let rec statement_never state (written : statement) =
  match written.kind with
  | Expression value -> (
      match state.tables.types.(value.id) with
      | Some type_ -> resolve state type_ = T.Never
      | None -> false)
  | While { condition = { kind = True; _ }; body; _ } -> not (contains_break body)
  (* A [parallel] or [concurrent] block ends only when every branch does. *)
  | Parallel body | Concurrent body -> List.exists (statement_never state) body.statements
  | _ -> false

and contains_break (written : block) =
  let found = ref false in
  let rec statement (written : statement) =
    match written.kind with
    | For _ | While _ -> ()
    | _ -> Syntax_walk.statement_parts ~expression ~statement written
  and expression (value : expression) =
    match value.kind with
    | Break -> found := true
    | Lambda _ -> ()
    | _ -> Syntax_walk.expression_parts ~expression ~statement value
  in
  List.iter statement written.statements;
  !found

(* Builds the core node of a block. The last expression is the block's
   value if the checker checked it as a value and not as a statement. *)
let build_block state (written : block) : Core.block =
  let rec go (statements : statement list) =
    match statements with
    | [] -> ([], None)
    | [ ({ kind = Expression value; _ } as last) ]
      when Option.is_none state.form.statement_builders.(last.id) ->
        ([], Some (build_expression state value))
    | first :: rest ->
        let first = build_statement state first in
        let rest, value = go rest in
        (first :: rest, value)
  in
  let statements, value = go written.statements in
  {
    statements;
    value;
    diverges =
      (match List.rev written.statements with
      | last :: _ -> statement_never state last
      | [] -> false);
  }

(* Locals *)

let declare state (name : name) type_ ~mutable_ ~mode =
  Hashtbl.replace state.locals name.id { type_; mutable_; mode };
  state.tables.local_types.(name.id) <- Some type_;
  match current_frame state with
  | Some frame -> frame.bindings <- name.id :: frame.bindings
  | None -> ()

let target state (name : name) = state.resolved.names.(name.id)

(* A literal used as a receiver takes its default type, as in
   [5.wrapping_add(3)], because the method lookup needs the receiver's
   type. *)
let default_literal state type_ =
  let decide default =
    ignore (Unify.unify state.unifier type_ default);
    default
  in
  match Unify.resolve state.unifier type_ with
  | T.Literal (Integer_literal, _) -> decide (T.builtin Int64)
  | T.Literal (Float_literal, _) -> decide (T.builtin Float64)
  | _ -> type_

(* The referent of a name expression, as name resolution decided. *)
let head state (value : expression) = Resolve.head state.resolved value

(* A member name that starts with a capital letter is a variant. *)
let names_variant (member : name) =
  member.text <> "" && member.text.[0] >= 'A' && member.text.[0] <= 'Z'

(* Showing types and fixes *)

let show state type_ = T.show (zonk state type_)

let mismatched state (span : span) ~expected ~found =
  let expected = zonk state expected and found = zonk state found in
  match (resolve state found, expected) with
  | T.Literal (Integer_literal, _), _ when T.is_float_type expected ->
      reported state Integer_for_float span
        ~fixes:[ fix "Write it as a float." [ insert span.stop ".0" ] ]
        (Printf.sprintf "An integer literal is never a float, and `%s` is expected here."
           (T.show expected))
  | _ ->
      reported state Mismatch span
        (Printf.sprintf "Expected `%s`, found `%s`." (T.show expected) (T.show found))

let mismatch state span ~expected ~found = ignore (mismatched state span ~expected ~found)

(* Places *)

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

(* The error type for an expression that is not valid where it is used.
   If resolution already reported the expression's name as unknown, this
   reuses that report instead of adding a second one. *)
let error_at state ?fixes code (value : expression) message =
  match head state value with
  | Some { target = Unknown report; _ } -> T.Error report
  | _ -> error state ?fixes code value.span message

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
          | Some (T.Function _ | T.Error _ | T.Hole) | None -> ()
          | Some other ->
              report state Not_callable name.span
                (Printf.sprintf "`calls` counts the calls through a function, and `%s` is a `%s`."
                   name.text (T.show other)))
      | Some (Unknown _) -> ()
      | _ ->
          report state Not_callable name.span
            (Printf.sprintf
               "`calls` counts the calls through a parameter that is a function, or of a \
                capability, and `%s` is neither."
               name.text))

(* An expression before a [.] or a [(] that names a type, a trait, or a
   capability instead of a value. *)
type static_ =
  | Static_type of T.ty
  | Static_trait of Path.t * T.argument list option
      (** The trait's type arguments, if they are written. *)
  | Static_capability of Path.t

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

   In every other case, [found] must unify with [expected]. *)
let convert state env ?(argument = false) ?expression (span : span) ~found ~expected =
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
              let expected = final state expected in
              let convert conversion =
                synthetic_expression state ~origin:id expected
                  (Convert { conversion; value = inner })
              in
              match conversion with
              | From_never -> inner
              (* If the value's type equals the expected type after the
                 capability variables are solved, there is no widening. *)
              | Function_widening -> if T.equal inner.type_ expected then inner else convert Widen
              | To_integer -> convert To_integer
              | From_integer -> convert From_integer
              (* An owned collection converts to its view by a call of its
                 [slice], which borrows the collection. *)
              | Owned_to_view -> (
                  match inner.type_ with
                  | T.Named { path; arguments } ->
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
                                   };
                               ];
                             lends = None;
                             uses = [];
                           })
                  | given -> bug "`%s` is viewed and has no view" (T.show given)))
            before
    | _ -> ()
  in
  converted
  @@
  let given = normalize state found and wanted = normalize state expected in
  let refused () =
    mismatch state span ~expected ~found;
    None
  in
  match (given, wanted, expression) with
  | T.Never, _, _ -> Some From_never
  | T.Named given_named, T.Named wanted_named, _
    when argument
         && List.exists
              (fun (owned, view) ->
                Path.equal given_named.path owned && Path.equal wanted_named.path view)
              [
                (Well_known.path List, Well_known.path Slice);
                (Well_known.path String, Well_known.path String_slice);
              ] ->
      if not (Unify.unify_arguments state.unifier wanted_named.arguments given_named.arguments) then
        mismatch state span ~expected ~found;
      Some Owned_to_view
  | T.Integer, _, Some _ when argument && env.specification && T.is_integer_type wanted ->
      Some From_integer
  (* In a specification, a built-in integer converts to [Integer]. *)
  | _, T.Integer, _ when env.specification && T.is_integer_type given -> Some To_integer
  | T.Function given_function, T.Function wanted_function, _
    when not (T.same_clauses given_function wanted_function) ->
      let unlisted =
        List.filter
          (fun capability -> not (List.mem capability wanted_function.uses))
          given_function.uses
      in
      (* If either set is not known yet, the check waits until the
         definition is checked: a subset constraint requires the value's
         [uses] to be within the expected type's. *)
      let unknown =
        T.capabilities_unsolved given_function.uses || T.capabilities_unsolved wanted_function.uses
      in
      let proven = T.costs_imply ~given:given_function.costs ~wanted:wanted_function.costs in
      if
        Unify.unify state.unifier wanted
          (T.Function
             { given_function with uses = wanted_function.uses; costs = wanted_function.costs })
        && (unlisted = [] || unknown)
        && (proven || argument || Option.is_some expression)
      then begin
        if unlisted <> [] then
          state.capability_constraints <-
            {
              subset = given_function.uses;
              superset = wanted_function.uses;
              report_missing =
                (fun _ ->
                  mismatch state span ~expected:(final state expected) ~found:(final state found));
            }
            :: state.capability_constraints;
        Some Function_widening
      end
      else refused ()
  | _ -> if Unify.unify state.unifier wanted given then None else refused ()

(* Bounds *)

(* Requires a type to satisfy a trait bound. The check is deferred until
   the type is inferred. The type must implement the trait, and each
   associated type that the bound fixes must unify with the one the [impl]
   defines, which can infer other types of the statement.

   [unmet] reports a failure: with [None] if the type does not implement
   the trait, and with the name of an associated type and the type the
   [impl] defines if those differ. A capability that the [impl] uses and
   that its package is not granted is reported at [at]. *)
let require state ~(at : span) type_ (bound : T.trait_reference) ~unmet =
  let trait = { bound with associated = [] } in
  defer state (fun () ->
      let type_ = normalize state type_ in
      if Unify.unknowns state.unifier type_ <> [] then false
      else begin
        (match implements state type_ trait with
        | None -> unmet type_ None
        | Some evidence ->
            check_evidence_grants state at evidence;
            List.iter
              (fun (name, wanted) ->
                match
                  Impls.associated_type state.database ~bounds:(bounds state) type_ trait name
                with
                | Some given when not (unify state given wanted) -> unmet type_ (Some (name, given))
                | _ -> ())
              bound.associated);
        true
      end)

(* Requires the type arguments of an instantiation to satisfy the bounds
   of their generic parameters. [of_type] is the type that declares the
   parameters. Without it, the parameters are a callee's. *)
let require_bounds state (span : span) ?of_type generics substitution =
  List.iter
    (fun (argument, bound) ->
      require state ~at:span argument bound ~unmet:(fun argument other ->
          let bound = Unify.zonk_trait state.unifier bound in
          let reported =
            match current_frame state with
            | Some frame ->
                let reported = List.mem (argument, bound) frame.unmet in
                frame.unmet <- (argument, bound) :: frame.unmet;
                reported
            | None -> false
          in
          if not reported then
            let needs =
              Printf.sprintf "%s needs `%s: %s`"
                (match of_type with
                | Some type_ -> Printf.sprintf "`%s`" (show state type_)
                | None -> "This")
                (T.show argument) (T.show_trait bound)
            in
            report state Unsatisfied_bound span
              (match other with
              | None -> needs ^ ", which does not hold."
              | Some (name, given) ->
                  Printf.sprintf "%s, and its `%s` is `%s`." needs name (show state given))))
    (Impls.required generics substitution)

(* Instantiating types *)

let fresh_arguments state (path : Path.t) =
  match Query.demand state.database Environment.type_interface path with
  | Some interface ->
      List.map
        (fun (generic : T.generic) ->
          match generic.kind with
          | Value_generic -> T.Value (Unify.fresh_value state.unifier)
          | Type_generic _ -> T.Type (fresh state)
          | Capability_generic -> T.Capabilities (Unify.fresh_capability_variable state.unifier))
        interface.type_generics
  | None -> []

let require_type_bounds state span path arguments =
  match Query.demand state.database Environment.type_interface path with
  | Some interface ->
      Option.iter
        (require_bounds state span ~of_type:(T.Named { path; arguments }) interface.type_generics)
        (T.substitution_of interface.type_generics arguments)
  | None -> ()

(* Fresh inference variables for the generic parameters of a type, each
   required to satisfy the bounds of its parameter. *)
let instantiate_type state span path =
  let arguments = fresh_arguments state path in
  require_type_bounds state span path arguments;
  arguments

let rec static_ state (value : expression) : static_ option =
  match (value.kind, head state value) with
  | Self_type_value, _ -> Option.map (fun self -> Static_type self) state.context.self_type
  | _, Some { target = Definition (Type, path); type_arguments; _ } ->
      Some (Static_type (named_type state value path type_arguments))
  | _, Some { target = Type_parameter parameter; name; type_arguments } ->
      if Option.is_some type_arguments then
        report state Arity value.span
          (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." name.text);
      Some (Static_type (T.Parameter parameter))
  | _, Some { target = Definition (Trait, path); type_arguments; _ } ->
      Some (Static_trait (path, Option.map (written_arguments state) type_arguments))
  | _, Some { target = Definition (Capability, path); _ } -> Some (Static_capability path)
  | Parenthesized inner, None -> static_ state inner
  | _ -> None

(* A type named in an expression, with the type arguments written after
   it, or with fresh inference variables if none are written. *)
and named_type state (value : expression) path type_arguments =
  let type_ arguments =
    match Intrinsic.builtin_of_path path with
    | Some Never -> T.Never
    | Some Integer -> T.Integer
    | _ -> T.Named { path; arguments }
  in
  match type_arguments with
  | None -> type_ (instantiate_type state value.span path)
  | Some items ->
      let arguments = written_arguments state items in
      (match Query.demand state.database Interface.Summary.generics_of path with
      | Some expected when List.length expected <> List.length arguments ->
          report state Arity value.span
            (Printf.sprintf "`%s` takes %d %s, and %d %s given."
               (T.show (Named { path; arguments = [] }))
               (List.length expected)
               (if List.length expected = 1 then "argument" else "arguments")
               (List.length arguments)
               (if List.length arguments = 1 then "is" else "are"))
      | _ -> require_type_bounds state value.span path arguments);
      type_ arguments

(* Type arguments written in an expression, as in [List[String].new()]. *)
and written_arguments state items =
  List.filter_map
    (function
      | Item item -> Some (type_argument_of_expression state item)
      | Item_constraint (name, _) ->
          report state Arity name.span
            "An associated type is fixed where a type is written, as in `any Trait[Name = Type]`, \
             not among type arguments in an expression.";
          None)
    items

and type_argument_of_expression state (value : expression) : T.argument =
  match (value.kind, head state value) with
  | Integer value, _ -> T.Value (Known value)
  | _, Some { target = Value_parameter parameter; _ } -> T.Value (Value_parameter parameter)
  | _, Some { target = Definition (Constant, path); name; _ } -> (
      match Query.demand state.database Interface.Constants.value_of path with
      | Some value -> T.Value (Known value)
      | None ->
          T.Type
            (error state Arity value.span
               (Printf.sprintf
                  "The value of `%s` cannot be worked out: a constant used in a type cannot refer \
                   to itself, and is made of literals, arithmetic, and other such constants."
                  name.text)))
  | _ -> (
      match static_ state value with
      | Some (Static_type type_) -> T.Type type_
      | Some (Static_trait _ | Static_capability _) | None ->
          T.Type (error_at state Not_a_type value "A type argument is a type, or a `USize` value."))

(* Instantiating signatures *)

type instance = {
  signature : T.signature;
  substitution : T.substitution;
  type_arguments : T.argument list;
}

(* Instantiates a signature at a use: its generic parameters are replaced
   by fresh inference variables, each required to satisfy its bounds. *)
let instantiate state (span : span) ?(extra = []) (signature : T.signature) =
  let substitution =
    List.map
      (fun (generic : T.generic) ->
        ( generic.generic,
          match generic.kind with
          | Value_generic -> T.Value (Unify.fresh_value state.unifier)
          | Type_generic _ -> T.Type (fresh state)
          | Capability_generic -> T.Capabilities (Unify.fresh_capability_variable state.unifier) ))
      signature.generics
    @ extra
  in
  require_bounds state span signature.generics substitution;
  {
    signature = T.substitute_signature substitution signature;
    substitution;
    type_arguments =
      List.map
        (fun (generic : T.generic) -> List.assoc generic.generic substitution)
        signature.generics;
  }

let output_type = function T.Returns type_ | Yields (_, type_) | Lends (_, type_) -> type_

let intrinsic_signature path =
  Option.map Intrinsic_signatures.signature (Intrinsic.operation_of_path path)

(* The signature of a function. [Error] with the report if the function's
   header did not parse. *)
let function_signature state (path : Path.t) =
  match intrinsic_signature path with
  | Some signature -> Some (Ok signature)
  | None -> Environment.signature_or_report state.database path

(* Lending *)

(* Records that a call is a call of a lending method, with the mode it
   lends with. The result of such a call is a part of the receiver, lent
   for the rest of the caller's statement. It is not a temporary: it is
   never moved. *)
let note_lending state (value : expression) (output : T.result) =
  match output with
  | Lends (mode, _) -> state.tables.lend_modes.(value.id) <- Some mode
  | Returns _ | Yields _ -> ()

(* The mode with which an expression is lent, if it is the result of a
   lending call, or a field or an element of one. A mark before the
   expression belongs to the receiver of the lending call. *)
let rec lent state (value : expression) : T.mode option =
  match value.kind with
  | Call _ -> state.tables.lend_modes.(value.id)
  | Member (base, _) | Parenthesized base -> lent state base
  | Bracket (base, _) when state.resolved.brackets.(value.id) <> Some Type_arguments ->
      lent state base
  | Mode (_, inner) when Option.is_some (marked_call state inner) -> lent state inner
  | _ -> None

(* Whether an expression is a slice, such as [items[1..3]]. A slice is
   written like an index, but it is a value: a view of part of its base. *)
let rec is_slice (value : expression) =
  match value.kind with
  | Bracket (_, [ Item { kind = Range _; _ } ]) -> true
  | Parenthesized inner | Mode (_, inner) -> is_slice inner
  | _ -> false

(* Whether a [let], [match], or [is] borrows the expression: it denotes a
   place, or a part that a lending call lends. The bindings then borrow
   parts of that place. A slice is a value, so it is not borrowed. *)
let borrowed state (value : expression) =
  (is_place state value || Option.is_some (lent state value)) && not (is_slice value)

(* The mode in which a pattern's bindings bind the parts of the scrutinee of
   a [match] or an [is]. A scrutinee marked [own] or [mut] has that mode. An
   unmarked place or lent part is borrowed, so the bindings are [Read]. Any
   other scrutinee is a value that the match consumes, so the bindings are
   [Own]. A mark that belongs to the receiver of a method call, as in [mut
   cursor.next()], is not a mark on the scrutinee. *)
let scrutinee_mode state (scrutinee : expression) : T.mode =
  match scrutinee.kind with
  | Mode (Own, inner) when Option.is_none (marked_call state inner) -> Own
  | Mode (Mut, inner) when Option.is_none (marked_call state inner) && not (is_slice inner) -> Mut
  | _ -> if borrowed state scrutinee then Read else Own

(* Mutation *)

(* Why a place cannot be mutated. *)
type immutable =
  | Read_only of string
      (** The place is, or is part of, a [let] binding, a parameter that is not [mut], a constant,
          or [self] in a method that does not take [mut self]. *)
  | Captured of string  (** Inside a lambda, the place belongs to the enclosing function. *)
  | Lent_read_only  (** The place is a part that a lending call lent read-only. *)
  | Not_a_place

(* Why a place cannot be mutated, or [None] if it can. Only a [var], a
   [mut] parameter, the variable of a [mut] loop, [mut self], a part of one
   of these, and a part that a call lends [mut] can be mutated. *)
let rec immutable state env (value : expression) : immutable option =
  match value.kind with
  | Name path -> (
      match target state path.last with
      | Some (Local id) -> (
          let captured =
            match (state.lambdas, Hashtbl.find_opt state.binding_spans id) with
            | (lambda : span) :: _, Some (binding : span) ->
                binding.start < lambda.start || binding.start >= lambda.stop
            | _ -> false
          in
          match Hashtbl.find_opt state.locals id with
          | _ when captured -> Some (Captured path.last.text)
          | Some local ->
              if local.mutable_ || local.mode = Mut then None else Some (Read_only path.last.text)
          | None -> None)
      | Some (Definition _ | Law_parameter _) -> Some (Read_only path.last.text)
      | _ -> None)
  | Self_value ->
      if state.lambdas <> [] then Some (Captured "self")
      else if env.self_mode = T.Mut then None
      else Some (Read_only "self")
  | Member (base, _) | Bracket (base, _) | Parenthesized base -> immutable state env base
  | Mode (Mut, inner) when Option.is_some (marked_call state inner) -> immutable state env inner
  | Call _ -> (
      match lent state value with
      | Some T.Mut -> None
      | Some _ -> Some Lent_read_only
      | None -> Some Not_a_place)
  | _ -> Some Not_a_place

(* Records that a place is mutated: every index expression in the place
   uses the [mut self] version of [at], which lends its element [mut]. *)
let rec use_mutable_indexes state (value : expression) =
  match value.kind with
  | Member (base, _) | Parenthesized base | Mode (_, base) -> use_mutable_indexes state base
  | Bracket (base, _) ->
      (match state.tables.calls.(value.id) with
      | Some ({ callee = Trait_method ({ name = "at"; _ } as method_); arguments; _ } as call) ->
          state.tables.calls.(value.id) <-
            Some
              {
                call with
                callee = Trait_method { method_ with receiver = Mut };
                arguments =
                  List.map
                    (fun (argument : C.argument) ->
                      if argument.parameter_index = 0 then { argument with mode = T.Mut }
                      else argument)
                    arguments;
              }
      | _ -> ());
      use_mutable_indexes state base
  | _ -> ()

type mutation =
  | Assignment
  | Mut_mark  (** The place is passed [mut], is a [mut] receiver, or is lent or yielded [mut]. *)

(* Checks that a place may be mutated, and records that it is. Every
   construct that mutates a place calls this. *)
let mutate state env ~(by : mutation) (value : expression) =
  let code : Diagnostic.Code.types =
    match by with Assignment -> Not_assignable | Mut_mark -> Wrong_mark
  in
  (match (immutable state env value, by) with
  | None, _ -> ()
  | Some (Captured name), _ ->
      report state code value.span
        (Printf.sprintf
           "A lambda cannot change what it captures, and `%s` is from outside it. Return the new \
            value instead, or use a loop."
           name)
  | Some (Read_only name), _ ->
      report state code value.span
        (Printf.sprintf
           "`%s` cannot change here: only a `var`, a `mut` parameter, or `mut self`, and their \
            parts, can be %s."
           name
           (match by with Assignment -> "assigned" | Mut_mark -> "marked `mut`"))
  | Some Lent_read_only, Assignment ->
      report state code value.span
        ~fixes:[ fix "Mark it `mut`." [ insert value.span.start "mut " ] ]
        "This part is lent read-only, so it cannot change. Mark the place it is lent from `mut`, \
         so that it is lent `mut`."
  | Some Not_a_place, Assignment ->
      report state code value.span
        "Only a place, such as a variable, a field, or an element, can be assigned."
  (* The check of the mark or of the receiver reports these. *)
  | Some (Lent_read_only | Not_a_place), Mut_mark -> ());
  use_mutable_indexes state value

(* Arguments and modes *)

(* Whether a place is a constant, or a field or an element of one. *)
let rec is_part_of_constant state (value : expression) =
  match value.kind with
  | Name path -> (
      match target state path.last with Some (Definition (Constant, _)) -> true | _ -> false)
  | Member (base, _) -> is_member_constant state value || is_part_of_constant state base
  | Bracket (base, _) | Parenthesized base -> is_part_of_constant state base
  | _ -> false

type argument_form = Marked of T.mode * expression | Place | Lent of T.mode | Temporary

let argument_form state (value : expression) =
  match value.kind with
  | Mode (mode, inner) when Option.is_none (marked_call state inner) ->
      Marked ((match mode with Mut -> Mut | Own -> Own), inner)
  | _ -> (
      match lent state value with
      | Some mode -> Lent mode
      | None -> if is_place state value then Place else Temporary)

(* The mode with which a field of a yielded constructor lends a place to
   the value that is built, or [None] if the field takes its value, as a
   field of any other constructor does. [type_] is the type of [value]. A
   method that yields read-only lends every place read-only, except a
   [Plain] place, which is copied. A method that yields [mut] lends the
   places that are marked [mut]. A slice is a value, so it is taken. *)
let lent_field state (value : expression) type_ : T.mode option =
  match (Hashtbl.find_opt state.yielded value.id, argument_form state value) with
  | _ when is_slice value -> None
  | Some Read, Marked (Mut, _) -> Some Read
  | Some Read, (Place | Lent _) when not (plain state type_) -> Some Read
  | Some Mut, Marked (Mut, _) -> Some Mut
  | _ -> None

let mark_span (value : expression) (inner : expression) =
  Span.make value.span.start inner.span.start

let check_mode state env (value : expression) (parameter : T.parameter_info) type_ =
  let name = parameter.name in
  match (parameter.mode, argument_form state value) with
  | Read, (Place | Temporary | Lent _) -> ()
  | Read, Marked (_, inner) ->
      report state Redundant_mark value.span
        ~fixes:
          [
            fix "Remove the mark."
              [ Diagnostic.delete (Span.make value.span.start inner.span.start) ];
          ]
        (Printf.sprintf "`%s` only reads its argument, so it takes no mark." name)
  | Mut, Marked (Mut, inner) -> mutate state env ~by:Mut_mark inner
  | Mut, Place ->
      report state Missing_mark value.span
        ~fixes:[ fix "Mark it `mut`." [ insert value.span.start "mut " ] ]
        (Printf.sprintf "`%s` may change its argument, so the call marks it `mut`." name)
  | Mut, Lent Mut -> mutate state env ~by:Mut_mark value
  | Mut, Lent (Read | Own) ->
      report state Wrong_mark value.span
        (Printf.sprintf
           "`%s` may change its argument, and this part is lent read-only. Mark the place it is \
            lent from `mut`, so that it is lent `mut`."
           name)
  | Own, Lent _ ->
      if not (plain state type_) then
        report state Missing_mark value.span
          ~fixes:
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else [])
          (Printf.sprintf
             "`%s` takes ownership of its argument, and a part that is lent cannot be given up. \
              Pass a copy."
             name)
  | Mut, (Temporary | Marked (Own, _)) ->
      report state Wrong_mark value.span
        (Printf.sprintf "`%s` changes its argument in place, so it must be a place marked `mut`."
           name)
  | Own, Marked (Own, inner) ->
      if plain state type_ then
        report state Redundant_mark value.span
          ~fixes:[ fix "Remove the mark." [ Diagnostic.delete (mark_span value inner) ] ]
          (Printf.sprintf "`%s` copies implicitly, so it needs no `own`." (show state type_))
  | Own, Temporary -> ()
  | Own, Place when Hashtbl.find_opt state.yielded value.id = Some Mut ->
      if not (plain state type_) then
        report state Missing_mark value.span
          ~fixes:
            (fix "Lend it `mut`." [ insert value.span.start "mut " ]
            ::
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else []))
          (Printf.sprintf
             "`%s` is a field of a value that is lent `mut`. Mark the place `mut` to lend it too, \
              or pass a copy."
             name)
  | Own, Place when is_part_of_constant state value ->
      if not (plain state type_) then
        report state Missing_mark value.span
          ~fixes:
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else [])
          (Printf.sprintf
             "`%s` takes ownership of its argument, and a constant cannot be given up. Pass a copy."
             name)
  | Own, Place ->
      if not (plain state type_) then
        report state Missing_mark value.span
          ~fixes:
            (fix "Give it up with `own`." [ insert value.span.start "own " ]
            ::
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else []))
          (Printf.sprintf
             "`%s` takes ownership of its argument. Give the place up with `own`, or pass a copy."
             name)
  | Own, Marked (Mut, _) ->
      report state Wrong_mark value.span
        (Printf.sprintf "`%s` takes ownership of its argument, so it is marked `own`, not `mut`."
           name)
  | (Mut | Own), Marked (Read, _) -> ()

(* A yielded constructor that lends a place owns nothing, so nothing drops
   it when the lend ends. Each of its other fields must then have nothing
   to drop: the field is a constructor too, or its type is [Plain].
   [operand] is the operand of the [yield]. *)
let check_lent_value state env (operand : expression) =
  let lends = ref false and taken = ref [] in
  let rec fields (value : expression) =
    match (value.kind, state.tables.calls.(value.id)) with
    | Call (_, arguments), Some { callee = Constructor _; arguments = checked; _ } ->
        List.iter
          (fun (argument : argument) ->
            match
              List.find_opt
                (fun (found : C.argument) -> found.expression = argument.value.id)
                checked
            with
            | Some { mode = Read | Mut; _ } -> lends := true
            | _ -> fields argument.value)
          arguments
    | _ -> taken := value :: !taken
  in
  fields operand;
  if !lends && runs env then
    List.iter
      (fun (value : expression) ->
        defer state (fun () ->
            match Option.map (normalize state) state.tables.types.(value.id) with
            | None -> true
            | Some type_ when T.contains_unsolved type_ -> false
            | Some type_ ->
                let fieldless_variant =
                  match (state.tables.resolutions.(value.id), type_) with
                  | Some (Variant_value _), T.Function _ -> false
                  | Some (Variant_value _), _ -> true
                  | _ -> false
                in
                if not (plain state type_ || fieldless_variant) then
                  state.diagnostics <-
                    Diagnostic.make ~code:(Ownership Owned_beside_lent) value.span
                      "This value is owned, but the value that is yielded lends a place, so it \
                       owns nothing. Bind this value to a name first, and pass the name."
                    :: state.diagnostics;
                true))
      !taken

(* Checks a value where an owned value is required and no parameter
   receives it: the initializer of a [var], the value of an assignment, an
   element of a collection literal, or a part of a tagged string. A place
   there must be marked [own] or copied, unless its type is [Plain]. This
   is a rule of ownership. The type checker reports it because only the
   syntax tree has the marks. *)
let check_owned state env (value : expression) type_ =
  if runs env then
    defer state (fun () ->
        let type_ = normalize state type_ in
        if T.contains_unsolved type_ then false
        else begin
          (match argument_form state value with
          | Place when not (plain state type_) ->
              let place = source state value.span in
              let copy =
                if copyable state type_ then [ fix "Copy it." [ insert value.span.stop ".copy()" ] ]
                else []
              in
              let fixes, message =
                if is_part_of_constant state value then
                  ( copy,
                    Printf.sprintf "An owned value is needed here, and `%s` is %s. Copy it." place
                      (match value.kind with
                      | Name _ -> "a constant"
                      | _ when is_member_constant state value -> "a constant"
                      | _ -> "part of a constant") )
                else
                  ( fix "Give it up with `own`." [ insert value.span.start "own " ] :: copy,
                    Printf.sprintf
                      "An owned value is needed here, and `%s` is a place. Mark it `own` to give \
                       it up, or copy it."
                      place )
              in
              state.diagnostics <-
                Diagnostic.make ~fixes ~code:(Ownership Needs_owned) value.span message
                :: state.diagnostics
          | _ -> ());
          true
        end)
