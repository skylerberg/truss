type local = int
type block = int

(** Whether a local is a source binding or a temporary. *)
type local_kind =
  | Source of { local : Core.local; mode : Types.mode; name : string option; is_var : bool }
      (** A parameter, [self], or a local that a pattern or a lambda binds, with the name it is
          written with and whether it is declared with [var]. With [Read] or [Mut], it is the place
          it was bound to, not a copy of it. *)
  | Temporary
      (** A value with no name. It is [Dead] at the end of the statement that makes it, unless it is
          the value of a block, which the enclosing statement reads. *)
  | Lent of Types.mode
      (** The part that a lending call lends, or the target of a compound assignment: the place
          itself, until it is [Dead]. *)

type local_info = { kind : local_kind; type_ : Types.ty; origin : Core.origin }

type place = { root : root; projections : projection list }
and root = Local of local | Constant of Path.t

and projection =
  | Field of string
  | Variant_field of { variant : string; field : string }
      (** A field of a variant, where a test has shown that the value holds the variant. *)

type constant = Unit | Integer of Z.t | Float of float | Boolean of bool | String of string

type operand =
  | Use of { place : place; type_ : Types.ty; node : Core.id; origin : Core.origin }
      (** The value at a place, of [type_], copied if the type copies implicitly and moved
          otherwise. [node] is the core node the value is read for. *)
  | Borrow of { place : place; type_ : Types.ty; mode : Types.mode; origin : Core.origin }
      (** The place itself, lent for the operation: read-only, or [mut]. *)
  | Take of { place : place; type_ : Types.ty; origin : Core.origin }
      (** The old value of a compound assignment's target, which the operator takes as owned. The
          statement assigns the target again before any other code runs. *)
  | Constant of { value : constant; type_ : Types.ty }

type callee = operand Core.target
(** A call's callee. An intrinsic called is one that is not a primitive operation: those are
    {!Operation}. *)

type argument =
  | Passed of { mode : Types.mode; value : operand; mark : Core.mark option }
  | Default  (** The callee fills in the parameter's default. *)

type call = {
  callee : callee;
  arguments : argument list;  (** One per parameter, in parameter order. *)
  uses : Types.capability_set;
  node : Core.id;  (** The core form's [Call]. *)
  origin : Core.origin;  (** The call's, for diagnostics. *)
}

type capture = { local : Core.local; type_ : Types.ty; place : place }
(** A local that a lambda captures: its core local, its type, and its place in the enclosing body.
*)

type rvalue =
  | Operand of operand
  | Operation of {
      operation : Intrinsic.operation;
      type_arguments : Types.argument list;
          (** The intrinsic's type arguments: for an operator, the types of its operands. *)
      operands : operand list;
    }
      (** A primitive operation on built-in types, written as an operator or as a call of the
          intrinsic. *)
  | Compare of { comparison : Core.comparison; left : operand; right : operand }
  | Not of operand
  | Construct of { variant : string option; fields : (string * operand option) list }
      (** A record or a variant, with every field in evaluation order. [None] takes the field's
          default. A [Borrow] field lends its place to the value, as a yielded construct does. *)
  | Array of operand list
  | Is_variant of { place : place; variant : string }
  | Convert of { conversion : Core.conversion; value : operand }
  | To_any of { value : operand; trait : Types.trait_reference; evidence : Core.evidence }
  | Copy of operand  (** A [copy()] that the compiler implements. *)
  | Function_value of { path : Path.t; type_arguments : Types.argument list }
  | Lambda of { body : int; captures : capture list; written : Core.expression }
      (** A function value made from a lambda. [body] indexes {!t.lambdas}, and [captures] are in
          the order of its body's {!body.captures}. [written] is the lambda as written, which the
          prover reads as a function's definition. *)
  | Value_parameter of Types.parameter

type yielded =
  | Part of operand
  | Built of {
      variant : string option;
      fields : (string * yielded option) list;
      type_ : Types.ty;
      node : Core.id;
    }
      (** A constructor of [type_], with every field in evaluation order. [None] takes the field's
          default. [node] is its core node. *)

type provided = {
  mode : Types.mode;
  value : operand;
  type_ : Types.ty;
  provides : Core.provided list;
  origin : Core.origin;
}

(** How long a loan lasts. *)
type loan_duration =
  | Loop_body  (** A loop borrows what it iterates over for its body. *)
  | Provide_body  (** A [provide] block borrows its implementations for its body. *)
  | Rest_of_statement  (** A lending call borrows its receiver until the statement ends. *)
  | Operand_evaluation
      (** An evaluated operand stays borrowed until its operation runs, so that a later operand
          cannot mutate it. *)

type statement = { kind : statement_kind; origin : Core.origin }

and statement_kind =
  | Assign of { target : place; value : rvalue; node : Core.id option }
      (** [node] is the core expression whose value the assignment computes, where it computes one,
          for the prover's messages. *)
  | Call of { destination : place option; call : call }
  | Lend of { part : local; call : call }
      (** A call of a lending method. The [Lent] local [part] is the part it lends. *)
  | Slice of { destination : place; base : place; call : call }
      (** A call of [slice_range], whose result views [base]. *)
  | Template of { destination : place; literals : string list; call : call }
      (** A tagged string: the call of the tag's [from_template], with the literal texts. *)
  | Live of local list  (** These locals start to hold values here. *)
  | Dead of local list  (** These locals hold nothing from here on. *)
  | Assert of { condition : operand; bit_vector : Core.expression option }
      (** An [assert] that can run. One proven by bit vectors has its condition as written in
          [bit_vector], which the prover reads as a formula. *)
  | Echo of operand
  | Provide of { provided : provided list; can_use_tasks : bool }
  | Provide_end
  | Loan_start of { loan : int; borrowed : operand; mode : Types.mode; duration : loan_duration }
      (** From here on, what [borrowed] borrows or views is lent with [mode]. *)
  | Loan_end of int list
  | Ghost_assert of { condition : Core.expression; by_bit_vector : bool }
      (** An [assert] that cannot run. Only the prover reads it. *)
  | Matched of { patterns : Core.origin list }
      (** An arm of a [match] whose patterns, by their origins, matched here, before its guard. Only
          the prover reads it, to tell which arm a counterexample takes. *)
  | Proof of Core.block  (** Only the prover reads it. *)

type loop = {
  clauses : Core.loop_clause list;
  schedule : Core.loop_mode;
  origin : Core.origin;
  formula : Core.expression option;
      (** The formula the prover reads for the loop: the quantifier a loop runs, or a [while] loop's
          condition, from which it guesses a measure that decreases. *)
}
(** The clauses of a loop, which its header carries. *)

(** What a [for] loop iterates over. *)
type iteration =
  | Range of { start : operand; stop : operand; inclusive : bool }
      (** The integers or characters from [start] to [stop], each once. A range of [Character] skips
          the surrogates. *)
  | Pull of { cursor : place; next : callee }
      (** The values a cursor gives until it has none, by its type's [Cursor.next]. *)

type early_exit = {
  resume : block;  (** Where the code after the group goes on, where this exit won *)
  returned : local option;  (** For a [return] with a value, the local the value is in *)
}
(** An early exit that leaves a group of tasks: a [return], [break], or [continue] out of a branch
    of a [concurrent] block or an iteration of a [concurrent for]. *)

type branch = {
  entry : block;
  blocks : block list;  (** Every block of the branch, [entry] first. *)
}
(** A branch of a [parallel] or [concurrent] block. *)

type lent_element = {
  element : local;  (** The [Lent] local of the element. *)
  count : Core.expression;
      (** The call of the collection's [count], which the prover reads: a loop that changes its
          elements leaves their number as it was. *)
  call : Core.expression;
      (** The call of the collection's [element] at the loop's position, which the prover reads: a
          loop that reads its elements was lent the values of this call at the positions before. *)
}
(** The element that an iteration of a loop over a collection is lent. *)

type terminator =
  | Goto of block
  | Branch of { condition : operand; yes : block; no : block; is_if_condition : bool }
      (** [is_if_condition]: the condition is an [if]'s, as written, which the prover names where it
          shows a path a counterexample takes. *)
  | Switch_variant of { place : place; cases : (string * block) list }
  | For of {
      iteration : iteration;
      part : local;
      lent : lent_element option;
          (** In a loop over the elements of a collection, the element that each iteration is lent.
              [part] is then the element's position. *)
      body : block;
      blocks : block list;  (** Every block of the body, [body] first, nested loops' included. *)
      after : block;
      loop : loop;
    }
  | Fork of { fork : Core.origin; concurrent : bool; branches : branch list; join : block option }
  | Join of { fork : Core.origin; next : block }
      (** The end of a branch of the {!Fork} [fork]. Read in order, [next] runs after it: the next
          branch's entry, or the block's end after the last branch. *)
  | Iteration_end of { loop : block }
      (** The end of an iteration of the enclosing {!For}, the terminator of [loop]. *)
  | Yield of { mode : Types.mode; part : yielded; resume : block }
  | Return of operand option
  | Cancel of {
      task : Core.task;
      task_end : block option;
      winner : local;
      number : int;
      returned : (operand * local) option;
    }
      (** An early exit that leaves [task]: the task cancels its group and ends, at [task_end] for a
          branch of a [concurrent] block, or where its iteration ends. The first task of the group
          to cancel sets [winner] to [number], and moves a value it returns into the local; a later
          one drops that value. The scopes inside the task end before it. *)
  | Resume of { winner : local; exits : early_exit list; next : block }
      (** Where a group of tasks has ended: the [resume] of the exit numbered [winner], counted from
          1 in [exits], where one won, or else [next]. *)
  | Unreachable
  | Written_unreachable
  | Todo  (** A [todo] that is reached stops the program. *)

type natural_loop = { loop : loop; body : block; after : block option }
(** A [while] loop, which its header block carries: its clauses, the first block of its body, which
    the loop's condition goes to where it holds, and the block it exits to where the condition does
    not hold or a [break] leaves. *)

type basic_block = {
  statements : statement list;
  terminator : terminator;
  terminator_origin : Core.origin;
  header : natural_loop option;  (** The [while] loop this block heads. *)
  inlined : inlined list;
      (** For a block of a method inlined into the body, the methods it was inlined from, innermost
          first. The block's origins are the innermost method's. Empty for the body's own blocks. *)
}

and inlined = {
  method_ : Path.t;
  type_arguments : Types.argument list;  (** The method's, as the instance has them. *)
  call : Core.origin;  (** Where the call is, in the code around it. *)
}
(** A method inlined at a call. *)

type body = {
  parameters : local list;
  defaults : (local * t) list;
      (** For each parameter with a default, the MIR of the default, which the callee runs where the
          argument is left out. *)
  captures : local list;
      (** For a lambda's body, the local of each value it captures, which its {!Lambda} gives, in
          order. *)
  locals : local_info array;
  blocks : basic_block array;  (** The entry is block 0. *)
}

and t = { body : body; lambdas : body array }

let bug format = Compiler_bug.bug ~stage:"MIR" format

(* The builder *)

type pending = {
  mutable statements : statement list;  (** In reverse. *)
  mutable ending : (terminator * Core.origin) option;
  mutable heading : natural_loop option;
}

(* A scope that a jump out of must end: a block's bindings, or a statement.
   It ends its bound locals, its loans, and a [provide] block. *)
type frame =
  | Bindings
  | Statement
  | Condition  (** A statement's condition, whose loans and temporaries end before its branches. *)

type scope = {
  frame : frame;
  mutable bound : local list;
  mutable loans : int list;
  mutable temporaries : local list;  (** In reverse. *)
  provides : bool;
}

(* How long the lends of a condition last: for the rest of the statement, as
   a [match] guard's do; until the guarded block ends, where an [if] or a
   [while] binds a name that may alias a lent part; or for the condition
   alone. *)
type condition_lends = For_statement | For_block | For_condition

(* Where an early exit from tasks goes once they have ended. *)
type task_exit =
  | Exit_return of operand option
  | Exit_to of block
  | Exit_iteration of { loop : block }

(* A group of tasks that early exits leave: the tasks of a [concurrent]
   block or loop. *)
type group = {
  winner : local;
  mutable exits : early_exit list;
  mutable after : block list;
      (** The blocks of the group's code that run once its tasks have ended *)
  mutable resumed : block option;  (** The block that takes the exit that won *)
}

type target = Jump of block | Next_iteration of block

type enclosing_loop = {
  break_ : block;
  continue_ : target;
  depth : int;
  tasks_around : int;  (** The number of tasks around the loop. *)
}

type builder = {
  infos : (local, local_info) Hashtbl.t;
  mutable local_count : int;
  pending : (block, pending) Hashtbl.t;
  mutable block_count : int;
  mutable current : block option;
  sources : (Core.local, local) Hashtbl.t;
  mutable scopes : scope list;  (** Innermost first. *)
  mutable loops : enclosing_loop list;
  mutable compound_target : place option;
  lambdas : body list ref;  (** In reverse, shared by the bodies of a definition. *)
  mutable loan_count : int;
  mutable deferred : local list option;
      (** While a [let] binds, the locals it binds, which join the scope after its [else]. *)
  mutable extended : Core.id list;
      (** While a [let] evaluates its value, the temporaries whose lifetime it extends to the end of
          its bindings' scope, by the id of their expression. *)
  mutable binds_into : frame;
      (** The frame new bindings belong to: a block's, or for [is], the statement around it. *)
  mutable tasks : (Core.task * (int * block option)) list;
      (** The tasks around the code being built, innermost first, each with the number of scopes
          around its start and, for a branch of a [concurrent] block, the block where it ends. *)
  groups : (Core.origin, group) Hashtbl.t;
      (** The groups of tasks that early exits leave, by the origin of their [concurrent] block or
          loop *)
  resume_ends : (block, (scope * int list) list) Hashtbl.t;
      (** For the block where an early exit goes on once a group of tasks has ended, the scopes
          between that group and the next one out, which end there *)
  mutable if_conditions : Core.origin list;  (** The conditions of the [if]s built so far. *)
}

let create ~lambdas =
  {
    infos = Hashtbl.create 16;
    local_count = 0;
    pending = Hashtbl.create 16;
    block_count = 0;
    current = None;
    sources = Hashtbl.create 16;
    scopes = [];
    loops = [];
    compound_target = None;
    lambdas;
    loan_count = 0;
    deferred = None;
    extended = [];
    binds_into = Bindings;
    tasks = [];
    groups = Hashtbl.create 1;
    resume_ends = Hashtbl.create 1;
    if_conditions = [];
  }

let new_local b kind type_ origin =
  let local = b.local_count in
  Hashtbl.replace b.infos local { kind; type_; origin };
  b.local_count <- local + 1;
  local

(* Makes a local dead where the innermost scope ends. *)
let add_temporary b local =
  match b.scopes with scope :: _ -> scope.temporaries <- local :: scope.temporaries | [] -> ()

let temporary b type_ origin =
  let local = new_local b Temporary type_ origin in
  add_temporary b local;
  local

let at local = { root = Local local; projections = [] }

let project (place : place) projection =
  { place with projections = place.projections @ [ projection ] }

let new_block b =
  let block = b.block_count in
  Hashtbl.replace b.pending block { statements = []; ending = None; heading = None };
  b.block_count <- block + 1;
  block

let start b block = b.current <- Some block

let emit b kind origin =
  match b.current with
  | Some block ->
      let pending = Hashtbl.find b.pending block in
      pending.statements <- { kind; origin } :: pending.statements
  | None -> ()

let terminate b terminator origin =
  (match b.current with
  | Some block -> (Hashtbl.find b.pending block).ending <- Some (terminator, origin)
  | None -> ());
  b.current <- None

let goto b target origin = terminate b (Goto target) origin
let assign ?node b target value origin = emit b (Assign { target; value; node }) origin

let hold ?node b type_ origin value =
  match b.current with
  | None -> None
  | Some _ ->
      let local = temporary b type_ origin in
      assign ?node b (at local) value origin;
      Some (Use { place = at local; type_; node = Option.value node ~default:origin; origin })

let source b (local : Core.local) =
  match Hashtbl.find_opt b.sources local with
  | Some found -> found
  | None -> bug "a local that nothing binds"

(* The scope that new bindings belong to. *)
let binding_scope b =
  match List.find_opt (fun scope -> scope.frame = b.binds_into) b.scopes with
  | Some scope -> Some scope
  | None -> List.find_opt (fun scope -> scope.frame <> Condition) b.scopes

let register_binding b local =
  Option.iter (fun scope -> scope.bound <- local :: scope.bound) (binding_scope b)

(* The local a core local is bound to. Each alternative of a pattern binds
   the same locals, and a loop binds its pattern again on each iteration, so
   a core local has one local wherever it is bound. *)
let bind_source ?name ?(is_var = false) b (local : Core.local) mode type_ origin =
  match Hashtbl.find_opt b.sources local with
  | Some found -> found
  | None ->
      let found = new_local b (Source { local; mode; name; is_var }) type_ origin in
      Hashtbl.replace b.sources local found;
      (match b.deferred with
      | Some deferred -> b.deferred <- Some (found :: deferred)
      | None -> register_binding b found);
      found

(* Starts a loan of what [borrowed] borrows or views. A jump out of the
   innermost scope ends it. *)
let start_loan b borrowed mode duration origin =
  let loan = b.loan_count in
  b.loan_count <- loan + 1;
  emit b (Loan_start { loan; borrowed; mode; duration }) origin;
  (match b.scopes with scope :: _ -> scope.loans <- loan :: scope.loans | [] -> ());
  loan

let end_loans b loans origin =
  if loans <> [] then begin
    emit b (Loan_end loans) origin;
    List.iter
      (fun scope -> scope.loans <- List.filter (fun loan -> not (List.mem loan loans)) scope.loans)
      b.scopes
  end

let scope_ends scope origin =
  List.map
    (fun kind -> { kind; origin })
    ((if scope.loans <> [] then [ Loan_end (List.rev scope.loans) ] else [])
    @ (if scope.bound <> [] then [ Dead (List.rev scope.bound) ] else [])
    @ (if scope.temporaries <> [] then [ Dead (List.rev scope.temporaries) ] else [])
    @ if scope.provides then [ Provide_end ] else [])

let end_scope b scope origin =
  List.iter (fun (ended : statement) -> emit b ended.kind ended.origin) (scope_ends scope origin)

let in_scope ?(provides = false) ?(held = ([], [], [])) b origin f =
  let names, lent, loans = held in
  let scope = { frame = Bindings; bound = names; loans; temporaries = lent; provides } in
  b.scopes <- scope :: b.scopes;
  let result = f () in
  b.scopes <- List.tl b.scopes;
  end_scope b scope origin;
  result

(* The scopes inside the [outer] outermost and among the [inner] outermost,
   innermost first, each with its loans now. *)
let scopes_between b ~outer ~inner =
  let count = List.length b.scopes in
  List.concat
    (List.mapi
       (fun position scope ->
         let depth = count - position in
         if depth > outer && depth <= inner then [ (scope, scope.loans) ] else [])
       b.scopes)

(* Ends the scopes inside the [depth] outermost, before a jump out of them. *)
let leave_scopes b ~depth origin =
  let rec leave scopes count =
    if count > depth then
      match scopes with
      | scope :: outer ->
          end_scope b scope origin;
          leave outer (count - 1)
      | [] -> ()
  in
  leave b.scopes (List.length b.scopes)

(* Runs [f] as one statement: its loans end after it, and the temporaries it
   makes are dead. *)
let in_statement b origin f =
  let scope = { frame = Statement; bound = []; loans = []; temporaries = []; provides = false } in
  b.scopes <- scope :: b.scopes;
  let result = f () in
  b.scopes <- List.tl b.scopes;
  end_scope b scope origin;
  result

let ( let* ) = Option.bind

let operand_type : Core.operand -> Types.ty = function
  | Place found -> Core_walk.place_type found
  | Value value -> value.type_

let operand_origin : Core.operand -> Core.origin = function
  | Place found -> Core_walk.place_origin found
  | Value value -> value.origin

(* Whether evaluating a place runs code: a lending call, or the value of a
   temporary. *)
let rec evaluates (found : Core.place) =
  match found with
  | Local _ | Constant _ -> false
  | Field { base; _ } -> evaluates base
  | Lent _ | Temporary _ -> true

let is_unit (type_ : Types.ty) = Types.equal type_ Types.unit
let diverges (type_ : Types.ty) = type_ = Types.Never

let rec field_path (place : place) = function
  | [] -> place
  | field :: rest -> field_path (project place (Field field)) rest

(* A value held in a local that no scope makes dead, for a jump that ends
   every scope it leaves. *)
let held_past_scopes b origin (value : operand) =
  match value with
  | Use { type_; node; _ } ->
      let local = new_local b Temporary type_ origin in
      assign b (at local) (Operand value) origin;
      Use { place = at local; type_; node; origin }
  | Constant _ | Borrow _ | Take _ -> value

(* Returns: every scope ends, then the function returns the value. *)
let return_ b value origin =
  let value = Option.map (held_past_scopes b origin) value in
  leave_scopes b ~depth:0 origin;
  terminate b (Return value) origin

let type_of_operand : operand -> Types.ty = function
  | Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } | Constant { type_; _ } -> type_

(* The origin of the [concurrent] block or loop whose group a task is in. *)
let group_key : Core.task -> Core.origin = function
  | Branch { block; _ } -> block
  | Iteration { loop } -> loop

(* How many scopes stay when a task's exit is taken. *)
let exit_depth b (exit : task_exit) =
  match (exit, b.loops) with
  | Exit_return _, _ -> Some 0
  | (Exit_to _ | Exit_iteration _), loop :: _ -> Some loop.depth
  | _, [] -> None

(* The temporaries that a [let] extends to the end of its bindings' scope,
   by the id of their expression, as Rust and C++ do: the base of a slice
   that the value is, through fields and nested slices, and the same in the
   fields of a record or variant that the value constructs, in the updated
   fields of a record update, and in the elements of an array literal. The
   binding can then hold a view of the temporary, as in
   [let middle = make_list()[1..4]], which would dangle if the temporary
   were dropped where the statement ends. A temporary elsewhere in the
   value, such as a method's receiver, ends with the statement. *)
let rec extended_temporaries (value : Core.operand) =
  match value with Place base -> extended_base base | Value value -> extended_by value

and extended_by (value : Core.expression) =
  match value.kind with
  | Slice { call = { kind = Call { arguments = Passed { value = Place base; _ } :: _; _ }; _ } } ->
      extended_base base
  | Construct { fields; _ } ->
      List.concat_map
        (fun (_, field) -> Option.fold ~none:[] ~some:extended_temporaries field)
        fields
  | Record_update { updates; _ } -> List.concat_map (fun (_, update) -> extended_by update) updates
  | Collection_literal { elements; construction = Array } -> List.concat_map extended_by elements
  | _ -> []

and extended_base (base : Core.place) =
  match base with
  | Temporary written -> written.id :: extended_by written
  | Field { base; _ } -> extended_base base
  | Local _ | Constant _ | Lent _ -> []

(* Expressions *)

let rec expression b (node : Core.expression) : operand option =
  let origin = node.origin in
  let hold value = hold ~node:node.id b node.type_ origin value in
  match b.current with
  | None -> None
  | Some _ -> (
      match node.kind with
      | Integer value -> Some (Constant { value = Integer value; type_ = node.type_ })
      | Float value -> Some (Constant { value = Float value; type_ = node.type_ })
      | Boolean value -> Some (Constant { value = Boolean value; type_ = node.type_ })
      | String value -> Some (Constant { value = String value; type_ = node.type_ })
      | Template { literals; call = { kind = Call called; _ } } ->
          let* call = call_of b called ~node:node.id ~origin:node.origin in
          let local = temporary b node.type_ origin in
          emit b (Template { destination = at local; literals; call }) origin;
          Some (Use { place = at local; type_ = node.type_; node = node.id; origin = node.origin })
      | Template _ -> bug "a tagged template whose value is not a call"
      | Use place_ ->
          let* place_ = place b place_ in
          Some (Use { place = place_; type_ = node.type_; node = node.id; origin = node.origin })
      | Copy copied ->
          let* copied = operand b Read copied in
          hold (Copy copied)
      | Function_value { path; type_arguments } -> hold (Function_value { path; type_arguments })
      | Value_parameter parameter -> hold (Value_parameter parameter)
      | Lambda { parameters; captures; body; _ } ->
          let index = lambda b parameters captures body in
          hold
            (Lambda
               {
                 written = node;
                 body = index;
                 captures =
                   List.map
                     (fun (capture : Core.capture) ->
                       {
                         local = capture.local;
                         type_ = capture.type_;
                         place = at (source b capture.local);
                       })
                     captures;
               })
      | Construct { variant; fields } ->
          let* fields = construct_fields b fields in
          hold (Construct { variant; fields })
      | Collection_literal { elements; construction = Array } ->
          let* elements = operands b elements in
          hold (Array elements)
      | Record_update { base; updates } -> (
          let* values = operands b (base :: List.map snd updates) in
          match values with
          | base_value :: update_values ->
              let local = temporary b node.type_ origin in
              assign b (at local) (Operand base_value) origin;
              List.iter2
                (fun (fields, (written : Core.expression)) value ->
                  assign b (field_path (at local) fields) (Operand value) written.origin)
                updates update_values;
              Some
                (Use { place = at local; type_ = node.type_; node = node.id; origin = node.origin })
          | [] -> bug "a record update without a base")
      | Slice { call = { kind = Call called; _ }; _ } -> (
          let* call = call_of b called ~node:node.id ~origin:node.origin in
          match call.arguments with
          | Passed { value = Borrow { place = base; _ }; _ } :: _ ->
              let local = temporary b node.type_ origin in
              emit b (Slice { destination = at local; base; call }) origin;
              Some
                (Use { place = at local; type_ = node.type_; node = node.id; origin = node.origin })
          | _ -> bug "a slice whose base is not its first argument")
      | Slice _ -> bug "a slice whose view is not a call"
      | Call called -> call_value b node called
      | Operator { operation; arguments } ->
          let* operands = operands b arguments in
          let type_arguments =
            List.map (fun (argument : Core.expression) -> Types.Type argument.type_) arguments
          in
          hold (Operation { operation; type_arguments; operands })
      | Compare { comparison; left; right } -> (
          let* compared = operands b [ left; right ] in
          match compared with
          | [ left; right ] -> hold (Compare { comparison; left; right })
          | _ -> bug "a comparison without two operands")
      | Not inner ->
          let* inner = expression b inner in
          hold (Not inner)
      | And _ | Or _ | Implies _ | Matches _ -> truth b node
      | Convert { conversion; value } ->
          let* value = expression b value in
          hold (Convert { conversion; value })
      | To_any { value; trait; evidence } ->
          let* value = expression b value in
          hold (To_any { value; trait; evidence })
      | If { condition = tested; then_; else_; binds_lent_part } ->
          b.if_conditions <- tested.origin :: b.if_conditions;
          let result = value_local b node in
          let yes = new_block b and no = new_block b and joined = new_block b in
          let held =
            scoped_condition b tested ~yes ~no
              ~lends:(if binds_lent_part then For_block else For_condition)
          in
          start b yes;
          branch_into ~held b result then_ joined origin;
          start b no;
          (match else_ with
          | Some else_ -> branch_into b result else_ joined origin
          | None -> goto b joined origin);
          start b joined;
          result_of b node result
      | Match { scrutinees; arms } ->
          let result = value_local b node in
          let joined = new_block b in
          match_ b scrutinees arms ~origin
            ~arm:(fun (arm : Core.arm) ->
              let value = block b arm.body in
              match (value, result) with
              | Some value, Some local -> assign b (at local) (Operand value) arm.origin
              | _ -> ())
            ~joined;
          start b joined;
          result_of b node result
      | Block inner -> scoped_block b inner origin
      | Provide { implementations; body } ->
          let* values =
            in_order b
              (List.map
                 (fun (implementation : Core.implementation) ->
                   ( (fun () -> operand b implementation.mode implementation.value),
                     implementation.type_,
                     implementation.origin ))
                 implementations)
          in
          let provided =
            List.map2
              (fun (implementation : Core.implementation) value ->
                {
                  mode = implementation.mode;
                  value;
                  type_ = implementation.type_;
                  provides = implementation.provides;
                  origin = implementation.origin;
                })
              implementations values
          in
          emit b (Provide { provided; can_use_tasks = Core_walk.can_use_tasks body }) origin;
          scoped_block ~provides:true b body origin ~loans:(fun () ->
              List.iter
                (fun (provided : provided) ->
                  match provided.value with
                  | Borrow _ ->
                      ignore
                        (start_loan b provided.value
                           (if provided.mode = Mut then Mut else Read)
                           Provide_body provided.origin)
                  | _ -> ())
                provided)
      | Return returned -> (
          match tasks_left b `Return with
          | [] ->
              (match returned with
              | None -> return_ b None origin
              | Some returned ->
                  Option.iter (fun value -> return_ b (Some value) origin) (expression b returned));
              None
          | tasks ->
              let exit =
                match returned with
                | Some returned ->
                    Option.map (fun value -> Exit_return (Some value)) (expression b returned)
                | None -> Some (Exit_return None)
              in
              Option.iter (fun exit -> leave_tasks b tasks exit origin) exit;
              None)
      | Break -> (
          match (b.loops, tasks_left b `Break) with
          | loop :: _, [] ->
              leave_scopes b ~depth:loop.depth origin;
              goto b loop.break_ origin;
              None
          | loop :: _, tasks ->
              leave_tasks b tasks (Exit_to loop.break_) origin;
              None
          | [], _ -> bug "a `break` outside a loop")
      | Continue -> (
          match (b.loops, tasks_left b `Continue) with
          | loop :: _, [] ->
              leave_scopes b ~depth:loop.depth origin;
              (match loop.continue_ with
              | Jump block -> goto b block origin
              | Next_iteration loop -> terminate b (Iteration_end { loop }) origin);
              None
          | loop :: _, tasks ->
              leave_tasks b tasks
                (match loop.continue_ with
                | Jump block -> Exit_to block
                | Next_iteration loop -> Exit_iteration { loop })
                origin;
              None
          | [], _ -> bug "a `continue` outside a loop")
      | Todo ->
          terminate b Todo origin;
          None
      | Unreachable ->
          terminate b Written_unreachable origin;
          None
      | Echo inner ->
          let* value = expression b inner in
          let local = temporary b inner.type_ origin in
          assign b (at local) (Operand value) origin;
          emit b
            (Echo (Borrow { place = at local; type_ = inner.type_; mode = Read; origin }))
            origin;
          Some (Use { place = at local; type_ = node.type_; node = node.id; origin = node.origin })
      | Current_target -> (
          match b.compound_target with
          | Some target -> Some (Take { place = target; type_ = node.type_; origin = node.origin })
          | None -> bug "the old value of a target outside a compound assignment")
      | Quantified { quantifier; binder = Over_range { pattern; start; stop; inclusive }; body } ->
          quantifier_loop b node quantifier pattern body (fun ~each ->
              range_loop b ~origin ~pattern ~start ~stop ~inclusive
                ~loop:{ (no_clauses origin) with formula = Some node }
                ~each)
      | Quantified { quantifier; binder = Over_elements { pattern; elements }; body } ->
          quantifier_loop b node quantifier pattern body (fun ~each ->
              elements_loop b ~origin ~pattern ~elements
                ~loop:{ (no_clauses origin) with formula = Some node }
                ~each)
      | Collection_literal { construction = Specification_only; _ }
      | Map_literal _ | Result | Old _ | Quantified _ | Yielded | Identical _
      | Specification_function _ | Method_time _ ->
          bug "a specification's expression in code that runs")

and no_clauses origin = { clauses = []; schedule = Sequential; origin; formula = None }

and operands b nodes =
  in_order b
    (List.map
       (fun (node : Core.expression) -> ((fun () -> expression b node), node.type_, node.origin))
       nodes)

(* Evaluates operands in order, each where it is written. A later operand
   must not change what an earlier one evaluated to, so each operand but the
   last is held where it is evaluated, and what it borrows or views stays
   lent read-only until the last is evaluated. *)
and in_order b (operands : ((unit -> operand option) * Types.ty * Core.origin) list) =
  let count = List.length operands in
  let loans = ref [] in
  let evaluated =
    List.fold_left
      (fun (reached, index) (evaluate, type_, origin) ->
        match reached with
        | None -> (None, index + 1)
        | Some evaluated -> (
            match evaluate () with
            | None -> (None, index + 1)
            | Some value ->
                let value =
                  if count > 1 then begin
                    let value = held b value type_ origin in
                    (match value with
                    | Constant _ | Take _ -> ()
                    | _ ->
                        if index < count - 1 then
                          loans := start_loan b value Read Operand_evaluation origin :: !loans);
                    value
                  end
                  else value
                in
                (Some (evaluated @ [ value ]), index + 1)))
      (Some [], 0) operands
    |> fst
  in
  (match operands with (_, _, origin) :: _ -> end_loans b (List.rev !loans) origin | [] -> ());
  evaluated

(* An operand kept where it is evaluated: a value is read into a temporary
   there, and a read-only borrow is taken there, so that later code cannot
   change what it read. A [mut] borrow starts where its operation runs, so
   later operands can still read the place. *)
and held b (value : operand) type_ origin =
  match value with
  | Constant _ | Borrow { mode = Mut; _ } | Take _ -> value
  | Use { place = { root = Local local; projections = [] }; _ }
    when (Hashtbl.find b.infos local).kind = Temporary ->
      value
  | Use { node; _ } ->
      let local = temporary b type_ origin in
      assign b (at local) (Operand value) origin;
      Use { place = at local; type_; node; origin }
  | Borrow { mode; _ } ->
      let local = new_local b (Lent Read) type_ origin in
      add_temporary b local;
      assign b (at local) (Operand value) origin;
      Borrow { place = at local; type_; mode; origin }

(* The fields of a constructor, in evaluation order. *)
and construct_fields b fields =
  let given =
    List.filter_map (fun (name, field) -> Option.map (fun field -> (name, field)) field) fields
  in
  let* values =
    in_order b
      (List.map
         (fun (_, (field : Core.operand)) ->
           ( (fun () ->
               match field with
               | Place _ ->
                   bug
                     "a constructor field that is a place, in a construct that no lending method \
                      lends"
               | Value value -> expression b value),
             operand_type field,
             operand_origin field ))
         given)
  in
  let values = ref values in
  Some
    (List.map
       (fun (name, field) ->
         match field with
         | None -> (name, None)
         | Some _ -> (
             match !values with
             | value :: rest ->
                 values := rest;
                 (name, Some value)
             | [] -> bug "a constructor with fewer values than fields"))
       fields)

and yielded b (mode : Types.mode) (part : Core.operand) : yielded option =
  let rec lends : Core.operand -> bool = function
    | Place _ -> true
    | Value { kind = Construct { fields; _ }; _ } ->
        List.exists (fun (_, field) -> Option.fold ~none:false ~some:lends field) fields
    | Value _ -> false
  in
  match part with
  | Value { kind = Construct _; _ } when lends part ->
      let rec leaves (field : Core.operand) =
        match field with
        | Value { kind = Construct { fields; _ }; _ } when lends field ->
            List.concat_map (fun (_, field) -> Option.fold ~none:[] ~some:leaves field) fields
        | _ -> [ ((fun () -> operand b mode field), operand_type field, operand_origin field) ]
      in
      let* values = in_order b (leaves part) in
      let remaining = ref values in
      let rec rebuild (field : Core.operand) =
        match field with
        | Value ({ kind = Construct { variant; fields }; _ } as node) when lends field ->
            Built
              {
                variant;
                fields = List.map (fun (name, field) -> (name, Option.map rebuild field)) fields;
                type_ = node.type_;
                node = node.id;
              }
        | _ -> (
            match !remaining with
            | value :: rest ->
                remaining := rest;
                Part value
            | [] -> bug "a yielded constructor with fewer values than fields")
      in
      Some (rebuild part)
  | _ -> Option.map (fun value -> Part value) (operand b mode part)

(* An operand passed with a mode: a place is borrowed, and a value is
   evaluated. *)
and operand b (mode : Types.mode) (passed : Core.operand) =
  match passed with
  | Place written ->
      let* passed = place b written in
      Some
        (Borrow
           {
             place = passed;
             type_ = Core_walk.place_type written;
             mode;
             origin = Core_walk.place_origin written;
           })
  | Value value -> expression b value

and place b (found : Core.place) : place option =
  match b.current with
  | None -> None
  | Some _ -> (
      match found with
      | Local { local; _ } -> Some (at (source b local))
      | Constant { path; _ } -> Some { root = Constant path; projections = [] }
      | Field { base; field; _ } ->
          let* base = place b base in
          Some (project base (Field field))
      | Lent lending -> lent b lending ~duration:Rest_of_statement
      | Temporary written ->
          let* value = expression b written in
          let local = new_local b Temporary written.type_ written.origin in
          (match binding_scope b with
          | Some scope when List.mem written.id b.extended ->
              scope.temporaries <- local :: scope.temporaries
          | _ -> add_temporary b local);
          assign b (at local) (Operand value) written.origin;
          Some (at local))

(* The part that a lending call lends, which the innermost scope ends. The
   receiver stays lent for as long. *)
and lent b (lending : Core.expression) ~duration : place option =
  match lending.kind with
  | Call ({ lends = Some mode; _ } as called) ->
      let* call = call_of b called ~node:lending.id ~origin:lending.origin in
      let part = new_local b (Lent mode) lending.type_ lending.origin in
      add_temporary b part;
      emit b (Lend { part; call }) lending.origin;
      (match call.arguments with
      | Passed { mode; value = Borrow _ as receiver; _ } :: _ ->
          ignore (start_loan b receiver (if mode = Mut then Mut else Read) duration lending.origin)
      | _ -> ());
      Some (at part)
  | Call _ -> bug "a lent place whose call does not lend"
  | _ -> bug "a lent place that is not a call"

and callee_of b (callee : Core.callee) : callee option =
  Core_walk.traverse_indirect (operand b Read) callee

(* A call: its callee, then its arguments in order. *)
and call_of b (called : Core.call) ~node ~origin : call option =
  let* callee = callee_of b called.callee in
  let* values =
    in_order b
      (List.filter_map
         (function
           | Core.Default -> None
           | Passed { mode; value; _ } ->
               Some ((fun () -> operand b mode value), operand_type value, operand_origin value))
         called.arguments)
  in
  let values = ref values in
  let arguments =
    List.map
      (fun (argument : Core.argument) ->
        match argument with
        | Default -> Default
        | Passed { mode; mark; _ } -> (
            match !values with
            | value :: rest ->
                values := rest;
                Passed { mode; value; mark }
            | [] -> bug "a call with fewer values than arguments"))
      called.arguments
  in
  Some { callee; arguments; uses = called.uses; node; origin }

and call_value b (node : Core.expression) (called : Core.call) =
  let origin = node.origin in
  match called.callee with
  | Intrinsic { operation; type_arguments } when Intrinsic.primitive operation ->
      let* operands =
        in_order b
          (List.map
             (function
               | Core.Passed { value; mode; _ } ->
                   ((fun () -> operand b mode value), operand_type value, operand_origin value)
               | Default -> bug "a primitive operation with a default argument")
             called.arguments)
      in
      hold ~node:node.id b node.type_ origin (Operation { operation; type_arguments; operands })
  | _ ->
      let* call = call_of b called ~node:node.id ~origin:node.origin in
      if diverges node.type_ then begin
        emit b (Call { destination = None; call }) origin;
        terminate b Unreachable origin;
        None
      end
      else if is_unit node.type_ then begin
        emit b (Call { destination = None; call }) origin;
        Some (Constant { value = Unit; type_ = Types.unit })
      end
      else
        let local = temporary b node.type_ origin in
        emit b (Call { destination = Some (at local); call }) origin;
        Some (Use { place = at local; type_ = node.type_; node = node.id; origin = node.origin })

(* A [Bool] value of a condition: true on the path where it holds. *)
and truth b (node : Core.expression) =
  let local = temporary b node.type_ node.origin in
  let yes = new_block b and no = new_block b and joined = new_block b in
  condition b node ~yes ~no;
  start b yes;
  assign b (at local) (Operand (Constant { value = Boolean true; type_ = Types.bool })) node.origin;
  goto b joined node.origin;
  start b no;
  assign b (at local) (Operand (Constant { value = Boolean false; type_ = Types.bool })) node.origin;
  goto b joined node.origin;
  start b joined;
  Some (Use { place = at local; type_ = node.type_; node = node.id; origin = node.origin })

and condition b (node : Core.expression) ~yes ~no =
  match node.kind with
  | And (left, right) ->
      let middle = new_block b in
      condition b left ~yes:middle ~no;
      start b middle;
      condition b right ~yes ~no
  | Or (left, right) ->
      let middle = new_block b in
      condition b left ~yes ~no:middle;
      start b middle;
      condition b right ~yes ~no
  | Implies (left, right) ->
      (* A [requires] clause that a template's check evaluates while compiling
         may hold [==>]. Its right operand is evaluated only where its left
         holds, since it may be defined only there. *)
      let middle = new_block b in
      condition b left ~yes:middle ~no:yes;
      start b middle;
      condition b right ~yes ~no
  | Not inner -> condition b inner ~yes:no ~no:yes
  | Boolean true -> goto b yes node.origin
  | Boolean false -> goto b no node.origin
  | Matches { value; pattern } -> (
      match scrutinee b value with
      | Some scrutinee ->
          (* The bindings of [is] are for the statement around it. *)
          let enclosing = b.binds_into in
          b.binds_into <- Statement;
          match_patterns b [ pattern ] [ scrutinee ] ~fail:no ~matched:yes node.origin;
          b.binds_into <- enclosing
      | None -> ())
  | _ -> (
      match expression b node with
      | Some value ->
          terminate b
            (Branch
               {
                 condition = value;
                 yes;
                 no;
                 is_if_condition = List.mem node.origin b.if_conditions;
               })
            node.origin
      | None -> ())

and scoped_condition ~lends b (node : Core.expression) ~yes ~no =
  let naming = List.find_opt (fun scope -> scope.frame = Statement) b.scopes in
  let named_before = match naming with Some scope -> scope.bound | None -> [] in
  let scope = { frame = Condition; bound = []; loans = []; temporaries = []; provides = false } in
  b.scopes <- scope :: b.scopes;
  let yes' = new_block b and no' = new_block b in
  condition b node ~yes:yes' ~no:no';
  b.scopes <- List.tl b.scopes;
  let lent, others =
    List.partition
      (fun local -> match (Hashtbl.find b.infos local).kind with Lent _ -> true | _ -> false)
      scope.temporaries
  in
  let loans = scope.loans in
  if lends = For_statement then begin
    List.iter (add_temporary b) (List.rev lent);
    match b.scopes with enclosing :: _ -> enclosing.loans <- loans @ enclosing.loans | [] -> ()
  end;
  let names =
    match (lends, naming) with
    | For_block, Some named ->
        let names = List.filter (fun local -> not (List.mem local named_before)) named.bound in
        named.bound <- named_before;
        names
    | _ -> []
  in
  let kept = { scope with temporaries = others; loans = [] } in
  let on_true, on_false =
    match lends with
    | For_statement -> (kept, kept)
    | For_block -> (kept, { scope with bound = names })
    | For_condition -> (scope, scope)
  in
  List.iter
    (fun (entry, target, ended) ->
      start b entry;
      end_scope b ended node.origin;
      goto b target node.origin)
    [ (yes', yes, on_true); (no', no, on_false) ];
  if lends = For_block then (names, lent, loans) else ([], [], [])

(* The local an [if] or a [match] writes its value to, if it has one. *)
and value_local b (node : Core.expression) =
  if is_unit node.type_ || diverges node.type_ then None
  else Some (temporary b node.type_ node.origin)

and result_of b (node : Core.expression) result =
  match (b.current, result) with
  | None, _ -> None
  | Some _, Some local ->
      Some (Use { place = at local; type_ = node.type_; node = node.id; origin = node.origin })
  | Some _, None ->
      if diverges node.type_ then None else Some (Constant { value = Unit; type_ = Types.unit })

(* A branch of an [if] or a [match]: its block, its value written to
   [result], then a jump to [joined]. *)
and branch_into ?held b result (body : Core.block) joined origin =
  in_scope ?held b origin (fun () ->
      match (block b body, result) with
      | Some value, Some local -> assign b (at local) (Operand value) origin
      | _ -> ());
  goto b joined origin

(* A block in a scope of its own: its value outlives the block's bindings
   and temporaries, for the enclosing statement. A temporary that holds it
   moves to the enclosing scope, and a binding's value is copied into a
   temporary there. *)
and scoped_block ?provides ?(loans = ignore) b (body : Core.block) origin =
  in_scope ?provides b origin (fun () ->
      loans ();
      let value = block b body in
      match (value, b.scopes) with
      | ( Some (Use { place = { root = Local local; _ }; type_; node; _ } as read),
          scope :: enclosing :: _ ) ->
          if List.mem local scope.temporaries then begin
            scope.temporaries <- List.filter (fun temporary -> temporary <> local) scope.temporaries;
            enclosing.temporaries <- local :: enclosing.temporaries;
            value
          end
          else if List.mem local scope.bound then begin
            let held = new_local b Temporary type_ origin in
            enclosing.temporaries <- held :: enclosing.temporaries;
            assign b (at held) (Operand read) origin;
            Some (Use { place = at held; type_; node; origin })
          end
          else value
      | _ -> value)

and block b (body : Core.block) : operand option =
  List.iter (statement b) body.statements;
  match body.value with
  | Some value -> expression b value
  | None -> (
      match b.current with
      | Some _ -> Some (Constant { value = Unit; type_ = Types.unit })
      | None -> None)

(* Patterns *)

(* A scrutinee as a place: a place is matched where it is, and a value is
   held in a temporary that the pattern's bindings own parts of. *)
and scrutinee b (found : Core.operand) : place option =
  match found with
  | Place found -> place b found
  | Value value ->
      let* value = expression b value in
      let local = temporary b (operand_type found) (operand_origin found) in
      assign b (at local) (Operand value) (operand_origin found);
      Some (at local)

(* The place a scrutinee is matched at: a borrowed place is matched where it
   is, and a value is held in a temporary. *)
and scrutinee_place b (value : operand) type_ origin : place =
  match value with
  | Borrow { place = found; _ } -> found
  | Use { place = { root = Local local; projections = [] } as found; _ }
    when (Hashtbl.find b.infos local).kind = Temporary ->
      found
  | Use _ | Take _ | Constant _ ->
      let local = temporary b type_ origin in
      assign b (at local) (Operand value) origin;
      at local

(* The tests of a pattern against a place: control goes on where it
   matches, and jumps to [fail] where it does not. Testing changes nothing,
   so bindings come after every test of an arm. *)
and test b (pattern : Core.pattern) (scrutinee : place) ~fail =
  let origin = pattern.origin in
  let branch_on value =
    let passed = new_block b in
    (match value with
    | Some condition ->
        terminate b (Branch { condition; yes = passed; no = fail; is_if_condition = false }) origin
    | None -> ());
    start b passed
  in
  let read =
    Use { place = scrutinee; type_ = pattern.type_; node = pattern.id; origin = pattern.origin }
  in
  match pattern.kind with
  | Wildcard | Bind _ -> ()
  | Variant { variant; fields } ->
      branch_on (hold b Types.bool origin (Is_variant { place = scrutinee; variant }));
      List.iter
        (fun (field, inner) ->
          test b inner (project scrutinee (Variant_field { variant; field })) ~fail)
        fields
  | Record fields ->
      List.iter (fun (field, inner) -> test b inner (project scrutinee (Field field)) ~fail) fields
  | Literal literal -> (
      match expression b literal with
      | Some value ->
          branch_on
            (hold b Types.bool origin (Compare { comparison = Equal; left = read; right = value }))
      | None -> ())
  | Range { start = low; stop = high; inclusive } -> (
      match (expression b low, expression b high) with
      | Some low, Some high ->
          branch_on
            (hold b Types.bool origin
               (Compare { comparison = Greater_equal; left = read; right = low }));
          branch_on
            (hold b Types.bool origin
               (Compare
                  {
                    comparison = (if inclusive then Less_equal else Less);
                    left = read;
                    right = high;
                  }))
      | _ -> ())
  | Equal_to { value; equal } -> (
      match (expression b value, callee_of b equal) with
      | Some value, Some callee ->
          let local = temporary b Types.bool origin in
          emit b
            (Call
               {
                 destination = Some (at local);
                 call =
                   {
                     callee;
                     arguments =
                       [
                         Passed
                           {
                             mode = Read;
                             value =
                               Borrow
                                 {
                                   place = scrutinee;
                                   type_ = pattern.type_;
                                   mode = Read;
                                   origin = pattern.origin;
                                 };
                             mark = None;
                           };
                         Passed { mode = Read; value; mark = None };
                       ];
                     uses = Types.no_capabilities;
                     node = pattern.id;
                     origin = pattern.origin;
                   };
               })
            origin;
          branch_on
            (Some
               (Use
                  {
                    place = at local;
                    type_ = Types.bool;
                    node = pattern.id;
                    origin = pattern.origin;
                  }))
      | _ -> ())
  | Alternatives _ -> bug "alternatives are expanded before they are tested"

(* Binds a pattern's locals to the parts of the place it matched. A binding
   with [Read] or [Mut] is the part itself, and one with [Own] takes the
   part. With [owned], every binding takes a copy, as a loop's counter is a
   value for each iteration and not a place. *)
and bind ?(owned = false) b (pattern : Core.pattern) (scrutinee : place) =
  let bind = bind ~owned in
  match pattern.kind with
  | Wildcard | Literal _ | Range _ | Equal_to _ -> ()
  | Bind { local; mode; name; is_var } ->
      let found =
        bind_source ~name ~is_var b local (if owned then Own else mode) pattern.type_ pattern.origin
      in
      emit b (Live [ found ]) pattern.origin;
      assign b (at found)
        (Operand
           (match mode with
           | Own ->
               Use
                 {
                   place = scrutinee;
                   type_ = pattern.type_;
                   node = pattern.id;
                   origin = pattern.origin;
                 }
           | (Read | Mut) when owned ->
               Use
                 {
                   place = scrutinee;
                   type_ = pattern.type_;
                   node = pattern.id;
                   origin = pattern.origin;
                 }
           | Read | Mut ->
               Borrow { place = scrutinee; type_ = pattern.type_; mode; origin = pattern.origin }))
        pattern.origin
  | Variant { variant; fields } ->
      List.iter
        (fun (field, inner) -> bind b inner (project scrutinee (Variant_field { variant; field })))
        fields
  | Record fields ->
      List.iter (fun (field, inner) -> bind b inner (project scrutinee (Field field))) fields
  | Alternatives _ -> bug "alternatives are expanded before they are bound"

(* The ways a list of patterns can match, without alternatives: one for each
   choice of an alternative in each. *)
and expansions (patterns : Core.pattern list) : Core.pattern list list =
  let rec expand (pattern : Core.pattern) : Core.pattern list =
    match pattern.kind with
    | Alternatives alternatives -> List.concat_map expand alternatives
    | Variant { variant; fields } ->
        List.map
          (fun fields -> { pattern with kind = Variant { variant; fields } })
          (expand_fields fields)
    | Record fields ->
        List.map (fun fields -> { pattern with kind = Record fields }) (expand_fields fields)
    | _ -> [ pattern ]
  and expand_fields fields =
    List.fold_right
      (fun (name, inner) rest ->
        List.concat_map
          (fun inner -> List.map (fun rest -> (name, inner) :: rest) rest)
          (expand inner))
      fields [ [] ]
  in
  List.fold_right
    (fun pattern rest ->
      List.concat_map (fun pattern -> List.map (fun rest -> pattern :: rest) rest) (expand pattern))
    patterns [ [] ]

(* Tests and binds patterns against places: control goes to [matched]
   where they match, and to [fail] where they do not. Each way the patterns
   can match, one for each choice among their alternatives, binds the same
   locals. *)
and match_patterns b patterns places ~fail ~matched origin =
  let expanded = expansions patterns in
  let count = List.length expanded in
  List.iteri
    (fun index patterns ->
      let failed = if index = count - 1 then fail else new_block b in
      List.iter2 (fun pattern found -> test b pattern found ~fail:failed) patterns places;
      List.iter2 (bind b) patterns places;
      goto b matched origin;
      if index < count - 1 then start b failed)
    expanded

(* A [match]: its scrutinees in order, then its arms in order. Each arm
   tests its patterns, binds, evaluates its guard, runs [arm], ends its
   bindings, and jumps to [joined]. *)
and match_ b scrutinees (arms : Core.arm list) ~origin ~arm ~joined =
  let evaluated =
    in_order b
      (List.map
         (fun (found : Core.operand) ->
           ((fun () -> operand b Read found), operand_type found, operand_origin found))
         scrutinees)
  in
  match evaluated with
  | None -> ()
  | Some evaluated ->
      let places =
        List.map2
          (fun (found : Core.operand) value ->
            scrutinee_place b value (operand_type found) (operand_origin found))
          scrutinees evaluated
      in
      List.iter
        (fun (current : Core.arm) ->
          let next = new_block b and body = new_block b and failed = new_block b in
          let arm_scope = ref None in
          in_scope b current.origin (fun () ->
              arm_scope := Some (List.hd b.scopes);
              match_patterns b current.patterns places ~fail:failed ~matched:body current.origin;
              start b body;
              if current.patterns <> [] then
                emit b
                  (Matched
                     {
                       patterns =
                         List.map (fun (pattern : Core.pattern) -> pattern.origin) current.patterns;
                     })
                  current.origin;
              match current.guard with
              | None -> arm current
              | Some guard ->
                  (* If the guard is false, later arms test the same
                     scrutinees, so the guard cannot change them. *)
                  let loans =
                    List.filter_map
                      (fun value ->
                        match value with
                        | Constant _ -> None
                        | _ -> Some (start_loan b value Read Operand_evaluation current.origin))
                      evaluated
                  in
                  let passed = new_block b and rejected = new_block b in
                  ignore (scoped_condition ~lends:For_statement b guard ~yes:passed ~no:rejected);
                  start b rejected;
                  end_loans b loans current.origin;
                  (match b.scopes with
                  | scope :: _ when scope.bound <> [] ->
                      emit b (Dead (List.rev scope.bound)) current.origin
                  | _ -> ());
                  goto b failed current.origin;
                  start b passed;
                  end_loans b loans current.origin;
                  arm current);
          goto b joined current.origin;
          (* Where a test or the guard fails, the arm ends the temporaries
             of its tests, and the next arm tests the scrutinees. *)
          start b failed;
          (match !arm_scope with
          | Some { temporaries = _ :: _ as temporaries; _ } ->
              emit b (Dead (List.rev temporaries)) current.origin
          | _ -> ());
          goto b next current.origin;
          start b next)
        arms;
      terminate b Unreachable origin

(* Statements *)

and statement b (node : Core.statement) =
  let origin = node.origin in
  in_statement b origin (fun () ->
      match node.kind with
      | Let { pattern; value; else_ } -> (
          let enclosing = b.extended in
          b.extended <- extended_temporaries value;
          let found = scrutinee b value in
          b.extended <- enclosing;
          match found with
          | None -> ()
          | Some found ->
              (* The pattern's bindings join the scope after the [else]
                 block, which runs where they are not bound. *)
              let failed = new_block b and matched = new_block b in
              let enclosing = b.deferred in
              b.deferred <- Some [];
              match_patterns b [ pattern ] [ found ] ~fail:failed ~matched origin;
              let bound = Option.value ~default:[] b.deferred in
              b.deferred <- enclosing;
              start b failed;
              (match else_ with
              | Some else_ -> ignore (in_scope b origin (fun () -> block b else_))
              | None -> ());
              terminate b Unreachable origin;
              List.iter (register_binding b) (List.rev bound);
              start b matched)
      | Evaluate value -> ignore (expression b value)
      | Assign { target; value = written; _ } -> (
          match expression b written with
          | Some value -> (
              (* The value is evaluated before the target, and what it
                 borrows or views stays lent while the target's index keys
                 are evaluated. *)
              let value = if evaluates target then held b value written.type_ origin else value in
              let loans =
                match value with
                | Constant _ -> []
                | _ -> [ start_loan b value Read Operand_evaluation origin ]
              in
              let target = place b target in
              end_loans b loans origin;
              match target with Some target -> assign b target (Operand value) origin | None -> ())
          | None -> ())
      | Compound_assign { target; operand = right; bound; value } -> (
          let mode : Types.mode = match right with Place _ -> Read | Value _ -> Own in
          match operand b mode right with
          | None -> ()
          | Some right_value -> (
              let local =
                new_local b
                  (Source { local = bound; mode; name = None; is_var = false })
                  (operand_type right) origin
              in
              Hashtbl.replace b.sources bound local;
              add_temporary b local;
              emit b (Live [ local ]) origin;
              assign b (at local) (Operand right_value) origin;
              let bound_value =
                match right_value with
                | Borrow _ ->
                    Borrow { place = at local; type_ = operand_type right; mode = Read; origin }
                | _ -> Use { place = at local; type_ = operand_type right; node = origin; origin }
              in
              let loans = [ start_loan b bound_value Read Operand_evaluation origin ] in
              let target = place b target in
              end_loans b loans origin;
              match target with
              | None -> ()
              | Some target -> (
                  let enclosing = b.compound_target in
                  b.compound_target <- Some target;
                  let updated = expression b value in
                  b.compound_target <- enclosing;
                  match updated with
                  | Some updated -> assign b target (Operand updated) origin
                  | None -> ())))
      | For { pattern; iteration; clauses; body; mode } -> (
          let loop = { clauses; schedule = mode; origin; formula = None } in
          let each ~bind_part =
            let is_task = mode = Concurrent_loop in
            if is_task then
              b.tasks <- (Core.Iteration { loop = origin }, (List.length b.scopes, None)) :: b.tasks;
            in_scope b origin (fun () ->
                bind_part ();
                ignore (block b body));
            if is_task then b.tasks <- List.tl b.tasks
          in
          match iteration with
          | Integer_range { start; stop; inclusive } ->
              range_loop b ~origin ~pattern ~start ~stop ~inclusive ~loop ~each:(fun bind_part ->
                  each ~bind_part)
          | Elements elements ->
              elements_loop b ~origin ~pattern ~elements ~loop ~each:(fun bind_part ->
                  each ~bind_part)
          | Cursor { cursor; next } ->
              cursor_loop b ~origin ~pattern ~cursor ~next ~loop ~each:(fun bind_part ->
                  each ~bind_part))
      | While { condition = tested; clauses; body; binds_lent_part } ->
          let header = new_block b and inside = new_block b and after = new_block b in
          goto b header origin;
          (Hashtbl.find b.pending header).heading <-
            Some
              {
                loop = { clauses; schedule = Sequential; origin; formula = Some tested };
                body = inside;
                after = Some after;
              };
          start b header;
          let held =
            scoped_condition b tested ~yes:inside ~no:after
              ~lends:(if binds_lent_part then For_block else For_condition)
          in
          start b inside;
          looping b ~break_:after ~continue_:(Jump header) (fun () ->
              ignore (in_scope ~held b origin (fun () -> block b body)));
          goto b header origin;
          start b after
      | Parallel branches | Concurrent branches ->
          let concurrent = match node.kind with Concurrent _ -> true | _ -> false in
          let entries = List.map (fun _ -> new_block b) branches and join = new_block b in
          let entry = b.current in
          let branches =
            List.mapi
              (fun index (branch : Core.statement) ->
                let branch_entry = List.nth entries index in
                let last = index + 1 = List.length entries in
                start b branch_entry;
                let first = b.block_count in
                if concurrent then begin
                  let branch_end = new_block b in
                  b.tasks <-
                    (Core.Branch { block = origin; index }, (List.length b.scopes, Some branch_end))
                    :: b.tasks;
                  statement b branch;
                  b.tasks <- List.tl b.tasks;
                  goto b branch_end branch.origin;
                  start b branch_end
                end
                else statement b branch;
                let next =
                  if last then resumed b origin ~next:join else List.nth entries (index + 1)
                in
                terminate b (Join { fork = origin; next }) branch.origin;
                {
                  entry = branch_entry;
                  blocks =
                    inside_group b origin
                      (branch_entry
                      :: List.init (b.block_count - first) (fun index -> first + index));
                })
              branches
          in
          b.current <- entry;
          start_group b origin origin;
          terminate b
            (Fork { fork = origin; concurrent; branches; join = Some (resumed b origin ~next:join) })
            origin;
          resume_group b origin ~next:join origin;
          start b join
      | Proof proof -> emit b (Proof proof) origin
      | Assert { condition = { value; executable = true }; by_bit_vector } -> (
          match expression b value with
          | Some condition ->
              emit b
                (Assert { condition; bit_vector = (if by_bit_vector then Some value else None) })
                origin
          | None -> ())
      | Assert { condition = { value; executable = false }; by_bit_vector } ->
          emit b (Ghost_assert { condition = value; by_bit_vector }) origin
      | Yield { mode; part = written } -> (
          match yielded b mode written with
          | Some part ->
              let resume = new_block b in
              terminate b (Yield { mode; part; resume }) origin;
              start b resume
          | None -> ()))

and looping b ~break_ ~continue_ f =
  b.loops <-
    { break_; continue_; depth = List.length b.scopes; tasks_around = List.length b.tasks }
    :: b.loops;
  f ();
  b.loops <- List.tl b.loops

(* The tasks an early exit ends, innermost first. A [return] ends every
   enclosing task. A [break] or [continue] ends the tasks inside its loop,
   and a [break] of a [concurrent for] also ends the iteration, which a
   [continue] of it only finishes. *)
and tasks_left b exit =
  match exit with
  | `Return -> List.map fst b.tasks
  | (`Break | `Continue) as exit -> (
      match b.loops with
      | loop :: _ ->
          List.filteri (fun index _ -> index < List.length b.tasks - loop.tasks_around) b.tasks
          |> List.filter_map (fun (task, _) ->
              match (task, exit) with Core.Iteration _, `Continue -> None | _ -> Some task)
      | [] -> bug "a loop exit outside a loop")

(* An early exit from [tasks], which takes effect once they have ended. *)
and leave_tasks b tasks exit origin =
  let exit =
    match exit with
    | Exit_return value -> Exit_return (Option.map (held_past_scopes b origin) value)
    | Exit_to _ | Exit_iteration _ -> exit
  in
  (* The task ends the scopes inside it. The scopes outside it
       are the enclosing code's, which ends them once the task has
       ended. *)
  let starts =
    List.map
      (fun task ->
        match List.assoc_opt task b.tasks with
        | Some (start, _) -> start
        | None -> bug "an exit from a task that does not enclose it")
      tasks
  in
  let target_depth =
    match (exit_depth b exit, List.rev starts) with
    | Some depth, _ -> depth
    | None, outermost :: _ -> outermost
    | None, [] -> List.length b.scopes
  in
  let rec around = function
    | inner :: (outer :: _ as rest) -> scopes_between b ~outer ~inner :: around rest
    | [ inner ] -> [ scopes_between b ~outer:target_depth ~inner ]
    | [] -> []
  in
  (match starts with
  | innermost :: _ -> leave_scopes b ~depth:innermost origin
  | [] -> leave_scopes b ~depth:target_depth origin);
  (* Each task cancels its group. Where the exit wins, the code after the
     group ends the scopes up to the next task out, which cancels its own
     group, and so on until the exit is taken. *)
  let rec cancel returned tasks scopes =
    match (tasks, scopes) with
    | task :: outer, scopes :: outer_scopes ->
        let group = group_of b task origin in
        let resume = new_block b in
        let slot =
          Option.map (fun value -> new_local b Temporary (type_of_operand value) origin) returned
        in
        group.exits <- group.exits @ [ { resume; returned = slot } ];
        group.after <- resume :: group.after;
        terminate b
          (Cancel
             {
               task;
               task_end = Option.bind (List.assoc_opt task b.tasks) snd;
               winner = group.winner;
               number = List.length group.exits;
               returned =
                 (match (returned, slot) with
                 | Some value, Some slot -> Some (value, slot)
                 | _ -> None);
             })
          origin;
        start b resume;
        Hashtbl.replace b.resume_ends resume scopes;
        cancel
          (match (returned, slot) with
          | Some value, Some slot ->
              Some (Use { place = at slot; type_ = type_of_operand value; node = origin; origin })
          | _ -> None)
          outer outer_scopes
    | [], [] -> (
        match exit with
        | Exit_return _ -> terminate b (Return returned) origin
        | Exit_to target -> goto b target origin
        | Exit_iteration { loop } -> terminate b (Iteration_end { loop }) origin)
    | _ -> bug "an early exit whose tasks and scopes differ in number"
  in
  if b.current <> None then
    cancel
      (match exit with Exit_return value -> value | Exit_to _ | Exit_iteration _ -> None)
      tasks (around starts)

(* The group of tasks a task belongs to, made where an early exit first
   leaves it. *)
and group_of b (task : Core.task) origin =
  let key = group_key task in
  match Hashtbl.find_opt b.groups key with
  | Some group -> group
  | None ->
      let winner = new_local b Temporary (Types.builtin UInt32) origin in
      let group = { winner; exits = []; after = []; resumed = None } in
      Hashtbl.replace b.groups key group;
      group

(* The blocks of a region of the code with the origin [key], without those
   that run once its group's tasks, or those of a group around it, have
   ended. *)
and inside_group b key blocks =
  let after =
    List.concat_map
      (fun key -> match Hashtbl.find_opt b.groups key with Some group -> group.after | None -> [])
      (key :: List.map (fun (task, _) -> group_key task) b.tasks)
  in
  List.filter (fun block -> not (List.mem block after)) blocks

(* Where a group's tasks have ended: a block that takes the exit that won,
   where an early exit leaves the group, or else [next]. *)
and resumed b key ~next =
  match Hashtbl.find_opt b.groups key with
  | Some ({ exits = _ :: _; resumed = None; _ } as group) ->
      let block = new_block b in
      group.resumed <- Some block;
      group.after <- block :: group.after;
      block
  | Some { resumed = Some block; _ } -> block
  | Some { resumed = None; _ } | None -> next

(* Before a group's tasks start, no exit has won. The winner is a
   temporary of the statement around the group. *)
and start_group b key origin =
  match Hashtbl.find_opt b.groups key with
  | Some { resumed = Some _; winner; _ } ->
      add_temporary b winner;
      assign b (at winner)
        (Operand (Constant { value = Integer Z.zero; type_ = Types.builtin UInt32 }))
        origin
  | _ -> ()

(* Once a group's tasks have ended, the exit that won goes on, and without
   one, the code after the group. *)
and resume_group b key ~next origin =
  match Hashtbl.find_opt b.groups key with
  | Some { resumed = Some block; winner; exits; _ } ->
      start b block;
      terminate b (Resume { winner; exits; next }) origin
  | _ -> ()

(* A loop over an integer range: a counter from the start, tested at the
   header against the stop, and stepped at the end of each iteration. An
   inclusive range ends at its stop before stepping, so the counter never
   steps past the type's greatest value. A [Character] steps over the
   surrogates. *)
(* A [for] loop: the structured [For] terminator, with its body as a region
   that [each] lowers, given a function that binds the pattern to the
   element. The loop borrows what it iterates over for the body. *)
and for_loop ?cursor_type ?(lent = ref None) b ~origin ~(pattern : Core.pattern) ~iteration ~loop
    ~each =
  let part = new_local b Temporary pattern.type_ origin in
  let inside = new_block b and after = new_block b in
  let entry = b.current in
  let loop_block = match entry with Some block -> block | None -> new_block b in
  start b inside;
  let first = b.block_count in
  looping b ~break_:after ~continue_:(Next_iteration loop_block) (fun () ->
      each (fun () ->
          (match iteration with
          | Pull { cursor; _ } ->
              ignore
                (start_loan b
                   (Borrow
                      {
                        place = cursor;
                        type_ = Option.value ~default:pattern.type_ cursor_type;
                        mode = Read;
                        origin;
                      })
                   Read Loop_body origin)
          | Range _ -> ());
          match iteration with
          | Range _ -> bind ~owned:true b pattern (at part)
          | Pull _ -> bind b pattern (at part)));
  terminate b (Iteration_end { loop = loop_block }) origin;
  let blocks =
    inside_group b origin (inside :: List.init (b.block_count - first) (fun index -> first + index))
  in
  let ended = resumed b origin ~next:after in
  b.current <- entry;
  start_group b origin origin;
  terminate b
    (For { iteration; part; lent = !lent; body = inside; blocks; after = ended; loop })
    origin;
  resume_group b origin ~next:after origin;
  start b after

and range_loop b ~origin ~pattern ~start:low ~stop:high ~inclusive ~loop ~each =
  match (expression b low, expression b high) with
  | Some start, Some stop ->
      let start = held b start low.type_ origin and stop = held b stop high.type_ origin in
      for_loop b ~origin ~pattern ~iteration:(Range { start; stop; inclusive }) ~loop ~each
  | _ -> ()

(* A loop over the elements of a collection: a loop over the positions from
   zero up to the collection's count, each iteration of which is lent the
   element at its position, and binds the pattern to it. *)
and elements_loop b ~origin ~(pattern : Core.pattern) ~(elements : Core.elements) ~loop ~each =
  let { Core.count; position; element } = elements in
  match (expression b count, element) with
  | Some stop, Lent lending ->
      let stop = held b stop count.type_ origin in
      let start = Constant { value = Integer Z.zero; type_ = count.type_ } in
      let lent_part = ref None in
      for_loop ~lent:lent_part b ~origin ~pattern:position
        ~iteration:(Range { start; stop; inclusive = false })
        ~loop
        ~each:(fun bind_position ->
          each (fun () ->
              bind_position ();
              Option.iter
                (fun (part : place) ->
                  (match part.root with
                  | Local element -> lent_part := Some { element; count; call = lending }
                  | Constant _ -> ());
                  bind b pattern part)
                (lent b lending ~duration:Loop_body)))
  | Some _, _ -> bug "a loop over elements that no call lends"
  | None, _ -> ()

(* A loop that pulls a cursor until it has no next value. *)
and cursor_loop b ~origin ~pattern ~cursor ~next ~loop ~each =
  match place b cursor with
  | None -> ()
  | Some place_ ->
      let cursor_type = Core_walk.place_type cursor in
      let cursor = place_ in
      Option.iter
        (fun next ->
          for_loop ~cursor_type b ~origin ~pattern ~iteration:(Pull { cursor; next }) ~loop ~each)
        (callee_of b next)

(* A quantifier that runs: a loop that stops at the first element that
   decides it. *)
and quantifier_loop b (node : Core.expression) (quantifier : Syntax.quantifier) _pattern
    (body : Core.expression) run =
  let origin = node.origin in
  let result = temporary b Types.bool origin in
  let deciding = quantifier = Exists in
  assign b (at result)
    (Operand (Constant { value = Boolean (not deciding); type_ = Types.bool }))
    origin;
  let after = new_block b in
  run ~each:(fun bind_part ->
      in_scope b origin (fun () ->
          bind_part ();
          let decided = new_block b and undecided = new_block b in
          if deciding then condition b body ~yes:decided ~no:undecided
          else condition b body ~yes:undecided ~no:decided;
          start b decided;
          assign b (at result)
            (Operand (Constant { value = Boolean deciding; type_ = Types.bool }))
            origin;
          (match b.loops with
          | loop :: _ ->
              leave_scopes b ~depth:loop.depth origin;
              goto b loop.break_ origin
          | [] -> goto b after origin);
          start b undecided));
  goto b after origin;
  start b after;
  Some (Use { place = at result; type_ = Types.bool; node = node.id; origin })

(* Lambdas *)

and lambda b (parameters : Core.pattern list) (captures : Core.capture list) (body : Core.block) =
  let inner = create ~lambdas:b.lambdas in
  let capture_locals =
    List.map
      (fun (capture : Core.capture) ->
        let name =
          match Option.map (Hashtbl.find b.infos) (Hashtbl.find_opt b.sources capture.local) with
          | Some { kind = Source { name; _ }; _ } -> name
          | _ -> None
        in
        let local =
          new_local inner
            (Source { local = capture.local; mode = Read; name; is_var = false })
            capture.type_ 0
        in
        Hashtbl.replace inner.sources capture.local local;
        local)
      captures
  in
  let entry = new_block inner in
  start inner entry;
  let parameter_locals =
    in_scope inner 0 (fun () ->
        let locals =
          List.map
            (fun (pattern : Core.pattern) ->
              match pattern.kind with
              | Bind { local; mode; name; is_var } ->
                  bind_source ~name ~is_var inner local mode pattern.type_ pattern.origin
              | _ -> new_local inner Temporary pattern.type_ pattern.origin)
            parameters
        in
        List.iter2
          (fun (pattern : Core.pattern) local ->
            match pattern.kind with Bind _ -> () | _ -> bind inner pattern (at local))
          parameters locals;
        Option.iter (fun value -> return_ inner (Some value) 0) (block inner body);
        locals)
  in
  let body = finish inner ~parameters:parameter_locals ~captures:capture_locals in
  b.lambdas := body :: !(b.lambdas);
  List.length !(b.lambdas) - 1

and finish ?(captures = []) ?(defaults = []) b ~parameters : body =
  let blocks =
    Array.init b.block_count (fun index ->
        let pending = Hashtbl.find b.pending index in
        let terminator, terminator_origin =
          match pending.ending with Some ending -> ending | None -> (Unreachable, 0)
        in
        let ends =
          match Hashtbl.find_opt b.resume_ends index with
          | Some scopes ->
              List.concat_map
                (fun (scope, loans) -> scope_ends { scope with loans } terminator_origin)
                scopes
          | None -> []
        in
        {
          statements = ends @ List.rev pending.statements;
          terminator;
          terminator_origin;
          header = pending.heading;
          inlined = [];
        })
  in
  {
    parameters;
    defaults;
    captures;
    locals = Array.init b.local_count (Hashtbl.find b.infos);
    blocks = canonical blocks;
  }

(* The blocks control can reach from the entry, in reverse postorder. The
   end of each iteration names the innermost loop it ends, of those
   reached: a pass that moves or copies loops, as inlining does, leaves
   that to this. *)
and canonical (blocks : basic_block array) =
  let visited = Array.make (Array.length blocks) false and order = ref [] in
  let rec visit block =
    if not visited.(block) then begin
      visited.(block) <- true;
      List.iter visit (successors blocks.(block).terminator);
      order := block :: !order
    end
  in
  visit 0;
  let renumbered = Array.make (Array.length blocks) (-1) in
  List.iteri (fun index block -> renumbered.(block) <- index) !order;
  let target block = renumbered.(block) in
  let reached blocks =
    List.filter_map (fun block -> if visited.(block) then Some (target block) else None) blocks
  in
  let innermost = Hashtbl.create 4 in
  List.iter
    (fun loop ->
      match blocks.(loop).terminator with
      | For { blocks = inside; _ } ->
          let size = List.length inside in
          List.iter
            (fun block ->
              match Hashtbl.find_opt innermost block with
              | Some (_, known) when known <= size -> ()
              | _ -> Hashtbl.replace innermost block (loop, size))
            inside
      | _ -> ())
    !order;
  let loop_of block =
    match Hashtbl.find_opt innermost block with
    | Some (loop, _) -> target loop
    | None -> bug "the end of an iteration outside every loop"
  in
  let renumber at = function
    | Goto block -> Goto (target block)
    | Branch branch -> Branch { branch with yes = target branch.yes; no = target branch.no }
    | Switch_variant { place; cases } ->
        Switch_variant
          { place; cases = List.map (fun (variant, block) -> (variant, target block)) cases }
    | For loop ->
        For
          {
            loop with
            body = target loop.body;
            blocks = reached loop.blocks;
            after = target loop.after;
          }
    | Fork fork ->
        Fork
          {
            fork with
            branches =
              List.filter_map
                (fun branch ->
                  if visited.(branch.entry) then
                    Some { entry = target branch.entry; blocks = reached branch.blocks }
                  else None)
                fork.branches;
            join =
              Option.bind fork.join (fun join ->
                  if visited.(join) then Some (target join) else None);
          }
    | Join { fork; next } -> Join { fork; next = target next }
    | Yield yielded -> Yield { yielded with resume = target yielded.resume }
    | Cancel cancel ->
        Cancel
          {
            cancel with
            task_end =
              Option.bind cancel.task_end (fun task_end ->
                  if visited.(task_end) then Some (target task_end) else None);
          }
    | Resume { winner; exits; next } ->
        Resume
          {
            winner;
            exits = List.map (fun exit -> { exit with resume = target exit.resume }) exits;
            next = target next;
          }
    | Iteration_end _ -> Iteration_end { loop = loop_of at }
    | (Return _ | Unreachable | Written_unreachable | Todo) as other -> other
  in
  Array.of_list
    (List.map
       (fun block ->
         {
           (blocks.(block)) with
           terminator = renumber block blocks.(block).terminator;
           header =
             Option.map
               (fun (natural : natural_loop) ->
                 {
                   natural with
                   body = target natural.body;
                   after =
                     Option.bind natural.after (fun after ->
                         if visited.(after) then Some (target after) else None);
                 })
               blocks.(block).header;
         })
       !order)

and successors = function
  | Goto block -> [ block ]
  | Branch { yes; no; _ } -> [ yes; no ]
  | Switch_variant { cases; _ } -> List.map snd cases
  | For { body; after; _ } -> [ body; after ]
  | Fork { branches = first :: _; _ } -> [ first.entry ]
  | Fork { branches = []; _ } -> []
  | Join { next; _ } -> [ next ]
  | Yield { resume; _ } -> [ resume ]
  | Cancel { task_end; _ } -> Option.to_list task_end
  | Resume { exits; next; _ } -> List.map (fun exit -> exit.resume) exits @ [ next ]
  | Iteration_end _ | Return _ | Unreachable | Written_unreachable | Todo -> []

let iteration_loop = function Iteration_end { loop } -> Some loop | _ -> None

let block_successors (body : body) block =
  let terminator = body.blocks.(block).terminator in
  (match Option.map (fun loop -> body.blocks.(loop).terminator) (iteration_loop terminator) with
    | Some (For { body = first; after; _ }) -> [ first; after ]
    | _ -> [])
  @ successors terminator

let conditional_lends (body : body) =
  let ends_of part (statement : statement) =
    match statement.kind with Dead locals -> List.mem part locals | _ -> false
  in
  let ends_in part (block : basic_block) = List.exists (ends_of part) block.statements in
  let lends = ref [] in
  Array.iteri
    (fun index (block : basic_block) ->
      List.iteri
        (fun position (statement : statement) ->
          match statement.kind with
          | Lend { part; _ } -> lends := (part, index, position) :: !lends
          | _ -> ())
        block.statements)
    body.blocks;
  List.filter_map
    (fun (part, lending, position) ->
      let ended_before =
        List.exists (ends_of part)
          (List.filteri (fun at _ -> at < position) body.blocks.(lending).statements)
      in
      let visited = Array.make (Array.length body.blocks) false in
      let rec reaches block =
        block <> lending
        && (not visited.(block))
        && begin
          visited.(block) <- true;
          ends_in part body.blocks.(block)
          || List.exists reaches (successors body.blocks.(block).terminator)
        end
      in
      if ended_before || reaches 0 then Some part else None)
    !lends

let rec of_expression ?(parameters = []) (written : Core.expression) =
  let b = create ~lambdas:(ref []) in
  let parameters =
    List.map
      (fun (parameter : Core.parameter) ->
        bind_source ~name:parameter.name b parameter.local parameter.mode parameter.type_ 0)
      parameters
  in
  start b (new_block b);
  in_scope b written.origin (fun () ->
      in_statement b written.origin (fun () ->
          Option.iter (fun value -> return_ b (Some value) written.origin) (expression b written)));
  let body = finish b ~parameters in
  { body; lambdas = Array.of_list (List.rev !(b.lambdas)) }

and of_definition (definition : Core.definition) =
  let code =
    match definition with
    | Function { parameters; body = Some body; _ } -> Some (parameters, body, true)
    | Test body -> Some ([], body, false)
    | Law_proof { parameters; body } -> Some (parameters, body, false)
    | Function { body = None; _ } | Type _ | Trait _ | Constant _ | Empty -> None
  in
  Option.map
    (fun ((parameters : Core.parameter list), (body : Core.block), returns) ->
      let b = create ~lambdas:(ref []) in
      let locals =
        List.map
          (fun (parameter : Core.parameter) ->
            bind_source ~name:parameter.name b parameter.local parameter.mode parameter.type_ 0)
          parameters
      in
      let defaults =
        List.concat
          (List.map2
             (fun (parameter : Core.parameter) local ->
               match parameter.default with
               | Some default -> [ (local, of_expression default) ]
               | None -> [])
             parameters locals)
      in
      start b (new_block b);
      in_scope b 0 (fun () ->
          Option.iter
            (fun value -> return_ b (if returns then Some value else None) 0)
            (block b body));
      let finished = finish b ~parameters:locals ~defaults in
      { body = finished; lambdas = Array.of_list (List.rev !(b.lambdas)) })
    code

let mir =
  Query.query ~name:"mir" ~phase:Phases.bodies ~show:Resolve.Names.show_key (fun database key ->
      match
        ( Query.demand database Infer.core key,
          Query.demand database Interface.Environment.lowered_interface key )
      with
      | Some form, Some lowered -> (
          match lowered.interface with
          | (Function_interface signature | Theorem_interface signature)
            when signature.specification_only ->
              None
          | _ -> of_definition form.definition)
      | _ -> None)

let of_path =
  Query.query ~name:"mir_of_path" ~phase:Phases.bodies ~show:Path.show (fun database path ->
      Option.bind (Query.demand database Infer.form_origin path) (fun (origin, substitution) ->
          Option.map
            (fun mir -> (mir, substitution))
            (match origin with
            | Infer.Written key | Inherited key -> Query.demand database mir key
            | Generated ->
                Option.bind (Query.demand database Infer.derived path) (fun (form : Core.t) ->
                    of_definition form.definition))))

let of_constant =
  Query.query ~name:"mir_of_constant" ~phase:Phases.bodies ~show:Path.show (fun database path ->
      match Query.demand database Infer.core_of_path path with
      | Some ({ definition = Constant value; _ }, _) -> Some (of_expression value)
      | _ -> None)
