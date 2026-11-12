type local = int
type block = int

(** Whether a local is a source binding or a temporary. *)
type local_kind =
  | Source of { local : Core.local; mode : Types.mode }
      (** A parameter, [self], or a local that a pattern or a lambda binds. With [Read] or [Mut], it
          is the place it was bound to, not a copy of it. *)
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
  | Constant of constant

type callee =
  | Function of { path : Path.t; type_arguments : Types.argument list }
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      type_arguments : Types.argument list;
      evidence : Core.evidence;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
      (** An intrinsic that is not a primitive operation. Those are {!Operation}. *)
  | Indirect of operand

type argument =
  | Passed of { mode : Types.mode; value : operand; mark : Core.mark option }
  | Default  (** The callee fills in the parameter's default. *)

type call = {
  callee : callee;
  arguments : argument list;  (** One per parameter, in parameter order. *)
  uses : Types.capability_set;
  node : Core.id;  (** The core form's [Call]. *)
}

type rvalue =
  | Operand of operand
  | Operation of { operation : Intrinsic.operation; operands : operand list }
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
  | Lambda of { body : int; captures : Core.capture list }
      (** A function value made from a lambda. [body] indexes {!t.lambdas}. *)
  | Value_parameter of Types.parameter

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
  | Assign of { target : place; value : rvalue }
  | Call of { destination : place option; call : call }
  | Lend of { part : local; call : call }
      (** A call of a lending method. The [Lent] local [part] is the part it lends. *)
  | Slice of { destination : place; base : place; call : call }
      (** A call of [slice_range], whose result views [base]. *)
  | Template of { destination : place; literals : string list; call : call }
      (** A tagged string: the call of the tag's [from_template], with the literal texts. *)
  | Pull of { destination : place; cursor : place }
      (** The next value of the built-in cursor of a yielding method, an [Option]. *)
  | Live of local list  (** These locals start to hold values here. *)
  | Dead of local list  (** These locals hold nothing from here on. *)
  | Assert of operand  (** An [assert] that can run. *)
  | Echo of operand
  | Provide of provided list
  | Provide_end
  | Fork_start of { fork : int; concurrent : bool }
      (** The start of a branch of a [parallel] or [concurrent] block. *)
  | Fork_end of { fork : int }  (** The end of the block's last branch. *)
  | Loan_start of { loan : int; borrowed : operand; mode : Types.mode; duration : loan_duration }
      (** From here on, what [borrowed] borrows or views is lent with [mode]. *)
  | Loan_end of int list
  | Ghost_assert of Core.expression  (** An [assert] that cannot run. Only the prover reads it. *)
  | Proof of Core.block  (** Only the prover reads it. *)

type loop = {
  clauses : Core.loop_clause list;
  schedule : Core.loop_mode;
  counter : local option;
      (** The counter of a loop over an integer range, which is at least the range's start and at
          most its stop at the header. *)
  origin : Core.origin;
}
(** The clauses of a loop, which its header carries. *)

(** Where an early exit from [concurrent] code goes once its tasks end. *)
type task_exit = Exit_return of operand option | Exit_to of block

type terminator =
  | Goto of block
  | Branch of { condition : operand; yes : block; no : block }
  | Switch_variant of { place : place; cases : (string * block) list }
  | Each of { call : call; part : local; body : block; after : block; loop : loop }
      (** A [for] loop over a call of a yielding method. [body] runs for each part the callee
          yields, which [part] holds, and ends with {!Iteration_end} or a jump to [after]. *)
  | Iteration_end  (** The end of an iteration of the enclosing {!Each}. *)
  | Yield of { mode : Types.mode; part : operand; resume : block }
  | Return of operand option
  | Exit_tasks of { tasks : Core.task list; exit : task_exit }
      (** An early exit from [concurrent] code: these tasks end, then the exit is taken. *)
  | Unreachable  (** A point the prover shows is never reached. *)
  | Todo  (** A [todo] that is reached stops the program. *)

type basic_block = {
  statements : statement list;
  terminator : terminator;
  terminator_origin : Core.origin;
  header : loop option;  (** The clauses of the natural loop this block heads. *)
}

type body = {
  parameters : local list;
  locals : local_info array;
  blocks : basic_block array;  (** The entry is block 0. *)
}

type t = { body : body; lambdas : body array }

let bug format = Compiler_bug.bug ~stage:"MIR" format

(* The builder *)

type pending = {
  mutable statements : statement list;  (** In reverse. *)
  mutable ending : (terminator * Core.origin) option;
  mutable heading : loop option;
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
  provides : bool;
}

type target = Jump of block | Next_iteration
type enclosing_loop = { break_ : block; continue_ : target; depth : int }

type builder = {
  infos : (local, local_info) Hashtbl.t;
  mutable local_count : int;
  pending : (block, pending) Hashtbl.t;
  mutable block_count : int;
  mutable current : block option;
      (** The block being built, or [None] where control does not reach. *)
  sources : (Core.local, local) Hashtbl.t;
  mutable temporaries : local list;  (** Of the statement being built. *)
  mutable scopes : scope list;  (** Innermost first. *)
  mutable loops : enclosing_loop list;
  mutable compound_target : place option;
  mutable yield_mode : Types.mode;
  lambdas : body list ref;  (** In reverse, shared by the bodies of a definition. *)
  forks : int ref;
  mutable loan_count : int;
  mutable binds_into : frame;
      (** The frame new bindings belong to: a block's, or for [is], the statement around it. *)
}

let create ~lambdas ~forks =
  {
    infos = Hashtbl.create 16;
    local_count = 0;
    pending = Hashtbl.create 16;
    block_count = 0;
    current = None;
    sources = Hashtbl.create 16;
    temporaries = [];
    scopes = [];
    loops = [];
    compound_target = None;
    yield_mode = Read;
    lambdas;
    forks;
    loan_count = 0;
    binds_into = Bindings;
  }

let new_local b kind type_ origin =
  let local = b.local_count in
  Hashtbl.replace b.infos local { kind; type_; origin };
  b.local_count <- local + 1;
  local

let temporary b type_ origin =
  let local = new_local b Temporary type_ origin in
  b.temporaries <- local :: b.temporaries;
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
let assign b target value origin = emit b (Assign { target; value }) origin

(* A new temporary that holds a value, or [None] where control does not
   reach. *)
let hold b type_ origin value =
  match b.current with
  | None -> None
  | Some _ ->
      let local = temporary b type_ origin in
      assign b (at local) value origin;
      Some (Use { place = at local; type_; node = origin; origin })

let source b (local : Core.local) =
  match Hashtbl.find_opt b.sources local with
  | Some found -> found
  | None -> bug "a local that nothing binds"

(* The local a core local is bound to. Each alternative of a pattern binds
   the same locals, and a loop binds its pattern again on each iteration, so
   a core local has one local wherever it is bound. *)
let bind_source b (local : Core.local) mode type_ origin =
  match Hashtbl.find_opt b.sources local with
  | Some found -> found
  | None ->
      let found = new_local b (Source { local; mode }) type_ origin in
      Hashtbl.replace b.sources local found;
      (match List.find_opt (fun scope -> scope.frame = b.binds_into) b.scopes with
      | Some scope -> scope.bound <- found :: scope.bound
      | None -> ());
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

(* What leaving a scope ends. *)
let end_scope b scope origin =
  if scope.loans <> [] then emit b (Loan_end (List.rev scope.loans)) origin;
  if scope.bound <> [] then emit b (Dead (List.rev scope.bound)) origin;
  if scope.provides then emit b Provide_end origin

(* Runs [f] in a new scope, and ends the scope's bindings where control
   leaves it normally. *)
let in_scope ?(provides = false) b origin f =
  let scope = { frame = Bindings; bound = []; loans = []; provides } in
  b.scopes <- scope :: b.scopes;
  let result = f () in
  b.scopes <- List.tl b.scopes;
  end_scope b scope origin;
  result

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
  let outer = b.temporaries in
  b.temporaries <- [];
  let scope = { frame = Statement; bound = []; loans = []; provides = false } in
  b.scopes <- scope :: b.scopes;
  let result = f () in
  b.scopes <- List.tl b.scopes;
  end_scope b scope origin;
  if b.temporaries <> [] then emit b (Dead (List.rev b.temporaries)) origin;
  b.temporaries <- outer;
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

(* Expressions *)

let rec expression b (node : Core.expression) : operand option =
  let origin = node.origin in
  let hold value = hold b node.type_ origin value in
  match b.current with
  | None -> None
  | Some _ -> (
      match node.kind with
      | Integer value -> Some (Constant (Integer value))
      | Float value -> Some (Constant (Float value))
      | Boolean value -> Some (Constant (Boolean value))
      | String value -> Some (Constant (String value))
      | Template { literals; call = { kind = Call called; _ } } ->
          let* call = call_of b called ~node:node.id in
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
          hold (Lambda { body = index; captures })
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
          let* call = call_of b called ~node:node.id in
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
          hold (Operation { operation; operands })
      | Compare { comparison; left; right } -> (
          let* compared = operands b [ left; right ] in
          match compared with
          | [ left; right ] -> hold (Compare { comparison; left; right })
          | _ -> bug "a comparison without two operands")
      | Not inner ->
          let* inner = expression b inner in
          hold (Not inner)
      | And _ | Or _ | Matches _ -> truth b node
      | Cursor_next cursor ->
          let* cursor = place b cursor in
          let local = temporary b node.type_ origin in
          emit b (Pull { destination = at local; cursor }) origin;
          Some (Use { place = at local; type_ = node.type_; node = node.id; origin = node.origin })
      | Convert { conversion; value } ->
          let* value = expression b value in
          hold (Convert { conversion; value })
      | To_any { value; trait; evidence } ->
          let* value = expression b value in
          hold (To_any { value; trait; evidence })
      | If { condition = tested; then_; else_ } ->
          let result = value_local b node in
          let yes = new_block b and no = new_block b and joined = new_block b in
          scoped_condition ~keeps_lent:true b tested ~yes ~no;
          start b yes;
          branch_into b result then_ joined origin;
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
          emit b (Provide provided) origin;
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
      | Return None ->
          terminate b (Return None) origin;
          None
      | Return (Some returned) ->
          Option.iter
            (fun value -> terminate b (Return (Some value)) origin)
            (expression b returned);
          None
      | Break -> (
          match b.loops with
          | loop :: _ ->
              leave_scopes b ~depth:loop.depth origin;
              goto b loop.break_ origin;
              None
          | [] -> bug "a `break` outside a loop")
      | Continue -> (
          match b.loops with
          | loop :: _ ->
              leave_scopes b ~depth:loop.depth origin;
              (match loop.continue_ with
              | Jump block -> goto b block origin
              | Next_iteration -> terminate b Iteration_end origin);
              None
          | [] -> bug "a `continue` outside a loop")
      | Task_exit { tasks; exit } ->
          let task_exit =
            match exit.kind with
            | Return returned -> (
                match returned with
                | Some returned ->
                    Option.map (fun value -> Exit_return (Some value)) (expression b returned)
                | None -> Some (Exit_return None))
            | Break -> (
                match b.loops with
                | loop :: _ -> Some (Exit_to loop.break_)
                | [] -> bug "a `break` outside a loop")
            | Continue -> (
                match b.loops with
                | { continue_ = Jump block; _ } :: _ -> Some (Exit_to block)
                | _ -> bug "a task's `continue` of a loop that does not continue by a jump")
            | _ -> bug "a task's exit that is not a `return`, `break`, or `continue`"
          in
          Option.iter (fun exit -> terminate b (Exit_tasks { tasks; exit }) origin) task_exit;
          None
      | Todo ->
          terminate b Todo origin;
          None
      | Unreachable ->
          terminate b Unreachable origin;
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
              range_loop b ~origin ~pattern ~start ~stop ~inclusive ~loop:(no_clauses origin) ~each)
      | Quantified
          {
            quantifier;
            binder = Over_each { pattern; call = { kind = Call called; _ } as call };
            body;
          } ->
          quantifier_loop b node quantifier pattern body (fun ~each ->
              each_loop b ~origin ~pattern ~called ~node:call.id ~loop:(no_clauses origin) ~each)
      | Collection_literal { construction = Specification_only; _ }
      | Map_literal _ | Implies _ | Result | Old _ | Quantified _ | Yielded | Finished | Identical _
      | Specification_function _ | Method_time _ ->
          bug "a specification's expression in code that runs")

and no_clauses origin = { clauses = []; schedule = Sequential; counter = None; origin }

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
      b.temporaries <- local :: b.temporaries;
      assign b (at local) (Operand value) origin;
      Borrow { place = at local; type_; mode; origin }

(* The fields of a constructor, in evaluation order. A field that is a place
   lends it to the value, with the enclosing [yield]'s mode. *)
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
               | Place written ->
                   let* lent = place b written in
                   Some
                     (Borrow
                        {
                          place = lent;
                          type_ = Core_walk.place_type written;
                          mode = b.yield_mode;
                          origin = Core_walk.place_origin written;
                        })
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
      | Lent ({ kind = Call called; _ } as lending) -> (
          let* call = call_of b called ~node:lending.id in
          match called.lends with
          | Some mode ->
              let part = new_local b (Lent mode) lending.type_ lending.origin in
              b.temporaries <- part :: b.temporaries;
              emit b (Lend { part; call }) lending.origin;
              (match call.arguments with
              | Passed { mode; value = Borrow _ as receiver; _ } :: _ ->
                  ignore
                    (start_loan b receiver
                       (if mode = Mut then Mut else Read)
                       Rest_of_statement lending.origin)
              | _ -> ());
              Some (at part)
          | None -> bug "a lent place whose call does not lend")
      | Lent _ -> bug "a lent place that is not a call"
      | Temporary written ->
          let* value = expression b written in
          let local = temporary b written.type_ written.origin in
          assign b (at local) (Operand value) written.origin;
          Some (at local))

and callee_of b (callee : Core.callee) : callee option =
  match callee with
  | Function { path; type_arguments } -> Some (Function { path; type_arguments })
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } ->
      Some (Trait_method { trait; name; receiver; self_type; type_arguments; evidence })
  | Capability_method { capability; name } -> Some (Capability_method { capability; name })
  | Intrinsic { operation; type_arguments } -> Some (Intrinsic { operation; type_arguments })
  | Indirect value ->
      let* value = operand b Read value in
      Some (Indirect value)

(* A call: its callee, then its arguments in order. *)
and call_of b (called : Core.call) ~node : call option =
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
  Some { callee; arguments; uses = called.uses; node }

and call_value b (node : Core.expression) (called : Core.call) =
  let origin = node.origin in
  match called.callee with
  | Intrinsic { operation; _ } when Intrinsic.primitive operation ->
      let* operands =
        in_order b
          (List.map
             (function
               | Core.Passed { value; mode; _ } ->
                   ((fun () -> operand b mode value), operand_type value, operand_origin value)
               | Default -> bug "a primitive operation with a default argument")
             called.arguments)
      in
      hold b node.type_ origin (Operation { operation; operands })
  | _ ->
      let* call = call_of b called ~node:node.id in
      if diverges node.type_ then begin
        emit b (Call { destination = None; call }) origin;
        terminate b Unreachable origin;
        None
      end
      else if is_unit node.type_ then begin
        emit b (Call { destination = None; call }) origin;
        Some (Constant Unit)
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
  assign b (at local) (Operand (Constant (Boolean true))) node.origin;
  goto b joined node.origin;
  start b no;
  assign b (at local) (Operand (Constant (Boolean false))) node.origin;
  goto b joined node.origin;
  start b joined;
  Some (Use { place = at local; type_ = node.type_; node = node.id; origin = node.origin })

(* Jumps to [yes] where a condition holds, and to [no] where it does not. A
   short-circuit operator evaluates its right operand only from the side of
   its left operand that does not decide it. *)
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
      | Some value -> terminate b (Branch { condition = value; yes; no }) node.origin
      | None -> ())

(* A condition whose temporaries end before either way out. *)
and scoped_condition ?(keeps_lent = false) b (node : Core.expression) ~yes ~no =
  let outer = b.temporaries in
  b.temporaries <- [];
  let scope = { frame = Condition; bound = []; loans = []; provides = false } in
  b.scopes <- scope :: b.scopes;
  let yes' = new_block b and no' = new_block b in
  condition b node ~yes:yes' ~no:no';
  b.scopes <- List.tl b.scopes;
  let made = List.rev b.temporaries in
  b.temporaries <- outer;
  (* The condition of an [if] or a guard lends for the rest of its statement,
     so that what [is] binds of a lent part can be used in the branch. A
     [while] condition's loans end before the body. *)
  let made =
    if keeps_lent then begin
      let lent, others =
        List.partition
          (fun local -> match (Hashtbl.find b.infos local).kind with Lent _ -> true | _ -> false)
          made
      in
      b.temporaries <- List.rev lent @ b.temporaries;
      (match b.scopes with
      | enclosing :: _ ->
          enclosing.loans <- scope.loans @ enclosing.loans;
          scope.loans <- []
      | [] -> ());
      others
    end
    else made
  in
  List.iter
    (fun (entry, target) ->
      start b entry;
      if scope.loans <> [] then emit b (Loan_end (List.rev scope.loans)) node.origin;
      if made <> [] then emit b (Dead made) node.origin;
      goto b target node.origin)
    [ (yes', yes); (no', no) ]

(* The local an [if] or a [match] writes its value to, if it has one. *)
and value_local b (node : Core.expression) =
  if is_unit node.type_ || diverges node.type_ then None
  else Some (temporary b node.type_ node.origin)

and result_of b (node : Core.expression) result =
  match (b.current, result) with
  | None, _ -> None
  | Some _, Some local ->
      Some (Use { place = at local; type_ = node.type_; node = node.id; origin = node.origin })
  | Some _, None -> if diverges node.type_ then None else Some (Constant Unit)

(* A branch of an [if] or a [match]: its block, its value written to
   [result], then a jump to [joined]. *)
and branch_into b result (body : Core.block) joined origin =
  in_scope b origin (fun () ->
      match (block b body, result) with
      | Some value, Some local -> assign b (at local) (Operand value) origin
      | _ -> ());
  goto b joined origin

(* A block in a scope of its own: its value is held past the end of its
   bindings, for the enclosing statement. *)
and scoped_block ?provides ?(loans = ignore) b (body : Core.block) origin =
  in_scope ?provides b origin (fun () ->
      loans ();
      let value = block b body in
      let bound_here local =
        match b.scopes with scope :: _ -> List.mem local scope.bound | [] -> false
      in
      match (value, body.value) with
      | Some (Use { place = { root = Local local; _ }; _ } as read), Some written
        when bound_here local ->
          hold b written.type_ origin (Operand read)
      | _ -> value)

and block b (body : Core.block) : operand option =
  List.iter (statement b) body.statements;
  match body.value with
  | Some value -> expression b value
  | None -> ( match b.current with Some _ -> Some (Constant Unit) | None -> None)

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
    | Some condition -> terminate b (Branch { condition; yes = passed; no = fail }) origin
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
  | Bind { local; mode; _ } ->
      let found = bind_source b local (if owned then Own else mode) pattern.type_ pattern.origin in
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
          let next = new_block b and body = new_block b in
          in_scope b current.origin (fun () ->
              match_patterns b current.patterns places ~fail:next ~matched:body current.origin;
              start b body;
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
                  scoped_condition ~keeps_lent:true b guard ~yes:passed ~no:rejected;
                  start b rejected;
                  end_loans b loans current.origin;
                  (match b.scopes with
                  | scope :: _ when scope.bound <> [] ->
                      emit b (Dead (List.rev scope.bound)) current.origin
                  | _ -> ());
                  goto b next current.origin;
                  start b passed;
                  end_loans b loans current.origin;
                  arm current);
          goto b joined current.origin;
          start b next)
        arms;
      terminate b Unreachable origin

(* Statements *)

and statement b (node : Core.statement) =
  let origin = node.origin in
  in_statement b origin (fun () ->
      match node.kind with
      | Let { pattern; value; else_ } -> (
          match scrutinee b value with
          | None -> ()
          | Some found ->
              let failed = new_block b and matched = new_block b in
              match_patterns b [ pattern ] [ found ] ~fail:failed ~matched origin;
              start b failed;
              (match else_ with
              | Some else_ -> ignore (in_scope b origin (fun () -> block b else_))
              | None -> ());
              terminate b Unreachable origin;
              start b matched)
      | Evaluate value -> ignore (expression b value)
      | Assign { target; value = written } -> (
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
                new_local b (Source { local = bound; mode }) (operand_type right) origin
              in
              Hashtbl.replace b.sources bound local;
              b.temporaries <- local :: b.temporaries;
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
          let loop = { clauses; schedule = mode; counter = None; origin } in
          let each ~bind_part =
            in_scope b origin (fun () ->
                bind_part ();
                ignore (block b body))
          in
          match iteration with
          | Integer_range { start; stop; inclusive } ->
              range_loop b ~origin ~pattern ~start ~stop ~inclusive ~loop ~each:(fun bind_part ->
                  each ~bind_part)
          | Yielding_call ({ kind = Call called; _ } as call) ->
              each_loop b ~origin ~pattern ~called ~node:call.id ~loop ~each:(fun bind_part ->
                  each ~bind_part)
          | Yielding_call _ -> bug "a loop over an expression that is not a call"
          | Cursor { cursor; next } ->
              cursor_loop b ~origin ~pattern ~cursor ~next ~loop ~each:(fun bind_part ->
                  each ~bind_part))
      | While { condition = tested; clauses; body } ->
          let header = new_block b and inside = new_block b and after = new_block b in
          goto b header origin;
          (Hashtbl.find b.pending header).heading <-
            Some { clauses; schedule = Sequential; counter = None; origin };
          start b header;
          scoped_condition b tested ~yes:inside ~no:after;
          start b inside;
          looping b ~break_:after ~continue_:(Jump header) (fun () ->
              ignore (in_scope b origin (fun () -> block b body)));
          goto b header origin;
          start b after
      | Parallel branches | Concurrent branches ->
          let concurrent = match node.kind with Concurrent _ -> true | _ -> false in
          let fork = !(b.forks) in
          incr b.forks;
          List.iter
            (fun (branch : Core.statement) ->
              emit b (Fork_start { fork; concurrent }) branch.origin;
              statement b branch)
            branches;
          emit b (Fork_end { fork }) origin
      | Proof proof -> emit b (Proof proof) origin
      | Assert { value; executable = true } -> (
          match expression b value with Some value -> emit b (Assert value) origin | None -> ())
      | Assert { value; executable = false } -> emit b (Ghost_assert value) origin
      | Yield { mode; part } -> (
          let enclosing = b.yield_mode in
          b.yield_mode <- mode;
          let part = operand b mode part in
          b.yield_mode <- enclosing;
          match part with
          | Some part ->
              let resume = new_block b in
              terminate b (Yield { mode; part; resume }) origin;
              start b resume
          | None -> ()))

and looping b ~break_ ~continue_ f =
  b.loops <- { break_; continue_; depth = List.length b.scopes } :: b.loops;
  f ();
  b.loops <- List.tl b.loops

(* A loop over an integer range: a counter from the start, tested at the
   header against the stop, and stepped at the end of each iteration. An
   inclusive range ends at its stop before stepping, so the counter never
   steps past the type's greatest value. A [Character] steps over the
   surrogates. *)
and range_loop b ~origin ~pattern ~start:low ~stop:high ~inclusive ~loop ~each =
  match (expression b low, expression b high) with
  | Some low_value, Some high_value ->
      let counter = new_local b Temporary low.type_ origin in
      b.temporaries <- counter :: b.temporaries;
      assign b (at counter) (Operand low_value) origin;
      let stop = temporary b high.type_ origin in
      assign b (at stop) (Operand high_value) origin;
      let read local = Use { place = at local; type_ = low.type_; node = origin; origin } in
      let header = new_block b
      and inside = new_block b
      and step = new_block b
      and after = new_block b in
      goto b header origin;
      (Hashtbl.find b.pending header).heading <- Some { loop with counter = Some counter };
      start b header;
      let more =
        hold b Types.bool origin
          (Compare
             {
               comparison = (if inclusive then Less_equal else Less);
               left = read counter;
               right = read stop;
             })
      in
      Option.iter
        (fun condition -> terminate b (Branch { condition; yes = inside; no = after }) origin)
        more;
      start b inside;
      looping b ~break_:after ~continue_:(Jump step) (fun () ->
          each (fun () -> bind ~owned:true b pattern (at counter)));
      goto b step origin;
      start b step;
      if inclusive then (
        let last =
          hold b Types.bool origin
            (Compare { comparison = Equal; left = read counter; right = read stop })
        in
        let next = new_block b in
        Option.iter
          (fun condition -> terminate b (Branch { condition; yes = after; no = next }) origin)
          last;
        start b next);
      let one = Constant (Integer Z.one) in
      assign b (at counter) (Operation { operation = Add; operands = [ read counter; one ] }) origin;
      if Types.is_builtin Character low.type_ then (
        let surrogate =
          hold b Types.bool origin
            (Compare
               {
                 comparison = Equal;
                 left = read counter;
                 right = Constant (Integer (Z.of_int 0xD800));
               })
        in
        let skip = new_block b and stepped = new_block b in
        Option.iter
          (fun condition -> terminate b (Branch { condition; yes = skip; no = stepped }) origin)
          surrogate;
        start b skip;
        assign b (at counter) (Operand (Constant (Integer (Z.of_int 0xE000)))) origin;
        goto b stepped origin;
        start b stepped);
      goto b header origin;
      start b after
  | _ -> ()

(* A loop over a call of a yielding method. *)
and each_loop b ~origin ~pattern ~called ~node ~loop ~each =
  match call_of b called ~node with
  | None -> ()
  | Some call ->
      let part = new_local b Temporary pattern.Core.type_ origin in
      let inside = new_block b and after = new_block b in
      terminate b (Each { call; part; body = inside; after; loop }) origin;
      start b inside;
      looping b ~break_:after ~continue_:Next_iteration (fun () ->
          each (fun () ->
              (match call.arguments with
              | Passed { mode; value = Borrow _ as receiver; _ } :: _ ->
                  ignore (start_loan b receiver (if mode = Mut then Mut else Read) Loop_body origin)
              | _ -> ());
              bind b pattern (at part)));
      terminate b Iteration_end origin;
      start b after

(* A loop that pulls a cursor until it has no next value. *)
and cursor_loop b ~origin ~pattern ~cursor ~next ~loop ~each =
  match place b cursor with
  | None -> ()
  | Some cursor_place ->
      let option_type = Types.named (Well_known.path Option) [ pattern.Core.type_ ] in
      let pulled = new_local b Temporary option_type origin in
      let header = new_block b and some = new_block b and after = new_block b in
      goto b header origin;
      (Hashtbl.find b.pending header).heading <- Some loop;
      start b header;
      (match next with
      | None -> emit b (Pull { destination = at pulled; cursor = cursor_place }) origin
      | Some next -> (
          match callee_of b next with
          | Some callee ->
              emit b
                (Call
                   {
                     destination = Some (at pulled);
                     call =
                       {
                         callee;
                         arguments =
                           [
                             Passed
                               {
                                 mode = Mut;
                                 value =
                                   Borrow
                                     {
                                       place = cursor_place;
                                       type_ = Core_walk.place_type cursor;
                                       mode = Mut;
                                       origin;
                                     };
                                 mark = None;
                               };
                           ];
                         uses = Types.no_capabilities;
                         node = origin;
                       };
                   })
                origin
          | None -> ()));
      terminate b
        (Switch_variant { place = at pulled; cases = [ ("Some", some); ("None", after) ] })
        origin;
      start b some;
      looping b ~break_:after ~continue_:(Jump header) (fun () ->
          each (fun () ->
              ignore
                (start_loan b
                   (Borrow
                      {
                        place = cursor_place;
                        type_ = Core_walk.place_type cursor;
                        mode = Read;
                        origin;
                      })
                   Read Loop_body origin);
              bind b pattern
                (project (at pulled) (Variant_field { variant = "Some"; field = "value" }))));
      goto b header origin;
      start b after

(* A quantifier that runs: a loop that stops at the first element that
   decides it. *)
and quantifier_loop b (node : Core.expression) (quantifier : Syntax.quantifier) _pattern
    (body : Core.expression) run =
  let origin = node.origin in
  let result = temporary b Types.bool origin in
  let deciding = quantifier = Exists in
  assign b (at result) (Operand (Constant (Boolean (not deciding)))) origin;
  let after = new_block b in
  run ~each:(fun bind_part ->
      in_scope b origin (fun () ->
          bind_part ();
          let decided = new_block b and undecided = new_block b in
          if deciding then condition b body ~yes:decided ~no:undecided
          else condition b body ~yes:undecided ~no:decided;
          start b decided;
          assign b (at result) (Operand (Constant (Boolean deciding))) origin;
          (match b.loops with loop :: _ -> goto b loop.break_ origin | [] -> goto b after origin);
          start b undecided));
  goto b after origin;
  start b after;
  Some (Use { place = at result; type_ = Types.bool; node = node.id; origin })

(* Lambdas *)

and lambda b (parameters : Core.pattern list) (captures : Core.capture list) (body : Core.block) =
  let inner = create ~lambdas:b.lambdas ~forks:b.forks in
  List.iter
    (fun (capture : Core.capture) ->
      Hashtbl.replace inner.sources capture.local
        (new_local inner (Source { local = capture.local; mode = Read }) capture.type_ 0))
    captures;
  let entry = new_block inner in
  start inner entry;
  let parameter_locals =
    in_scope inner 0 (fun () ->
        let locals =
          List.map
            (fun (pattern : Core.pattern) ->
              match pattern.kind with
              | Bind { local; mode; _ } -> bind_source inner local mode pattern.type_ pattern.origin
              | _ -> new_local inner Temporary pattern.type_ pattern.origin)
            parameters
        in
        List.iter2
          (fun (pattern : Core.pattern) local ->
            match pattern.kind with Bind _ -> () | _ -> bind inner pattern (at local))
          parameters locals;
        Option.iter (fun value -> terminate inner (Return (Some value)) 0) (block inner body);
        locals)
  in
  let body = finish inner ~parameters:parameter_locals in
  b.lambdas := body :: !(b.lambdas);
  List.length !(b.lambdas) - 1

and finish b ~parameters : body =
  let blocks =
    Array.init b.block_count (fun index ->
        let pending = Hashtbl.find b.pending index in
        let terminator, terminator_origin =
          match pending.ending with Some ending -> ending | None -> (Unreachable, 0)
        in
        {
          statements = List.rev pending.statements;
          terminator;
          terminator_origin;
          header = pending.heading;
        })
  in
  {
    parameters;
    locals = Array.init b.local_count (Hashtbl.find b.infos);
    blocks = canonical blocks;
  }

(* The blocks control can reach from the entry, in reverse postorder. *)
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
  let renumber = function
    | Goto block -> Goto (target block)
    | Branch { condition; yes; no } -> Branch { condition; yes = target yes; no = target no }
    | Switch_variant { place; cases } ->
        Switch_variant
          { place; cases = List.map (fun (variant, block) -> (variant, target block)) cases }
    | Each each -> Each { each with body = target each.body; after = target each.after }
    | Yield yielded -> Yield { yielded with resume = target yielded.resume }
    | Exit_tasks { tasks; exit = Exit_to block } ->
        Exit_tasks { tasks; exit = Exit_to (target block) }
    | (Iteration_end | Return _ | Exit_tasks _ | Unreachable | Todo) as other -> other
  in
  Array.of_list
    (List.map
       (fun block -> { (blocks.(block)) with terminator = renumber blocks.(block).terminator })
       !order)

and successors = function
  | Goto block -> [ block ]
  | Branch { yes; no; _ } -> [ yes; no ]
  | Switch_variant { cases; _ } -> List.map snd cases
  | Each { body; after; _ } -> [ body; after ]
  | Yield { resume; _ } -> [ resume ]
  | Exit_tasks { exit = Exit_to block; _ } -> [ block ]
  | Iteration_end | Return _ | Exit_tasks _ | Unreachable | Todo -> []

let of_definition (definition : Core.definition) =
  let code =
    match definition with
    | Function { parameters; body = Some body; _ } -> Some (parameters, body, true)
    | Test body -> Some ([], body, false)
    | Law_proof { parameters; body } -> Some (parameters, body, false)
    | Function { body = None; _ } | Type _ | Trait _ | Constant _ | Empty -> None
  in
  Option.map
    (fun ((parameters : Core.parameter list), (body : Core.block), returns) ->
      let b = create ~lambdas:(ref []) ~forks:(ref 0) in
      let parameters =
        List.map
          (fun (parameter : Core.parameter) ->
            bind_source b parameter.local parameter.mode parameter.type_ 0)
          parameters
      in
      start b (new_block b);
      in_scope b 0 (fun () ->
          Option.iter
            (fun value -> terminate b (Return (if returns then Some value else None)) 0)
            (block b body));
      let body = finish b ~parameters in
      { body; lambdas = Array.of_list (List.rev !(b.lambdas)) })
    code

(* Text *)

let show_place (place : place) =
  let root =
    match place.root with
    | Local local -> Printf.sprintf "_%d" local
    | Constant path -> Path.show path
  in
  root
  ^ String.concat ""
      (List.map
         (function
           | Field field -> "." ^ field
           | Variant_field { variant; field } -> Printf.sprintf ".(%s).%s" variant field)
         place.projections)

let show_mode : Types.mode -> string = function Own -> "own" | Read -> "read" | Mut -> "mut"

let show_operand = function
  | Use { place; _ } -> show_place place
  | Take { place; _ } -> "take " ^ show_place place
  | Borrow { place; mode; _ } -> Printf.sprintf "%s %s" (show_mode mode) (show_place place)
  | Constant Unit -> "()"
  | Constant (Integer value) -> Z.to_string value
  | Constant (Float value) -> Printf.sprintf "%h" value
  | Constant (Boolean value) -> string_of_bool value
  | Constant (String value) -> Printf.sprintf "%S" value

let show_operands operands = String.concat ", " (List.map show_operand operands)

let show_callee = function
  | Function { path; _ } -> Path.show path
  | Trait_method { trait; name; _ } -> Printf.sprintf "%s.%s" (Path.show trait.trait) name
  | Capability_method { capability; name } -> Printf.sprintf "%s.%s" (Path.show capability) name
  | Intrinsic { operation; _ } -> "intrinsic::" ^ Intrinsic.operation_name operation
  | Indirect value -> show_operand value

let show_call (call : call) =
  Printf.sprintf "%s(%s)" (show_callee call.callee)
    (String.concat ", "
       (List.map
          (function Passed { value; _ } -> show_operand value | Default -> "default")
          call.arguments))

let show_comparison : Core.comparison -> string = function
  | Equal -> "=="
  | Not_equal -> "!="
  | Less -> "<"
  | Less_equal -> "<="
  | Greater -> ">"
  | Greater_equal -> ">="

let show_rvalue = function
  | Operand value -> show_operand value
  | Operation { operation; operands } ->
      Printf.sprintf "%s(%s)" (Intrinsic.operation_name operation) (show_operands operands)
  | Compare { comparison; left; right } ->
      Printf.sprintf "%s %s %s" (show_operand left) (show_comparison comparison)
        (show_operand right)
  | Not value -> "!" ^ show_operand value
  | Construct { variant; fields } ->
      Printf.sprintf "%s(%s)"
        (match variant with Some variant -> variant | None -> "record")
        (String.concat ", "
           (List.map
              (fun (name, field) ->
                Printf.sprintf "%s: %s" name
                  (match field with Some field -> show_operand field | None -> "default"))
              fields))
  | Array elements -> Printf.sprintf "[%s]" (show_operands elements)
  | Is_variant { place; variant } -> Printf.sprintf "%s is %s" (show_place place) variant
  | Convert { value; _ } -> Printf.sprintf "convert(%s)" (show_operand value)
  | To_any { value; trait; _ } ->
      Printf.sprintf "any %s(%s)" (Path.show trait.trait) (show_operand value)
  | Copy value -> Printf.sprintf "copy(%s)" (show_operand value)
  | Function_value { path; _ } -> Path.show path
  | Lambda { body; _ } -> Printf.sprintf "lambda %d" body
  | Value_parameter parameter -> parameter.name

let show_locals locals = String.concat ", " (List.map (Printf.sprintf "_%d") locals)

let show_statement (statement : statement) =
  match statement.kind with
  | Assign { target; value } -> Printf.sprintf "%s = %s" (show_place target) (show_rvalue value)
  | Call { destination = Some destination; call } ->
      Printf.sprintf "%s = %s" (show_place destination) (show_call call)
  | Call { destination = None; call } -> show_call call
  | Lend { part; call } -> Printf.sprintf "_%d = lend %s" part (show_call call)
  | Slice { destination; call; _ } ->
      Printf.sprintf "%s = slice %s" (show_place destination) (show_call call)
  | Template { destination; call; _ } ->
      Printf.sprintf "%s = template %s" (show_place destination) (show_call call)
  | Pull { destination; cursor } ->
      Printf.sprintf "%s = pull %s" (show_place destination) (show_place cursor)
  | Live locals -> Printf.sprintf "live %s" (show_locals locals)
  | Dead locals -> Printf.sprintf "dead %s" (show_locals locals)
  | Assert value -> "assert " ^ show_operand value
  | Echo value -> "echo " ^ show_operand value
  | Provide provided ->
      Printf.sprintf "provide %s"
        (show_operands (List.map (fun (p : provided) -> p.value) provided))
  | Provide_end -> "provide end"
  | Fork_start { fork; concurrent } ->
      Printf.sprintf "%s branch of #%d" (if concurrent then "concurrent" else "parallel") fork
  | Fork_end { fork } -> Printf.sprintf "end of #%d" fork
  | Loan_start { loan; borrowed; mode; duration } ->
      Printf.sprintf "loan %d: %s %s for %s" loan (show_mode mode) (show_operand borrowed)
        (match duration with
        | Loop_body -> "the loop"
        | Provide_body -> "the provide"
        | Rest_of_statement -> "the statement"
        | Operand_evaluation -> "the operation")
  | Loan_end loans -> "end loans " ^ String.concat ", " (List.map string_of_int loans)
  | Ghost_assert _ -> "ghost assert"
  | Proof _ -> "proof"

let show_terminator = function
  | Goto block -> Printf.sprintf "goto %d" block
  | Branch { condition; yes; no } ->
      Printf.sprintf "branch %s %d %d" (show_operand condition) yes no
  | Switch_variant { place; cases } ->
      Printf.sprintf "switch %s %s" (show_place place)
        (String.concat " "
           (List.map (fun (variant, block) -> Printf.sprintf "%s: %d" variant block) cases))
  | Each { call; part; body; after; _ } ->
      Printf.sprintf "each _%d in %s %d after %d" part (show_call call) body after
  | Iteration_end -> "next"
  | Yield { mode; part; resume } ->
      Printf.sprintf "yield %s %s %d" (show_mode mode) (show_operand part) resume
  | Return None -> "return"
  | Return (Some value) -> "return " ^ show_operand value
  | Exit_tasks { exit = Exit_return value; _ } -> (
      "exit tasks, return" ^ match value with Some value -> " " ^ show_operand value | None -> "")
  | Exit_tasks { exit = Exit_to block; _ } -> Printf.sprintf "exit tasks, goto %d" block
  | Unreachable -> "unreachable"
  | Todo -> "todo"

let show_body (body : body) =
  String.concat "\n"
    (List.concat
       (List.mapi
          (fun index (block : basic_block) ->
            Printf.sprintf "%d:%s" index (match block.header with Some _ -> " loop" | None -> "")
            :: List.map (fun statement -> "  " ^ show_statement statement) block.statements
            @ [ "  " ^ show_terminator block.terminator ])
          (Array.to_list body.blocks)))

let show (mir : t) =
  String.concat "\n\n"
    (show_body mir.body
    :: List.mapi
         (fun index body -> Printf.sprintf "lambda %d\n%s" index (show_body body))
         (Array.to_list mir.lambdas))

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
