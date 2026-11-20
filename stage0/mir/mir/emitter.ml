module Local_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Core.local
end))

let raise_bug format = Compiler_bug.raise_bug ~stage:"MIR" format

type frame = Bindings | Statement

type scope = {
  frame : frame;
  mutable bound : Tree.local list;
  mutable loans : int list;
  mutable temporaries : Tree.local list;
}

type task_exit = Exit_return of Tree.operand option | Exit_break | Exit_continue

type group = {
  winner : Tree.local;
  mutable exits : (Tree.local option * (unit -> Tree.block)) list;
}

type enclosing_loop = { depth : int; tasks_around : int }

type t = {
  infos : (Tree.local, Tree.local_info) Hashtbl.t;
  mutable local_count : int;
  mutable statements : Tree.statement list;
  mutable reaches : bool;
  sources : Tree.local Local_table.t;
  mutable scopes : scope list;
  mutable loops : enclosing_loop list;
  mutable compound_target : Tree.place option;
  lambdas : Tree.body list ref;
  mutable loan_count : int;
  mutable deferred : Tree.local list option;
  mutable extended : Core.id list;
  mutable binds_to_statement : bool;
  mutable tasks : (Tree.task * int) list;
  groups : (Core.id, group) Hashtbl.t;
  held_places : (Tree.local, Tree.place) Hashtbl.t;
  bound_to_places : (Tree.local, unit) Hashtbl.t;
  lent_parts : (Tree.local, unit) Hashtbl.t;
  aliasing_names : (Tree.local, unit) Hashtbl.t;
  is_specification : bool;
  entry_locals : Core.local list;
  mutable in_old : bool;
  takes_free_locals : bool;
  mutable free : Tree.local list;
}

let create ?(is_specification = false) ~entry_locals ?(takes_free_locals = false) () =
  {
    takes_free_locals;
    free = [];
    is_specification;
    entry_locals;
    in_old = false;
    infos = Hashtbl.create 16;
    local_count = 0;
    statements = [];
    reaches = true;
    sources = Local_table.create 16;
    scopes = [];
    loops = [];
    compound_target = None;
    lambdas = ref [];
    loan_count = 0;
    deferred = None;
    extended = [];
    binds_to_statement = false;
    tasks = [];
    groups = Hashtbl.create 1;
    held_places = Hashtbl.create 8;
    bound_to_places = Hashtbl.create 8;
    lent_parts = Hashtbl.create 8;
    aliasing_names = Hashtbl.create 8;
  }

let allocate_local builder kind type_ origin =
  let local = builder.local_count in
  Hashtbl.replace builder.infos local { kind; type_; origin; has_several_bindings = false };
  builder.local_count <- local + 1;
  local

let add_temporary builder local =
  match builder.scopes with
  | scope :: _ -> scope.temporaries <- local :: scope.temporaries
  | [] -> ()

let add_lent_part builder local =
  Hashtbl.replace builder.lent_parts local ();
  add_temporary builder local

let note_may_alias builder local = Hashtbl.replace builder.aliasing_names local ()

let allocate_temporary builder type_ origin =
  let local = allocate_local builder Temporary type_ origin in
  add_temporary builder local;
  local

let make_local_place local = { Tree.root = Local local; projections = [] }

let emit builder kind origin =
  if builder.reaches then builder.statements <- { kind; origin } :: builder.statements

let jump builder jump origin =
  emit builder (Jump jump) origin;
  builder.reaches <- false

let assign builder target value origin = emit builder (Basic (Assign { target; value })) origin

let hold_in_temporary builder type_ origin write =
  if not builder.reaches then None
  else
    let local = allocate_temporary builder type_ origin in
    write (make_local_place local);
    Some (Tree.Use { place = make_local_place local; type_; origin })

let hold builder type_ origin value =
  hold_in_temporary builder type_ origin (fun target -> assign builder target value origin)

let hold_choice builder type_ origin choice =
  hold_in_temporary builder type_ origin (fun target ->
      emit builder (Choose { target; choice }) origin)

let build_block builder (build : unit -> Tree.operand option) : Tree.block =
  let enclosing = builder.statements in
  builder.statements <- [];
  builder.reaches <- true;
  let value = build () in
  let block =
    {
      statements = List.rev builder.statements;
      Tree.value = (if builder.reaches then value else None);
    }
  in
  if builder.reaches && value = None then raise_bug "a block that control leaves by no jump";
  builder.statements <- enclosing;
  builder.reaches <- true;
  block

let obtain_free_source builder (local : Core.local) ~type_ ~origin =
  match Local_table.find_opt builder.sources local with
  | Some local -> local
  | None when builder.takes_free_locals ->
      let free =
        allocate_local builder
          (Source { local; mode = Read; is_var = false; is_binding = false })
          type_ origin
      in
      Local_table.replace builder.sources local free;
      builder.free <- free :: builder.free;
      free
  | None -> raise_bug "a local that nothing binds"

let find_statement_scope builder =
  match List.find_opt (fun scope -> scope.frame = Statement) builder.scopes with
  | Some scope -> scope
  | None -> raise_bug "code lowered outside any statement"

let find_binding_scope builder =
  if builder.binds_to_statement then Some (find_statement_scope builder)
  else List.find_opt (fun scope -> scope.frame = Bindings) builder.scopes

let register_binding builder local =
  Option.iter (fun scope -> scope.bound <- local :: scope.bound) (find_binding_scope builder)

let bind_source ?(is_var = false) builder (local : Core.local) mode type_ origin =
  match Local_table.find_opt builder.sources local with
  | Some bound -> bound
  | None ->
      let bound =
        allocate_local builder (Source { local; mode; is_var; is_binding = true }) type_ origin
      in
      Local_table.replace builder.sources local bound;
      (match builder.deferred with
      | Some deferred -> builder.deferred <- Some (bound :: deferred)
      | None -> register_binding builder bound);
      bound

let start_loan builder borrowed mode duration origin =
  let loan = builder.loan_count in
  if not builder.is_specification then begin
    builder.loan_count <- loan + 1;
    emit builder (Basic (Loan_start { loan; borrowed; mode; duration })) origin;
    match builder.scopes with scope :: _ -> scope.loans <- loan :: scope.loans | [] -> ()
  end;
  loan

let end_loans builder loans origin =
  if loans <> [] && not builder.is_specification then begin
    emit builder (Basic (Loan_end loans)) origin;
    List.iter
      (fun scope -> scope.loans <- List.filter (fun loan -> not (List.mem loan loans)) scope.loans)
      builder.scopes
  end

let list_scope_ends scope origin =
  List.map
    (fun basic -> { Tree.kind = Basic basic; origin })
    ((if scope.loans <> [] then [ Tree.Loan_end (List.rev scope.loans) ] else [])
    @ (if scope.bound <> [] then [ Tree.Dead (List.rev scope.bound) ] else [])
    @ if scope.temporaries <> [] then [ Tree.Dead (List.rev scope.temporaries) ] else [])

let end_scope builder scope origin =
  List.iter
    (fun (ended : Tree.statement) -> emit builder ended.kind ended.origin)
    (list_scope_ends scope origin)

let make_block_scope () = { frame = Bindings; bound = []; loans = []; temporaries = [] }

let run_in_block_scope builder scope origin f =
  builder.scopes <- scope :: builder.scopes;
  let result = f () in
  builder.scopes <- List.tl builder.scopes;
  end_scope builder scope origin;
  result

let run_in_scope builder origin f = run_in_block_scope builder (make_block_scope ()) origin f

let leave_scopes builder ~depth origin =
  let rec leave scopes count =
    if count > depth then
      match scopes with
      | scope :: outer ->
          end_scope builder scope origin;
          leave outer (count - 1)
      | [] -> ()
  in
  leave builder.scopes (List.length builder.scopes)

let run_in_statement builder origin f =
  let scope = { frame = Statement; bound = []; loans = []; temporaries = [] } in
  builder.scopes <- scope :: builder.scopes;
  let result = f () in
  builder.scopes <- List.tl builder.scopes;
  end_scope builder scope origin;
  result

let hold_past_scopes builder origin (value : Tree.operand) =
  match value with
  | Use { type_; _ } ->
      let local = allocate_local builder Temporary type_ origin in
      assign builder (make_local_place local) (Operand value) origin;
      Tree.Use { place = make_local_place local; type_; origin }
  | Immediate _ | Borrow _ | Take _ -> value

let return_from_scopes builder value origin =
  let value = Option.map (hold_past_scopes builder origin) value in
  leave_scopes builder ~depth:0 origin;
  jump builder (Return value) origin

let unit_value = Tree.Immediate { value = Unit; type_ = Types.unit }

let group_key : Tree.task -> Core.id = function
  | Branch { fork; _ } -> fork
  | Iteration { loop } -> loop

let hold_operand builder (value : Tree.operand) type_ origin =
  match value with
  | Immediate _ | Borrow { mode = Mut; _ } | Take _ -> value
  | Use { place = { root = Local local; projections = [] }; _ }
    when (Hashtbl.find builder.infos local).kind = Temporary ->
      value
  | Use _ ->
      let local = allocate_temporary builder type_ origin in
      assign builder (make_local_place local) (Operand value) origin;
      Use { place = make_local_place local; type_; origin }
  | Borrow { place; mode; _ } ->
      let local = allocate_local builder (Lent Read) type_ origin in
      add_temporary builder local;
      Hashtbl.replace builder.held_places local place;
      assign builder (make_local_place local) (Operand value) origin;
      Borrow { place = make_local_place local; type_; mode; origin }

let rec borrow_place builder (place : Tree.place) =
  match place.root with
  | Local local -> (
      match Hashtbl.find_opt builder.held_places local with
      | Some held ->
          let held = borrow_place builder held in
          { held with Tree.projections = held.Tree.projections @ place.projections }
      | None -> place)
  | Constant _ | Literal _ -> place

let partition_lent_parts builder temporaries =
  List.partition (Hashtbl.mem builder.lent_parts) temporaries

let run_in_condition builder scope evaluate =
  let statement_scope = find_statement_scope builder in
  let bound_before = statement_scope.bound in
  builder.scopes <- scope :: builder.scopes;
  let value = Fun.protect ~finally:(fun () -> builder.scopes <- List.tl builder.scopes) evaluate in
  let names = List.filter (fun local -> not (List.mem local bound_before)) statement_scope.bound in
  statement_scope.bound <- bound_before;
  scope.bound <- names @ scope.bound;
  value

let run_in_scrutinee_frame builder evaluate =
  let scope = make_block_scope () in
  let value = run_in_condition builder scope evaluate in
  let lent_parts, others = partition_lent_parts builder scope.temporaries in
  List.iter (add_temporary builder) (List.rev others);
  scope.temporaries <- lent_parts;
  (value, scope)

let make_arm_scope ~scrutinee =
  {
    frame = Bindings;
    bound = scrutinee.bound;
    loans = scrutinee.loans;
    temporaries = scrutinee.temporaries;
  }

let run_in_guarded_block builder scope origin build =
  let lent_parts, others = partition_lent_parts builder scope.temporaries in
  let block_scope =
    if lent_parts <> [] && List.exists (Hashtbl.mem builder.aliasing_names) scope.bound then begin
      end_scope builder { scope with bound = []; loans = []; temporaries = others } origin;
      { scope with temporaries = lent_parts }
    end
    else begin
      end_scope builder { scope with bound = [] } origin;
      { scope with loans = []; temporaries = [] }
    end
  in
  run_in_block_scope builder block_scope origin build

let run_in_value_scope builder origin (build : unit -> Tree.operand option) =
  run_in_scope builder origin (fun () ->
      let value = build () in
      match (value, builder.scopes) with
      | Some (Use { place = { root = Local local; _ }; type_; _ } as read), scope :: enclosing :: _
        ->
          if List.mem local scope.temporaries then begin
            scope.temporaries <- List.filter (fun temporary -> temporary <> local) scope.temporaries;
            enclosing.temporaries <- local :: enclosing.temporaries;
            value
          end
          else if List.mem local scope.bound then begin
            let held = allocate_local builder Temporary type_ origin in
            enclosing.temporaries <- held :: enclosing.temporaries;
            assign builder (make_local_place held) (Operand read) origin;
            Some (Use { place = make_local_place held; type_; origin })
          end
          else value
      | _ -> value)

let run_in_loop builder build =
  builder.loops <-
    { depth = List.length builder.scopes; tasks_around = List.length builder.tasks }
    :: builder.loops;
  build ();
  builder.loops <- List.tl builder.loops

let obtain_group builder (task : Tree.task) origin =
  let key = group_key task in
  match Hashtbl.find_opt builder.groups key with
  | Some group -> group
  | None ->
      let winner = allocate_local builder Temporary (Types.make_builtin UInt32) origin in
      let group = { winner; exits = [] } in
      Hashtbl.replace builder.groups key group;
      group

let list_tasks_left builder exit =
  match exit with
  | `Return -> List.map fst builder.tasks
  | (`Break | `Continue) as exit -> (
      match builder.loops with
      | loop :: _ ->
          List.take (List.length builder.tasks - loop.tasks_around) builder.tasks
          |> List.filter_map (fun (task, _) ->
              match (task, exit) with Tree.Iteration _, `Continue -> None | _ -> Some task)
      | [] -> raise_bug "a loop exit outside a loop")

let leave_tasks builder tasks exit origin =
  let exit =
    match exit with
    | Exit_return value -> Exit_return (Option.map (hold_past_scopes builder origin) value)
    | Exit_break | Exit_continue -> exit
  in
  let loop_count = List.length builder.loops in
  let target_depth =
    match (exit, builder.loops) with
    | Exit_return _, _ -> 0
    | (Exit_break | Exit_continue), loop :: _ -> loop.depth
    | (Exit_break | Exit_continue), [] -> raise_bug "a loop exit outside a loop"
  in
  let rec leave returned = function
    | [] -> (
        leave_scopes builder ~depth:target_depth origin;
        match exit with
        | Exit_return _ -> jump builder (Return returned) origin
        | Exit_continue -> jump builder Continue origin
        | Exit_break -> if List.length builder.loops >= loop_count then jump builder Break origin)
    | task :: outer ->
        let start =
          match List.assoc_opt task builder.tasks with
          | Some start -> start
          | None -> raise_bug "an exit from a task that does not enclose it"
        in
        leave_scopes builder ~depth:start origin;
        let group = obtain_group builder task origin in
        let slot =
          Option.map
            (fun value -> allocate_local builder Temporary (Walk.extract_operand_type value) origin)
            returned
        in
        let moved =
          match (returned, slot) with Some value, Some slot -> Some (value, slot) | _ -> None
        in
        let build_resumed () =
          build_block builder (fun () ->
              leave
                (Option.map
                   (fun (value, slot) ->
                     Tree.Use
                       {
                         place = make_local_place slot;
                         type_ = Walk.extract_operand_type value;
                         origin;
                       })
                   moved)
                outer;
              if builder.reaches then Some unit_value else None)
        in
        group.exits <- group.exits @ [ (slot, build_resumed) ];
        jump builder
          (Cancel
             { task; winner = group.winner; number = List.length group.exits; returned = moved })
          origin
  in
  leave (match exit with Exit_return value -> value | Exit_break | Exit_continue -> None) tasks

let start_group builder key origin =
  match Hashtbl.find_opt builder.groups key with
  | Some { winner; exits = _ :: _ } ->
      add_temporary builder winner;
      assign builder (make_local_place winner)
        (Operand (Immediate { value = Integer Z.zero; type_ = Types.make_builtin UInt32 }))
        origin
  | _ -> ()

let resume_group builder key origin =
  match Hashtbl.find_opt builder.groups key with
  | Some { winner; exits = _ :: _ as exits } ->
      let exits =
        List.map
          (fun (returned, build_resumed) -> { Tree.resumed = build_resumed (); returned })
          exits
      in
      emit builder (Resume { winner; exits }) origin
  | _ -> ()

let reaches builder = builder.reaches
let mark_unreachable builder = builder.reaches <- false
let is_specification builder = builder.is_specification
let entry_locals builder = builder.entry_locals
let lookup_local_info builder local = Hashtbl.find builder.infos local
let collect_locals builder = Array.init builder.local_count (Hashtbl.find builder.infos)
let find_source builder local = Local_table.find_opt builder.sources local
let add_source builder core local = Local_table.replace builder.sources core local
let free_locals builder = List.rev builder.free
let statements builder = List.rev builder.statements
let emitted builder = builder.statements

let add_lambda builder body =
  builder.lambdas := body :: !(builder.lambdas);
  List.length !(builder.lambdas) - 1

let lambdas builder = Array.of_list (List.rev !(builder.lambdas))

let make_lambda_builder builder =
  {
    (create ~is_specification:builder.is_specification ~entry_locals:builder.entry_locals ()) with
    lambdas = builder.lambdas;
    in_old = builder.in_old;
  }

let with_set : 'value. (unit -> 'value) -> set:(unit -> unit) -> restore:(unit -> unit) -> 'value =
 fun build ~set ~restore ->
  set ();
  Fun.protect ~finally:restore build

let run_in_old builder build =
  let enclosing = builder.in_old in
  with_set build
    ~set:(fun () -> builder.in_old <- true)
    ~restore:(fun () -> builder.in_old <- enclosing)

let reads_entry builder local = builder.in_old && List.mem local builder.entry_locals

let run_binding_to_statement builder build =
  let enclosing = builder.binds_to_statement in
  with_set build
    ~set:(fun () -> builder.binds_to_statement <- true)
    ~restore:(fun () -> builder.binds_to_statement <- enclosing)

let run_extending builder extended build =
  let enclosing = builder.extended in
  with_set build
    ~set:(fun () -> builder.extended <- extended)
    ~restore:(fun () -> builder.extended <- enclosing)

let run_deferring builder build =
  let enclosing = builder.deferred in
  builder.deferred <- Some [];
  let built = build () in
  let bound = Option.value ~default:[] builder.deferred in
  builder.deferred <- enclosing;
  (built, List.rev bound)

let with_compound_target builder target build =
  let enclosing = builder.compound_target in
  with_set build
    ~set:(fun () -> builder.compound_target <- Some target)
    ~restore:(fun () -> builder.compound_target <- enclosing)

let compound_target builder = builder.compound_target

let allocate_place_temporary builder ~node type_ origin =
  let local = allocate_local builder Temporary type_ origin in
  (match find_binding_scope builder with
  | Some scope when List.mem node builder.extended ->
      scope.temporaries <- local :: scope.temporaries
  | _ -> add_temporary builder local);
  local

let note_bound_to_place builder local =
  if Hashtbl.mem builder.bound_to_places local then
    Hashtbl.replace builder.infos local
      { (Hashtbl.find builder.infos local) with has_several_bindings = true }
  else Hashtbl.replace builder.bound_to_places local ()

type suspended = Tree.statement list

let suspend_block builder =
  let enclosing = builder.statements in
  builder.statements <- [];
  enclosing

let resume_block builder (enclosing : suspended) =
  let statements = List.rev builder.statements in
  builder.statements <- enclosing;
  statements

let list_unmatched_ends scope ~scrutinee origin =
  list_scope_ends
    {
      scope with
      bound = List.filter (fun local -> not (List.mem local scrutinee.bound)) scope.bound;
      loans = List.filter (fun loan -> not (List.mem loan scrutinee.loans)) scope.loans;
      temporaries =
        List.filter (fun local -> not (List.mem local scrutinee.temporaries)) scope.temporaries;
    }
    origin

let run_in_task builder task build =
  builder.tasks <- (task, List.length builder.scopes) :: builder.tasks;
  Fun.protect ~finally:(fun () -> builder.tasks <- List.tl builder.tasks) build

let return_ builder value origin =
  match list_tasks_left builder `Return with
  | [] -> return_from_scopes builder value origin
  | tasks -> leave_tasks builder tasks (Exit_return value) origin

let break_ builder origin =
  match (builder.loops, list_tasks_left builder `Break) with
  | loop :: _, [] ->
      leave_scopes builder ~depth:loop.depth origin;
      jump builder Break origin
  | _ :: _, tasks -> leave_tasks builder tasks Exit_break origin
  | [], _ -> raise_bug "a `break` outside a loop"

let continue_ builder origin =
  match (builder.loops, list_tasks_left builder `Continue) with
  | loop :: _, [] ->
      leave_scopes builder ~depth:loop.depth origin;
      jump builder Continue origin
  | _ :: _, tasks -> leave_tasks builder tasks Exit_continue origin
  | [], _ -> raise_bug "a `continue` outside a loop"

let finish ?(captures = []) ?(is_functional = false) ?value_type builder ~parameters : Tree.body =
  if builder.reaches then raise_bug "a body whose end control reaches";
  {
    parameters;
    captures;
    locals = collect_locals builder;
    code = { statements = statements builder; value = None };
    is_functional;
    value_type;
  }

let build_formula builder ~origin ~type_ (build : unit -> Tree.local list * Tree.operand option) :
    Tree.formula =
  let built = ref None in
  let record_formula parameters value =
    built :=
      Some
        {
          Tree.parameters;
          locals = [||];
          value = { statements = statements builder; value };
          type_;
          origin;
          lambdas = [||];
          holds_when = [];
        }
  in
  let held = ref None in
  run_in_scope builder origin (fun () ->
      run_in_statement builder origin (fun () ->
          let parameters, value = build () in
          match value with
          | Some value when reaches builder ->
              if is_specification builder then record_formula parameters (Some value)
              else held := Some (parameters, Some (hold_past_scopes builder origin value))
          | Some _ | None -> held := Some (parameters, None)));
  Option.iter (fun (parameters, value) -> record_formula parameters value) !held;
  match !built with
  | Some formula -> { formula with locals = collect_locals builder; lambdas = lambdas builder }
  | None -> raise_bug "a formula that was not built"
