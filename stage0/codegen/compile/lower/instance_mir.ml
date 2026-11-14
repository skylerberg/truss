let bug format = Compiler_bug.bug ~stage:"Instance MIR" format

type change = {
  local : Mir.local -> Mir.local;
  block : Mir.block -> Mir.block;
  lambda : int -> int;
  fork : Core.origin -> Core.origin;
  ty : Types.ty -> Types.ty;
  argument : Types.argument -> Types.argument;
}

let unchanged =
  { local = Fun.id; block = Fun.id; lambda = Fun.id; fork = Fun.id; ty = Fun.id; argument = Fun.id }

let change_place change (place : Mir.place) : Mir.place =
  match place.root with
  | Local local -> { place with root = Local (change.local local) }
  | Constant _ -> place

let change_operand change : Mir.operand -> Mir.operand = function
  | Use use -> Use { use with place = change_place change use.place; type_ = change.ty use.type_ }
  | Borrow borrow ->
      Borrow
        { borrow with place = change_place change borrow.place; type_ = change.ty borrow.type_ }
  | Take take ->
      Take { take with place = change_place change take.place; type_ = change.ty take.type_ }
  | Constant constant -> Constant { constant with type_ = change.ty constant.type_ }

let change_evidence change : Core.evidence -> Core.evidence = function
  | Impl { impl; arguments } ->
      Impl
        {
          impl;
          arguments =
            List.map (fun (parameter, argument) -> (parameter, change.argument argument)) arguments;
        }
  | (Bound | Dynamic) as evidence -> evidence

let change_trait change (trait : Types.trait_reference) : Types.trait_reference =
  {
    trait with
    trait_arguments = List.map change.argument trait.trait_arguments;
    associated = List.map (fun (name, ty) -> (name, change.ty ty)) trait.associated;
  }

let change_callee change : Mir.callee -> Mir.callee = function
  | Function { path; type_arguments } ->
      Function { path; type_arguments = List.map change.argument type_arguments }
  | Trait_method method_ ->
      Trait_method
        {
          method_ with
          trait = change_trait change method_.trait;
          self_type = change.ty method_.self_type;
          type_arguments = List.map change.argument method_.type_arguments;
          evidence = change_evidence change method_.evidence;
        }
  | Capability_method _ as callee -> callee
  | Intrinsic { operation; type_arguments } ->
      Intrinsic { operation; type_arguments = List.map change.argument type_arguments }
  | Indirect value -> Indirect (change_operand change value)

let change_call change (call : Mir.call) : Mir.call =
  {
    call with
    callee = change_callee change call.callee;
    arguments =
      List.map
        (function
          | Mir.Passed passed ->
              Mir.Passed { passed with value = change_operand change passed.value }
          | Default -> Default)
        call.arguments;
  }

let change_rvalue change : Mir.rvalue -> Mir.rvalue =
  let operand = change_operand change in
  function
  | Operand value -> Operand (operand value)
  | Operation operation ->
      Operation
        {
          operation with
          type_arguments = List.map change.argument operation.type_arguments;
          operands = List.map operand operation.operands;
        }
  | Compare compare ->
      Compare { compare with left = operand compare.left; right = operand compare.right }
  | Not value -> Not (operand value)
  | Construct construct ->
      Construct
        {
          construct with
          fields = List.map (fun (name, field) -> (name, Option.map operand field)) construct.fields;
        }
  | Array elements -> Array (List.map operand elements)
  | Is_variant test -> Is_variant { test with place = change_place change test.place }
  | Convert convert -> Convert { convert with value = operand convert.value }
  | To_any any ->
      To_any
        {
          value = operand any.value;
          trait = change_trait change any.trait;
          evidence = change_evidence change any.evidence;
        }
  | Copy value -> Copy (operand value)
  | Function_value { path; type_arguments } ->
      Function_value { path; type_arguments = List.map change.argument type_arguments }
  | Lambda lambda ->
      Lambda
        {
          lambda with
          body = change.lambda lambda.body;
          captures =
            List.map
              (fun (capture : Mir.capture) ->
                {
                  capture with
                  type_ = change.ty capture.type_;
                  place = change_place change capture.place;
                })
              lambda.captures;
        }
  | Value_parameter parameter -> (
      match change.argument (Value (Value_parameter parameter)) with
      | Value (Known number) ->
          Operand (Constant { value = Integer number; type_ = Types.builtin USize })
      | Value (Value_parameter parameter) -> Value_parameter parameter
      | _ -> bug "a value parameter that is no value")

let rec change_yielded change : Mir.yielded -> Mir.yielded = function
  | Part value -> Part (change_operand change value)
  | Built built ->
      Built
        {
          built with
          fields =
            List.map
              (fun (name, field) -> (name, Option.map (change_yielded change) field))
              built.fields;
          type_ = change.ty built.type_;
        }

let change_statement change (statement : Mir.statement) : Mir.statement =
  let place = change_place change and operand = change_operand change in
  let call = change_call change in
  let kind : Mir.statement_kind =
    match statement.kind with
    | Assign assign ->
        Assign
          { assign with target = place assign.target; value = change_rvalue change assign.value }
    | Call { destination; call = called } ->
        Call { destination = Option.map place destination; call = call called }
    | Lend { part; call = called } -> Lend { part = change.local part; call = call called }
    | Slice { destination; base; call = called } ->
        Slice { destination = place destination; base = place base; call = call called }
    | Template template ->
        Template
          { template with destination = place template.destination; call = call template.call }
    | Live locals -> Live (List.map change.local locals)
    | Dead locals -> Dead (List.map change.local locals)
    | Assert assert_ -> Assert { assert_ with condition = operand assert_.condition }
    | Echo value -> Echo (operand value)
    | Provide { provided; can_use_tasks } ->
        Provide
          {
            provided =
              List.map
                (fun (provided : Mir.provided) ->
                  { provided with value = operand provided.value; type_ = change.ty provided.type_ })
                provided;
            can_use_tasks;
          }
    | Loan_start loan -> Loan_start { loan with borrowed = operand loan.borrowed }
    | (Provide_end | Loan_end _ | Ghost_assert _ | Matched _ | Proof _) as kind -> kind
  in
  { statement with kind }

let change_terminator change (terminator : Mir.terminator) : Mir.terminator =
  let block = change.block and operand = change_operand change in
  match terminator with
  | Goto target -> Goto (block target)
  | Branch branch ->
      Branch
        {
          branch with
          condition = operand branch.condition;
          yes = block branch.yes;
          no = block branch.no;
        }
  | Switch_variant { place; cases } ->
      Switch_variant
        {
          place = change_place change place;
          cases = List.map (fun (variant, target) -> (variant, block target)) cases;
        }
  | For loop ->
      For
        {
          loop with
          iteration =
            (match loop.iteration with
            | Range range ->
                Range { range with start = operand range.start; stop = operand range.stop }
            | Pull { cursor; next } ->
                Pull { cursor = change_place change cursor; next = change_callee change next });
          part = change.local loop.part;
          lent =
            Option.map
              (fun (lent : Mir.lent_element) -> { lent with element = change.local lent.element })
              loop.lent;
          body = block loop.body;
          blocks = List.map block loop.blocks;
          after = block loop.after;
        }
  | Fork fork ->
      Fork
        {
          fork with
          fork = change.fork fork.fork;
          branches =
            List.map
              (fun (branch : Mir.branch) ->
                { Mir.entry = block branch.entry; blocks = List.map block branch.blocks })
              fork.branches;
          join = Option.map block fork.join;
        }
  | Join join -> Join { fork = change.fork join.fork; next = block join.next }
  | Yield yielded ->
      Yield
        { yielded with part = change_yielded change yielded.part; resume = block yielded.resume }
  | Return value -> Return (Option.map operand value)
  | Cancel { task; task_end; winner; number; returned } ->
      Cancel
        {
          task =
            (match task with
            | Branch { block = fork; index } -> Branch { block = change.fork fork; index }
            | Iteration _ -> task);
          task_end = Option.map block task_end;
          winner = change.local winner;
          number;
          returned = Option.map (fun (value, slot) -> (operand value, change.local slot)) returned;
        }
  | Resume { winner; exits; next } ->
      Resume
        {
          winner = change.local winner;
          exits =
            List.map
              (fun (exit : Mir.early_exit) ->
                { Mir.resume = block exit.resume; returned = Option.map change.local exit.returned })
              exits;
          next = block next;
        }
  | Iteration_end { loop } -> Iteration_end { loop = block loop }
  | (Unreachable | Written_unreachable | Todo) as terminator -> terminator

let change_block change (basic : Mir.basic_block) : Mir.basic_block =
  {
    basic with
    statements = List.map (change_statement change) basic.statements;
    terminator = change_terminator change basic.terminator;
    header =
      Option.map
        (fun (natural : Mir.natural_loop) ->
          {
            natural with
            body = change.block natural.body;
            after = Option.map change.block natural.after;
          })
        basic.header;
  }

let change_body change (body : Mir.body) : Mir.body =
  {
    parameters = List.map change.local body.parameters;
    captures = List.map change.local body.captures;
    locals =
      Array.map
        (fun (info : Mir.local_info) -> { info with type_ = change.ty info.type_ })
        body.locals;
    blocks = Array.map (change_block change) body.blocks;
  }

(* A method's MIR with its type arguments substituted, which makes its
   types the instance's. *)
let substituted (substitution : Types.substitution) (mir : Mir.t) : Mir.t =
  let change =
    {
      unchanged with
      ty = Types.substitute substitution;
      argument = Types.substitute_argument substitution;
    }
  in
  { body = change_body change mir.body; lambdas = Array.map (change_body change) mir.lambdas }

(* Inlining *)

module Locals = Set.Make (Int)

type building = {
  locals : Mir.local_info Dynarray.t;
  blocks : Mir.basic_block Dynarray.t;
  lambdas : Mir.body Dynarray.t;
  mutable last_fork : Core.origin;
}

let add_block building (basic : Mir.basic_block) =
  let block = Dynarray.length building.blocks in
  Dynarray.add_last building.blocks basic;
  block

let block_at building block = Dynarray.get building.blocks block
let set_block building block basic = Dynarray.set building.blocks block basic

let new_local building (info : Mir.local_info) =
  let local = Dynarray.length building.locals in
  Dynarray.add_last building.locals info;
  local

let fresh_forks building =
  let forks = Hashtbl.create 1 in
  fun fork ->
    match Hashtbl.find_opt forks fork with
    | Some fresh -> fresh
    | None ->
        building.last_fork <- building.last_fork - 1;
        Hashtbl.replace forks fork building.last_fork;
        building.last_fork

let copy building ~path ~type_arguments ~origin ~(inlined : Mir.inlined list) ?same_locals
    (mir : Mir.t) =
  let local_offset, lambda_offset =
    match same_locals with
    | Some offsets -> offsets
    | None ->
        let local_offset = Dynarray.length building.locals
        and lambda_offset = Dynarray.length building.lambdas in
        Array.iter (Dynarray.add_last building.locals) mir.body.locals;
        Array.iter
          (fun lambda ->
            Dynarray.add_last building.lambdas
              (change_body { unchanged with lambda = (fun index -> index + lambda_offset) } lambda))
          mir.lambdas;
        (local_offset, lambda_offset)
  in
  let block_offset = Dynarray.length building.blocks in
  let change =
    {
      unchanged with
      local = (fun local -> local + local_offset);
      block = (fun block -> block + block_offset);
      lambda = (fun index -> index + lambda_offset);
      fork = (if same_locals = None then Fun.id else fresh_forks building);
    }
  in
  Array.iter
    (fun (basic : Mir.basic_block) ->
      ignore
        (add_block building
           {
             (change_block change basic) with
             inlined = basic.inlined @ ({ method_ = path; type_arguments; call = origin } :: inlined);
           }))
    mir.body.blocks;
  (change, (local_offset, lambda_offset), block_offset, Array.length mir.body.blocks)

let bind_parameter building ~origin ~temporaries ~is_default parameter (value : Mir.operand) =
  let assign target rvalue : Mir.statement =
    {
      kind =
        Assign { target = { root = Local target; projections = [] }; value = rvalue; node = None };
      origin;
    }
  in
  let held type_ mode =
    let temporary = new_local building { kind = Temporary; type_; origin } in
    temporaries := temporary :: !temporaries;
    [
      assign temporary (Operand value);
      assign parameter
        (Operand
           (Borrow { place = { root = Local temporary; projections = [] }; type_; mode; origin }));
    ]
  in
  match ((Dynarray.get building.locals parameter).kind, value) with
  | ( Source { mode = (Read | Mut) as mode; _ },
      (Use { type_; _ } | Constant { type_; _ } | Take { type_; _ }) )
    when is_default ->
      held type_ mode
  | Source { mode = (Read | Mut) as mode; _ }, Use { place; type_; origin; _ } ->
      [ assign parameter (Operand (Borrow { place; type_; mode; origin })) ]
  | Source { mode = (Read | Mut) as mode; _ }, (Constant { type_; _ } | Take { type_; _ }) ->
      held type_ mode
  | _ -> [ assign parameter (Operand value) ]

let bind_parameters building ~path ~type_arguments ~origin ~inlined ~(change : change) (mir : Mir.t)
    ~(defaults : (int * Mir.t) list) (arguments : Mir.argument list) ~entry =
  let parameters = List.map change.local mir.body.parameters in
  let temporaries = ref [] in
  let bound =
    List.concat
      (List.map2
         (fun parameter (argument : Mir.argument) ->
           match argument with
           | Passed { value; _ } ->
               bind_parameter building ~origin ~temporaries ~is_default:false parameter value
           | Default -> [])
         parameters arguments)
  in
  (* Each default runs in turn, from the last, so that the first runs first. *)
  let first =
    List.fold_right2
      (fun (position, parameter) (argument : Mir.argument) next ->
        match argument with
        | Passed _ -> next
        | Default -> (
            match List.assoc_opt position defaults with
            | None -> bug "%s is given no argument for a parameter" (Path.show path)
            | Some default ->
                let _, _, offset, count =
                  copy building ~path ~type_arguments ~origin ~inlined default
                in
                for block = offset to offset + count - 1 do
                  let basic = block_at building block in
                  match basic.terminator with
                  | Return (Some value) ->
                      set_block building block
                        {
                          basic with
                          statements =
                            basic.statements
                            @ bind_parameter building ~origin ~temporaries ~is_default:true
                                parameter value;
                          terminator = Goto next;
                        }
                  | _ -> ()
                done;
                offset))
      (List.mapi (fun position parameter -> (position, parameter)) parameters)
      arguments entry
  in
  (bound, first, !temporaries)

(* The locals a statement gives a value, and those it ends. *)
let written (statement : Mir.statement) =
  let whole (place : Mir.place) =
    match place with { root = Local local; projections = [] } -> [ local ] | _ -> []
  in
  match statement.kind with
  | Assign { target; _ } -> (whole target, [])
  | Call { destination = Some destination; _ }
  | Slice { destination; _ }
  | Template { destination; _ } ->
      (whole destination, [])
  | Lend { part; _ } -> ([ part ], [])
  | Live locals -> (locals, [])
  | Dead locals -> ([], locals)
  | Call { destination = None; _ }
  | Assert _ | Echo _ | Provide _ | Provide_end | Loan_start _ | Loan_end _ | Ghost_assert _
  | Matched _ | Proof _ ->
      ([], [])

let alive building ~entry ~bound ~(is_method_local : Mir.local -> bool) =
  let reaching = Hashtbl.create 16 and pending = Queue.create () in
  let flow block locals =
    let before = Option.value (Hashtbl.find_opt reaching block) ~default:Locals.empty in
    let merged = Locals.union before locals in
    if (not (Hashtbl.mem reaching block)) || not (Locals.equal merged before) then begin
      Hashtbl.replace reaching block merged;
      Queue.add block pending
    end
  in
  flow entry (Locals.of_list (List.filter is_method_local bound));
  let ending = Hashtbl.create 16 in
  while not (Queue.is_empty pending) do
    let block = Queue.pop pending in
    let basic = block_at building block in
    let locals =
      List.fold_left
        (fun locals statement ->
          let given, ended = written statement in
          Locals.diff
            (Locals.union locals (Locals.of_list (List.filter is_method_local given)))
            (Locals.of_list ended))
        (Hashtbl.find reaching block) basic.statements
    in
    Hashtbl.replace ending block locals;
    List.iter
      (fun target ->
        match basic.terminator with
        | For { iteration = Pull _; part; body; _ } when target = body && is_method_local part ->
            flow target (Locals.add part locals)
        | _ -> flow target locals)
      (Mir.successors basic.terminator)
  done;
  fun block -> Option.value (Hashtbl.find_opt ending block) ~default:Locals.empty

let rec yielded_into building ~part ~(mode : Types.mode) ~origin (yielded : Mir.yielded) :
    Mir.statement list =
  let assign value : Mir.statement =
    {
      kind = Assign { target = { root = Local part; projections = [] }; value; node = None };
      origin;
    }
  in
  match (yielded, mode) with
  | Part (Use { place; type_; origin; _ }), (Read | Mut) ->
      [ assign (Operand (Borrow { place; type_; mode; origin })) ]
  | Part value, _ -> [ assign (Operand value) ]
  | Built { variant; fields; _ }, _ ->
      let statements, fields =
        List.fold_left
          (fun (statements, fields) (name, field) ->
            match (field : Mir.yielded option) with
            | None -> (statements, fields @ [ (name, None) ])
            | Some (Part value) -> (statements, fields @ [ (name, Some value) ])
            | Some (Built inner as built) ->
                let held =
                  new_local building
                    { kind = (Dynarray.get building.locals part).kind; type_ = inner.type_; origin }
                in
                ( statements @ yielded_into building ~part:held ~mode ~origin built,
                  fields
                  @ [
                      ( name,
                        Some
                          (Mir.Use
                             {
                               place = { root = Local held; projections = [] };
                               type_ = inner.type_;
                               node = inner.node;
                               origin;
                             }) );
                    ] ))
          ([], []) fields
      in
      statements @ [ assign (Construct { variant; fields }) ]

(* The blocks of a loop's body that end its own iterations, not those of a
   loop nested in it. *)
let own_iteration_ends building (blocks : Mir.block list) =
  let nested =
    List.concat_map
      (fun block ->
        match (block_at building block).terminator with
        | For { blocks = inner; _ } -> inner
        | _ -> [])
      blocks
  in
  List.filter
    (fun block ->
      (not (List.mem block nested))
      && match (block_at building block).terminator with Iteration_end _ -> true | _ -> false)
    blocks

(* The tasks that run in [blocks]: each iteration of a loop there and each
   branch of a fork there, and each iteration of the loop with the origin
   [iteration], if its iterations run as tasks. *)
let tasks_in building (blocks : Mir.block list) ~iteration : Core.task list =
  Option.to_list (Option.map (fun loop -> Core.Iteration { loop }) iteration)
  @ List.concat_map
      (fun block ->
        match (block_at building block).terminator with
        | For { loop; _ } -> [ Core.Iteration { loop = loop.origin } ]
        | Fork { fork; branches; _ } ->
            List.mapi (fun index _ -> Core.Branch { block = fork; index }) branches
        | _ -> [])
      blocks

let end_on_exits building ~(blocks : Mir.block list) ~stays ~locals ~iteration ~origin =
  if locals <> [] then begin
    let dead : Mir.statement = { kind = Dead locals; origin } in
    let pads = Hashtbl.create 4 in
    let leave target =
      if stays target then target
      else
        match Hashtbl.find_opt pads target with
        | Some pad -> pad
        | None ->
            let pad =
              add_block building
                {
                  statements = [ dead ];
                  terminator = Goto target;
                  terminator_origin = origin;
                  header = None;
                  inlined = (block_at building target).inlined;
                }
            in
            Hashtbl.replace pads target pad;
            pad
    in
    let inside = tasks_in building blocks ~iteration in
    List.iter
      (fun block ->
        let basic = block_at building block in
        set_block building block
          (match basic.terminator with
          | Return _ -> { basic with statements = basic.statements @ [ dead ] }
          (* An early exit that leaves a task around the region leaves the
             region, once the groups inside it have ended. *)
          | Cancel { task; _ } when not (List.mem task inside) ->
              { basic with statements = basic.statements @ [ dead ] }
          | Cancel _ | Iteration_end _ -> basic
          | terminator ->
              {
                basic with
                terminator = change_terminator { unchanged with block = leave } terminator;
              }))
      blocks
  end

(* A method the instance calls, ready to inline: its path, its type
   arguments, and its MIR with them substituted. *)
type callee = {
  path : Path.t;
  type_arguments : Types.argument list;
  mir : Mir.t;
  defaults : (int * Mir.t) list;
}

let copied_locals (change : change) (mir : Mir.t) ~temporaries =
  let first = change.local 0 and count = Array.length mir.body.locals in
  ( (fun local -> (local >= first && local < first + count) || List.mem local temporaries),
    List.map change.local mir.body.parameters @ temporaries )

let join_regions building ~at ~start =
  let made = List.init (Dynarray.length building.blocks - start) (fun index -> start + index) in
  for block = 0 to start - 1 do
    let basic = block_at building block in
    match basic.terminator with
    | For loop when List.mem at loop.blocks ->
        set_block building block
          { basic with terminator = For { loop with blocks = loop.blocks @ made } }
    | Fork fork
      when List.exists (fun (branch : Mir.branch) -> List.mem at branch.blocks) fork.branches ->
        set_block building block
          {
            basic with
            terminator =
              Fork
                {
                  fork with
                  branches =
                    List.map
                      (fun (branch : Mir.branch) ->
                        if List.mem at branch.blocks then
                          { branch with blocks = branch.blocks @ made }
                        else branch)
                      fork.branches;
                };
          }
    | _ -> ()
  done

(* The blocks of a body being built, as a body, for an analysis of it. *)
let snapshot building (body : Mir.body) =
  {
    body with
    locals = Dynarray.to_array building.locals;
    blocks = Dynarray.to_array building.blocks;
  }

let ends_of building part ~from =
  let visited = Hashtbl.create 16 and ends = ref [] in
  let rec visit block =
    if not (Hashtbl.mem visited block) then begin
      Hashtbl.replace visited block ();
      let basic = block_at building block in
      match
        List.find_index
          (fun (statement : Mir.statement) ->
            match statement.kind with Dead locals -> List.mem part locals | _ -> false)
          basic.statements
      with
      | Some position -> ends := (block, position) :: !ends
      | None -> List.iter visit (Mir.successors basic.terminator)
    end
  in
  visit from;
  List.rev !ends

(* The entry of the innermost loop body or branch of a fork that [block] is
   in, or of the body. *)
let region_entry building block =
  let innermost = ref None in
  let consider entry blocks =
    if List.mem block blocks then
      match !innermost with
      | Some (_, size) when size <= List.length blocks -> ()
      | _ -> innermost := Some (entry, List.length blocks)
  in
  Dynarray.iter
    (fun (basic : Mir.basic_block) ->
      match basic.terminator with
      | For { body; blocks; _ } -> consider body blocks
      | Fork { branches; _ } ->
          List.iter (fun (branch : Mir.branch) -> consider branch.entry branch.blocks) branches
      | _ -> ())
    building.blocks;
  match !innermost with Some (entry, _) -> entry | None -> 0

let int_type = Types.builtin USize

let constant_int number : Mir.operand =
  Constant { value = Integer (Z.of_int number); type_ = int_type }

let local_operand local type_ origin : Mir.operand =
  Use { place = { root = Local local; projections = [] }; type_; node = origin; origin }

let inline_lend building ~(body : Mir.body) ~at ~position ~part ~(callee : callee)
    ~(call : Mir.call) ~origin =
  let basic = block_at building at in
  let conditional = List.mem part (Mir.conditional_lends (snapshot building body)) in
  let before = List.filteri (fun index _ -> index < position) basic.statements
  and rest = List.filteri (fun index _ -> index > position) basic.statements in
  let continuation = add_block building { basic with statements = rest; header = None } in
  let change, offsets, offset, count =
    copy building ~path:callee.path ~type_arguments:callee.type_arguments ~origin
      ~inlined:basic.inlined callee.mir
  in
  let bound, first, temporaries =
    bind_parameters building ~path:callee.path ~type_arguments:callee.type_arguments ~origin
      ~inlined:basic.inlined ~change callee.mir ~defaults:callee.defaults call.arguments
      ~entry:offset
  in
  set_block building at { basic with statements = before @ bound; terminator = Goto first };
  let yields =
    List.filter_map
      (fun block ->
        match (block_at building block).terminator with
        | Yield { part = yielded; resume; mode } -> Some (block, (yielded, mode), resume)
        | _ -> None)
      (List.init count (fun index -> offset + index))
  in
  let held =
    let is_method_local, parameters = copied_locals change callee.mir ~temporaries in
    let alive_at = alive building ~entry:offset ~bound:parameters ~is_method_local in
    Locals.elements
      (List.fold_left
         (fun held (block, _, _) -> Locals.union held (alive_at block))
         Locals.empty yields)
  in
  let selector =
    if List.length yields > 1 || conditional then
      Some (new_local building { kind = Temporary; type_ = int_type; origin })
    else None
  in
  let set_selector number : Mir.statement list =
    match selector with
    | Some selector ->
        [
          {
            kind =
              Assign
                {
                  target = { root = Local selector; projections = [] };
                  value = Operand (constant_int number);
                  node = None;
                };
            origin;
          };
        ]
    | None -> []
  in
  if conditional then begin
    let entry = region_entry building at in
    let basic = block_at building entry in
    set_block building entry { basic with statements = set_selector 0 @ basic.statements }
  end;
  List.iteri
    (fun index (block, (yielded, mode), _) ->
      (* The part is the caller's, so the caller's code binds it. *)
      let binding =
        add_block building
          {
            statements = yielded_into building ~part ~mode ~origin yielded @ set_selector (index + 1);
            terminator = Goto continuation;
            terminator_origin = origin;
            header = None;
            inlined = basic.inlined;
          }
      in
      set_block building block { (block_at building block) with terminator = Goto binding })
    yields;
  (* The rest of the method, where the part ends. A method that never
     yields never reaches the code after the call. *)
  if yields <> [] then
    List.iter
      (fun (ending, at_end) ->
        let ended = block_at building ending in
        let kept = List.filteri (fun index _ -> index <= at_end) ended.statements
        and after = List.filteri (fun index _ -> index > at_end) ended.statements in
        let goes_on =
          add_block building
            {
              ended with
              statements =
                (if held = [] then [] else [ { Mir.kind = Dead held; origin } ])
                @ (if conditional then set_selector 0 else [])
                @ after;
              header = None;
            }
        in
        let _, _, again, _ =
          copy building ~path:callee.path ~type_arguments:callee.type_arguments ~origin
            ~inlined:basic.inlined ~same_locals:offsets callee.mir
        in
        for block = again to again + count - 1 do
          let copied = block_at building block in
          match copied.terminator with
          | Return _ -> set_block building block { copied with terminator = Goto goes_on }
          | Yield _ -> set_block building block { copied with terminator = Unreachable }
          | _ -> ()
        done;
        let resume_of (_, _, (resume : Mir.block)) = resume - offset + again in
        let dispatch =
          match selector with
          | None -> (
              match yields with [ yielded ] -> resume_of yielded | _ -> bug "a lend with no yield")
          | Some selector ->
              let choices =
                (if conditional then [ (0, goes_on) ] else [])
                @ List.mapi (fun index yielded -> (index + 1, resume_of yielded)) yields
              in
              List.fold_right
                (fun (number, target) otherwise ->
                  let tested =
                    new_local building { kind = Temporary; type_ = Types.bool; origin }
                  in
                  add_block building
                    {
                      statements =
                        [
                          {
                            kind =
                              Assign
                                {
                                  target = { root = Local tested; projections = [] };
                                  value =
                                    Compare
                                      {
                                        comparison = Equal;
                                        left = local_operand selector int_type origin;
                                        right = constant_int number;
                                      };
                                  node = None;
                                };
                            origin;
                          };
                        ];
                      terminator =
                        Branch
                          {
                            condition = local_operand tested Types.bool origin;
                            yes = target;
                            no = otherwise;
                            is_if_condition = false;
                          };
                      terminator_origin = origin;
                      header = None;
                      inlined = ended.inlined;
                    })
                choices
                (add_block building
                   {
                     statements = [];
                     terminator = Unreachable;
                     terminator_origin = origin;
                     header = None;
                     inlined = ended.inlined;
                   })
        in
        set_block building ending { ended with statements = kept; terminator = Goto dispatch })
      (ends_of building part ~from:continuation)

(* Whether a lent part ends only in its own tasks' code, not where an early
   exit goes on once a group of tasks has ended. *)
let ends_only_in_statements building part =
  Dynarray.for_all
    (fun (basic : Mir.basic_block) ->
      match basic.terminator with
      | Resume { exits; _ } ->
          List.for_all
            (fun (exit : Mir.early_exit) ->
              List.for_all
                (fun (statement : Mir.statement) ->
                  match statement.kind with Dead locals -> not (List.mem part locals) | _ -> true)
                (block_at building exit.resume).statements)
            exits
      | _ -> true)
    building.blocks

let end_loop_parts building =
  for block = 0 to Dynarray.length building.blocks - 1 do
    match block_at building block with
    | { terminator = For { iteration = Pull _; part; blocks; loop; _ }; inlined = []; _ } ->
        let dead : Mir.statement = { kind = Dead [ part ]; origin = loop.origin } in
        List.iter
          (fun ending ->
            let basic = block_at building ending in
            set_block building ending { basic with statements = basic.statements @ [ dead ] })
          (own_iteration_ends building blocks);
        end_on_exits building ~blocks
          ~stays:(fun inner -> List.mem inner blocks)
          ~locals:[ part ] ~iteration:None ~origin:loop.origin
    | _ -> ()
  done

let rec inlined ~(resolve : Mir.callee -> callee option) ~enclosing (mir : Mir.t) : Mir.t =
  let lambdas = Dynarray.of_array mir.lambdas in
  let body = inlined_body ~resolve ~enclosing ~lambdas mir.body in
  for index = 0 to Array.length mir.lambdas - 1 do
    Dynarray.set lambdas index
      (inlined_body ~resolve ~enclosing ~lambdas (Dynarray.get lambdas index))
  done;
  { body; lambdas = Dynarray.to_array lambdas }

and inlined_body ~resolve ~enclosing ~lambdas (body : Mir.body) : Mir.body =
  let building =
    {
      locals = Dynarray.of_array body.locals;
      blocks = Dynarray.of_array body.blocks;
      lambdas;
      last_fork = -1;
    }
  in
  let pending = Queue.create () in
  let examine_from start =
    for block = start to Dynarray.length building.blocks - 1 do
      if (block_at building block).inlined = [] then Queue.add block pending
    done
  in
  examine_from 0;
  let is_recursive (callee : callee) = List.exists (Path.equal callee.path) enclosing in
  let prepared (callee : callee) =
    { callee with mir = inlined ~resolve ~enclosing:(callee.path :: enclosing) callee.mir }
  in
  while not (Queue.is_empty pending) do
    let at = Queue.pop pending in
    let basic = block_at building at in
    let lend =
      List.find_mapi
        (fun position (statement : Mir.statement) ->
          match statement.kind with
          | Lend { call = { callee = Intrinsic _; _ }; _ } -> None
          | Lend { part; call } when ends_only_in_statements building part -> (
              match resolve call.callee with
              | Some callee when not (is_recursive callee) ->
                  Some (position, part, call, prepared callee, statement.origin)
              | _ -> None)
          | _ -> None)
        basic.statements
    in
    let start = Dynarray.length building.blocks in
    match lend with
    | Some (position, part, call, callee, origin) ->
        inline_lend building ~body ~at ~position ~part ~callee ~call ~origin;
        join_regions building ~at ~start;
        examine_from start
    | None -> ()
  done;
  end_loop_parts building;
  {
    body with
    locals = Dynarray.to_array building.locals;
    blocks = Mir.canonical (Dynarray.to_array building.blocks);
  }
