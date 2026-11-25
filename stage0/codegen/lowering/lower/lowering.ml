type cleanup =
  | Drop_value of Lowered.place
  | Free_pointed of Lowered.place
  | Join_group of Lowered.statement

type scope_kind = Bindings | Statement
type scope = { kind : scope_kind; mutable owned : cleanup list }

type loop = {
  continue_ : Lowered.block;
  continue_depth : int;
  break_ : Lowered.block;
  break_depth : int;
}

type lending = {
  slot : Lowered.place option;
  part : Ground.ty;
  record : Lowered.operand;
  arena : Lowered.operand;
  site : Lowered.operand;
}

type frame = {
  code : Definitions.code;
  mutable self_place : Lowered.place option;
  exit : (Lowered.block * int) option;
  mir : mir_frame option;
}

and mir_frame = {
  body : Mir.Graph.body;
  lambdas : Mir.Graph.body array;
  places : (Mir.local, Lowered.place) Hashtbl.t;
  owner : scope option;
  returns_into : Lowered.place option;
  mutable provides : (Path.t * Lowered.operand) list list;
  returned : Mir.local list;
  mutable taken : Mir.place list;
  moves : Moves.t;
  flags : (Moves.path * Lowered.place) list;
  mutable move_state : Moves.state;
  mutable move_state_at_return : Moves.state option;
  applied_defaults : (Mir.local, applied_default) Hashtbl.t;
  lending : lending option;
  called_parts : Mir.local list;
  lend_records : (Mir.local, Lowered.place) Hashtbl.t;
  placed_parts : (Mir.local, unit) Hashtbl.t;
  mutable forwarded_locals : int;
  ended_after_lend : Mir.local list;
  after_lend : bool array;
  mutable block : Mir.Graph.block;
}

and applied_default = { default_frame : frame; is_applied : Lowered.place }

type task = { id : Mir.task; group : Lowered.place; end_block : Lowered.block; scope_depth : int }

type spawn_loop = {
  task : Mir.task;
  group : Lowered.place;
  item : Lowered.local;
  element : Ground.ty;
}

type schedule = Sequential | Chunked | Spawned of spawn_loop
type result_slot = Through of Lowered.local | Returned_in of Lowered.local | No_result

type state = {
  context : Definitions.context;
  mutable frame : frame;
  builder : Emit_c.Ir_builder.t;
  mutable scopes : scope list;
  mutable loops : loop list;
  mutable result : result_slot;
  nested : int ref;
  mutable evidence : (Path.t * Lowered.operand) list;
  mutable tasks : task list;
  mutable moved : Lowered.place list;
  mutable lend_arena : Lowered.operand option;
}

let make_frame code = { code; self_place = None; exit = None; mir = None }

let enter context ?(nested = ref 0) ~builder frame =
  {
    context;
    frame;
    builder;
    scopes = [ { kind = Bindings; owned = [] } ];
    loops = [];
    result = No_result;
    nested;
    evidence = [];
    tasks = [];
    moved = [];
    lend_arena = None;
  }

let enter_item context ~item (code : Definitions.code) =
  let site =
    Option.map (fun _ : Lowered.site -> { definition = code.definition; offset = 0 }) code.written
  in
  enter context ~builder:(Emit_c.Ir_builder.create ?site context.env ~item) (make_frame code)

let may_fork state = state.frame.exit = None

let allocate_local state ?name ty : Lowered.place =
  Lowered.make_local_place (Emit_c.Ir_builder.allocate_local state.builder ?name ty)

let outline state ~parts body =
  let nested = !(state.nested) in
  incr state.nested;
  let enclosing = state.lend_arena in
  state.lend_arena <- None;
  let holder = Emit_c.Ir_builder.outline state.builder ~index:nested ~parts body in
  state.lend_arena <- enclosing;
  (nested, Lowered.Address { place = Lowered.make_local_place holder; writable = false })

let ground state ty = Monomorphic.ground state.context.monomorphic state.frame.code.substitution ty
let is_trivial state ty = Drop_and_copy.is_trivial state.context.drop_and_copy ty
let is_zero_size state = Memory_layout.has_zero_size state.context.env

let make_site state (span : Source.Definition_span.t) : Lowered.site =
  { definition = state.frame.code.definition; offset = span.start }

type unsupported = { construct : string; at : Lowered.site option }

exception Unsupported of unsupported

let raise_unsupported ?at format =
  Printf.ksprintf (fun construct -> raise (Unsupported { construct; at })) format

let require_written state =
  match state.frame.code.written with
  | Some written -> written
  | None ->
      Definitions.raise_bug "%s is generated code, which has no source"
        (Path.show state.frame.code.definition)

let quote_span state span = Source.Definition_span.quote (require_written state).text span

let rec lookup_binding_scope = function
  | ({ kind = Bindings; _ } as scope) :: _ -> scope
  | { kind = Statement; _ } :: rest -> lookup_binding_scope rest
  | [] -> Definitions.raise_bug "no scope"

let lookup_innermost_scope state =
  match state.scopes with scope :: _ -> scope | [] -> Definitions.raise_bug "no scope"

let move_place state place =
  if not (List.mem place state.moved) then state.moved <- place :: state.moved;
  Lowered.Move place

let own_in_scope state place =
  let scope = lookup_binding_scope state.scopes in
  scope.owned <- Drop_value place :: scope.owned

let allocate_owned_local state (scope : scope) ty =
  let place =
    Lowered.make_local_place (Emit_c.Ir_builder.allocate_local state.builder (Value ty))
  in
  if not (is_trivial state ty) then scope.owned <- Drop_value place :: scope.owned;
  place

let allocate_temporary state ty = allocate_owned_local state (lookup_innermost_scope state) ty
let allocate_binding state ty = allocate_owned_local state (lookup_binding_scope state.scopes) ty

let allocate_parameter state ?(in_scope = true) ?name ~owned (mode : Language.Mode.t) ty =
  let own place = if in_scope && owned && not (is_trivial state ty) then own_in_scope state place in
  match Convention.classify_parameter state.context.env mode ty with
  | None -> (None, allocate_temporary state ty)
  | Some (Lowered.Pointer _ as pointer) ->
      let arrives = Emit_c.Ir_builder.allocate_local state.builder ?name pointer in
      let place = Lowered.make_deref_place arrives in
      own place;
      (Some arrives, place)
  | Some passed ->
      let arrives = Emit_c.Ir_builder.allocate_local state.builder ?name passed in
      own (Lowered.make_local_place arrives);
      (Some arrives, Lowered.make_local_place arrives)

let list_evidence_parameters state capabilities =
  let arriving =
    List.map
      (fun capability ->
        (capability, Emit_c.Ir_builder.allocate_local state.builder Convention.evidence))
      capabilities
  in
  state.evidence <-
    List.map
      (fun (capability, evidence_local) ->
        (capability, Lowered.Copy (Lowered.make_local_place evidence_local)))
      arriving;
  List.map snd arriving

let look_up_capabilities state ~table capabilities =
  state.evidence <-
    List.map
      (fun capability ->
        let evidence = Emit_c.Ir_builder.allocate_local state.builder Convention.evidence in
        Emit_c.Ir_builder.emit state.builder
          (Call
             {
               target = Intrinsic Capability_find;
               arguments = [ table; Constant (Capability capability) ];
               result = Returned (Lowered.make_local_place evidence);
             });
        (capability, Lowered.Copy (Lowered.make_local_place evidence)))
      capabilities

let find_panic_trace state =
  Option.map snd
    (List.find_opt
       (fun (capability, _) -> Path.equal capability Definitions.panic_path)
       state.evidence)

let set_result_slot state (convention : Convention.result) =
  state.result <-
    (match convention with
    | Through_pointer pointer -> Through (Emit_c.Ir_builder.allocate_local state.builder pointer)
    | Returned ty -> Returned_in (Emit_c.Ir_builder.allocate_local state.builder ty)
    | Nothing -> No_result)

let find_result_place state : Lowered.place option =
  match state.result with
  | Through pointer -> Some (Lowered.make_deref_place pointer)
  | Returned_in local -> Some (Lowered.make_local_place local)
  | No_result -> None

let return_result state : Lowered.terminator =
  Return
    (match state.result with
    | Returned_in local -> Some (Move (Lowered.make_local_place local))
    | _ -> None)

let drop_scope state (scope : scope) =
  List.iter
    (function
      | Drop_value place ->
          if not (List.mem place state.moved) then Emit_c.Ir_builder.emit state.builder (Drop place)
      | Free_pointed pointer ->
          Emit_c.Ir_builder.emit state.builder
            (Call { target = Intrinsic Free; arguments = [ Copy pointer ]; result = Discarded })
      | Join_group join -> Emit_c.Ir_builder.emit state.builder join)
    scope.owned

let leave_to state depth =
  List.iteri
    (fun position scope ->
      if List.length state.scopes - position > depth then drop_scope state scope)
    state.scopes

let open_scope state kind =
  let scope = { kind; owned = [] } in
  state.scopes <- scope :: state.scopes;
  scope

let pop_scope state scope =
  match state.scopes with
  | top :: rest when top == scope -> state.scopes <- rest
  | _ -> Definitions.raise_bug "a scope closed out of order"

let close_scope state scope =
  drop_scope state scope;
  pop_scope state scope

let with_scope state kind body =
  let scope = open_scope state kind in
  let result = body () in
  close_scope state scope;
  result

let run_in_scope state body = with_scope state Bindings body
let run_in_statement state body = with_scope state Statement body

let finish_function state ?(returns = true) ~first ~rest () : Emit_c.Ir_builder.prototype =
  (match state.scopes with
  | [ scope ] -> drop_scope state scope
  | _ -> Definitions.raise_bug "a function ended in a scope");
  Emit_c.Ir_builder.finish state.builder (if returns then return_result state else Unreachable);
  let pointer = match state.result with Through pointer -> Some pointer | _ -> None in
  let result =
    match state.result with
    | Returned_in local -> Some (Emit_c.Ir_builder.lookup_local_type state.builder local)
    | _ -> None
  in
  { parameters = first @ Option.to_list pointer @ rest; result; returns }

let finish_item state ?returns ~rest () =
  Emit_c.Ir_builder.build state.builder (finish_function state ?returns ~first:[] ~rest ())

let emit_unreachable_block state =
  Emit_c.Ir_builder.finish state.builder Unreachable;
  Emit_c.Ir_builder.start state.builder (Emit_c.Ir_builder.allocate_block state.builder)

let make_owned_operand state place ty =
  if is_trivial state ty then Lowered.Copy place else move_place state place

let take state (place : Lowered.place) ty ~destination =
  match place.root with
  | Static _ when not (is_trivial state ty) ->
      Drop_and_copy.copy_into state.context.drop_and_copy state.builder ~destination ~source:place
        ty
  | Static _ | Local _ ->
      Emit_c.Ir_builder.emit state.builder
        (Assign (destination, Use (make_owned_operand state place ty)))

let snapshot state (place : Lowered.place) =
  {
    place with
    projections =
      List.map
        (function
          | Lowered.Index (Copy index_place) ->
              let fixed = allocate_binding state state.context.types.uint64 in
              Emit_c.Ir_builder.emit state.builder (Assign (fixed, Use (Copy index_place)));
              Lowered.Index (Copy fixed)
          | projection -> projection)
        place.projections;
  }

let run_in_loop state ~continue_ ~break_ ~depth body =
  state.loops <- { continue_; continue_depth = depth; break_; break_depth = depth } :: state.loops;
  body ();
  state.loops <- List.tl state.loops

let find_place_type state (place : Lowered.place) =
  let raise_environment_place _ =
    Definitions.raise_bug "a place in an environment, whose type lowering does not track"
  in
  let rec find_projected_type (ty : Lowered.ty) = function
    | [] -> Some ty
    | _ :: _ when match ty with Environment _ | Evidence _ -> true | _ -> false -> None
    | projection :: rest ->
        Option.bind
          (Lowered.find_projection_type state.context.env ~list_environment:raise_environment_place
             ty projection) (fun ty -> find_projected_type ty rest)
  in
  match place with
  | _ ->
      let root : Lowered.ty =
        match place.root with
        | Local local -> Emit_c.Ir_builder.lookup_local_type state.builder local
        | Static { ty; _ } -> Value ty
      in
      if Lowered.is_erased state.context.env root then None
      else find_projected_type root place.projections

let is_reached_through_pointer state (place : Lowered.place) =
  let rec walk (ty : Lowered.ty) (projections : Lowered.projection list) =
    match (projections, ty) with
    | [], _ -> false
    | Deref :: _, _ -> true
    | Index _ :: _, Raw (Pointer _ | Nullable_pointer _) -> true
    | _ :: _, (Environment _ | Evidence _) ->
        List.exists (function Lowered.Deref -> true | _ -> false) projections
    | projection :: rest, _ -> (
        match
          Lowered.find_projection_type state.context.env
            ~list_environment:(fun _ ->
              Definitions.raise_bug "a place in an environment, whose type lowering does not track")
            ty projection
        with
        | Some projected -> walk projected rest
        | None -> false)
  in
  match place.root with
  | Static _ -> true
  | Local local -> walk (Emit_c.Ir_builder.lookup_local_type state.builder local) place.projections

let make_int_constant integer value = Lowered.Constant (Integer (integer, value))

let classify_scalar state ty =
  match (Memory_layout.of_type state.context.env ty).form with
  | Scalar scalar -> scalar
  | _ -> Definitions.raise_bug "%s is not a number" (Ground.to_string ty)
