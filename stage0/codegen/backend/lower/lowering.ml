type cleanup =
  | Drop_value of Lowered.place
  | Drop_flagged of { place : Lowered.place; flag : Lowered.place }
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
  site : Lowered.operand;
}

type lent_call = { mark : Lowered.place; record : Lowered.operand }

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
  mutable state : Moves.state;
  lending : lending option;
  called_parts : Mir.local list;
  lent_calls : (Mir.local, lent_call) Hashtbl.t;
  placed_parts : (Mir.local, unit) Hashtbl.t;
  mutable forwarded_locals : int;
  ended_after_lend : Mir.local list;
  after_lend : bool array;
  mutable block : Mir.Graph.block;
}

type task = { id : Mir.task; group : Lowered.place; end_block : Lowered.block; scope_depth : int }

type spawn_loop = {
  origin : Core.origin;
  group : Lowered.place;
  item : Lowered.local;
  element : Ground.ty;
}

type schedule = Sequential | Chunked | Spawned of spawn_loop
type result_slot = Through of Lowered.local | Returned_in of Lowered.local | No_result

type state = {
  context : Definitions.context;
  mutable frame : frame;
  builder : Emit_c.Builder.t;
  mutable scopes : scope list;
  mutable loops : loop list;
  mutable result : result_slot;
  nested : int ref;
  mutable evidence : (Path.t * Lowered.operand) list;
  mutable tasks : task list;
  mutable moved : Lowered.place list;
  mutable lend_record : Lowered.operand option;
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
    lend_record = None;
  }

let may_fork st = st.frame.exit = None
let checks_operations st = st.context.checks || Types.may_panic st.frame.code.uses

let allocate_local st ?name ty : Lowered.place =
  Lowered.make_local_place (Emit_c.Builder.allocate_local st.builder ?name ty)

let outline st ~parts body =
  let nested = !(st.nested) in
  incr st.nested;
  let enclosing = st.lend_record in
  st.lend_record <- None;
  let holder = Emit_c.Builder.outline st.builder ~index:nested ~parts body in
  st.lend_record <- enclosing;
  (nested, Lowered.Address { place = Lowered.make_local_place holder; writable = false })

let ground st ty = Monomorphic.ground st.context.monomorphic st.frame.code.substitution ty
let is_trivial st ty = Drop_and_copy.is_trivial st.context.drop_and_copy ty
let is_zero_size st = Memory_layout.has_zero_size st.context.env

let make_site st (span : Source.Definition_span.t) : Lowered.site =
  { definition = st.frame.code.definition; offset = span.start }

type unsupported = { construct : string; at : Lowered.site option }

exception Unsupported of unsupported

let raise_unsupported ?at format =
  Printf.ksprintf (fun construct -> raise (Unsupported { construct; at })) format

let require_written st =
  match st.frame.code.written with
  | Some written -> written
  | None ->
      Definitions.raise_bug "%s is generated code, which has no source"
        (Path.show st.frame.code.definition)

let quote_span st span = Source.Definition_span.quote (require_written st).text span

let rec lookup_binding_scope = function
  | ({ kind = Bindings; _ } as scope) :: _ -> scope
  | { kind = Statement; _ } :: rest -> lookup_binding_scope rest
  | [] -> Definitions.raise_bug "no scope"

let lookup_innermost_scope st =
  match st.scopes with scope :: _ -> scope | [] -> Definitions.raise_bug "no scope"

let move_place st place =
  if not (List.mem place st.moved) then st.moved <- place :: st.moved;
  Lowered.Move place

let own_in_scope st place =
  let scope = lookup_binding_scope st.scopes in
  scope.owned <- Drop_value place :: scope.owned

let allocate_owned_local st (scope : scope) ty =
  let place = Lowered.make_local_place (Emit_c.Builder.allocate_local st.builder (Value ty)) in
  if not (is_trivial st ty) then scope.owned <- Drop_value place :: scope.owned;
  place

let allocate_temporary st ty = allocate_owned_local st (lookup_innermost_scope st) ty
let allocate_binding st ty = allocate_owned_local st (lookup_binding_scope st.scopes) ty

let allocate_flagged_binding st ty ~flag =
  let place = Lowered.make_local_place (Emit_c.Builder.allocate_local st.builder (Value ty)) in
  if not (is_trivial st ty) then begin
    let scope = lookup_binding_scope st.scopes in
    scope.owned <- Drop_flagged { place; flag } :: scope.owned
  end;
  place

let allocate_parameter st ?(in_scope = true) ?name ~owned (mode : Ground.mode) ty =
  let own place = if in_scope && owned && not (is_trivial st ty) then own_in_scope st place in
  match Convention.classify_parameter st.context.env mode ty with
  | None -> (None, allocate_temporary st ty)
  | Some (Lowered.Pointer _ as pointer) ->
      let arrives = Emit_c.Builder.allocate_local st.builder ?name pointer in
      let place : Lowered.place = { root = Local arrives; projections = [ Deref ] } in
      own place;
      (Some arrives, place)
  | Some passed ->
      let arrives = Emit_c.Builder.allocate_local st.builder ?name passed in
      own (Lowered.make_local_place arrives);
      (Some arrives, Lowered.make_local_place arrives)

let list_evidence_parameters st capabilities =
  let arriving =
    List.map
      (fun capability -> (capability, Emit_c.Builder.allocate_local st.builder Convention.evidence))
      capabilities
  in
  st.evidence <-
    List.map
      (fun (capability, evidence_local) ->
        (capability, Lowered.Copy (Lowered.make_local_place evidence_local)))
      arriving;
  List.map snd arriving

let start_trace st = st.evidence <- (Definitions.panic_path, Lowered.Constant Null) :: st.evidence

let find_panic_trace st =
  Option.map snd
    (List.find_opt
       (fun (capability, _) -> Path.equal capability Definitions.panic_path)
       st.evidence)

let set_result_slot st (convention : Convention.result) =
  st.result <-
    (match convention with
    | Through_pointer pointer -> Through (Emit_c.Builder.allocate_local st.builder pointer)
    | Returned ty -> Returned_in (Emit_c.Builder.allocate_local st.builder ty)
    | Nothing -> No_result)

let find_result_place st : Lowered.place option =
  match st.result with
  | Through pointer -> Some { root = Local pointer; projections = [ Deref ] }
  | Returned_in local -> Some (Lowered.make_local_place local)
  | No_result -> None

let return_result st : Lowered.terminator =
  Return
    (match st.result with
    | Returned_in local -> Some (Move (Lowered.make_local_place local))
    | _ -> None)

let drop_scope st (scope : scope) =
  List.iter
    (function
      | Drop_value place ->
          if not (List.mem place st.moved) then Emit_c.Builder.emit st.builder (Drop place)
      | Drop_flagged { place; flag } ->
          if not (List.mem place st.moved) then
            Emit_c.Builder.emit_when st.builder (Copy flag) (fun () ->
                Emit_c.Builder.emit st.builder (Drop place))
      | Free_pointed pointer ->
          Emit_c.Builder.emit st.builder
            (Call { target = Intrinsic Free; arguments = [ Copy pointer ]; result = Discarded })
      | Join_group join -> Emit_c.Builder.emit st.builder join)
    scope.owned

let leave_to st depth =
  List.iteri
    (fun position scope -> if List.length st.scopes - position > depth then drop_scope st scope)
    st.scopes

let open_scope st kind =
  let scope = { kind; owned = [] } in
  st.scopes <- scope :: st.scopes;
  scope

let pop_scope st scope =
  match st.scopes with
  | top :: rest when top == scope -> st.scopes <- rest
  | _ -> Definitions.raise_bug "a scope closed out of order"

let close_scope st scope =
  drop_scope st scope;
  pop_scope st scope

let with_scope st kind body =
  let scope = open_scope st kind in
  let result = body () in
  close_scope st scope;
  result

let run_in_scope st body = with_scope st Bindings body
let run_in_statement st body = with_scope st Statement body

let finish_function st ?(returns = true) ~first ~rest () : Emit_c.Builder.prototype =
  (match st.scopes with
  | [ scope ] -> drop_scope st scope
  | _ -> Definitions.raise_bug "a function ended in a scope");
  Emit_c.Builder.finish st.builder (if returns then return_result st else Unreachable);
  let pointer = match st.result with Through pointer -> Some pointer | _ -> None in
  let result =
    match st.result with
    | Returned_in local -> Some (Emit_c.Builder.lookup_local_type st.builder local)
    | _ -> None
  in
  { parameters = first @ Option.to_list pointer @ rest; result; returns }

let finish_item st ?returns ~rest () =
  Emit_c.Builder.build st.builder (finish_function st ?returns ~first:[] ~rest ())

let emit_unreachable_block st =
  Emit_c.Builder.finish st.builder Unreachable;
  Emit_c.Builder.start st.builder (Emit_c.Builder.allocate_block st.builder)

let make_owned_operand st place ty =
  if is_trivial st ty then Lowered.Copy place else move_place st place

let take st (place : Lowered.place) ty ~destination =
  match place.root with
  | Static _ when not (is_trivial st ty) ->
      Drop_and_copy.copy_into st.context.drop_and_copy st.builder ~destination ~source:place ty
  | Static _ | Local _ ->
      Emit_c.Builder.emit st.builder (Assign (destination, Use (make_owned_operand st place ty)))

let snapshot st (place : Lowered.place) =
  {
    place with
    projections =
      List.map
        (function
          | Lowered.Index (Copy index_place) ->
              let fixed = allocate_binding st st.context.types.uint64 in
              Emit_c.Builder.emit st.builder (Assign (fixed, Use (Copy index_place)));
              Lowered.Index (Copy fixed)
          | projection -> projection)
        place.projections;
  }

let run_in_loop st ~continue_ ~break_ ~depth body =
  st.loops <- { continue_; continue_depth = depth; break_; break_depth = depth } :: st.loops;
  body ();
  st.loops <- List.tl st.loops

let find_place_type st (place : Lowered.place) =
  let raise_environment_place _ =
    Definitions.raise_bug "a place in an environment, whose type lowering does not track"
  in
  let rec find_projected_type (ty : Lowered.ty) = function
    | [] -> Some ty
    | _ :: _ when match ty with Environment _ | Evidence _ -> true | _ -> false -> None
    | projection :: rest ->
        Option.bind
          (Lowered.find_projection_type st.context.env ~list_environment:raise_environment_place ty
             projection) (fun ty -> find_projected_type ty rest)
  in
  match place with
  | _ ->
      let root : Lowered.ty =
        match place.root with
        | Local local -> Emit_c.Builder.lookup_local_type st.builder local
        | Static { ty; _ } -> Value ty
      in
      if Lowered.is_erased st.context.env root then None
      else find_projected_type root place.projections

let make_int_constant integer value = Lowered.Constant (Integer (integer, value))

let classify_scalar st ty =
  match (Memory_layout.of_type st.context.env ty).form with
  | Scalar scalar -> scalar
  | _ -> Definitions.raise_bug "%s is not a number" (Ground.to_string ty)
