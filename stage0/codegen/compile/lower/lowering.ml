(* The state of lowering one function: its frame, scopes, loops, and
   temporaries, and the small helpers every part of lowering shares. *)

open Definitions
open Emit_c.Builder

type cleanup =
  | Drop_value of Lowered.place  (** Drops the place's value, if the place still owns it. *)
  | Free_pointed of Lowered.place
      (** Frees the heap block that the pointer at the place points to, after the block's contents
          are dropped. *)
  | Free_blocks of { place : Lowered.place; variants : string list }
      (** Frees the block of the value at [place] where its variant is one of [variants], without
          dropping the block's contents. *)
  | Write_back of { destination : Lowered.place; source : Lowered.place; ty : Ground.ty }
      (** Moves the value at [source] into [destination], the place it was moved out of so that the
          caller could change it. *)
  | Join_group of Lowered.statement  (** Joins a task group with the call of [Tasks.join]. *)

(* A scope owns the values dropped as it ends: the scope of a block's names,
   or the scope of one statement, whose temporaries end with it. *)
type scope_kind = Bindings | Statement
type scope = { kind : scope_kind; mutable owned : cleanup list  (** Most recent first *) }

(* Where [continue] and [break] go, and how many scopes each keeps. *)
type loop = {
  continue_ : Lowered.block;
  continue_depth : int;
  break_ : Lowered.block;
  break_depth : int;
}

(* The code being lowered: the function's own, or a method's inlined into
   it, whose blocks carry it, each with its own tables and names. *)
type frame = {
  code : code;
  mutable self_place : Lowered.place option;
  inlined : Path.t list;
      (** The code's own method and those it is inlined into, whose cursors the code boxes *)
  reported : Lowered.site option;
      (** In the standard library's code that is inlined into a program's, the position of the
          program's call, where a check that fails in this code is reported *)
  exit : (Lowered.block * int) option;
      (** In an expression lowered on its own, where its [return] goes and how many scopes that
          keeps *)
  mir : mir_frame option;  (** The MIR being lowered in this frame *)
}

(* A body of the MIR being lowered, with the place of each of its locals. *)
and mir_frame = {
  body : Mir.body;
  lambdas : Mir.body array;  (** The bodies of the definition's lambdas *)
  places : (Mir.local, Lowered.place) Hashtbl.t;
  owner : scope option;
      (** The scope that owns the body's locals, which drops them on each way out *)
  returns_into : Lowered.place option;
      (** In an expression lowered on its own, such as a default, where its value is written *)
  mutable provides : (Path.t * Lowered.operand) list list;
      (** The evidence that each [provide] around the code being lowered replaced, innermost first
      *)
  returned : Mir.local list;
      (** The temporaries that a [return] returns, which are the result's slot where the function
          has one, so that the value is written before the [return] leaves its scopes *)
  mutable taken : Mir.place list;
      (** The targets of compound assignments whose old value an operator has taken, which hold
          nothing until they are assigned again *)
  moves : Moves.t;  (** Which places may hold a value at each point *)
  kept : Mir.local list;  (** In a pulled method, the locals its cursor holds *)
  flags : (Moves.path * Lowered.place) list;
      (** The [Bool] local that says whether each flagged path holds a value *)
  mutable state : Moves.state;  (** What may hold a value where the code being lowered is *)
}

(* The early exits of the tasks of one [concurrent] block or loop. An
   early exit is a [return], [break], or [continue] that leaves a task
   before its end. The task calls [Tasks.cancel] on its group, and the
   first task to cancel wins: it stores its exit's number, counted from 1
   in [exits], in [winner], and the value of a [return] in [return_value].
   The code that joins the group then switches on [winner] and performs
   that exit. Each branch of a block has its own record, because each
   branch is a separate region. The iterations of a loop share one. *)
type early_exits = {
  winner : Lowered.place;  (** A [UInt32], 0 while no exit has won *)
  mutable return_value : Lowered.place option;
  scope : scope;  (** The scope enclosing the block or loop, which owns [return_value] *)
  mutable exits : early_exit list;  (** Most recent first *)
}

(* An early exit that a task of a group took, which the code that joins
   the group performs. *)
and early_exit = {
  ends : Mir.statement list;
      (** The ends of the scopes between the task and the next task or the exit's target *)
  remaining : (Core.task * Mir.statement list) list;
      (** The enclosing tasks that the exit has yet to end, innermost first *)
  exit : Mir.task_exit;
  state : Moves.state;  (** What may hold a value where the exit was taken *)
}

(* A task whose body is being lowered. *)
type task = {
  id : Core.task;
  group : Lowered.place;
  early_exits : early_exits;
  end_block : Lowered.block;  (** Every exit from the task jumps here *)
  scope_depth : int;  (** The number of scopes enclosing the task *)
}

(* A [concurrent for] loop whose iterations are being spawned. *)
type spawn_loop = {
  origin : Core.origin;
  group : Lowered.place;
  early_exits : early_exits;
  item : Lowered.local;  (** A [UInt64]: the argument of the next task *)
  element : Ground.ty;  (** The type of the value that the loop's pattern matches *)
}

(* The cursor of a pulled method: [next] keeps in it the values it needs
   from one call to the next, and its drop function drops them. *)
type cursor = {
  pointer : Lowered.local;  (** [next]'s parameter, and the drop function's, that points to it *)
  drop : Emit_c.Builder.separate;  (** The cursor's drop function *)
  fields : (string * Lowered.ty) list ref;  (** Its fields but its state, most recent first *)
  mutable resumes : Lowered.block list;
      (** Where [next] goes on in each state after the first, most recent first *)
  mutable stops : Lowered.block list;
      (** Where the drop function starts in each state after the first, most recent first *)
}

(* How the iterations of a loop run: one after another, as chunks of a
   range on several threads, or each as a spawned task. *)
type schedule = Sequential | Chunked | Spawned of spawn_loop

(* Where a function's result goes: through the pointer it is given, into a
   local it returns, or nowhere. *)
type result_slot = Through of Lowered.local | Returned_in of Lowered.local | No_result

type state = {
  context : context;
  mutable frame : frame;
  builder : Emit_c.Builder.t;
  mutable scopes : scope list;  (** Innermost first *)
  mutable loops : loop list;
  mutable result : result_slot;
  nested : int ref;  (** How many nested functions, lambdas and outlined code, the instance has *)
  mutable evidence : (Path.t * Lowered.operand) list;
      (** The evidence for each capability available *)
  cursor : cursor option;
      (** In a yielding method's pulled version, the cursor it keeps values in *)
  mutable tasks : task list;  (** The tasks around the code being lowered, innermost first *)
  mutable moved : Lowered.place list;
      (** The places of locals that lowering owns, other than the MIR's, that its code has moved out
          of, so that the scope that owns one drops it only if it holds a value *)
}

(* The code a function starts lowering: its own, with nothing bound yet. *)
let frame_of code ~inlined =
  { code; self_place = None; inlined; reported = None; exit = None; mir = None }

(* The state to write one function in, with [builder], and the function's
   scope. A lambda shares [nested] with the function around it. *)
let enter context ?cursor ?(nested = ref 0) ~builder frame =
  {
    context;
    frame;
    builder;
    scopes = [ { kind = Bindings; owned = [] } ];
    loops = [];
    result = No_result;
    nested;
    evidence = [];
    cursor;
    tasks = [];
    moved = [];
  }

(* Whether a [parallel] statement's parts are outlined here, as functions
   of their own that the runtime may run at the same time.
   They are not in a method's pulled version, whose code is a state
   machine, nor in an expression lowered on its own, whose [return] leaves
   to its end, and a region has one way out. *)
let may_fork st = st.cursor = None && st.frame.exit = None

(* A field of the cursor, with the place it is at. *)
let cursor_field (cursor : cursor) name ty : Lowered.place =
  if not (List.mem_assoc name !(cursor.fields)) then cursor.fields := (name, ty) :: !(cursor.fields);
  { root = Local cursor.pointer; projections = [ Deref; Field name ] }

(* A place that holds a value [kept] across a [yield]: a new field of the
   cursor in a pulled method, or else a new local. *)
let held st ~kept ?name ty : Lowered.place =
  match st.cursor with
  | Some cursor when kept ->
      cursor_field cursor (Printf.sprintf "held%d" (List.length !(cursor.fields))) ty
  | _ -> at (local st.builder ?name ty)

(* Writes code with [body] as an outlined function, nested in the instance,
   given [parts] as its parameters. Gives the function's number and the
   operand for its environment. *)
let outlined st ~parts body =
  let nested = !(st.nested) in
  incr st.nested;
  let holder = Emit_c.Builder.outline st.builder ~nested ~parts body in
  (nested, Lowered.Address { place = at holder; writable = false })

(* A record for the early exits of a block's branch or a loop's
   iterations. The current scope owns the return value, so the value
   outlives the tasks. *)
let new_early_exits st =
  let winner = at (local st.builder ~name:"winner" (Raw (Integer UInt32))) in
  emit st.builder (Assign (winner, Use (Constant (Integer (UInt32, Z.zero)))));
  { winner; return_value = None; scope = List.hd st.scopes; exits = [] }

let ground st ty = Monomorphic.ground st.context.monomorphic st.frame.code.substitution ty
let trivial st ty = Glue.trivial st.context.glue ty
let is_zero_size st = Memory_layout.has_zero_size st.context.env

let site st (span : Syntax.span) : Lowered.site =
  let text = st.frame.code.text in
  let line = ref 0 and column = ref 1 in
  String.iteri
    (fun position capability ->
      if position < span.start then
        if capability = '\n' then begin
          incr line;
          column := 1
        end
        else incr column)
    text;
  { definition = st.frame.code.anchor; line = !line; column = !column }

type unsupported = { construct : string; at : Lowered.site option }

exception Unsupported of unsupported

let unsupported ?at format =
  Printf.ksprintf (fun construct -> raise (Unsupported { construct; at })) format

let source st (span : Syntax.span) =
  let text = st.frame.code.text in
  let start = min span.start (String.length text) in
  String.sub text start (min span.stop (String.length text) - start)

(* The scope a new name belongs to: the innermost that holds names. *)
let rec binding_scope = function
  | ({ kind = Bindings; _ } as scope) :: _ -> scope
  | { kind = Statement; _ } :: rest -> binding_scope rest
  | [] -> bug "no scope"

let innermost_scope st = match st.scopes with scope :: _ -> scope | [] -> bug "no scope"

(* A move out of a place, which the scope that owns the place, if lowering
   owns it, then does not drop. *)
let moved st place =
  if not (List.mem place st.moved) then st.moved <- place :: st.moved;
  Lowered.Move place

(* Has the scope of the names around own the value at a place. *)
let own_in_scope st place =
  let scope = binding_scope st.scopes in
  scope.owned <- Drop_value place :: scope.owned

(* A new local for a value, owned from the start, so that every way out of
   its owner drops whatever it still holds, and nothing it is given can be
   forgotten. A type with nothing to drop needs no owner. *)
let owned_local st ?name (scope : scope) ty =
  let place = at (local st.builder ?name (Value ty)) in
  if not (trivial st ty) then scope.owned <- Drop_value place :: scope.owned;
  place

(* A local that lasts for the statement being lowered, or for the scope
   around when no statement is. *)
let temporary st ?name ty = owned_local st ?name (innermost_scope st) ty

(* A local that lasts as long as the names around it. *)
let binding st ?name ty = owned_local st ?name (binding_scope st.scopes) ty

(* A parameter of the function being written, as the calling convention
   passes it, or as [how] does: the local it arrives in, unless it has no
   size, and the place its value is read at. The function owns it when
   [owned], and the scope around drops it unless [in_scope] is false;
   otherwise it is the caller's. *)
let parameter st ?how ?(in_scope = true) ~owned (mode : Ground.mode) ty =
  let how = Option.value how ~default:(Convention.parameter st.context.env) in
  let own place = if in_scope && owned && not (trivial st ty) then own_in_scope st place in
  match how mode ty with
  | None -> (None, temporary st ty)
  | Some (Lowered.Pointer _ as pointer) ->
      let arrives = local st.builder pointer in
      let place : Lowered.place = { root = Local arrives; projections = [ Deref ] } in
      own place;
      (Some arrives, place)
  | Some passed ->
      let arrives = local st.builder passed in
      own (at arrives);
      (Some arrives, at arrives)

(* A parameter for the evidence of each capability, which the code then
   reaches by it. Gives the parameters, in order. *)
let evidence_parameters st capabilities =
  let arriving =
    List.map
      (fun capability -> (capability, local st.builder ~name:"evidence" Convention.evidence))
      capabilities
  in
  st.evidence <-
    List.map
      (fun (capability, evidence_local) -> (capability, Lowered.Copy (at evidence_local)))
      arriving;
  List.map snd arriving

(* Makes the slot for the function's result, as the convention passes one.
   Nothing here owns it: it is the caller's once the function returns. *)
let result_slot st (convention : Convention.result) =
  st.result <-
    (match convention with
    | Through_pointer pointer -> Through (local st.builder ~name:"result" pointer)
    | Returned ty -> Returned_in (local st.builder ~name:"result" ty)
    | Nothing -> No_result)

(* Where the function's result is written, if it has one with a size. *)
let result_place st : Lowered.place option =
  match st.result with
  | Through pointer -> Some { root = Local pointer; projections = [ Deref ] }
  | Returned_in local -> Some (at local)
  | No_result -> None

(* The type of the function's result, if it has one with a size. *)
let returned_type st =
  match st.result with
  | Through slot | Returned_in slot -> (
      match local_type st.builder slot with
      | Value ty | Pointer { target = Value ty; _ } -> Some ty
      | _ -> None)
  | No_result -> None

let return_result st : Lowered.terminator =
  Return (match st.result with Returned_in local -> Some (Move (at local)) | _ -> None)

let drop_scope st (scope : scope) =
  List.iter
    (function
      | Drop_value place -> if not (List.mem place st.moved) then emit st.builder (Drop place)
      | Free_pointed pointer ->
          emit st.builder
            (Call { target = Intrinsic Free; arguments = [ Copy pointer ]; result = Discarded })
      | Free_blocks { place; variants } ->
          let after = block st.builder in
          let cases =
            List.map
              (fun variant ->
                let case = block st.builder in
                in_block st.builder case (fun () ->
                    emit st.builder (Free_block { place; variant });
                    finish st.builder (Goto after));
                (variant, case))
              variants
          in
          finish st.builder (Switch_variant { place; cases; default = Some after });
          start st.builder after
      | Write_back { destination; source; ty } ->
          emit st.builder
            (Assign (destination, Use (if trivial st ty then Copy source else moved st source)))
      | Join_group join -> emit st.builder join)
    scope.owned

(* Drops everything owned in the scopes inside the [depth] outermost, as a
   [return], [break], or [continue] leaves them. *)
let leave_to st depth =
  List.iteri
    (fun position scope -> if List.length st.scopes - position > depth then drop_scope st scope)
    st.scopes

(* A scope opened here and ended by [close_scope], with its drops, or by
   [pop_scope], whose caller writes the drops on each path the scope ends
   on. *)
let open_scope st kind =
  let scope = { kind; owned = [] } in
  st.scopes <- scope :: st.scopes;
  scope

let pop_scope st scope =
  match st.scopes with
  | top :: rest when top == scope -> st.scopes <- rest
  | _ -> bug "a scope closed out of order"

let close_scope st scope =
  drop_scope st scope;
  pop_scope st scope

let with_scope st kind body =
  let scope = open_scope st kind in
  let result = body () in
  close_scope st scope;
  result

let in_scope st body = with_scope st Bindings body
let in_statement st body = with_scope st Statement body

(* Ends the function being written: its scope's remaining values are dropped
   and its result returned. Its parameters are [first], which it is given
   before anything else, the pointer its result is written through, if it
   has one, and [rest]. *)
let finish_function st ?(returns = true) ~first ~rest () =
  (match st.scopes with [ scope ] -> drop_scope st scope | _ -> bug "a function ended in a scope");
  finish st.builder (if returns then return_result st else Unreachable);
  let pointer = match st.result with Through pointer -> Some pointer | _ -> None in
  let result =
    match st.result with Returned_in local -> Some (local_type st.builder local) | _ -> None
  in
  build st.builder ~returns ~parameters:(first @ Option.to_list pointer @ rest) ~result

(* The instance written: its function, which [finish_function] ends with
   [rest] as its parameters, and the nested functions it made. *)
let finish_instance st ?returns ~rest () =
  finish_function st ?returns ~first:[] ~rest ();
  built st.builder

let unreachable_block st =
  finish st.builder Unreachable;
  start st.builder (block st.builder)

(* An operand for an owned position: a [var], an [own] argument, a field, a
   returned value. The type checker has made sure a place there is a
   temporary or was marked [own], or copies implicitly. *)
let owned st place ty = if trivial st ty then Lowered.Copy place else moved st place

(* Gives [destination], which holds nothing, the value at a place as its
   own: moved out of the place, or for a constant's static data, which
   nothing moves from, copied. *)
let take st (place : Lowered.place) ty ~destination =
  match place.root with
  | Static _ when not (trivial st ty) ->
      Glue.copy_into st.context.glue st.builder ~destination ~source:place ty
  | Static _ | Local _ -> emit st.builder (Assign (destination, Use (owned st place ty)))

(* A place whose indexes are fixed now, so that an alias of it refers to the
   same element however the index variables change later. *)
let snapshot st ~kept (place : Lowered.place) =
  {
    place with
    projections =
      List.map
        (function
          | Lowered.Index (Copy index_place) ->
              let fixed =
                if kept then held st ~kept (Value st.context.types.usize)
                else binding st st.context.types.usize
              in
              emit st.builder (Assign (fixed, Use (Copy index_place)));
              Lowered.Index (Copy fixed)
          | projection -> projection)
        place.projections;
  }

(* Runs [f], the body of a loop whose [continue] and [break] each leave
   every scope inside the [depth] outermost. *)
let looping st ~continue_ ~break_ ~depth body =
  st.loops <- { continue_; continue_depth = depth; break_; break_depth = depth } :: st.loops;
  body ();
  st.loops <- List.tl st.loops

(* The type of a place in the function being written, or [None] where it has
   zero size or is reached through a lambda's environment. *)
let place_type st (place : Lowered.place) =
  let environment _ = bug "a place in an environment, whose type lowering does not track" in
  let rec projected (ty : Lowered.ty) = function
    | [] -> Some ty
    | _ :: _ when match ty with Environment _ | Evidence _ -> true | _ -> false -> None
    | projection :: rest ->
        Option.bind (Lowered.projection_type st.context.env ~environment ty projection) (fun ty ->
            projected ty rest)
  in
  match (st.cursor, place) with
  | Some cursor, { root = Local pointer; projections = Deref :: Field field :: rest }
    when pointer = cursor.pointer -> (
      (* A field of the cursor that the code is writing the fields of. *)
      match List.assoc_opt field !(cursor.fields) with
      | Some ty -> projected ty rest
      | None when field = Convention.cursor_state -> projected (Raw (Integer UInt32)) rest
      | None -> bug "the cursor has no field %s" field)
  | _ ->
      let root : Lowered.ty =
        match place.root with
        | Local local -> local_type st.builder local
        | Static { ty; _ } -> Value ty
      in
      if Lowered.erased st.context.env root then None else projected root place.projections

(* The lent value at a place, if the place holds one. *)
let lent_at st place =
  match place_type st place with Some (Value (Lent lent)) -> Some lent | _ -> None

(* A field or a variant's field of a place. A field of a lent value that
   holds an address is the place it points at. *)
let project st (place : Lowered.place) (projection : Lowered.projection) =
  let projected = place / projection in
  let variant, field =
    match projection with
    | Field field -> (None, field)
    | Variant_field { variant; field } -> (Some variant, field)
    | Index _ | Deref -> (None, "")
  in
  match lent_at st place with
  | Some lent
    when List.exists
           (fun (lent : Ground.lent_field) ->
             lent.variant = variant && lent.field = field && lent.holds = Address)
           lent.fields ->
      projected / Deref
  | _ -> projected

let constant_int integer value = Lowered.Constant (Integer (integer, value))

let scalar_of st ty =
  match (Memory_layout.of_type st.context.env ty).form with
  | Scalar scalar -> scalar
  | _ -> bug "%s is not a number" (Ground.to_string ty)
