(* The state of lowering one function: its frame, scopes, loops, and
   temporaries, and the small helpers every part of lowering shares. *)

open Definitions
open Lir_builder

(* Lowering one function *)

(* What leaving a scope does: drop what a place still owns, free the heap
   block a pointer points at, once what is in it has been dropped, give a
   place back the value that was lent out of it to be changed, or let a
   lending method go on. *)
type cleanup =
  | Drop_value of Lir.place
  | Free_pointed of Lir.place
  | Give_back of { lent : Lir.place; source : Lir.place; ty : Ground.ty }
  | Finish_lend of lend

(* A lending call whose method has more to do once it has lent its part. The
   method's body is written into the caller up to its [yield]; the rest of
   it waits at [resume] and ends at [finished]. Each way out of the scope
   that owns the lend jumps to [resume], with [selector] saying which way it
   was going, and [finished] sends it on, to one of [ways]. *)
and lend = {
  resume : Lir.block;
  finished : Lir.block;
  selector : Lir.local;
  mutable ways : Lir.block list;  (** Most recent first, numbered from the first *)
}

(* A scope owns what is dropped as it ends: the scope of a block's names,
   or the scope of one statement, whose temporaries end with it. *)
type scope_kind = Bindings | Statement
type scope = { kind : scope_kind; mutable owned : cleanup list  (** Most recent first *) }

(* Where [continue] and [break] go, and how many scopes each keeps. *)
type loop = { continue_ : Lir.block; continue_depth : int; break_ : Lir.block; break_depth : int }

(* The code being lowered: the function's own body, or the body of a
   method inlined into it, each with its own tables and names. *)
type frame = {
  code : code;
  bindings : (S.id, Lir.place) Hashtbl.t;
  synthetic : (int, Lir.place) Hashtbl.t;
      (** The places of the core form's synthetic locals, by number *)
  mutable self_place : Lir.place option;
  on_yield : (Lir.place -> resume:Lir.block -> stop:Lir.block -> unit) option;
      (** In an inlined lending or yielding method, what a [yield] of a place does *)
  yield_into : Lir.place option;
      (** In an inlined lending method with a [yield] on each of several paths, where a value the
          method makes to lend is put, so that one owner drops it whichever [yield] is reached *)
  inlined : Path.t list;  (** The methods inlined around this frame, to refuse recursion *)
  exit : (Lir.block * int) option;
      (** In an inlined method, where its [return] goes and how many scopes that keeps *)
}

(* Where a function's result goes: through the pointer it is given, into a
   local it returns, or nowhere. *)
type result_slot = Through of Lir.local | Returned_in of Lir.local | No_result

type state = {
  context : context;
  mutable frame : frame;
  b : Lir_builder.t;
  mutable scopes : scope list;  (** Innermost first *)
  mutable loops : loop list;
  mutable result : result_slot;
  nested : Lir.function_ option list ref;  (** The instance's lambdas, in order *)
  mutable evidence : (Path.t * Lir.operand) list;  (** The evidence for each capability available *)
  mutable compound_target : Lir.place option;
      (** The target of the compound assignment whose new value is being lowered *)
  pulling : bool;  (** Whether this is a yielding method's pulled version, whose [yield]s stay *)
}

(* The code a function starts lowering: its own, with nothing bound yet. *)
let frame_of code ~inlined =
  {
    code;
    bindings = Hashtbl.create 16;
    synthetic = Hashtbl.create 4;
    self_place = None;
    on_yield = None;
    yield_into = None;
    inlined;
    exit = None;
  }

(* The state to write one function in: a builder of its own and the
   function's scope. A lambda shares [nested] with the function around it. *)
let enter context ?(pulling = false) ?(nested = ref []) frame =
  {
    context;
    frame;
    b = Lir_builder.create ();
    scopes = [ { kind = Bindings; owned = [] } ];
    loops = [];
    result = No_result;
    nested;
    evidence = [];
    compound_target = None;
    pulling;
  }

let ground st ty = Monomorphic.ground st.context.monomorphic st.frame.code.substitution ty
let trivial st ty = Glue.trivial st.context.glue ty
let zero_size st ty = (Memory_layout.of_type st.context.env ty).size = 0

let site st (span : S.span) : Lir.site =
  let text = st.frame.code.text in
  let line = ref 0 and column = ref 1 in
  String.iteri
    (fun i c ->
      if i < span.start then
        if c = '\n' then begin
          incr line;
          column := 1
        end
        else incr column)
    text;
  { definition = st.frame.code.anchor; line = !line; column = !column }

(* A valid program stage0 cannot lower yet, at a place in the code being
   lowered. *)
let at_site ({ definition; line; column } : Lir.site) : Compiler_bug.site =
  { definition; line; column }

let source st (span : S.span) =
  let text = st.frame.code.text in
  let start = min span.start (String.length text) in
  String.sub text start (min span.stop (String.length text) - start)

(* The scope a new name belongs to: the innermost that holds names. *)
let rec binding_scope = function
  | ({ kind = Bindings; _ } as scope) :: _ -> scope
  | { kind = Statement; _ } :: rest -> binding_scope rest
  | [] -> bug "no scope"

let innermost_scope st = match st.scopes with scope :: _ -> scope | [] -> bug "no scope"

(* Has the scope of the names around own what is at a place. *)
let own_in_scope st place =
  let scope = binding_scope st.scopes in
  scope.owned <- Drop_value place :: scope.owned

(* A heap block the scope frees as it ends, after the drops of what is in it,
   which are owned later and so come first. *)
let free_in_scope st pointer =
  let scope = binding_scope st.scopes in
  scope.owned <- Free_pointed pointer :: scope.owned

(* A new local for a value, owned from the start, so that every way out of
   its owner drops whatever it still holds, and nothing it is given can be
   forgotten. A type with nothing to drop needs no owner. *)
let owned_local st ?name (scope : scope) ty =
  let place = at (local st.b ?name (Value ty)) in
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
   [owned]; otherwise it is the caller's, and one passed by value is
   borrowed. *)
let parameter st ?how ~owned (mode : Ground.mode) ty =
  let how = Option.value how ~default:(Convention.parameter st.context.env) in
  let own place = if owned && not (trivial st ty) then own_in_scope st place in
  match how mode ty with
  | None -> (None, temporary st ty)
  | Some (Lir.Pointer _ as pointer) ->
      let arrives = local st.b pointer in
      let place : Lir.place = { root = Local arrives; projections = [ Deref ] } in
      own place;
      (Some arrives, place)
  | Some passed ->
      let arrives = local st.b ~borrowed:(not owned) passed in
      own (at arrives);
      (Some arrives, at arrives)

(* A parameter for the evidence of each capability, which the code then
   reaches by it. Gives the parameters, in order. *)
let evidence_parameters st capabilities =
  let arriving =
    List.map
      (fun capability -> (capability, local st.b ~name:"evidence" Convention.evidence))
      capabilities
  in
  st.evidence <- List.map (fun (capability, l) -> (capability, Lir.Copy (at l))) arriving;
  List.map snd arriving

(* Makes the slot for the function's result, as the convention passes one.
   Nothing here owns it: it is the caller's once the function returns. *)
let result_slot st (convention : Convention.result) =
  st.result <-
    (match convention with
    | Through_pointer pointer -> Through (local st.b ~name:"result" pointer)
    | Returned ty -> Returned_in (local st.b ~name:"result" ty)
    | Nothing -> No_result)

(* Where the function's result is written, if it has one with a size. *)
let result_place st : Lir.place option =
  match st.result with
  | Through pointer -> Some { root = Local pointer; projections = [ Deref ] }
  | Returned_in local -> Some (at local)
  | No_result -> None

(* Drops what the result's slot holds, before it is written again: an early
   [return] can come after part of the result was written. *)
let clear_result st =
  match (st.result, result_place st) with
  | (Through slot | Returned_in slot), Some place -> (
      match local_type st.b slot with
      | Value ty | Pointer { target = Value ty; _ } ->
          if not (trivial st ty) then emit st.b (Drop place)
      | _ -> ())
  | _ -> ()

let return_result st : Lir.terminator =
  Return (match st.result with Returned_in local -> Some (Move (at local)) | _ -> None)

let drop_scope st (scope : scope) =
  List.iter
    (function
      | Drop_value place -> emit st.b (Drop place)
      | Free_pointed pointer ->
          emit st.b
            (Call { target = Intrinsic Free; arguments = [ Copy pointer ]; result = Discarded })
      | Give_back { lent; source; ty } ->
          emit st.b (Assign (source, Use (if trivial st ty then Copy lent else Move lent)))
      | Finish_lend lend ->
          (* The method goes on from its [yield] now, and comes back here. *)
          let way = block st.b in
          emit st.b
            (Assign
               ( at lend.selector,
                 Use (Constant (Integer (UInt32, Z.of_int (List.length lend.ways)))) ));
          lend.ways <- way :: lend.ways;
          finish st.b (Goto lend.resume);
          aside st.b lend.finished (fun () ->
              finish st.b
                (match lend.ways with
                | [ only ] -> Goto only
                | ways ->
                    Switch
                      {
                        value = Copy (at lend.selector);
                        cases =
                          List.mapi (fun i way -> (Z.of_int (List.length ways - 1 - i), way)) ways;
                        default = None;
                      }));
          start st.b way)
    scope.owned

(* Drops everything owned in the scopes inside the [depth] outermost, as a
   [return], [break], or [continue] leaves them. *)
let leave_to st depth =
  List.iteri
    (fun i scope -> if List.length st.scopes - i > depth then drop_scope st scope)
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

let within st kind f =
  let scope = open_scope st kind in
  let result = f () in
  close_scope st scope;
  result

let in_scope st f = within st Bindings f
let in_statement st f = within st Statement f

(* Ends the function being written: what its scope still owns is dropped
   and its result returned. Its parameters are [first], which it is given
   before anything else, the pointer its result is written through, if it
   has one, and [rest]. *)
let finish_function st ?(returns = true) ~first ~rest () : Lir.function_ =
  (match st.scopes with [ scope ] -> drop_scope st scope | _ -> bug "a function ended in a scope");
  finish st.b (if returns then return_result st else Unreachable);
  let pointer = match st.result with Through pointer -> Some pointer | _ -> None in
  let result =
    match st.result with Returned_in local -> Some (local_type st.b local) | _ -> None
  in
  let built =
    Lir_builder.build st.b ?written_result:pointer
      ~parameters:(first @ Option.to_list pointer @ rest)
      ~result
  in
  { built with returns }

(* The lambdas the function made, in order. *)
let nested_functions st =
  Array.of_list
    (List.map (function Some f -> f | None -> bug "a lambda left unfinished") !(st.nested))

let unreachable_block st =
  finish st.b Unreachable;
  start st.b (block st.b)

(* An operand for an owned position: a [var], an [own] argument, a field, a
   returned value. The type checker has made sure a place there is a
   temporary or was marked [own], or copies implicitly. *)
let owned st place ty = if trivial st ty then Lir.Copy place else Lir.Move place

(* Gives [destination], which holds nothing, the value at a place as its
   own: moved out of the place, or for a constant's static data, which
   nothing moves from, copied. *)
let take st (place : Lir.place) ty ~destination =
  match place.root with
  | Static _ when not (trivial st ty) ->
      Glue.copy_into st.context.glue st.b ~destination ~source:place ty
  | Static _ | Local _ -> emit st.b (Assign (destination, Use (owned st place ty)))

(* A place whose indexes are fixed now, so that an alias of it refers to the
   same element however the index variables change later. *)
let snapshot st (place : Lir.place) =
  {
    place with
    projections =
      List.map
        (function
          | Lir.Index (Copy index_place) ->
              let fixed = binding st st.context.types.usize in
              emit st.b (Assign (fixed, Use (Copy index_place)));
              Lir.Index (Copy fixed)
          | projection -> projection)
        place.projections;
  }

(* Runs [f], the body of a loop whose [continue] and [break] each leave
   every scope inside the [depth] outermost. *)
let looping st ~continue_ ~break_ ~depth f =
  st.loops <- { continue_; continue_depth = depth; break_; break_depth = depth } :: st.loops;
  f ();
  st.loops <- List.tl st.loops

(* Replaces the value at a place the program names with one worked out
   beforehand: what the place still owns is dropped, and the new value moved
   in. *)
let replace st place ty ~by =
  if not (trivial st ty) then emit st.b (Drop place);
  emit st.b (Assign (place, Use (owned st by ty)))

let constant_int integer value = Lir.Constant (Integer (integer, value))

let integer_of st ty =
  match (Memory_layout.of_type st.context.env ty).form with
  | Scalar (Integer integer) -> integer
  | _ -> bug "%s is not an integer type" (Ground.to_string ty)

let scalar_of st ty =
  match (Memory_layout.of_type st.context.env ty).form with
  | Scalar scalar -> scalar
  | _ -> bug "%s is not a number" (Ground.to_string ty)
