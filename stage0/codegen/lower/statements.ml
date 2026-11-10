(* Statements: blocks, statements, [let], loops, conditions lowered as
   jumps, and [match]. *)

open Definitions
open Lowering
open Targets
open Matching
open Calls
open Values
open Lir_builder

(* Blocks and statements *)

let rec block_into st (block : S.block) destination =
  in_scope st (fun () ->
      let rec go = function
        | [] -> ()
        | [ ({ S.kind = Expression e; _ } : S.statement) ] -> (
            match destination with
            | Some d -> in_statement st (fun () -> into st e d)
            | None ->
                statement st
                  { kind = Expression e; span = e.span; blank_line_before = false; id = e.id })
        | s :: rest ->
            statement st s;
            go rest
      in
      go block.statements)

and statement st (s : S.statement) =
  in_statement st (fun () ->
      match s.kind with
      | Expression e -> ignore (expression st e)
      | Let { mutable_; pattern; value; else_ = None; _ } -> let_ st ~mutable_ pattern value
      | Let { pattern; value; else_ = Some else_; _ } ->
          let place, made = scrutinee st value in
          let matched = block st.b and failed = block st.b in
          test_pattern st pattern place (type_of st value.id) ~matched ~failed;
          start st.b failed;
          block_into st else_ None;
          unreachable_block st;
          start st.b matched;
          bind_pattern st pattern place (type_of st value.id) ~owned:made
      | Assignment { target; operator = Assign; value } -> (
          (* The new value is worked out into a place of its own, which
             nothing else names, before it replaces the old one. *)
          match place_expression st target with
          | Some place ->
              let ty = type_of st target.id in
              let fresh = temporary st ty in
              into st value fresh;
              replace st place ty ~by:fresh
          | None -> bug "an assignment to something that is not a place")
      | Assignment { target; value; _ } -> (
          match (place_expression st target, st.frame.code.checked.calls.(s.id)) with
          | Some place, Some call_ ->
              (* The target is evaluated once: the operator is given the
                 place it names, and its result replaces what is there. *)
              let ty = type_of st target.id in
              let result = temporary st ty in
              let arguments =
                [
                  {
                    C.expression = target.id;
                    parameter = 0;
                    mode = (if trivial st ty then Read else Own);
                    conversion = None;
                  };
                  { C.expression = value.id; parameter = 1; mode = Read; conversion = None };
                ]
              in
              call_with st call_
                ~evaluated:[ (target.id, place) ]
                ~expressions:[ target; value ] ~arguments result ~span:s.span;
              replace st place ty ~by:result
          | _ -> bug "a compound assignment that is not lowered: %s" (source st s.span))
      | While { condition; body; _ } ->
          (* Each test's temporaries end before the body or the exit; the
             names it binds live until the body ends. *)
          let test = block st.b and inside = block st.b and failed = block st.b in
          let after = block st.b in
          let depth = List.length st.scopes in
          finish st.b (Goto test);
          start st.b test;
          let names = open_scope st Bindings in
          let tested = open_scope st Statement in
          branch st condition ~yes:inside ~no:failed;
          pop_scope st tested;
          start st.b failed;
          drop_scope st tested;
          drop_scope st names;
          finish st.b (Goto after);
          start st.b inside;
          drop_scope st tested;
          st.loops <-
            { continue_ = test; continue_depth = depth; break_ = after; break_depth = depth }
            :: st.loops;
          block_into st body None;
          st.loops <- List.tl st.loops;
          close_scope st names;
          finish st.b (Goto test);
          start st.b after
      | For { pattern; iterable; body; parallel = _; _ } -> for_ st s ~pattern ~iterable ~body
      | Assert condition ->
          let value = operand st condition in
          let failed = block st.b and after = block st.b in
          finish st.b (Switch { value; cases = [ (Z.one, after) ]; default = Some failed });
          start st.b failed;
          let message = "assert " ^ source st condition.span in
          finish st.b
            (Fail
               {
                 failure = Assertion;
                 message = Constant (Bytes message);
                 length = usize (String.length message);
                 site = site st s.span;
               });
          start st.b after
      | Proof _ -> ()
      | Parallel block ->
          (* Stage0 runs a [parallel] block's branches one after another. *)
          List.iter (statement st) block.statements
      | Yield value -> (
          match st.frame.on_yield with
          | Some on_yield ->
              let place = expression st value in
              let resume = block st.b and stop = block st.b in
              on_yield place ~resume ~stop;
              (* The [stop] path: what the method owns is dropped as the loop
                 leaves it. *)
              start st.b stop;
              (match st.frame.exit with
              | Some (exit, depth) ->
                  leave_to st depth;
                  finish st.b (Goto exit)
              | None -> finish st.b Unreachable);
              start st.b resume
          | None when st.pulling ->
              (* In a pulled method, a [yield] stays, for yield lowering to make
                 a state of. Its [stop] path drops what the method owns. *)
              let ty = type_of st value.id in
              let place, made = scrutinee st value in
              (* [next] gives its caller a value of its own: what the method
                 makes, or a copy of a part it yields a view of. *)
              let given =
                if made || trivial st ty then place
                else begin
                  let copy = temporary st ty in
                  Glue.copy_into st.context.glue st.b ~destination:copy ~source:place ty;
                  copy
                end
              in
              let resume = block st.b and stop = block st.b in
              finish st.b (Yield { value = owned st given ty; resume; stop = Some stop });
              start st.b stop;
              leave_to st 0;
              finish st.b (Return None);
              start st.b resume
          | None -> bug "a yield outside an inlined method")
      | Statement_error -> bug "a statement that did not parse")

(* Evaluates an expression once, for a pattern to look into: the place it
   names, or a temporary holding its value, and whether it is a temporary,
   whose parts the pattern's names then own. *)
and scrutinee st (e : S.expression) =
  match place_expression st e with Some place -> (place, false) | None -> (expression st e, true)

and let_ st ~mutable_ (pattern : S.pattern) (value : S.expression) =
  let ty = type_of st value.id in
  match pattern.kind with
  | Wildcard -> ignore (expression st value)
  | Binding_or_constant name -> (
      let bind place = Hashtbl.replace st.frame.bindings name.id place in
      match place_expression st value with
      | Some place when (not mutable_) && not (trivial st ty) ->
          (* A [let] of a place views it. *)
          bind (snapshot st place)
      | Some place ->
          let local = binding st ~name:name.text ty in
          take st place ty ~destination:local;
          bind local
      | None ->
          let local = binding st ~name:name.text ty in
          into st value local;
          bind local)
  | _ ->
      let place, made = scrutinee st value in
      bind_pattern st pattern place ty ~owned:(made || mutable_)

(* A place whose indexes are fixed now, so a view of it means the same
   element however the index variables change later. *)
and snapshot st (place : Lir.place) =
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

and for_ st (s : S.statement) ~pattern ~iterable ~body =
  match st.frame.code.checked.loops.(s.id) with
  | Some (Integer_range { element; inclusive }) -> (
      let element = ground st element in
      match iterable.kind with
      | Range { start = Some low; stop = Some high; _ } ->
          let index = binding st ~name:"index" element in
          let stop = binding st element in
          emit st.b (Assign (index, Use (operand st low)));
          emit st.b (Assign (stop, Use (operand st high)));
          let test = block st.b
          and inside = block st.b
          and step = block st.b
          and after = block st.b in
          let depth = List.length st.scopes in
          finish st.b (Goto test);
          start st.b test;
          let going = local st.b (Raw Bool) in
          emit st.b
            (Assign
               (at going, Binary ((if inclusive then Less_equal else Less), Copy index, Copy stop)));
          finish st.b
            (Switch { value = Copy (at going); cases = [ (Z.one, inside) ]; default = Some after });
          start st.b inside;
          in_scope st (fun () ->
              let bound = binding st element in
              emit st.b (Assign (bound, Use (Copy index)));
              bind_pattern st pattern bound element ~owned:true;
              looping st ~continue_:step ~break_:after ~depth (fun () -> block_into st body None));
          finish st.b (Goto step);
          start st.b step;
          (* An inclusive range ends at its last value rather than past
             it, which might not fit the type. *)
          if inclusive then begin
            let last = local st.b (Raw Bool) in
            emit st.b (Assign (at last, Binary (Equal, Copy index, Copy stop)));
            let next = block st.b in
            finish st.b
              (Switch { value = Copy (at last); cases = [ (Z.one, after) ]; default = Some next });
            start st.b next
          end;
          emit st.b
            (Assign (index, Binary (Add, Copy index, constant_int (integer_of st element) Z.one)));
          finish st.b (Goto test);
          start st.b after
      | _ -> bug "a counted loop that is not over a range")
  | Some (Yielding { call = call_; mode }) -> (
      (* The loop is over a call of a yielding method that is written out,
         whose arguments are that call's, or over a value, which is the
         receiver of the [each] the checker chose. *)
      let rec written (e : S.expression) =
        match e.kind with Parenthesized inner | Mode (_, inner) -> written inner | _ -> e
      in
      let expressions, arguments =
        match written iterable with
        | { kind = Call (callee, passed); id; _ } when st.frame.code.checked.calls.(id) = Some call_
          ->
            let expressions = call_expressions call_ callee passed in
            (expressions, with_receiver st call_ ~expressions call_.arguments)
        | _ ->
            ( [ iterable ],
              [ { C.expression = iterable.id; parameter = 0; mode; conversion = None } ] )
      in
      match resolve_callee st call_ with
      | Some (path, type_arguments) when List.exists (Path.equal path) st.frame.inlined ->
          recursive_loop st s call_ ~expressions ~arguments ~path ~type_arguments ~pattern ~body
      | Some (path, type_arguments) ->
          let arguments = evaluate_arguments st ~expressions ~arguments in
          let caller = st.frame in
          let depth = List.length st.scopes in
          let after = block st.b in
          let call_site = site st s.span in
          inline st path type_arguments ~arguments ~call_site ~on_yield:(fun place ~resume ~stop ->
              let inner = st.frame in
              st.frame <- caller;
              let element_ty = yielded_type st path type_arguments in
              let around = List.length st.scopes in
              in_scope st (fun () ->
                  bind_pattern st pattern place element_ty ~owned:(mode = T.Own)
                    ~changed:(mode = T.Mut);
                  st.loops <-
                    {
                      continue_ = resume;
                      continue_depth = around;
                      break_ = after;
                      break_depth = depth;
                    }
                    :: st.loops;
                  block_into st body None;
                  st.loops <- List.tl st.loops);
              finish st.b (Goto resume);
              ignore stop;
              st.frame <- inner);
          finish st.b (Goto after);
          start st.b after
      | None -> bug "a loop over something that is not a method")
  | Some (Pulled { cursor }) -> (
      match ground st cursor with
      | Cursor yielding -> pull_loop st yielding (expression st iterable) ~pattern ~body
      | cursor_ty -> bug "a pulled loop over %s" (Ground.to_string cursor_ty))
  | None -> bug "a for loop with no meaning"

(* Runs [f], the body of a loop whose [continue] and [break] each leave
   every scope inside the [depth] outermost. *)
and looping st ~continue_ ~break_ ~depth f =
  st.loops <- { continue_; continue_depth = depth; break_; break_depth = depth } :: st.loops;
  f ();
  st.loops <- List.tl st.loops

(* Pulls a cursor until it ends, running the body with each value it gives.
   The loop owns the value [next] gave, so whatever the body did not take
   is dropped before the next is asked for, and on every way out. *)
and pull_loop st (yielding : Ground.yielding) cursor ~pattern ~body =
  let option = cursor_result st.context yielding in
  let element = cursor_element st.context yielding in
  in_scope st (fun () ->
      let next = binding st option in
      let depth = List.length st.scopes in
      let test = block st.b and inside = block st.b and after = block st.b in
      finish st.b (Goto test);
      start st.b test;
      if not (trivial st option) then emit st.b (Drop next);
      call_next st yielding cursor next;
      let more = local st.b (Raw Bool) in
      emit st.b (Assign (at more, Is_variant (next, "Some")));
      finish st.b
        (Switch { value = Copy (at more); cases = [ (Z.one, inside) ]; default = Some after });
      start st.b inside;
      in_scope st (fun () ->
          bind_pattern st pattern
            (next / Variant_field { variant = "Some"; field = "value" })
            element ~owned:true;
          looping st ~continue_:test ~break_:after ~depth (fun () -> block_into st body None));
      finish st.b (Goto test);
      start st.b after)

(* A loop over a yielding method already inlined around it, which yields
   through recursion: inlining it again would never end, so the loop pulls a
   cursor over it instead, held in a heap block of its own so that a cursor
   over the method can hold another, and freed as the loop ends. A pulled
   cursor gives values of their own, so a view the method yields reaches the
   loop as a copy. *)
and recursive_loop st (s : S.statement) call_ ~expressions ~arguments ~path ~type_arguments ~pattern
    ~body =
  let yielding : Ground.yielding = { method_ = path; type_arguments } in
  let cursor_ty = Ground.Cursor yielding in
  in_scope st (fun () ->
      let boxed =
        local st.b ~name:"cursor" (Pointer { target = Value cursor_ty; writable = true })
      in
      emit st.b
        (Call
           {
             target = Intrinsic Allocate;
             arguments = [ Constant (Size_of cursor_ty); Constant (Alignment_of cursor_ty) ];
             result = Returned (at boxed);
           });
      free_in_scope st (at boxed);
      let cursor = { Lir.root = Local boxed; projections = [ Deref ] } in
      call_with st call_ ~expressions ~arguments cursor ~span:s.span;
      own_in_scope st cursor;
      pull_loop st yielding cursor ~pattern ~body)

(* The type a yielding method yields, in this instance. *)
and yielded_type st path type_arguments =
  let signature = signature_of st.context path in
  match signature.output with
  | Yields (_, ty) | Lends (_, ty) ->
      Monomorphic.ground st.context.monomorphic (bind signature.generics type_arguments) ty
  | Returns _ -> bug "%s does not yield" (Path.show path)

and if_ st ~condition ~then_ ~else_ destination =
  let yes = block st.b and no = block st.b and after = block st.b in
  (* The names the condition binds are in the [then] block, not the
     [else]. *)
  let scope = open_scope st Bindings in
  branch st condition ~yes ~no;
  start st.b yes;
  block_into st then_ destination;
  close_scope st scope;
  finish st.b (Goto after);
  start st.b no;
  drop_scope st scope;
  (match else_ with
  | None -> ()
  | Some (S.Else block) -> block_into st block destination
  | Some (Else_if e) -> (
      match destination with Some d -> into st e d | None -> ignore (expression st e)));
  finish st.b (Goto after);
  start st.b after

(* Lowers a condition as jumps: to [yes] when it holds, and to [no] when it
   does not. The names its [is] tests bind are bound on the way to [yes],
   owned in the current scope, which the caller has opened to cover where
   they can be used and drops on every path out. *)
and branch st (e : S.expression) ~yes ~no =
  match e.kind with
  | Parenthesized inner -> branch st inner ~yes ~no
  | Binary { operator = And; left; right; _ } ->
      let middle = block st.b in
      branch st left ~yes:middle ~no;
      start st.b middle;
      branch st right ~yes ~no
  | Binary { operator = Or; left; right; _ } ->
      let middle = block st.b in
      branch st left ~yes ~no:middle;
      start st.b middle;
      branch st right ~yes ~no
  | Prefix (Not, inner) when st.frame.code.checked.calls.(e.id) = None || is_built_in st e ->
      branch st inner ~yes:no ~no:yes
  | Is { value; pattern; _ } ->
      let ty = type_of st value.id in
      let place, made = scrutinee st value in
      let matched = block st.b in
      test_pattern st pattern place ty ~matched ~failed:no;
      start st.b matched;
      bind_pattern st pattern place ty ~owned:made;
      finish st.b (Goto yes)
  | _ ->
      let value = operand st e in
      finish st.b (Switch { value; cases = [ (Z.one, yes) ]; default = Some no })

and match_ st ~scrutinees ~arms destination =
  let values =
    List.map
      (fun e ->
        let place, made = scrutinee st e in
        (place, type_of st e.S.id, made))
      scrutinees
  in
  let after = block st.b in
  List.iter
    (fun (arm : S.arm) ->
      let next = block st.b in
      let rec test patterns values =
        match (patterns, values) with
        | [], [] -> ()
        | pattern :: patterns, (place, ty, _) :: values ->
            let matched = block st.b in
            test_pattern st pattern place ty ~matched ~failed:next;
            start st.b matched;
            test patterns values
        | _ -> bug "a match arm with the wrong number of patterns"
      in
      test arm.patterns values;
      let bind ~owned =
        List.iter2
          (fun pattern (place, ty, made) -> bind_pattern st pattern place ty ~owned:(owned && made))
          arm.patterns values
      in
      in_scope st (fun () ->
          (match arm.guard with
          | Some guard ->
              (* The guard sees views of what the arm binds, so a guard that
                 fails leaves the values whole for the next arm; the body
                 then owns the parts. *)
              bind ~owned:false;
              let body = block st.b and failed = block st.b in
              branch st guard ~yes:body ~no:failed;
              start st.b failed;
              drop_scope st (List.hd st.scopes);
              finish st.b (Goto next);
              start st.b body;
              bind ~owned:true
          | None -> bind ~owned:true);
          match (arm.body.kind, destination) with
          | Expression e, Some d -> into st e d
          | _, _ -> statement st arm.body);
      finish st.b (Goto after);
      start st.b next)
    arms;
  finish st.b Unreachable;
  start st.b after
