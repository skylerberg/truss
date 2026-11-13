(* The rules on [yield]: a lending method yields exactly once on every path
   of its MIR, only some yielding methods can be pulled as cursors, and a
   [concurrent for] keeps no borrow its yielding method can invalidate. Each
   reads a callee's facts from the callee's MIR. *)
open Context

(* How many times a path has yielded. *)
type count = Zero | One | Many

let add left right = match (left, right) with Zero, other | other, Zero -> other | _ -> Many

(* The yield counts at the returns of a body: a forward dataflow over its
   blocks, from no yield at the entry. A [yield] adds one; an iteration's
   end goes back to its [for], which may run its body again or end, so the
   counts grow until they stop changing, which, with three counts, they
   do. A path that reaches [todo] is incomplete and one that reaches
   [unreachable] has no end, so neither is counted. No [yield] runs in a
   task, so an early exit from tasks takes its counts to where it goes. *)
let yield_counts (body : Mir.body) : count list =
  let reaching = Array.make (Array.length body.blocks) [] in
  let iteration_loops = Mir.iteration_loops body in
  let returned = ref [] and pending = Queue.create () in
  let flow block counts =
    let merged = List.sort_uniq compare (reaching.(block) @ counts) in
    if merged <> reaching.(block) then begin
      reaching.(block) <- merged;
      Queue.add block pending
    end
  in
  flow 0 [ Zero ];
  while not (Queue.is_empty pending) do
    let block = Queue.pop pending in
    let counts = reaching.(block) in
    match body.blocks.(block).terminator with
    | Yield { resume; _ } -> flow resume (List.map (add One) counts)
    | Return _ | Exit_tasks { exit = Exit_return _; _ } -> returned := counts @ !returned
    | Exit_tasks { exit = Exit_to target; _ } -> flow target counts
    | Iteration_end | Exit_tasks { exit = Exit_iteration; _ } ->
        Option.iter (fun loop -> flow loop counts) (Hashtbl.find_opt iteration_loops block)
    | (Goto _ | Branch _ | Switch_variant _ | For _ | Fork _ | Join _ | Todo | Unreachable) as
      terminator ->
        List.iter (fun target -> flow target counts) (Mir.successors terminator)
  done;
  List.sort_uniq compare !returned

(* A lending method yields exactly once on every path. *)
let check_yields_once context (body : Mir.body) ~(name : Syntax.span) =
  let counts = yield_counts body in
  if List.mem Zero counts then
    report context Yield_count name
      "A path through this lending method never yields. It must yield exactly once on every path."
  else if List.mem Many counts then
    report context Yield_count name
      "A path through this lending method yields more than once. It must yield exactly once on \
       every path."

(* The facts of a callee's [yield]s, if it has code. *)
let yielding database (path : Path.t) : Mir.yielding option =
  Option.map (fun ((mir : Mir.t), _) -> mir.yielding) (Query.demand database Mir.of_path path)

(* Whether a yielding method can be pulled as a cursor, and if not, why. *)
type pulling =
  | Pullable
  | Yields_mut  (** A cursor would store [mut] access between pulls. *)
  | Recursive
      (** The method yields through itself, as a tree's [each] that loops over its subtrees. Its
          cursor would need a stack of its own. *)
  | Yields_places
      (** The method yields read-only views of places, such as [self[index]]. A pull returns an
          owned value, so only a [Plain] element can be pulled: an element of any other type would
          be copied implicitly. *)

let pullable =
  Query.query ~name:"pullable" ~phase:Phases.bodies ~saved:true ~show:Path.show
    (fun database (path : Path.t) ->
      let through path =
        match yielding database path with Some facts -> facts.through | None -> []
      in
      let rec reaches visited = function
        | [] -> false
        | next :: rest ->
            if Path.equal next path then true
            else if List.exists (Path.equal next) visited then reaches visited rest
            else reaches (next :: visited) (through next @ rest)
      in
      match
        Option.map
          (fun (signature : Types.signature) -> signature.output)
          (Query.demand database Interface.Environment.signature path)
      with
      | Some (Yields (Mut, _)) -> Yields_mut
      | _ when reaches [] (through path) -> Recursive
      | Some (Yields (Read, _))
        when Option.fold ~none:false
               ~some:(fun (facts : Mir.yielding) -> facts.yields_places)
               (yielding database path) ->
          Yields_places
      | _ -> Pullable)

(* Reports a cursor that is created from a method that cannot be pulled.
   Every holder of a cursor may pull it, through [next], a [for] loop, or
   generic code, so the rule is checked once, where the cursor is created.
   [element] is the type of the value that a pull returns. *)
let check_cursor context (at : Syntax.span) method_ element =
  let refuse message = report context Not_pullable at message in
  match Query.demand context.database pullable method_ with
  | Pullable -> ()
  | Yields_mut ->
      refuse
        "A method that yields `mut` access can drive a `for` loop, but it cannot be made into a \
         cursor, because the cursor would store a `mut` borrow between pulls."
  | Recursive ->
      refuse
        (Printf.sprintf
           "`%s` yields recursively, so it can drive a `for` loop but cannot be made into a \
            cursor. Write a cursor type that keeps its own stack."
           (Path.show method_))
  | Yields_places ->
      if not (plain context element) then
        refuse
          (Printf.sprintf
             "`%s` yields views of its elements, and a cursor returns each element by value, which \
              would copy a `%s` implicitly. Loop over it with `for`, or create the cursor from a \
              method that yields owned values."
             (Path.show method_) (Types.show element))

(* Calls [visit] on each block of the definition's bodies, its lambdas'
   included. *)
let each_block (mir : Mir.t) visit =
  List.iter
    (fun (body : Mir.body) -> Array.iter (visit body) body.blocks)
    (mir.body :: Array.to_list mir.lambdas)

(* Checks every cursor that a definition creates: each call whose result is
   a cursor. A [for] loop or a quantifier over a call of a yielding method
   iterates over the call without a cursor. *)
let check_cursors context (mir : Mir.t) =
  each_block mir (fun body (block : Mir.basic_block) ->
      List.iter
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Call { destination = Some { root = Local local; projections = [] }; call } -> (
              match body.locals.(local).type_ with
              | Types.Cursor { method_; arguments } ->
                  Option.iter
                    (check_cursor context (span context call.origin) method_)
                    (Interface.Impls.cursor_element context.database method_ arguments)
              | _ -> ())
          | _ -> ())
        block.statements)

(* How a callee yields: the mode of its [yields] clause, if it has one. *)
let yield_mode context (callee : Mir.callee) : Types.mode option =
  let of_output : Types.result -> Types.mode option = function
    | Yields (mode, _) -> Some mode
    | Returns _ | Lends _ -> None
  in
  match callee with
  | Function { path; _ } ->
      Option.bind (Interface.Impls.signature context.database path)
        (fun (signature : Types.signature) -> of_output signature.output)
  | Trait_method { trait; name; receiver; _ } ->
      Option.bind (Infer.Members.trait_method context.database trait.trait name receiver)
        (fun (method_ : Types.trait_method) -> of_output method_.method_signature.output)
  | Capability_method _ | Intrinsic _ | Indirect _ -> None

(* Use after free in a [concurrent for]. Each iteration runs as a task, and
   the task outlives the [yield] that started it: the yielding method
   resumes while the task still runs. So the task can keep a borrow or a
   view only of a place that the method cannot mutate or drop, which is a
   place inside a read-only parameter of the method. [Views.task_hazard] is
   that fact about a method's body, and [task_hazard] reads it for a
   callee.

   - A method that yields by position is exempt. Its body is a single loop
     over a range, the tasks run as that loop's iterations, and the method
     does nothing after the loop.
   - A [Plain] element that is not a view is copied to the task, so it is
     accepted whatever it was borrowed from.
   - For a callee without a known body, such as a trait method called
     through a bound, and for a cursor, the task needs an owned element that
     is not a view, or a [Plain] copy of a read-only one. *)
let check_concurrent_loops context ~(task_hazard : Path.t -> Views.task_hazard option option)
    (mir : Mir.t) =
  each_block mir (fun body (block : Mir.basic_block) ->
      match block.terminator with
      | For { loop = { schedule = Concurrent_loop; _ }; part; iteration; _ } -> (
          let element = body.locals.(part).type_ in
          let copied = plain context element && not (is_view context element) in
          let reject (at : Core.origin) problem =
            report context Task_outlives_yield (span context at)
              (Printf.sprintf
                 "Each iteration of a `concurrent for` runs as a task that outlives the `yield` \
                  that started it. %s Use a `for` loop, or iterate over a method that yields owned \
                  values or borrows of its read-only parameters."
                 problem)
          in
          let yields_mut at =
            reject at
              "This method yields `mut` borrows, which it could invalidate when it resumes, so the \
               task would have a dangling borrow."
          in
          let view at =
            if is_view context element then
              reject at
                (Printf.sprintf
                   "The element type `%s` is a view, and the method could invalidate its original \
                    when it resumes, which would leave the task with a dangling view."
                   (Types.show element))
          in
          let unknown_body (call : Mir.call) =
            match yield_mode context call.callee with
            | Some Mut -> yields_mut call.origin
            | Some Read when not (plain context element) ->
                reject call.origin
                  (Printf.sprintf
                     "This method yields borrowed elements of type `%s`, and its body is not known \
                      here, so it could mutate or drop them when it resumes."
                     (Types.show element))
            | _ -> view call.origin
          in
          match iteration with
          | Range _ -> ()
          | Yielding ({ callee = Function { path; _ }; _ } as call) -> (
              match yielding context.database path with
              | Some { by_position = true; _ } -> ()
              | Some _ -> (
                  match Option.join (task_hazard path) with
                  | Some Yields_mut -> yields_mut call.origin
                  | Some (Borrows place) when not copied ->
                      reject call.origin
                        (Printf.sprintf
                           "This method yields a borrow or a view of its `%s`, which it could \
                            mutate or drop when it resumes, so the task would have a dangling \
                            borrow."
                           place)
                  | Some (Borrows _) | None -> ())
              | None -> unknown_body call)
          | Yielding call -> unknown_body call
          | Pull _ -> view block.terminator_origin)
      | _ -> ())
