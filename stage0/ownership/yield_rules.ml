(* The rules on [yield], checked on the core form: a lending method yields
   exactly once on every path, and only some yielding methods can be pulled
   as cursors. *)

module T = Types
open Context

(* How many times a path has yielded. *)
type count = Zero | One | Many

let add left right = match (left, right) with Zero, other | other, Zero -> other | _ -> Many

(* The yield counts at the ends of the paths through a body. *)
let yield_counts (body : Core.block) : count list =
  let returned = ref [] in
  (* For each enclosing loop, innermost first: the counts of the paths that
     left it by [break], and of those that ended an iteration by
     [continue]. *)
  let loops = ref [] in
  let rec block counts (body : Core.block) =
    let counts = List.fold_left statement counts body.statements in
    match body.value with Some value -> evaluated counts value | None -> counts
  (* An expression statement. A path that reaches [todo] is incomplete, so
     it is not reported. A path through an expression of type [Never]
     diverges, so it has no end. *)
  and evaluated counts (value : Core.expression) =
    match value.kind with
    | Todo -> List.map (fun _ -> One) counts
    | _ ->
        let after = expression counts value in
        if value.type_ = T.Never then [] else after
  and statement counts (node : Core.statement) =
    match node.kind with
    | Yield _ -> List.map (fun count -> add count One) counts
    | Evaluate value | Let { value = Value value; _ } -> evaluated counts value
    | For { body; _ } | While { body; _ } ->
        let broken = ref [] and continued = ref [] in
        loops := (broken, continued) :: !loops;
        (* The paths at the start of an iteration: those that reach the
           loop, and those that reach the end of the body or a [continue].
           A body whose every path returns adds none, so the paths after
           the loop are those that reached it. There are three counts, so
           the set stops growing. *)
        let rec before_iteration reached =
          continued := [];
          let ended = block reached body in
          let next = List.sort_uniq compare (reached @ ended @ !continued) in
          if next = reached then reached else before_iteration next
        in
        let reached = before_iteration (List.sort_uniq compare counts) in
        loops := List.tl !loops;
        List.sort_uniq compare (reached @ !broken)
    (* Every branch runs, so the yields of the branches add up. *)
    | Parallel branches | Concurrent branches -> List.fold_left statement counts branches
    | Let { value = Place _; _ } | Assign _ | Compound_assign _ | Proof _ | Assert _ -> counts
  and expression counts (value : Core.expression) =
    match value.kind with
    | If { then_; else_; _ } ->
        List.sort_uniq compare
          (block counts then_ @ match else_ with Some else_ -> block counts else_ | None -> counts)
    | Match { arms; _ } ->
        List.sort_uniq compare
          (List.concat_map (fun (arm : Core.arm) -> block counts arm.body) arms)
    | Return _ ->
        returned := counts @ !returned;
        []
    | Break -> (
        match !loops with
        | (broken, _) :: _ ->
            broken := counts @ !broken;
            []
        | [] -> counts)
    | Continue -> (
        match !loops with
        | (_, continued) :: _ ->
            continued := counts @ !continued;
            []
        | [] -> counts)
    | Task_exit { exit; _ } -> expression counts exit
    | Block body -> block counts body
    | _ -> counts
  in
  let ended = block [ Zero ] body in
  ended @ !returned

(* A lending method yields exactly once on every path. *)
let check_yields_once context (body : Core.block) ~(name : Syntax.span) =
  let counts = yield_counts body in
  if List.mem Zero counts then
    report context Yield_count name
      "A path through this lending method never yields. It must yield exactly once on every path."
  else if List.mem Many counts then
    report context Yield_count name
      "A path through this lending method yields more than once. It must yield exactly once on \
       every path."

let body_of database (path : Path.t) : Core.block option =
  match
    Option.bind
      (Query.demand database Interface.Summary.key path)
      (Query.demand database Infer.core)
  with
  | Some { definition = Function { body; _ }; _ } -> body
  | _ -> None

(* Calls [visit] on every statement of a block, at any depth. *)
let each_statement (body : Core.block) visit =
  Core_walk.block (Core_walk.deep { Core_walk.ignore_all with statement = visit }) body

(* The yielding functions that a function delegates to: those that a [for]
   loop in its body iterates over, where the loop body yields. *)
let yields_through =
  Query.query ~name:"yields_through" ~phase:Phases.bodies ~saved:true ~show:Path.show
    (fun database (path : Path.t) ->
      match body_of database path with
      | Some body ->
          let through = ref [] in
          each_statement body (fun (node : Core.statement) ->
              match node.kind with
              | For
                  {
                    iteration =
                      Yielding_call { kind = Call { callee = Function { path; _ }; _ }; _ };
                    body = loop_body;
                    _;
                  } ->
                  let yields = ref false in
                  each_statement loop_body (fun (inner : Core.statement) ->
                      match inner.kind with Yield _ -> yields := true | _ -> ());
                  if !yields then through := path :: !through
              | _ -> ());
          List.sort_uniq Path.compare !through
      | None -> [])

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
      let rec reaches visited = function
        | [] -> false
        | next :: rest ->
            if Path.equal next path then true
            else if List.exists (Path.equal next) visited then reaches visited rest
            else reaches (next :: visited) (Query.demand database yields_through next @ rest)
      in
      let yields_places () =
        match body_of database path with
        | Some body ->
            let yields_place = ref false in
            each_statement body (fun (node : Core.statement) ->
                match node.kind with
                | Yield { part; _ }
                  when List.exists
                         (fun lent -> Option.is_some (Place.of_core lent))
                         (Core_walk.lent_places part) ->
                    yields_place := true
                | _ -> ());
            !yields_place
        | None -> false
      in
      match
        Option.map
          (fun (signature : T.signature) -> signature.output)
          (Query.demand database Interface.Environment.signature path)
      with
      | Some (Yields (Mut, _)) -> Yields_mut
      | _ when reaches [] (Query.demand database yields_through path) -> Recursive
      | Some (Yields (Read, _)) when yields_places () -> Yields_places
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
             (Path.show method_) (T.show element))

(* Checks every cursor that a definition creates: each call of a yielding
   method that is not the iteration of a [for] loop or of a quantifier. *)
let check_cursors context (definition : Core.definition) =
  let driving = Hashtbl.create 8 in
  Core_walk.definition
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) ->
          match node.kind with
          | Quantified { binder = Over_each { call; _ }; _ } -> Hashtbl.replace driving call.id ()
          | _ -> ());
      statement =
        (fun (node : Core.statement) ->
          match node.kind with
          | For { iteration = Yielding_call call; _ } -> Hashtbl.replace driving call.id ()
          | _ -> ());
    }
    definition;
  Core_walk.definition
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) ->
          match (node.kind, node.type_) with
          | Call _, T.Cursor { method_; arguments } when not (Hashtbl.mem driving node.id) ->
              Option.iter
                (check_cursor context (span context node.origin) method_)
                (Interface.Impls.cursor_element context.database method_ arguments)
          | _ -> ());
    }
    definition

(* How a callee yields: the mode of its [yields] clause, if it has one. *)
let yield_mode context (callee : Core.callee) : T.mode option =
  let of_output : T.result -> T.mode option = function
    | Yields (mode, _) -> Some mode
    | Returns _ | Lends _ -> None
  in
  match callee with
  | Function { path; _ } ->
      Option.bind (Interface.Impls.signature context.database path)
        (fun (signature : T.signature) -> of_output signature.output)
  | Trait_method { trait; name; receiver; _ } ->
      Option.bind (Infer.Members.trait_method context.database trait.trait name receiver)
        (fun (method_ : T.trait_method) -> of_output method_.method_signature.output)
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
    (definition : Core.definition) =
  let body : Core.callee -> (Path.t * Core.block) option = function
    | Function { path; _ } -> Option.map (fun body -> (path, body)) (body_of context.database path)
    | Trait_method _ | Capability_method _ | Intrinsic _ | Indirect _ -> None
  in
  Core_walk.definition
    {
      Core_walk.ignore_all with
      statement =
        (fun (node : Core.statement) ->
          match node.kind with
          | For { mode = Concurrent_loop; pattern; iteration; _ } -> (
              let element = pattern.type_ in
              let copied = plain context element && not (is_view context element) in
              let reject (at : Core.origin) problem =
                report context Task_outlives_yield (span context at)
                  (Printf.sprintf
                     "Each iteration of a `concurrent for` runs as a task that outlives the \
                      `yield` that started it. %s Use a `for` loop, or iterate over a method that \
                      yields owned values or borrows of its read-only parameters."
                     problem)
              in
              let yields_mut at =
                reject at
                  "This method yields `mut` borrows, which it could invalidate when it resumes, so \
                   the task would have a dangling borrow."
              in
              let view at =
                if is_view context element then
                  reject at
                    (Printf.sprintf
                       "The element type `%s` is a view, and the method could invalidate what it \
                        views when it resumes, which would leave the task with a dangling view."
                       (T.show element))
              in
              match iteration with
              | Integer_range _ -> ()
              | Yielding_call { kind = Call { callee; _ }; origin; _ } -> (
                  match body callee with
                  | Some (_, body) when Core_walk.yields_by_position body -> ()
                  | Some (path, _) -> (
                      match Option.join (task_hazard path) with
                      | Some Yields_mut -> yields_mut origin
                      | Some (Borrows place) when not copied ->
                          reject origin
                            (Printf.sprintf
                               "This method yields a borrow or a view of its `%s`, which it could \
                                mutate or drop when it resumes, so the task would have a dangling \
                                borrow."
                               place)
                      | Some (Borrows _) | None -> ())
                  | None -> (
                      match yield_mode context callee with
                      | Some Mut -> yields_mut origin
                      | Some Read when not (plain context element) ->
                          reject origin
                            (Printf.sprintf
                               "This method yields borrowed elements of type `%s`, and its body is \
                                not known here, so it could mutate or drop them when it resumes."
                               (T.show element))
                      | _ -> view origin))
              | Yielding_call _ -> ()
              | Cursor { cursor; _ } -> view (Core_walk.place_origin cursor))
          | _ -> ());
    }
    definition
