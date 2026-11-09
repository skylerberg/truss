(* Yielding and lending: a [lends] method yields once on every path, and
   which [yields] methods can be pulled as cursors, and why not. See
   TYPECHECKER.md, "Yielding and lending". *)

open Syntax
module T = Types
module C = Checked
module Properties = Interface.Properties
open Context
open Flow

(* [lends]: one [yield] on every path *)

type count = Zero | One | Many

let add left right = match (left, right) with Zero, other | other, Zero -> other | _ -> Many

let lends_count context (body : block) ~report_span =
  let finished = ref [] in
  let rec block counts (written : block) = List.fold_left statement counts written.statements
  and statement counts (written : statement) =
    match written.kind with
    | Yield _ -> List.map (fun count -> add count One) counts
    (* A path that reaches [todo] is unfinished, not wrong. *)
    | Expression { kind = Todo; _ } -> List.map (fun _ -> One) counts
    | Expression value -> diverges value (expression counts value)
    | Let { value; _ } -> diverges value (expression counts value)
    | For { body; _ } | While { body; _ } ->
        if block [ Zero ] body <> [ Zero ] then
          List.concat_map (fun count -> [ count; add count Many ]) counts
        else counts
    | _ -> counts
  and expression counts (value : expression) =
    match value.kind with
    | If { then_; else_; _ } ->
        let then_counts = block counts then_ in
        let else_counts =
          match else_ with
          | Some (Else other) -> block counts other
          | Some (Else_if other) -> expression counts other
          | None -> counts
        in
        List.sort_uniq compare (then_counts @ else_counts)
    | Match { arms; _ } ->
        List.sort_uniq compare (List.concat_map (fun (arm : arm) -> statement counts arm.body) arms)
    | Return _ ->
        finished := counts @ !finished;
        []
    | Block written -> block counts written
    | _ -> counts
  (* A path through code of type [Never], such as [unreachable] or a call to
     [crash], never reaches the end, so it yields nothing there. *)
  and diverges (value : expression) counts =
    match context.checked.types.(value.id) with Some T.Never -> [] | _ -> counts
  in
  let ends = block [ Zero ] body @ !finished in
  if List.mem Zero ends then
    report context Lends_count report_span
      "A path through this lending method never yields. It must yield exactly once on every path."
  else if List.mem Many ends then
    report context Lends_count report_span
      "A path through this lending method yields more than once. It must yield exactly once on \
       every path."

(* Pullability, the one fact callers read from a body *)

(* The [yields] methods a method yields through: those a [for] loop in its
   body drives with a [yield] somewhere inside the loop. *)
let yields_through =
  Query.query ~name:"yields_through" ~phase:Bodies ~saved:true ~show:Path.show
    (fun database (path : Path.t) ->
      match Interface.Summary.definition database path with
      | Some (key, { kind = Function { body; _ }; _ }) -> (
          match Query.demand database Infer.checked key with
          | Some result ->
              let contains_yield (loop_body : block) =
                let found = ref false in
                let rec statement (written : statement) =
                  (match written.kind with Yield _ -> found := true | _ -> ());
                  Syntax_walk.statement_parts ~expression ~statement written
                and expression value = Syntax_walk.expression_parts ~expression ~statement value in
                List.iter statement loop_body.statements;
                !found
              in
              let through = ref [] in
              let rec statement (written : statement) =
                (match written.kind with
                | For { iterable; body = loop_body; _ } when contains_yield loop_body -> (
                    let driven =
                      match result.checked.loops.(written.id) with
                      | Some (Yielding { call = { callee = Function { path; _ }; _ }; _ }) ->
                          Some path
                      | _ -> (
                          match result.checked.calls.(iterable.id) with
                          | Some { callee = Function { path; _ }; _ } -> Some path
                          | _ -> None)
                    in
                    match driven with Some driven -> through := driven :: !through | None -> ())
                | _ -> ());
                Syntax_walk.statement_parts ~expression ~statement written
              and expression value = Syntax_walk.expression_parts ~expression ~statement value in
              List.iter statement body.statements;
              List.sort_uniq Path.compare !through
          | None -> [])
      | _ -> [])

(* Whether a [yields] method can be pulled as a cursor, and if not, why. *)
type pulling =
  | Pullable
  | Yields_mut  (** A cursor would store [mut] access between pulls. *)
  | Recursive
      (** In its own cycle of yielding through, as a tree's [each] that loops over its subtrees, so
          its cursor would need a stack of its own. *)
  | Yields_places
      (** It yields read-only views of places, such as [self[index]], which a pull hands out as
          owned values: only a [Plain] element can be pulled, since anything else would be copied
          unasked. *)

let pullable =
  Query.query ~name:"pullable" ~phase:Bodies ~saved:true ~show:Path.show
    (fun database (path : Path.t) ->
      let rec reaches visited = function
        | [] -> false
        | next :: rest ->
            if Path.equal next path then true
            else if List.exists (Path.equal next) visited then reaches visited rest
            else reaches (next :: visited) (Query.demand database yields_through next @ rest)
      in
      let yields_places () =
        match Interface.Summary.definition database path with
        | Some (key, { kind = Function { body; _ }; _ }) -> (
            match
              (Query.demand database Resolve.resolved key, Query.demand database Infer.checked key)
            with
            | Some resolved, Some result ->
                let found = ref false in
                let rec statement (written : statement) =
                  (match written.kind with
                  | Yield value when place_in resolved result.checked value <> None -> found := true
                  | _ -> ());
                  Syntax_walk.statement_parts ~expression ~statement written
                and expression value = Syntax_walk.expression_parts ~expression ~statement value in
                List.iter statement body.statements;
                !found
            | _ -> false)
        | _ -> false
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

(* A pull of a method that cannot be pulled: [next()] on its cursor, or a
   [for] loop over a cursor held in a variable. [element] is the type a
   pull hands out. *)
let check_pull context (span : span) method_ element =
  let report_it message = report context Not_pullable span message in
  match Query.demand context.database pullable method_ with
  | Pullable -> ()
  | Yields_mut ->
      report_it
        "A method that yields `mut` access cannot be pulled, since a cursor would store that \
         access."
  | Recursive ->
      report_it
        (Printf.sprintf
           "`%s` yields through a recursive loop, so it can drive a `for` loop but cannot be \
            pulled. A cursor over it is a type with its own stack."
           (Path.show method_))
  | Yields_places ->
      if not (plain context element) then
        report_it
          (Printf.sprintf
             "`%s` yields views of its elements, and pulling one would copy a `%s` unasked. Loop \
              over it with `for`, or pull from a method that yields owned values."
             (Path.show method_) (T.show element))

let check_pulls context =
  Array.iteri
    (fun id call ->
      match call with
      | Some
          {
            C.callee = Trait_method { name = "next"; self_type = T.Cursor { method_; _ }; _ };
            result;
            _;
          } ->
          let element =
            match result with
            | T.Named { arguments = [ T.Type element ]; _ } -> element
            | _ -> T.Error
          in
          Option.iter
            (fun (value : expression) -> check_pull context value.span method_ element)
            (find_expression context id)
      | _ -> ())
    context.checked.calls;
  let rec statement (written : statement) =
    (match (written.kind, context.checked.loops.(written.id)) with
    | For { iterable; pattern; _ }, Some (Pulled { cursor = T.Cursor { method_; _ } }) ->
        check_pull context iterable.span method_
          (Option.value ~default:T.Error context.checked.pattern_types.(pattern.id))
    | _ -> ());
    Syntax_walk.statement_parts ~expression ~statement written
  and expression value = Syntax_walk.expression_parts ~expression ~statement value in
  Syntax_walk.definition ~statement (fun _ -> ()) context.definition
