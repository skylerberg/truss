(* The rules on [yield], checked on the core form: a lending method yields
   exactly once on every path, and only some yielding methods can be pulled
   as cursors. *)

module T = Types
open Context

(* How many times a path has yielded. *)
type count = Zero | One | Many

let add left right = match (left, right) with Zero, other | other, Zero -> other | _ -> Many

(* The counts that the paths through a body end with. *)
let yield_counts (body : Core.block) : count list =
  let returned = ref [] in
  let rec block counts (body : Core.block) =
    let counts = List.fold_left statement counts body.statements in
    match body.value with Some value -> evaluated counts value | None -> counts
  (* An expression evaluated for its effect. A path that reaches [todo] is
     unfinished, not wrong. A path through an expression of type [Never]
     does not reach the end. *)
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
        if block [ Zero ] body <> [ Zero ] then
          List.concat_map (fun count -> [ count; add count Many ]) counts
        else counts
    | Let { value = Place _; _ } | Assign _ | Compound_assign _ | Parallel _ | Proof _ | Assert _ ->
        counts
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
    | Block body -> block counts body
    | _ -> counts
  in
  let ended = block [ Zero ] body in
  ended @ !returned

(* A lending method yields exactly once on every path. *)
let check_lends context (body : Core.block) ~(name : Syntax.span) =
  let counts = yield_counts body in
  if List.mem Zero counts then
    report context Lends_count name
      "A path through this lending method never yields. It must yield exactly once on every path."
  else if List.mem Many counts then
    report context Lends_count name
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

(* Calls [found] on every statement of a block, at any depth. *)
let each_statement (body : Core.block) found =
  Core_walk.block (Core_walk.deep { Core_walk.ignore_all with statement = found }) body

(* The yielding functions that a function yields through: those that a
   [for] loop in its body iterates over, where the loop's body yields. *)
let yields_through =
  Query.query ~name:"yields_through" ~phase:Bodies ~saved:true ~show:Path.show
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
      (** The method yields read-only views of places, such as [self[index]]. A pull hands out an
          owned value, so only a [Plain] element can be pulled: anything else would be copied
          without a [copy()]. *)

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
        match body_of database path with
        | Some body ->
            let found = ref false in
            each_statement body (fun (node : Core.statement) ->
                match node.kind with
                | Yield { part; _ }
                  when List.exists
                         (fun lent -> Option.is_some (Place.of_core lent))
                         (Core_walk.lent_places part) ->
                    found := true
                | _ -> ());
            !found
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

(* A pull of a method that cannot be pulled. [element] is the type that a
   pull hands out. *)
let check_pull context (at : Syntax.span) method_ element =
  let refuse message = report context Not_pullable at message in
  match Query.demand context.database pullable method_ with
  | Pullable -> ()
  | Yields_mut ->
      refuse
        "A method that yields `mut` access cannot be pulled, since a cursor would store that \
         access."
  | Recursive ->
      refuse
        (Printf.sprintf
           "`%s` yields through a recursive loop, so it can drive a `for` loop but cannot be \
            pulled. A cursor over it is a type with its own stack."
           (Path.show method_))
  | Yields_places ->
      if not (plain context element) then
        refuse
          (Printf.sprintf
             "`%s` yields views of its elements, and pulling one would copy a `%s` unasked. Loop \
              over it with `for`, or pull from a method that yields owned values."
             (Path.show method_) (T.show element))

(* Every pull in a definition: a call of [next] on a cursor, and a [for]
   loop over a cursor held in a variable. *)
let check_pulls context (definition : Core.definition) =
  Core_walk.definition
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) ->
          match (node.kind, node.type_) with
          | Cursor_next cursor, T.Named { arguments = [ T.Type element ]; _ } -> (
              match Core_walk.place_type cursor with
              | T.Cursor { method_; _ } ->
                  check_pull context (span context node.origin) method_ element
              | _ -> ())
          | _ -> ());
      statement =
        (fun (node : Core.statement) ->
          match node.kind with
          | For { iteration = Cursor { cursor; _ }; pattern; _ } -> (
              match Core_walk.place_type cursor with
              | T.Cursor { method_; _ } ->
                  check_pull context
                    (with_mark context (span context (Core_walk.place_origin cursor)))
                    method_ pattern.type_
              | _ -> ())
          | _ -> ());
    }
    definition
