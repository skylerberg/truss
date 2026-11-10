(* The control-flow graph of a definition's body, built from its core
   form. Each point does one thing to one place, and the edges follow the
   order of evaluation. The ownership check runs its analyses on this
   graph.

   The order of evaluation: a call evaluates an indirect callee and then
   its arguments in order. An assignment evaluates its value, then the
   index keys of its target, and then assigns. The right operand of [&&],
   [||], and [==>] may not run. An arm of a [match] binds its names, then
   evaluates its guard, then runs its body.

   The body of a lambda is a separate entry into the graph: it runs when
   the lambda is called, not where the lambda is created. Contracts and
   [proof] blocks are not in the graph, because they move nothing. *)

module T = Types

type action =
  | Enter  (** The start of a function's body, a test's body, or a lambda's body. *)
  | Read of Place.t  (** The place is read or borrowed read-only. *)
  | Move of {
      place : Place.t;
      use : Core.id;  (** The [Use] node that takes the value. *)
      type_ : T.ty;
      returned : bool;  (** The value is the result of the function. *)
      captured : bool;  (** The place belongs to a function that encloses the current lambda. *)
    }  (** A value that is not [Plain] is taken out of the place. *)
  | Take_lent of T.ty  (** A value that is not [Plain] is taken out of a part that a call lends. *)
  | Mutate of Place.t  (** The place is borrowed [mut]. *)
  | Assign of Place.t
  | Bind of Core.local list  (** A pattern binds these locals to new values. *)
  | Exit  (** The function returns. *)

type point = { action : action; origin : Core.origin; mutable successors : int list }

type t = {
  points : point array;
  entries : int list;  (** The [Enter] points: the definition's body first, then each lambda. *)
}

type builder = {
  table : (int, point) Hashtbl.t;
  mutable count : int;
  mutable entries : int list;
  mutable loops : (int list ref * int list ref) list;
      (** For each enclosing loop, innermost first: the points that [break] out of it and the points
          that [continue] it. *)
  mutable captured : Core.local list;  (** The captures of the enclosing lambdas. *)
  plain : T.ty -> bool;
}

let add builder action origin =
  let id = builder.count in
  builder.count <- id + 1;
  Hashtbl.replace builder.table id { action; origin; successors = [] };
  id

let link builder (frontier : int list) target =
  List.iter
    (fun from ->
      let point = Hashtbl.find builder.table from in
      if not (List.mem target point.successors) then point.successors <- target :: point.successors)
    frontier

(* Adds a point after every point of the frontier. A frontier is the set of
   points that control can come from. An empty frontier is unreachable
   code, which gets no points. *)
let emit builder (frontier : int list) action origin : int list =
  match frontier with
  | [] -> []
  | _ ->
      let id = add builder action origin in
      link builder frontier id;
      [ id ]

let rec pattern_locals (pattern : Core.pattern) : Core.local list =
  match pattern.kind with
  | Bind { local; _ } -> [ local ]
  | Variant { fields; _ } | Record fields ->
      List.concat_map (fun (_, inner) -> pattern_locals inner) fields
  | Alternatives (first :: _) -> pattern_locals first
  | Alternatives [] | Wildcard | Literal _ | Range _ | Equal_to _ -> []

let rec expression builder frontier (node : Core.expression) : int list =
  let all frontier nodes = List.fold_left (expression builder) frontier nodes in
  match node.kind with
  | Integer _ | Float _ | Boolean _ | String _ | Function_value _ | Value_parameter _ | Result
  | Current_target | Yielded | Finished | Todo | Quantified _ ->
      frontier
  | Unreachable -> []
  | Break ->
      (match builder.loops with (breaks, _) :: _ -> breaks := frontier @ !breaks | [] -> ());
      []
  | Continue ->
      (match builder.loops with
      | (_, continues) :: _ -> continues := frontier @ !continues
      | [] -> ());
      []
  | Interpolated { pieces; _ } ->
      List.fold_left
        (fun frontier (piece : Core.piece) ->
          match piece with
          | Text _ -> frontier
          | Displayed { value; _ } -> operand builder frontier Read value)
        frontier pieces
  | Template { call; _ } -> expression builder frontier call
  | Use found -> use builder frontier node found ~returned:false
  | Copy value -> operand builder frontier Read value
  | Lambda { parameters; captures; body; _ } ->
      let frontier =
        List.fold_left
          (fun frontier (capture : Core.capture) ->
            emit builder frontier (Read { root = Local capture.local; steps = [] }) node.origin)
          frontier captures
      in
      let loops = builder.loops and captured = builder.captured in
      builder.loops <- [];
      builder.captured <-
        List.map (fun (capture : Core.capture) -> capture.local) captures @ captured;
      let entry = add builder Enter node.origin in
      builder.entries <- entry :: builder.entries;
      let inside =
        emit builder [ entry ] (Bind (List.concat_map pattern_locals parameters)) node.origin
      in
      ignore (block builder inside body);
      builder.loops <- loops;
      builder.captured <- captured;
      frontier
  | Construct { fields; _ } -> all frontier (List.filter_map snd fields)
  | Collection_literal { elements; _ } -> all frontier elements
  | Map_literal { entries; _ } ->
      all frontier (List.concat_map (fun (key, value) -> [ key; value ]) entries)
  | Record_update { base; updates } -> all (expression builder frontier base) (List.map snd updates)
  | Slice { base; start; stop; _ } -> (
      let frontier = place_parts builder frontier base in
      let frontier = all frontier (Option.to_list start @ Option.to_list stop) in
      match Place.of_core base with
      | Some place -> emit builder frontier (Read place) (Core_walk.place_origin base)
      | None -> frontier)
  | Call call ->
      let frontier =
        match call.callee with
        | Indirect function_value -> operand builder frontier Read function_value
        | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> frontier
      in
      arguments builder frontier call.arguments
  | Operator { arguments; _ } | Cost_function { arguments; _ } -> all frontier arguments
  | Compare { left; right; _ } | Identical (left, right) -> all frontier [ left; right ]
  | And (left, right) | Or (left, right) | Implies (left, right) ->
      let after_left = expression builder frontier left in
      after_left @ expression builder after_left right
  | Not inner | Echo inner | Old inner | To_any { value = inner; _ } | Convert { value = inner; _ }
    ->
      expression builder frontier inner
  | Matches { value; pattern } ->
      let frontier = operand builder frontier Read value in
      emit builder frontier (Bind (pattern_locals pattern)) node.origin
  | Cursor_next cursor -> operand builder frontier Mut (Place cursor)
  | If { condition; then_; else_ } ->
      let after = expression builder frontier condition in
      let then_end = block builder after then_ in
      let else_end = match else_ with Some else_ -> block builder after else_ | None -> after in
      then_end @ else_end
  | Match { scrutinees; arms; _ } ->
      let after =
        List.fold_left
          (fun frontier scrutinee -> operand builder frontier Read scrutinee)
          frontier scrutinees
      in
      List.concat_map
        (fun (arm : Core.arm) ->
          let frontier =
            emit builder after (Bind (List.concat_map pattern_locals arm.patterns)) arm.origin
          in
          let frontier =
            match arm.guard with
            | Some guard -> expression builder frontier guard
            | None -> frontier
          in
          block builder frontier arm.body)
        arms
  | Block body -> block builder frontier body
  | Provide { implementations; body } ->
      let frontier =
        List.fold_left
          (fun frontier (implementation : Core.implementation) ->
            operand builder frontier implementation.mode implementation.value)
          frontier implementations
      in
      block builder frontier body
  | Return value ->
      let frontier =
        match value with Some value -> returned builder frontier value | None -> frontier
      in
      ignore (emit builder frontier Exit node.origin);
      []

and arguments builder frontier (given : Core.argument list) =
  List.fold_left
    (fun frontier (argument : Core.argument) ->
      match argument with
      | Passed { mode; value } -> operand builder frontier mode value
      | Default -> frontier)
    frontier given

(* An operand: a place that is borrowed with the given mode, or a value. *)
and operand builder frontier (mode : T.mode) (found : Core.operand) =
  match found with
  | Place found -> (
      let frontier = place_parts builder frontier found in
      match Place.of_core found with
      | Some place ->
          emit builder frontier
            (if mode = Mut then Mutate place else Read place)
            (Core_walk.place_origin found)
      | None -> frontier)
  | Value ({ kind = Slice _; _ } as slice) when mode = Mut -> (
      let frontier = expression builder frontier slice in
      match Place.of_slice slice with
      | Some place -> emit builder frontier (Mutate place) slice.origin
      | None -> frontier)
  | Value value -> expression builder frontier value

(* The expressions that are evaluated to reach a place: the keys of its
   indexes, a lending call, and the value of a temporary. *)
and place_parts builder frontier (found : Core.place) =
  match found with
  | Local _ | Constant _ -> frontier
  | Field { base; _ } -> place_parts builder frontier base
  | Lent index -> (
      match (Place.storage_index index, index.kind) with
      | Some collection, Call { arguments = _ :: keys; _ } ->
          arguments builder (place_parts builder frontier collection) keys
      | _ -> expression builder frontier index)
  | Temporary value -> expression builder frontier value

(* A [Use]: the value is taken out of the place. *)
and use builder frontier (node : Core.expression) (found : Core.place) ~returned =
  let frontier = place_parts builder frontier found in
  match Place.of_core found with
  | Some place ->
      if builder.plain node.type_ then emit builder frontier (Read place) node.origin
      else
        let captured =
          match place.root with
          | Local local -> List.mem local builder.captured
          | Constant _ -> false
        in
        emit builder frontier
          (Move { place; use = node.id; type_ = node.type_; returned; captured })
          node.origin
  | None ->
      if Place.is_lent_part found && not (builder.plain node.type_) then
        emit builder frontier (Take_lent node.type_) node.origin
      else frontier

(* The value that a function returns. *)
and returned builder frontier (value : Core.expression) =
  match value.kind with
  | Use found -> use builder frontier value found ~returned:true
  | _ -> expression builder frontier value

and block builder frontier (body : Core.block) =
  let frontier = List.fold_left (statement builder) frontier body.statements in
  match body.value with Some value -> expression builder frontier value | None -> frontier

and statement builder frontier (node : Core.statement) =
  match node.kind with
  | Let { pattern; value; else_ } ->
      let frontier = operand builder frontier Read value in
      Option.iter (fun else_ -> ignore (block builder frontier else_)) else_;
      emit builder frontier (Bind (pattern_locals pattern)) node.origin
  | Evaluate value -> expression builder frontier value
  | Assign { target; value } -> (
      let frontier = expression builder frontier value in
      let frontier = place_parts builder frontier target in
      match Place.of_core target with
      | Some place -> emit builder frontier (Assign place) (Core_walk.place_origin target)
      | None -> frontier)
  | Compound_assign { target; value } -> (
      let frontier = expression builder frontier value in
      let frontier = place_parts builder frontier target in
      match Place.of_core target with
      | Some place ->
          let origin = Core_walk.place_origin target in
          emit builder (emit builder frontier (Read place) origin) (Assign place) origin
      | None -> frontier)
  | For { pattern; iteration; body; _ } ->
      let frontier =
        match iteration with
        | Integer_range { start; stop; _ } ->
            expression builder (expression builder frontier start) stop
        | Yielding_call call -> expression builder frontier call
        | Cursor { cursor; _ } -> operand builder frontier Mut (Place cursor)
      in
      loop builder frontier ~bound:(pattern_locals pattern) ~condition:None body node.origin
  | While { condition; body; _ } ->
      loop builder frontier ~bound:[] ~condition:(Some condition) body node.origin
  | Parallel branches -> List.fold_left (statement builder) frontier branches
  | Proof _ -> frontier
  | Assert { value; _ } -> expression builder frontier value
  | Yield { mode; part } -> operand builder frontier mode part

(* A loop has a head point, which every iteration passes. A [while] loop
   evaluates its condition after the head. The loop ends from the head or
   the condition, and from every [break]. *)
and loop builder frontier ~bound ~condition (body : Core.block) origin =
  match frontier with
  | [] -> []
  | _ ->
      let head = add builder (Bind bound) origin in
      link builder frontier head;
      let breaks = ref [] and continues = ref [] in
      builder.loops <- (breaks, continues) :: builder.loops;
      let tested =
        match condition with
        | Some condition -> expression builder [ head ] condition
        | None -> [ head ]
      in
      let body_end = block builder tested body in
      builder.loops <- List.tl builder.loops;
      link builder (body_end @ !continues) head;
      tested @ !breaks

(* The graph of a definition, or [None] if the definition has no body to
   check: only a function, a test, and a law's proof have one. *)
let of_definition ~plain (definition : Core.definition) : t option =
  let body =
    match definition with
    | Function { body = Some body; _ } -> Some (body, true)
    | Test body | Law_proof body -> Some (body, false)
    | Function { body = None; _ } | Type _ | Trait _ | Constant _ | Empty -> None
  in
  Option.map
    (fun ((body : Core.block), returns) ->
      let builder =
        { table = Hashtbl.create 64; count = 0; entries = []; loops = []; captured = []; plain }
      in
      let entry = add builder Enter 0 in
      let frontier = List.fold_left (statement builder) [ entry ] body.statements in
      let frontier =
        match body.value with
        | Some value when returns -> returned builder frontier value
        | Some value -> expression builder frontier value
        | None -> frontier
      in
      if returns then ignore (emit builder frontier Exit 0);
      {
        points = Array.init builder.count (Hashtbl.find builder.table);
        entries = entry :: List.rev builder.entries;
      })
    body
