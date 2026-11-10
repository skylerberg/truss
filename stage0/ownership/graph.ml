(* The control-flow graph of a definition's body, built from its core
   form. Each point does one thing, and the edges follow the order of
   evaluation. The ownership check runs its analyses on this graph.

   The order of evaluation: a call evaluates an indirect callee and then
   its arguments in order. An assignment evaluates its value, then the
   index keys of its target, and then assigns. The right operand of [&&],
   [||], and [==>] may not run. An arm of a [match] binds its names, then
   evaluates its guard, then runs its body.

   The body of a lambda is a separate entry into the graph: it runs when
   the lambda is called, not where the lambda is created. Contracts and
   [proof] blocks are not in the graph, because they move nothing. *)

module T = Types

(* A place that is lent for a stretch of code: to a loop, for the loop's
   body, or by a lending call, for the rest of the statement. While a place
   is lent read-only, the code may not change it. While it is lent [mut],
   the code may not use it at all. *)
type lender = To_loop | To_statement
type loan = { lent : Place.t; mode : T.mode; lender : lender }

(* A place passed to a call, with the mode it is passed with. A place that
   is not [Plain] and is passed [own] is moved. A [Plain] place passed
   [own] is copied, which counts as [Read]. *)
type passed = { place : Place.t; mode : T.mode; at : Core.origin; position : int }

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
  | Hold of { holders : Core.local list; views : Place.t list }
      (** A [let] binds names to a value that views these places, and whatever the roots of these
          places view. *)
  | Store of { place : Place.t; views : Place.t list }
      (** A value that views these places is put in the place: by an assignment, or by a call that
          takes the place [mut] and may keep a view in it. *)
  | Return_view of Place.t list  (** The function returns a value that views these places. *)
  | Views_temporary of Place.t option
      (** A value that the statement drops is viewed by what the statement binds, or by the given
          place. The origin is the dropped value. *)
  | Keeps_lent_part of T.ty  (** A [let] binds a part that a call lends only for the statement. *)
  | Arguments of { places : passed list; lent : (int * Place.t * T.mode * Core.origin) list }
      (** The places passed to one call, in argument order. [lent] lists the arguments that are
          parts lent by a call: the argument's position, the place that lends the part, and how. *)

(* The points with an index from [first] up to, but not including, [limit].
   Points are numbered in the order they are created, so the points of a
   statement are a range. *)
type range = { first : int; limit : int }

type point = {
  action : action;
  origin : Core.origin;
  loans : loan list;  (** The loans in force at the point. *)
  mutable successors : int list;
}

type t = {
  points : point array;
  entries : int list;  (** The [Enter] points: the definition's body first, then each lambda. *)
  parallel_blocks : range list list;  (** For each [parallel] block, the points of each branch. *)
  parallel_loops : (range * Core.local list) list;
      (** For each [parallel for], the points of its body and the locals that its pattern binds. *)
}

type builder = {
  table : (int, point) Hashtbl.t;
  mutable count : int;
  mutable entries : int list;
  mutable loops : (int list ref * int list ref) list;
      (** For each enclosing loop, innermost first: the points that [break] out of it and the points
          that [continue] it. *)
  mutable captured : Core.local list;  (** The captures of the enclosing lambdas. *)
  mutable loans : loan list;
  mutable parallel_blocks : range list list;
  mutable parallel_loops : (range * Core.local list) list;
  plain : T.ty -> bool;
  is_view : T.ty -> bool;
}

let add builder action origin =
  let id = builder.count in
  builder.count <- id + 1;
  Hashtbl.replace builder.table id { action; origin; loans = builder.loans; successors = [] };
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

let operand_type : Core.operand -> T.ty = function
  | Place found -> Core_walk.place_type found
  | Value value -> value.type_

(* Views *)

(* Whether a call's result may view an argument: the argument is lent to
   the call and is not [Plain], or the argument is itself a view. *)
let lends_to_call builder (mode : T.mode) type_ =
  (mode <> Own && not (builder.plain type_)) || builder.is_view type_

(* The places that a value may view, before the analysis adds what the
   roots of those places are known to view. A place used as a value views
   itself. A slice views its base. A lambda views its captures. The result
   of a call views the arguments that the call may keep a view of. *)
let rec viewed builder (value : Core.expression) : Place.t list =
  match value.kind with
  | Use found -> viewed_place builder found
  | Slice { base; _ } -> (
      match Place.of_slice value with Some place -> [ place ] | None -> viewed_place builder base)
  | Lambda { captures; _ } ->
      List.map
        (fun (capture : Core.capture) : Place.t -> { root = Local capture.local; steps = [] })
        captures
  | Call call -> List.concat_map (viewed_operand builder) (lent_arguments builder call)
  | Construct { fields; _ } ->
      List.concat_map
        (fun (_, (field : Core.expression option)) ->
          match field with
          | Some field when builder.is_view field.type_ -> viewed builder field
          | _ -> [])
        fields
  | Echo inner -> viewed builder inner
  | _ -> []

and viewed_place builder (found : Core.place) : Place.t list =
  match (Place.of_core found, found) with
  | Some place, _ -> [ place ]
  | None, Lent call -> viewed builder call
  | None, _ -> []

and viewed_operand builder (found : Core.operand) =
  match found with Place found -> viewed_place builder found | Value value -> viewed builder value

and lent_arguments builder (call : Core.call) : Core.operand list =
  List.filter_map
    (fun (argument : Core.argument) ->
      match argument with
      | Passed { mode; value } when lends_to_call builder mode (operand_type value) -> Some value
      | _ -> None)
    call.arguments

(* The values that the statement drops and that a view-typed value views:
   an owned value with no name, passed read-only to the call that made the
   view. A string literal is in static memory, so it is never dropped. *)
let rec viewed_temporaries builder (value : Core.expression) : Core.expression list =
  match value.kind with
  | Echo inner -> viewed_temporaries builder inner
  | Slice { base; _ } -> owned_temporary_place builder base
  | Call call ->
      List.concat_map
        (fun (argument : Core.argument) ->
          match argument with
          | Passed { mode = Read; value } -> owned_temporary builder value
          | Passed { value = Value value; _ } when builder.is_view value.type_ ->
              viewed_temporaries builder value
          | _ -> [])
        call.arguments
  | Construct { fields; _ } ->
      List.concat_map
        (fun (_, (field : Core.expression option)) ->
          match field with
          | Some field when builder.is_view field.type_ -> viewed_temporaries builder field
          | _ -> [])
        fields
  | _ -> []

and owned_temporary builder (found : Core.operand) : Core.expression list =
  match found with
  | Place found -> owned_temporary_place builder found
  | Value value -> (
      match value.kind with
      | String _ | Lambda _ -> []
      | Use found when Option.is_some (Place.of_core found) -> []
      | _ when builder.plain value.type_ -> []
      | _ when builder.is_view value.type_ -> viewed_temporaries builder value
      | _ -> [ value ])

and owned_temporary_place builder (found : Core.place) : Core.expression list =
  match (Place.of_core found, found) with
  | Some _, _ -> []
  | None, (Lent value | Temporary value) ->
      if builder.plain value.type_ then []
      else if builder.is_view value.type_ then viewed_temporaries builder value
      else [ value ]
  | None, _ -> []

(* The graph *)

let rec expression builder frontier (node : Core.expression) : int list =
  let all frontier nodes = List.fold_left (expression builder) frontier nodes in
  match node.kind with
  | Integer _ | Float _ | Boolean _ | String _ | Function_value _ | Value_parameter _ | Result
  | Current_target | Yielded | Finished | Todo | Quantified _ | Method_time _ ->
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
      let loops = builder.loops and captured = builder.captured and loans = builder.loans in
      builder.loops <- [];
      builder.loans <- [];
      builder.captured <-
        List.map (fun (capture : Core.capture) -> capture.local) captures @ captured;
      let entry = add builder Enter node.origin in
      builder.entries <- entry :: builder.entries;
      let inside =
        emit builder [ entry ] (Bind (List.concat_map pattern_locals parameters)) node.origin
      in
      ignore (block builder inside body);
      builder.loops <- loops;
      builder.loans <- loans;
      builder.captured <- captured;
      frontier
  | Construct { fields; _ } -> all frontier (List.filter_map snd fields)
  | Collection_literal { elements; _ } -> all frontier elements
  | Map_literal { entries } ->
      all frontier (List.concat_map (fun (key, value) -> [ key; value ]) entries)
  | Record_update { base; updates } -> all (expression builder frontier base) (List.map snd updates)
  | Slice { call = { kind = Call call; _ }; _ } -> arguments builder frontier call.arguments
  | Slice { call; _ } -> expression builder frontier call
  | Call call -> call_ builder frontier node call
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

(* A call: its arguments in order, then what the call means for the places
   it is given. *)
and call_ builder frontier (node : Core.expression) (call : Core.call) =
  let frontier =
    match call.callee with
    | Indirect function_value -> operand builder frontier Read function_value
    | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> frontier
  in
  let frontier = arguments builder frontier call.arguments in
  (* The places passed to the call must not overlap if one of them is
     borrowed [mut] or moved. *)
  let passed position (argument : Core.argument) =
    match argument with
    | Passed { mode; value = Place found } -> (
        match Place.of_core found with
        | Some place -> `Place { place; mode; at = Core_walk.place_origin found; position }
        | None -> (
            match Place.lender found with
            | Some (lent, lent_mode) ->
                `Lent (position, lent, lent_mode, Core_walk.place_origin found)
            | None -> `Neither))
    | Passed { mode = Own; value = Value ({ kind = Use found; _ } as value) } -> (
        match Place.of_core found with
        | Some place ->
            `Place
              {
                place;
                mode = (if builder.plain value.type_ then Read else Own);
                at = value.origin;
                position;
              }
        | None -> `Neither)
    | Passed { mode = Mut; value = Value ({ kind = Slice _; _ } as slice) } -> (
        match Place.of_slice slice with
        | Some place -> `Place { place; mode = Mut; at = slice.origin; position }
        | None -> `Neither)
    | Passed _ | Default -> `Neither
  in
  let given = List.mapi passed call.arguments in
  let places = List.filter_map (function `Place place -> Some place | _ -> None) given in
  let lent = List.filter_map (function `Lent lent -> Some lent | _ -> None) given in
  let frontier =
    if List.length places + List.length lent > 1 then
      emit builder frontier (Arguments { places; lent }) node.origin
    else frontier
  in
  (* A place passed [mut] that can hold views may keep a view of what the
     call's other arguments view. *)
  let frontier =
    List.fold_left
      (fun frontier (argument : Core.argument) ->
        match argument with
        | Passed { mode = Mut; value = Place found as kept }
          when builder.is_view (Core_walk.place_type found) -> (
            match Place.of_core found with
            | Some place ->
                let others =
                  List.filter (fun other -> other != kept) (lent_arguments builder call)
                in
                keeps_views builder frontier place node.origin
                  ~views:(List.concat_map (viewed_operand builder) others)
                  ~temporaries:
                    (List.concat_map
                       (function
                         | Core.Value value -> viewed_temporaries builder value | Place _ -> [])
                       others)
            | None -> frontier)
        | _ -> frontier)
      frontier call.arguments
  in
  (* A lending call lends its receiver for the rest of the statement. *)
  (match (call.lends, call.arguments) with
  | Some _, Passed { mode; value = Place receiver } :: _ -> (
      match Place.of_core receiver with
      | Some lent ->
          builder.loans <-
            { lent; mode = (if mode = Mut then Mut else Read); lender = To_statement }
            :: builder.loans
      | None -> ())
  | _ -> ());
  frontier

(* A place comes to hold views of what some values view. None of them may
   be a value that the statement drops. *)
and keeps_views builder frontier (place : Place.t) origin ~views ~temporaries =
  let frontier =
    List.fold_left
      (fun frontier (temporary : Core.expression) ->
        emit builder frontier (Views_temporary (Some place)) temporary.origin)
      frontier temporaries
  in
  emit builder frontier (Store { place; views }) origin

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

(* The value that a function returns. The value of a block, an [if], or a
   [match] that is returned is returned too. *)
and returned builder frontier (value : Core.expression) =
  match value.kind with
  | Block body -> returned_block builder frontier body
  | If { condition; then_; else_ = Some else_ } ->
      let after = expression builder frontier condition in
      returned_block builder after then_ @ returned_block builder after else_
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
          returned_block builder frontier arm.body)
        arms
  | _ ->
      let frontier =
        match value.kind with
        | Use found -> use builder frontier value found ~returned:true
        | _ -> expression builder frontier value
      in
      if builder.is_view value.type_ then
        emit builder frontier (Return_view (viewed builder value)) value.origin
      else frontier

and returned_block builder frontier (body : Core.block) =
  let frontier = List.fold_left (statement builder) frontier body.statements in
  match body.value with Some value -> returned builder frontier value | None -> frontier

and block builder frontier (body : Core.block) =
  let frontier = List.fold_left (statement builder) frontier body.statements in
  match body.value with Some value -> expression builder frontier value | None -> frontier

(* A statement. What a lending call lends in it is lent until its end. *)
and statement builder frontier (node : Core.statement) =
  let loans = builder.loans in
  let frontier = statement_parts builder frontier node in
  builder.loans <- loans;
  frontier

and statement_parts builder frontier (node : Core.statement) =
  match node.kind with
  | Let { pattern; value; else_ } -> let_ builder frontier node pattern value else_
  | Evaluate value -> expression builder frontier value
  | Assign { target; value } -> (
      let frontier = expression builder frontier value in
      let frontier = place_parts builder frontier target in
      match Place.of_core target with
      | Some place ->
          let frontier = emit builder frontier (Assign place) (Core_walk.place_origin target) in
          if builder.is_view value.type_ then
            keeps_views builder frontier place node.origin ~views:(viewed builder value)
              ~temporaries:(viewed_temporaries builder value)
          else frontier
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
      let frontier, held =
        match iteration with
        | Integer_range { start; stop; _ } ->
            (expression builder (expression builder frontier start) stop, None)
        | Yielding_call
            ({ kind = Call { arguments = Passed { mode; value = Place found } :: _; _ }; _ } as call)
          ->
            ( expression builder frontier call,
              Option.map
                (fun lent : loan ->
                  { lent; mode = (if mode = Mut then Mut else Read); lender = To_loop })
                (Place.of_core found) )
        | Yielding_call call -> (expression builder frontier call, None)
        | Cursor { cursor; _ } ->
            ( operand builder frontier Mut (Place cursor),
              Option.map
                (fun lent : loan -> { lent; mode = Read; lender = To_loop })
                (Place.of_core cursor) )
      in
      loop builder frontier ~bound:(pattern_locals pattern) ~held ~condition:None body node.origin
        ~parallel:(match node.kind with For { parallel; _ } -> parallel | _ -> false)
  | While { condition; body; _ } ->
      loop builder frontier ~bound:[] ~held:None ~condition:(Some condition) body node.origin
        ~parallel:false
  | Parallel branches ->
      let frontier, ranges =
        List.fold_left
          (fun (frontier, ranges) branch ->
            let first = builder.count in
            let frontier = statement builder frontier branch in
            (frontier, { first; limit = builder.count } :: ranges))
          (frontier, []) branches
      in
      builder.parallel_blocks <- List.rev ranges :: builder.parallel_blocks;
      frontier
  | Proof _ -> frontier
  | Assert { value; _ } -> expression builder frontier value
  | Yield { mode; part } -> operand builder frontier mode part

(* A [let]: its value, then what its names come to view. *)
and let_ builder frontier (node : Core.statement) (pattern : Core.pattern) (value : Core.operand)
    else_ =
  let frontier = operand builder frontier Read value in
  Option.iter (fun else_ -> ignore (block builder frontier else_)) else_;
  let type_ = operand_type value in
  let mutable_ = match pattern.kind with Bind { mutable_; _ } -> mutable_ | _ -> false in
  let is_place =
    match value with
    | Place found | Value { kind = Use found; _ } -> Option.is_some (Place.of_core found)
    | Value _ -> false
  in
  let lent_part = match value with Place found -> Place.is_lent_part found | Value _ -> false in
  let origin =
    match value with Place found -> Core_walk.place_origin found | Value value -> value.origin
  in
  (* A name cannot keep a part that a call lends, because the part goes
     back at the end of the statement. A [Plain] part is copied, unless it
     is a view, which still refers to the place that lent it. *)
  let frontier =
    if (not mutable_) && lent_part && ((not (builder.plain type_)) || builder.is_view type_) then
      emit builder frontier (Keeps_lent_part type_) origin
    else frontier
  in
  let holds_views = builder.is_view type_ || match type_ with T.Cursor _ -> true | _ -> false in
  let views =
    if mutable_ && is_place then []
    else if (is_place && not (builder.plain type_)) || holds_views then viewed_operand builder value
    else []
  in
  let frontier =
    if holds_views then
      List.fold_left
        (fun frontier (temporary : Core.expression) ->
          emit builder frontier (Views_temporary None) temporary.origin)
        frontier
        (match value with Value value -> viewed_temporaries builder value | Place _ -> [])
    else frontier
  in
  let holders = pattern_locals pattern in
  let frontier = emit builder frontier (Bind holders) node.origin in
  if holds_views || views <> [] then emit builder frontier (Hold { holders; views }) node.origin
  else frontier

(* A loop has a head point, which every iteration passes. A [while] loop
   evaluates its condition after the head, as a statement of its own. The
   loop ends from the head or the condition, and from every [break]. A
   loop over a place lends the place for the body. *)
and loop builder frontier ~bound ~held ~condition ~parallel (body : Core.block) origin =
  match frontier with
  | [] -> []
  | _ ->
      let head = add builder (Bind bound) origin in
      link builder frontier head;
      let breaks = ref [] and continues = ref [] in
      builder.loops <- (breaks, continues) :: builder.loops;
      let loans = builder.loans in
      let tested =
        match condition with
        | Some condition ->
            let tested = expression builder [ head ] condition in
            builder.loans <- loans;
            tested
        | None -> [ head ]
      in
      builder.loans <- Option.to_list held @ loans;
      let first = builder.count in
      let body_end = block builder tested body in
      if parallel then
        builder.parallel_loops <-
          ({ first; limit = builder.count }, bound) :: builder.parallel_loops;
      builder.loans <- loans;
      builder.loops <- List.tl builder.loops;
      link builder (body_end @ !continues) head;
      tested @ !breaks

(* The graph of a definition, or [None] if the definition has no body to
   check: only a function, a test, and a law's proof have one. *)
let of_definition ~plain ~is_view (definition : Core.definition) : t option =
  let body =
    match definition with
    | Function { body = Some body; _ } -> Some (body, true)
    | Test body | Law_proof body -> Some (body, false)
    | Function { body = None; _ } | Type _ | Trait _ | Constant _ | Empty -> None
  in
  Option.map
    (fun ((body : Core.block), returns) ->
      let builder =
        {
          table = Hashtbl.create 64;
          count = 0;
          entries = [];
          loops = [];
          captured = [];
          loans = [];
          parallel_blocks = [];
          parallel_loops = [];
          plain;
          is_view;
        }
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
        parallel_blocks = List.rev builder.parallel_blocks;
        parallel_loops = List.rev builder.parallel_loops;
      })
    body
