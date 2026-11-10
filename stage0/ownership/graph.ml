(* The control-flow graph of a definition's body, built from its core
   form. Each point does one thing, and the edges follow the order of
   evaluation. The ownership check runs its analyses on this graph.

   The order of evaluation: a call evaluates an indirect callee and then
   its arguments in order, and then borrows the places that it is given
   [mut]. An assignment evaluates its value, then the index keys of its
   target, and then assigns. The right operand of [&&],
   [||], and [==>] may not run. An arm of a [match] binds its names, then
   evaluates its guard, then runs its body.

   The body of a lambda is a separate entry into the graph: it runs when
   the lambda is called, not where the lambda is created. Contracts and
   [proof] blocks are not in the graph, because they move nothing. *)

module T = Types

(* A place that is lent for a stretch of code: to a loop, for the loop's
   body; by a lending call, for the rest of the statement; or to an operand
   that has been evaluated, until the operation that the operand belongs to
   runs. While a place is lent read-only, the code may not change it. While
   it is lent [mut], the code may not use it at all. *)
type lender = To_loop | To_statement | To_operand
type loan = { lent : Place.t; mode : T.mode; lender : lender }

(* A place that a value views, and how. *)
type view = {
  place : Place.t;
  taken : bool;
      (** The value was copied or moved out of the place, so it views what the place's root views
          and not the place. If false, the value refers to the place itself. *)
}

(* A place that a call borrows, with the mode it is borrowed with. *)
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
  | Ends of Core.local list
      (** These locals stop being bound: a loop's variables when the loop ends, an arm's names after
          the arm, and a lambda's parameters at the end of its body. *)
  | Suspend  (** A [yield]. A loop may stop a yielding method here. *)
  | Exit  (** The function returns. *)
  | Hold of { holders : Core.local list; views : view list }
      (** A [let] binds names to a value that views these places, and whatever the roots of these
          places view. *)
  | Store of { place : Place.t; views : view list }
      (** A value that views these places is put in the place: by an assignment, or by a call that
          takes the place [mut] and may keep a view in it. *)
  | Return_view of view list  (** The function returns a value that views these places. *)
  | Views_temporary of Place.t option
      (** A value that the statement drops is viewed by what the statement binds, or by the given
          place. The origin is the dropped value. *)
  | Keeps_lent_part of T.ty  (** A [let] binds a part that a call lends only for the statement. *)
  | Gives_function of view list
      (** A function value that views these places is passed to an [own] parameter. The callee may
          keep the function after the caller returns. *)
  | Write_through of Place.t
      (** A mutation writes through a slice that is held in this place. The mutation changes
          everything that the slice views. *)
  | Arguments of {
      places : passed list;
      views : (int * view list * Core.origin) list;
      yielded : bool;
    }
      (** The places that one call borrows, in argument order. [views] lists the arguments of a view
          type: the argument's position and the places it views. If [yielded], the places are
          instead the ones that a yielded construct lends, and there are no views. *)

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
   roots of those places are known to view. A value read out of a place is
   a copy or a moved value: it views what the place's root views. A slice
   refers to the elements of its base, unless the base is itself a slice. A
   lambda refers to what it captures and to its environment. The result of
   a call views the arguments that the call may keep a view of. *)
let rec viewed builder (value : Core.expression) : view list =
  match value.kind with
  | Use found -> taken_from builder found
  | Slice { base; _ } -> (
      match Place.of_slice value with
      | Some place -> [ { place; taken = Place.is_slice_type (Core_walk.place_type base) } ]
      | None -> viewed_place builder base)
  | Lambda { captures = []; _ } -> []
  | Lambda { captures; _ } ->
      { place = { root = Environment; steps = [] }; taken = false }
      :: List.map
           (fun (capture : Core.capture) ->
             { place = { root = Local capture.local; steps = [] }; taken = false })
           captures
  | Call call -> List.concat_map (viewed_operand builder) (lent_arguments builder call)
  | Construct { fields; _ } ->
      List.concat_map
        (fun (_, (field : Core.operand option)) ->
          match field with
          | Some (Value field) when builder.is_view field.type_ -> viewed builder field
          | Some (Place found) -> viewed_place builder found
          | _ -> [])
        fields
  | Collection_literal { elements; _ } ->
      List.concat_map
        (fun (element : Core.expression) ->
          if builder.is_view element.type_ then viewed builder element else [])
        elements
  | Echo inner | To_any { value = inner; _ } | Convert { value = inner; _ } -> viewed builder inner
  | _ -> []

(* What a value that is copied or moved out of a place views. *)
and taken_from builder (found : Core.place) : view list =
  match (Place.of_core found, found) with
  | Some place, _ -> [ { place; taken = true } ]
  | None, Lent call -> viewed builder call
  | None, _ -> []

(* What a borrow of a place views: the place itself. A place of a [Plain]
   type is copied instead. *)
and viewed_place builder (found : Core.place) : view list =
  match (Place.of_core found, found) with
  | Some place, _ -> [ { place; taken = builder.plain (Core_walk.place_type found) } ]
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
  | Echo inner | To_any { value = inner; _ } | Convert { value = inner; _ } ->
      viewed_temporaries builder inner
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
        (fun (_, (field : Core.operand option)) ->
          match field with
          | Some (Value field) when builder.is_view field.type_ -> viewed_temporaries builder field
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

(* What an evaluated operand refers to until the operation that it belongs
   to runs: a place that is borrowed, and what a view-typed value views. *)
let pending builder (found : Core.operand) : Place.t list =
  match found with
  | Place found -> Option.to_list (Place.of_core found)
  | Value value when builder.is_view value.type_ ->
      List.map (fun (view : view) -> view.place) (viewed builder value)
  | Value _ -> []

(* The graph *)

(* Lends places read-only to an evaluated operand. *)
let reserve builder (places : Place.t list) : loan list =
  let added = List.map (fun lent -> { lent; mode = T.Read; lender = To_operand }) places in
  builder.loans <- added @ builder.loans;
  added

let release builder (added : loan list) =
  builder.loans <- List.filter (fun loan -> not (List.memq loan added)) builder.loans

(* Evaluates the operands of one operation in order. An operand that has
   been evaluated must stay as it is until the operation runs, so what it
   refers to is lent while the operands after it are evaluated. *)
let in_order builder frontier operands ~evaluate ~pending =
  let frontier, added =
    List.fold_left
      (fun (frontier, added) operand ->
        let frontier = evaluate frontier operand in
        (frontier, reserve builder (pending operand) @ added))
      (frontier, []) operands
  in
  release builder added;
  frontier

let rec expression builder frontier (node : Core.expression) : int list =
  let all frontier nodes =
    in_order builder frontier nodes ~evaluate:(expression builder) ~pending:(fun node ->
        pending builder (Value node))
  in
  let scrutinized frontier scrutinees =
    in_order builder frontier scrutinees
      ~evaluate:(fun frontier scrutinee -> operand builder frontier Read scrutinee)
      ~pending:(pending builder)
  in
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
      let bound = List.concat_map pattern_locals parameters in
      let inside = emit builder [ entry ] (Bind bound) node.origin in
      ignore (emit builder (block builder inside body) (Ends bound) node.origin);
      builder.loops <- loops;
      builder.loans <- loans;
      builder.captured <- captured;
      frontier
  | Construct { fields; _ } -> construct builder frontier Read fields
  | Collection_literal { elements; _ } -> all frontier elements
  | Map_literal { entries } ->
      all frontier (List.concat_map (fun (key, value) -> [ key; value ]) entries)
  | Record_update { base; updates } -> all frontier (base :: List.map snd updates)
  | Slice { call = { kind = Call call; _ }; _ } -> arguments builder frontier call.arguments
  | Slice { call; _ } -> expression builder frontier call
  | Call call -> call_ builder frontier node call
  | Operator { arguments; _ } | Specification_function { arguments; _ } -> all frontier arguments
  | Compare { left; right; _ } | Identical (left, right) -> all frontier [ left; right ]
  | And (left, right) | Or (left, right) | Implies (left, right) ->
      let after_left = expression builder frontier left in
      after_left @ expression builder after_left right
  | Not inner | Echo inner | Old inner | To_any { value = inner; _ } | Convert { value = inner; _ }
    ->
      expression builder frontier inner
  | Matches { value; pattern } ->
      let frontier = operand builder frontier Read value in
      binds builder frontier (pattern_locals pattern) [ value ] node.origin
  | Cursor_next cursor -> operand builder frontier Mut (Place cursor)
  | If { condition; then_; else_ } ->
      let after = expression builder frontier condition in
      let then_end = block builder after then_ in
      let else_end = match else_ with Some else_ -> block builder after else_ | None -> after in
      then_end @ else_end
  | Match { scrutinees; arms; _ } ->
      arms_ builder (scrutinized frontier scrutinees) scrutinees arms ~body:(block builder)
  | Block body -> block builder frontier body
  | Provide { implementations; body } ->
      let frontier =
        in_order builder frontier implementations
          ~evaluate:(fun frontier (implementation : Core.implementation) ->
            operand builder frontier implementation.mode implementation.value)
          ~pending:(fun (implementation : Core.implementation) ->
            pending builder implementation.value)
      in
      block builder frontier body
  | Return value ->
      let frontier =
        match value with Some value -> returned builder frontier value | None -> frontier
      in
      ignore (emit builder frontier Exit node.origin);
      []

(* The fields of a construct, evaluated in order. A field that is a place
   is lent to the constructed value with the mode of the [yield] that
   yields it. A [mut] lend begins at the [yield], after every field is
   evaluated, as a [mut] borrow for an argument begins at the call. *)
and construct builder frontier (mode : T.mode) fields =
  in_order builder frontier (List.filter_map snd fields)
    ~evaluate:(fun frontier (field : Core.operand) ->
      match field with
      | Value { kind = Construct { fields; _ }; _ } -> construct builder frontier mode fields
      | _ -> evaluated builder frontier mode field)
    ~pending:(fun field ->
      pending builder field @ List.filter_map Place.of_core (Core_walk.lent_places field))

(* A pattern binds names to parts of what it matches. The names of a
   pattern on a place refer to the place, so they view it. The names of a
   pattern on a value view what the value views. *)
and binds builder frontier (bound : Core.local list) (scrutinees : Core.operand list) origin =
  let frontier = emit builder frontier (Bind bound) origin in
  let views =
    List.concat_map
      (fun (scrutinee : Core.operand) ->
        match scrutinee with
        | Place found -> (
            match Place.of_core found with
            | Some place -> [ { place; taken = false } ]
            | None -> viewed_place builder found)
        | Value value -> if builder.is_view value.type_ then viewed builder value else [])
      scrutinees
  in
  if bound = [] || views = [] then frontier
  else emit builder frontier (Hold { holders = bound; views }) origin

(* The arms of a [match], after its scrutinees. [body] builds the body of
   an arm. *)
and arms_ builder frontier scrutinees (arms : Core.arm list) ~body =
  List.concat_map
    (fun (arm : Core.arm) ->
      let bound = List.concat_map pattern_locals arm.patterns in
      let frontier = binds builder frontier bound scrutinees arm.origin in
      let frontier =
        match arm.guard with Some guard -> expression builder frontier guard | None -> frontier
      in
      emit builder (body frontier arm.body) (Ends bound) arm.origin)
    arms

(* A call: its arguments in order, then what the call means for the places
   it is given. *)
and call_ builder frontier (node : Core.expression) (call : Core.call) =
  let frontier =
    match call.callee with
    | Indirect function_value -> operand builder frontier Read function_value
    | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> frontier
  in
  let frontier = arguments builder frontier call.arguments in
  (* The places that the call borrows must not overlap if one of them is
     borrowed [mut]. *)
  let places =
    List.concat
      (List.mapi
         (fun position (argument : Core.argument) ->
           let place, at =
             match argument with
             | Passed { value = Place found; _ } ->
                 (Place.of_core found, Core_walk.place_origin found)
             | Passed { mode = Mut; value = Value ({ kind = Slice _; _ } as slice) } ->
                 (Place.of_slice slice, slice.origin)
             | Passed { value = Value value; _ } -> (None, value.origin)
             | Default -> (None, node.origin)
           in
           match (place, argument) with
           | Some place, Passed { mode; _ } -> [ { place; mode; at; position } ]
           | _ -> [])
         call.arguments)
  in
  (* A view passed to the call must not view a place that the call borrows
     [mut]. The operations that give a view back to its owner are the
     exception: they take the owner [mut] and the view. *)
  let views =
    match call.callee with
    | Intrinsic { operation = Storage_take_view | View_take_view | Array_take_view; _ } -> []
    | _ ->
        List.concat
          (List.mapi
             (fun position (argument : Core.argument) ->
               match argument with
               | Passed { value; _ } when builder.is_view (operand_type value) ->
                   let origin =
                     match value with
                     | Place found -> Core_walk.place_origin found
                     | Value value -> value.origin
                   in
                   [ (position, viewed_operand builder value, origin) ]
               | Passed _ | Default -> [])
             call.arguments)
  in
  let frontier =
    if List.length places > 1 || (places <> [] && views <> []) then
      emit builder frontier (Arguments { places; views; yielded = false }) node.origin
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
  (* A function value given to an [own] parameter may be kept by the callee. *)
  let frontier =
    List.fold_left
      (fun frontier (argument : Core.argument) ->
        match argument with
        | Passed { mode = Own; value = Value ({ type_ = T.Function _; _ } as value) } ->
            emit builder frontier (Gives_function (viewed builder value)) value.origin
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

(* The arguments of a call. A [mut] borrow for an argument takes effect at
   the call, after every argument is evaluated, so the place is mutated
   after the arguments that follow it are read. *)
and arguments builder frontier (given : Core.argument list) =
  let passed =
    List.filter_map
      (function Core.Passed { mode; value } -> Some (mode, value) | Default -> None)
      given
  in
  let frontier =
    in_order builder frontier passed
      ~evaluate:(fun frontier (mode, value) -> evaluated builder frontier mode value)
      ~pending:(fun (_, value) -> pending builder value)
  in
  List.fold_left
    (fun frontier (mode, value) ->
      if mode = T.Mut then mutated builder frontier value else frontier)
    frontier passed

(* An operand: a place that is borrowed with the given mode, or a value. *)
and operand builder frontier (mode : T.mode) (found : Core.operand) =
  let frontier = evaluated builder frontier mode found in
  if mode = Mut then mutated builder frontier found else frontier

(* What runs when an operand is evaluated. A [mut] borrow of the operand
   comes after it. *)
and evaluated builder frontier (mode : T.mode) (found : Core.operand) =
  match found with
  | Place found -> (
      let frontier = place_parts builder frontier found in
      match Place.of_core found with
      | Some place when mode <> Mut ->
          emit builder frontier (Read place) (Core_walk.place_origin found)
      | _ -> frontier)
  | Value value -> expression builder frontier value

(* The [mut] borrow of an operand. *)
and mutated builder frontier (found : Core.operand) =
  match found with
  | Place found -> (
      let frontier = writes_through builder frontier found ~whole:true in
      match Place.of_core found with
      | Some place -> emit builder frontier (Mutate place) (Core_walk.place_origin found)
      | None -> frontier)
  | Value ({ kind = Slice _; _ } as slice) -> (
      match Place.of_slice slice with
      | Some place -> emit builder frontier (Mutate place) slice.origin
      | None -> frontier)
  | Value _ -> frontier

(* A mutation of a place may write through a slice on the way to it. *)
and writes_through builder frontier (found : Core.place) ~whole =
  match
    Option.bind (Place.written_slice ~whole found) (fun slice ->
        Option.map (fun place -> (place, slice)) (Place.of_core slice))
  with
  | Some (place, slice) ->
      emit builder frontier (Write_through place) (Core_walk.place_origin slice)
  | None -> frontier

(* The expressions that are evaluated to reach a place: the keys of its
   indexes, a lending call, and the value of a temporary. *)
and place_parts builder frontier (found : Core.place) =
  match found with
  | Local _ | Constant _ -> frontier
  | Field { base; _ } -> place_parts builder frontier base
  | Lent index -> (
      match (Place.storage_index index, index.kind) with
      | Some collection, Call { arguments = _ :: keys; _ } ->
          let frontier = place_parts builder frontier collection in
          let added =
            reserve builder
              (List.map (fun (view : view) -> view.place) (viewed_place builder collection))
          in
          let frontier = arguments builder frontier keys in
          release builder added;
          frontier
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
          | Constant _ | Environment -> false
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
        in_order builder frontier scrutinees
          ~evaluate:(fun frontier scrutinee -> operand builder frontier Read scrutinee)
          ~pending:(pending builder)
      in
      arms_ builder after scrutinees arms ~body:(returned_block builder)
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

and statement_kind builder frontier (node : Core.statement) =
  match node.kind with
  | Let { pattern; value; else_ } -> let_ builder frontier node pattern value else_
  | Evaluate value -> expression builder frontier value
  | Assign { target; value } -> (
      let frontier = expression builder frontier value in
      let added = reserve builder (pending builder (Value value)) in
      let frontier = place_parts builder frontier target in
      release builder added;
      let frontier = writes_through builder frontier target ~whole:false in
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
      let frontier = writes_through builder frontier target ~whole:false in
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
      (* The loop's names view what the loop goes over. A name of a [Plain]
         type is a copy, so it views only what that views. *)
      let views =
        match iteration with
        | Integer_range _ -> []
        | Yielding_call call ->
            List.map
              (fun (view : view) ->
                if builder.plain pattern.type_ then { view with taken = true } else view)
              (viewed builder call)
        | Cursor { cursor; _ } -> taken_from builder cursor
      in
      loop builder frontier ~bound:(pattern_locals pattern) ~views ~held ~condition:None body
        node.origin
        ~parallel:(match node.kind with For { parallel; _ } -> parallel | _ -> false)
  | While { condition; body; _ } ->
      loop builder frontier ~bound:[] ~views:[] ~held:None ~condition:(Some condition) body
        node.origin ~parallel:false
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
  | Yield { mode; part = Value { kind = Construct { fields; _ }; _ } as part } ->
      let frontier = construct builder frontier mode fields in
      let lent = Core_walk.lent_places part in
      if mode = Mut then
        let frontier =
          List.fold_left
            (fun frontier found -> mutated builder frontier (Place found))
            frontier lent
        in
        (* The places that the yielded value is lent [mut] must not overlap. *)
        let places =
          List.concat
            (List.mapi
               (fun position (found : Core.place) ->
                 match Place.of_core found with
                 | Some place -> [ { place; mode; at = Core_walk.place_origin found; position } ]
                 | None -> [])
               lent)
        in
        if List.length places > 1 then
          emit builder frontier (Arguments { places; views = []; yielded = true }) node.origin
        else frontier
      else frontier
  | Yield { mode; part } -> operand builder frontier mode part

and statement_parts builder frontier (node : Core.statement) =
  let frontier = statement_kind builder frontier node in
  match node.kind with Yield _ -> emit builder frontier Suspend node.origin | _ -> frontier

(* A [let]: its value, then what its names come to view. *)
and let_ builder frontier (node : Core.statement) (pattern : Core.pattern) (value : Core.operand)
    else_ =
  let frontier = operand builder frontier Read value in
  Option.iter (fun else_ -> ignore (block builder frontier else_)) else_;
  let type_ = operand_type value in
  let mutable_ = match pattern.kind with Bind { mutable_; _ } -> mutable_ | _ -> false in
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
  (* A name bound to a place views the place. A name bound to a value views
     what the value views, if its type can hold views. A value that is
     moved into the name is the name's own, so the name views nothing. *)
  let views =
    match value with
    | Place found
      when holds_views || (Option.is_some (Place.of_core found) && not (builder.plain type_)) ->
        viewed_place builder found
    | Value value when holds_views -> viewed builder value
    | Place _ | Value _ -> []
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
and loop builder frontier ~bound ~views ~held ~condition ~parallel (body : Core.block) origin =
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
      let entered =
        if bound = [] || views = [] then tested
        else emit builder tested (Hold { holders = bound; views }) origin
      in
      let first = builder.count in
      let body_end = block builder entered body in
      if parallel then
        builder.parallel_loops <-
          ({ first; limit = builder.count }, bound) :: builder.parallel_loops;
      builder.loans <- loans;
      builder.loops <- List.tl builder.loops;
      link builder (body_end @ !continues) head;
      let ended = tested @ !breaks in
      if bound = [] then ended else emit builder ended (Ends bound) origin

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
