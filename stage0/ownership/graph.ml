(* The control-flow graph of a definition's body, built from its core form.
   Each point performs one action, and the edges follow evaluation order.
   [Moves] and [Views] run dataflow analyses on this graph.

   Evaluation order:
   - A call evaluates an indirect callee, then its arguments in order. The
     [mut] borrows of its arguments start after the last argument is
     evaluated.
   - An assignment evaluates its value, then the index keys of its target,
     then assigns.
   - [&&], [||], and [==>] short-circuit: the right operand may not run.
   - A [match] arm binds its pattern, then evaluates its guard, then runs
     its body.

   A lambda's body is a separate entry point: it runs when the lambda is
   called, not where the lambda is created. Contracts and [proof] blocks are
   not in the graph, because they are not executed. *)

module T = Types

(* A loan: a borrow of a place that lasts for a region of code. While a
   read-only loan is live, the place cannot be mutated. While a [mut] loan
   is live, the place cannot be used at all.

   - [Loop_body]: a loop borrows the collection that it iterates over.
   - [Provide_body]: a [provide] block borrows its implementations.
   - [Rest_of_statement]: a call of a lending method borrows its receiver
     until the statement ends.
   - [Operand_evaluation]: an evaluated operand stays borrowed until its
     operation runs, so that a later operand cannot mutate it. *)
type duration = Loop_body | Provide_body | Rest_of_statement | Operand_evaluation
type loan = { borrowed : Place.t; mode : T.mode; duration : duration }

(* A place that a view-typed value may borrow from. *)
type view = {
  place : Place.t;
  copied_out : bool;
      (** If false, the value borrows [place] itself, as a slice of a list borrows the list. If
          true, the value is a copy of a view that is stored in [place], so it borrows what the
          stored view borrows and not [place]. *)
}

(* An argument that is a place: the place, the parameter's mode, the
   argument's origin, and its position in the argument list. *)
type borrowed_argument = { place : Place.t; mode : T.mode; at : Core.origin; position : int }

type action =
  | Enter  (** The start of a function's body, a test's body, or a lambda's body. *)
  | Read of Place.t  (** The place is read or borrowed read-only. *)
  | Move of {
      place : Place.t;
      use : Core.id;  (** The [Use] node that moves the value. *)
      type_ : T.ty;
      returned : bool;  (** The moved value is the function's return value. *)
      captured : bool;
          (** The place is a local of an enclosing function, which the current lambda captures. *)
    }  (** A value that is not [Plain] is moved out of the place. *)
  | Move_out_of_lent of T.ty
      (** A value that is not [Plain] is moved out of a part that a lending call lent. *)
  | Mutate of Place.t  (** The place is borrowed [mut]. *)
  | Assign of Place.t
  | Bind of Core.local list  (** A pattern binds these locals to new values. *)
  | Scope_end of Core.local list
      (** These locals go out of scope: a loop's pattern variables after the loop, a [match] arm's
          bindings after the arm, and a lambda's parameters at the end of its body. *)
  | Task_end of { first : int; limit : int }
      (** The end of a [concurrent] branch, whose points are [first] up to [limit], exclusive. If
          another branch exits the block early, the code after the block does not run. So by this
          point the branch must have reinitialized every place that it moved out of a [mut] borrow.
      *)
  | Yield_point of { mode : T.mode; lent : Place.t option list; views : view list }
      (** A [yield]. The caller's loop may [break] here, in which case the method never resumes.
          [lent] is the places that the yield lends, where [None] is a place that the check does not
          track. [views] is the views of the yielded value, if it has a view type. *)
  | Exit  (** The function returns. *)
  | Bind_views of { locals : Core.local list; views : view list }
      (** A pattern binds [locals] to a value that has these views. *)
  | Store of { place : Place.t; views : view list }
      (** A value that has these views is stored in the place: by an assignment, or by a call that
          borrows the place [mut] and may store one of its view arguments there. *)
  | Return_view of view list  (** The function returns a value that has these views. *)
  | View_of_temporary of Place.t option
      (** A dangling view: a temporary is dropped when the statement ends, but a view of it is bound
          by the statement ([None]) or stored in the given place. The point's origin is the
          temporary. *)
  | Bind_lent_part of T.ty
      (** A [let] binds a part that a lending call lent. The loan ends with the statement. *)
  | Pass_owned_function of view list
      (** A function value that has these views is passed to an [own] parameter. The callee may
          store the function, so the function could outlive what it captures. *)
  | Write_through of Place.t
      (** A mutation writes through the slice that is stored in this place, so it mutates every
          place that the slice views. *)
  | Arguments of {
      places : borrowed_argument list;
      views : (int * view list * Core.origin) list;
      yielded : bool;
    }
      (** The places that one call borrows, in argument order, to be checked for aliasing. [views]
          lists each argument of a view type: its position, its views, and its origin. If [yielded],
          the places are those that a yielded constructor lends, and [views] is empty. *)

(* The points numbered [first] up to [limit], exclusive. Points are numbered
   in creation order, so the points of one statement are contiguous. *)
type range = { first : int; limit : int }

type point = {
  action : action;
  origin : Core.origin;
  loans : loan list;  (** The loans that are live at the point. *)
  mutable successors : int list;
}

type fork_join_block = { keyword : string; branches : range list }
(** A [parallel] or [concurrent] block: a fork-join of its branches, which may run at the same time.
    [keyword] is "parallel" or "concurrent", for error messages. *)

type fork_join_loop = { keyword : string; body : range; bound : Core.local list }
(** A [parallel for] or [concurrent for]: a fork-join of its iterations, which may run at the same
    time. [body] is the points of the loop body, and [bound] is the locals that the loop's pattern
    binds. *)

type t = {
  points : point array;
  entries : int list;  (** The [Enter] points: the definition's body first, then each lambda. *)
  fork_join_blocks : fork_join_block list;
  fork_join_loops : fork_join_loop list;
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
  mutable fork_join_blocks : fork_join_block list;
  mutable fork_join_loops : fork_join_loop list;
  plain : T.ty -> bool;
  is_view : T.ty -> bool;
  holds_function : T.ty -> bool;
  stores_function : Core.callee -> int -> bool;
      (** Whether the callee declares the parameter at a position as an [own] parameter of a
          function type. *)
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

(* Adds a point whose predecessors are the points of the frontier. A
   frontier is the set of points from which control reaches the code being
   built. An empty frontier means that the code is unreachable, and it gets
   no points. *)
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
  | Place core_place -> Core_walk.place_type core_place
  | Value value -> value.type_

(* Views *)

(* Whether a call's result may be a view of an argument: the argument is
   borrowed and is not [Plain], or the argument is itself a view. The
   callee's body is not inspected, so this is the conservative answer. *)
let result_may_view builder (mode : T.mode) type_ =
  (mode <> Own && not (builder.plain type_)) || builder.is_view type_

(* The tail expressions of an [if], a [match], or a block. The expression's
   value is the value of one of them. *)
let tail_values (value : Core.expression) : Core.expression list =
  let of_block (body : Core.block) = Option.to_list body.value in
  match value.kind with
  | If { then_; else_; _ } -> of_block then_ @ Option.fold ~none:[] ~some:of_block else_
  | Match { arms; _ } -> List.concat_map (fun (arm : Core.arm) -> of_block arm.body) arms
  | Block body | Provide { body; _ } -> of_block body
  | _ -> []

(* The views of a value, derived from its expression alone. [Views.resolve]
   later adds the views that the roots of these places hold.

   - A value that is copied or moved out of a place is a copy of a view
     stored there.
   - A slice borrows the elements of its base. A slice of a slice is a copy
     of the base slice's view.
   - A capturing lambda borrows each captured local, and its environment
     record.
   - A call's result may view each argument for which [result_may_view]
     holds. *)
let rec views_of builder (value : Core.expression) : view list =
  match value.kind with
  | Use core_place | Copy (Place core_place) | Cursor_next core_place ->
      views_of_copy builder core_place
  | Copy (Value copied) -> views_of builder copied
  | Slice { base; _ } -> (
      match Place.of_slice value with
      | Some place -> [ { place; copied_out = Place.is_slice_type (Core_walk.place_type base) } ]
      | None -> views_of_borrow builder base)
  | Lambda { captures = []; _ } -> []
  | Lambda { captures; _ } ->
      { place = { root = Environment; steps = [] }; copied_out = false }
      :: List.map
           (fun (capture : Core.capture) ->
             { place = { root = Local capture.local; steps = [] }; copied_out = false })
           captures
  | Call call -> List.concat_map (views_of_operand builder) (viewable_arguments builder call)
  | Template { call; _ } -> views_of builder call
  | Construct { fields; _ } ->
      List.concat_map
        (fun (_, (field : Core.operand option)) ->
          match field with
          | Some (Value field) when builder.is_view field.type_ -> views_of builder field
          | Some (Place core_place) -> views_of_borrow builder core_place
          | _ -> [])
        fields
  | Collection_literal { elements; _ } -> List.concat_map (views_of_part builder) elements
  | Record_update { base; updates } ->
      views_of builder base
      @ List.concat_map (fun (_, update) -> views_of_part builder update) updates
  | Echo inner | To_any { value = inner; _ } | Convert { value = inner; _ } ->
      views_of builder inner
  (* The value of an [if], a [match], or a block is one of its tail
     expressions. *)
  | If _ | Match _ | Block _ | Provide _ -> List.concat_map (views_of builder) (tail_values value)
  (* These produce a value that has no views, or no value. Every kind is
     listed, so that adding a kind to the core form forces a decision here. *)
  | Integer _ | Float _ | Boolean _ | String _ | Function_value _ | Value_parameter _
  | Map_literal _ | Operator _ | Compare _ | Not _ | And _ | Or _ | Implies _ | Matches _ | Return _
  | Break | Continue | Task_exit _ | Todo | Unreachable | Result | Old _ | Current_target
  | Quantified _ | Yielded | Finished | Identical _ | Specification_function _ | Method_time _ ->
      []

(* The views of a subexpression, if it has a view type. *)
and views_of_part builder (part : Core.expression) : view list =
  if builder.is_view part.type_ then views_of builder part else []

(* The views of a value that is copied or moved out of a place. *)
and views_of_copy builder (core_place : Core.place) : view list =
  match (Place.of_core core_place, core_place) with
  | Some place, _ -> [ { place; copied_out = true } ]
  | None, Lent call -> views_of builder call
  | None, _ -> []

(* The views of a borrow of a place: the place itself. A place of a [Plain]
   type is copied, not borrowed. *)
and views_of_borrow builder (core_place : Core.place) : view list =
  match (Place.of_core core_place, core_place) with
  | Some place, _ -> [ { place; copied_out = builder.plain (Core_walk.place_type core_place) } ]
  | None, Lent call -> views_of builder call
  | None, _ -> []

and views_of_operand builder (core_operand : Core.operand) =
  match core_operand with
  | Place core_place -> views_of_borrow builder core_place
  | Value value -> views_of builder value

and viewable_arguments builder (call : Core.call) : Core.operand list =
  List.filter_map
    (fun (argument : Core.argument) ->
      match argument with
      | Passed { mode; value; _ } when result_may_view builder mode (operand_type value) ->
          Some value
      | _ -> None)
    call.arguments

(* The temporaries that a view-typed value borrows from: owned values that
   have no name and were passed read-only to the call that produced the
   view. A temporary is dropped when its statement ends. A string literal
   has static storage, so it is never dropped. *)
let rec viewed_temporaries builder (value : Core.expression) : Core.expression list =
  let of_part (part : Core.expression) =
    if builder.is_view part.type_ then viewed_temporaries builder part else []
  in
  match value.kind with
  | Echo inner | To_any { value = inner; _ } | Convert { value = inner; _ } | Copy (Value inner) ->
      viewed_temporaries builder inner
  | If _ | Match _ | Block _ | Provide _ ->
      List.concat_map (viewed_temporaries builder) (tail_values value)
  | Slice { base; _ } -> owned_temporary_place builder base
  | Call call ->
      List.concat_map
        (fun (argument : Core.argument) ->
          match argument with
          | Passed { mode = Read; value; _ } -> owned_temporary builder value
          | Passed { value = Value value; _ } -> of_part value
          | _ -> [])
        call.arguments
  | Template { call; _ } -> viewed_temporaries builder call
  | Construct { fields; _ } ->
      List.concat_map
        (fun (_, (field : Core.operand option)) ->
          match field with Some (Value field) -> of_part field | Some (Place _) | None -> [])
        fields
  | Collection_literal { elements; _ } -> List.concat_map of_part elements
  | Record_update { base; updates } ->
      viewed_temporaries builder base @ List.concat_map (fun (_, update) -> of_part update) updates
  (* A value copied out of a place borrows from a named place, not from a
     temporary. A lambda borrows locals. The rest have no views. Every kind
     is listed, so that adding a kind to the core form forces a decision
     here. *)
  | Use _
  | Copy (Place _)
  | Cursor_next _ | Lambda _ | Integer _ | Float _ | Boolean _ | String _ | Function_value _
  | Value_parameter _ | Map_literal _ | Operator _ | Compare _ | Not _ | And _ | Or _ | Implies _
  | Matches _ | Return _ | Break | Continue | Task_exit _ | Todo | Unreachable | Result | Old _
  | Current_target | Quantified _ | Yielded | Finished | Identical _ | Specification_function _
  | Method_time _ ->
      []

and owned_temporary builder (core_operand : Core.operand) : Core.expression list =
  match core_operand with
  | Place core_place -> owned_temporary_place builder core_place
  | Value value -> (
      match value.kind with
      | String _ | Lambda _ -> []
      | Use core_place when Option.is_some (Place.of_core core_place) -> []
      | _ when builder.plain value.type_ -> []
      | _ when builder.is_view value.type_ -> viewed_temporaries builder value
      | _ -> [ value ])

and owned_temporary_place builder (core_place : Core.place) : Core.expression list =
  match (Place.of_core core_place, core_place) with
  | Some _, _ -> []
  | None, (Lent value | Temporary value) ->
      if builder.plain value.type_ then []
      else if builder.is_view value.type_ then viewed_temporaries builder value
      else [ value ]
  | None, _ -> []

(* The places that an evaluated operand depends on until its operation runs:
   the place that it borrows, or the places that its view-typed value views. *)
let operand_borrows builder (core_operand : Core.operand) : Place.t list =
  match core_operand with
  | Place core_place -> Option.to_list (Place.of_core core_place)
  | Value value when builder.is_view value.type_ ->
      List.map (fun (view : view) -> view.place) (views_of builder value)
  | Value _ -> []

(* The graph *)

(* Starts a read-only [Operand_evaluation] loan on each place. *)
let add_operand_loans builder (places : Place.t list) : loan list =
  let added =
    List.map (fun borrowed -> { borrowed; mode = T.Read; duration = Operand_evaluation }) places
  in
  builder.loans <- added @ builder.loans;
  added

let remove_loans builder (added : loan list) =
  builder.loans <- List.filter (fun loan -> not (List.memq loan added)) builder.loans

(* Evaluates the operands of one operation in order. A later operand must
   not mutate what an earlier operand evaluated to, so the places of each
   evaluated operand stay borrowed read-only until the last operand is
   evaluated. *)
let evaluate_in_order builder frontier operands ~evaluate ~borrows =
  let frontier, added =
    List.fold_left
      (fun (frontier, added) operand ->
        let frontier = evaluate frontier operand in
        (frontier, add_operand_loans builder (borrows operand) @ added))
      (frontier, []) operands
  in
  remove_loans builder added;
  frontier

let rec expression builder frontier (node : Core.expression) : int list =
  let all frontier nodes =
    evaluate_in_order builder frontier nodes ~evaluate:(expression builder) ~borrows:(fun node ->
        operand_borrows builder (Value node))
  in
  let scrutinized frontier scrutinees =
    evaluate_in_order builder frontier scrutinees
      ~evaluate:(fun frontier scrutinee -> operand builder frontier Read scrutinee)
      ~borrows:(operand_borrows builder)
  in
  match node.kind with
  | Integer _ | Float _ | Boolean _ | String _ | Function_value _ | Value_parameter _ | Result
  | Current_target | Yielded | Finished | Todo | Method_time _ ->
      frontier
  | Quantified { binder; body; _ } -> quantified builder frontier node binder body
  (* An early exit from a [concurrent] task transfers control to the exit's
     target. The sibling tasks have finished by then, and each is modeled by
     its own control flow. *)
  | Task_exit { exit; _ } -> expression builder frontier exit
  | Unreachable -> []
  | Break ->
      (match builder.loops with (breaks, _) :: _ -> breaks := frontier @ !breaks | [] -> ());
      []
  | Continue ->
      (match builder.loops with
      | (_, continues) :: _ -> continues := frontier @ !continues
      | [] -> ());
      []
  | Template { call; _ } -> expression builder frontier call
  | Use core_place -> use builder frontier node core_place ~returned:false
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
      ignore (emit builder (block builder inside body) (Scope_end bound) node.origin);
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
  | And _ | Or _ | Implies _ | Not _ ->
      let on_true, on_false = condition builder frontier node in
      List.sort_uniq compare (on_true @ on_false)
  | Echo inner | Old inner | To_any { value = inner; _ } | Convert { value = inner; _ } ->
      expression builder frontier inner
  | Matches { value; pattern } ->
      let frontier = operand builder frontier Read value in
      bind_pattern builder frontier (pattern_locals pattern) [ value ] node.origin
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
        evaluate_in_order builder frontier implementations
          ~evaluate:(fun frontier (implementation : Core.implementation) ->
            operand builder frontier implementation.mode implementation.value)
          ~borrows:(fun (implementation : Core.implementation) ->
            operand_borrows builder implementation.value)
      in
      (* The body uses the implementations, so an implementation that is a
         place stays borrowed for the body. *)
      let loans = builder.loans in
      builder.loans <-
        List.filter_map
          (fun (implementation : Core.implementation) ->
            match implementation.value with
            | Place core_place ->
                Option.map
                  (fun borrowed : loan ->
                    {
                      borrowed;
                      mode = (if implementation.mode = Mut then Mut else Read);
                      duration = Provide_body;
                    })
                  (Place.of_core core_place)
            | Value _ -> None)
          implementations
        @ loans;
      let frontier = block builder frontier body in
      builder.loans <- loans;
      frontier
  | Return value ->
      let frontier =
        match value with Some value -> returned_value builder frontier value | None -> frontier
      in
      ignore (emit builder frontier Exit node.origin);
      []

(* Evaluates a constructor's fields in order. A field that is a place is
   lent to the constructed value, with the mode of the enclosing [yield]. A
   [mut] loan starts at the [yield], after every field is evaluated, as an
   argument's [mut] borrow starts at the call. *)
and construct builder frontier (mode : T.mode) fields =
  evaluate_in_order builder frontier (List.filter_map snd fields)
    ~evaluate:(fun frontier (field : Core.operand) ->
      match field with
      | Value { kind = Construct { fields; _ }; _ } -> construct builder frontier mode fields
      | _ -> evaluate_operand builder frontier mode field)
    ~borrows:(fun field ->
      operand_borrows builder field @ List.filter_map Place.of_core (Core_walk.lent_places field))

(* Binds a pattern's locals. If the scrutinee is a place, the bindings alias
   parts of the place, so they view it. If the scrutinee is a value, the
   bindings have the value's views. *)
and bind_pattern builder frontier (bound : Core.local list) (scrutinees : Core.operand list) origin
    =
  let frontier = emit builder frontier (Bind bound) origin in
  let views =
    List.concat_map
      (fun (scrutinee : Core.operand) ->
        match scrutinee with
        | Place core_place -> (
            match Place.of_core core_place with
            | Some place -> [ { place; copied_out = false } ]
            | None -> views_of_borrow builder core_place)
        | Value value -> if builder.is_view value.type_ then views_of builder value else [])
      scrutinees
  in
  if bound = [] || views = [] then frontier
  else emit builder frontier (Bind_views { locals = bound; views }) origin

(* An executable quantifier is a loop that stops at the first counterexample
   or witness: it evaluates its range or collection, then its body once per
   element. It borrows the collection for the loop, as a [for] loop does. A
   quantifier in a specification is not executed. *)
and quantified builder frontier (node : Core.expression) (binder : Core.binder)
    (body : Core.expression) =
  let run frontier (pattern : Core.pattern) ~views ~loan =
    loop builder frontier ~bound:(pattern_locals pattern) ~views ~loan ~condition:None
      { statements = []; value = Some body; diverges = false }
      node.origin ~fork_join:None
  in
  match binder with
  | Over_type _ | Over_collection _ -> frontier
  | Over_range { pattern; start; stop; _ } ->
      run (expression builder (expression builder frontier start) stop) pattern ~views:[] ~loan:None
  | Over_each { pattern; call } ->
      let loan =
        match call.kind with
        | Call { arguments = Passed { value = Place core_place; _ } :: _; _ } ->
            Option.map
              (fun borrowed : loan -> { borrowed; mode = Read; duration = Loop_body })
              (Place.of_core core_place)
        | _ -> None
      in
      let views =
        List.map
          (fun (view : view) ->
            if builder.plain pattern.type_ then { view with copied_out = true } else view)
          (views_of builder call)
      in
      run (expression builder frontier call) pattern ~views ~loan

(* The arms of a [match], given the frontier after its scrutinees are
   evaluated. [body] builds an arm's body. *)
and arms_ builder frontier scrutinees (arms : Core.arm list) ~body =
  List.concat_map
    (fun (arm : Core.arm) ->
      let bound = List.concat_map pattern_locals arm.patterns in
      let frontier = bind_pattern builder frontier bound scrutinees arm.origin in
      (* If a guard is false, the later arms are matched against the same
         scrutinees. So the scrutinees stay borrowed read-only while a guard
         is evaluated, and a guard cannot mutate them. *)
      let frontier =
        match arm.guard with
        | Some guard ->
            let added =
              add_operand_loans builder (List.concat_map (operand_borrows builder) scrutinees)
            in
            let frontier = expression builder frontier guard in
            remove_loans builder added;
            frontier
        | None -> frontier
      in
      emit builder (body frontier arm.body) (Scope_end bound) arm.origin)
    arms

(* A call: evaluates the callee and the arguments, then emits the checks and
   the effects of the call on the places that it borrows. *)
and call_ builder frontier (node : Core.expression) (call : Core.call) =
  let frontier =
    match call.callee with
    | Indirect function_value -> operand builder frontier Read function_value
    | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> frontier
  in
  let frontier = arguments builder frontier call.arguments in
  (* Aliasing: two places that the call borrows must not overlap if either
     is borrowed [mut]. *)
  let places =
    List.concat
      (List.mapi
         (fun position (argument : Core.argument) ->
           let place, at =
             match argument with
             | Passed { value = Place core_place; _ } ->
                 (Place.of_core core_place, Core_walk.place_origin core_place)
             | Passed { mode = Mut; value = Value ({ kind = Slice _; _ } as slice); _ } ->
                 (Place.of_slice slice, slice.origin)
             | Passed { value = Value value; _ } -> (None, value.origin)
             | Default -> (None, node.origin)
           in
           match (place, argument) with
           | Some place, Passed { mode; _ } -> [ { place; mode; at; position } ]
           | _ -> [])
         call.arguments)
  in
  (* Aliasing: a view argument must not view a place that the call borrows
     [mut]. The intrinsics that return a view to its owner are exempt: they
     take the owner [mut] together with its view. *)
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
                     | Place core_place -> Core_walk.place_origin core_place
                     | Value value -> value.origin
                   in
                   [ (position, views_of_operand builder value, origin) ]
               | Passed _ | Default -> [])
             call.arguments)
  in
  let frontier =
    if List.length places > 1 || (places <> [] && views <> []) then
      emit builder frontier (Arguments { places; views; yielded = false }) node.origin
    else frontier
  in
  (* The callee may store its view arguments in a [mut] argument whose type
     can hold views. It cannot store a view of a borrowed argument that is
     not a view: the callee's own check rejects that. From a function whose
     result is not a view, the callee gets no view but the function itself,
     so it can store that argument only in a type that holds a function. *)
  let can_store_in target (other : Core.operand) =
    match operand_type other with
    | T.Function { output = Returns output; _ } when not (builder.is_view output) ->
        builder.holds_function target
    | _ -> true
  in
  let frontier =
    List.fold_left
      (fun frontier (argument : Core.argument) ->
        match argument with
        | Passed { mode = Mut; value = Place core_place as target; _ }
          when builder.is_view (Core_walk.place_type core_place) -> (
            match Place.of_core core_place with
            | Some place ->
                let others =
                  List.filter
                    (fun other ->
                      other != target
                      && builder.is_view (operand_type other)
                      && can_store_in (Core_walk.place_type core_place) other)
                    (viewable_arguments builder call)
                in
                store_views builder frontier place node.origin
                  ~views:(List.concat_map (views_of_operand builder) others)
                  ~temporaries:
                    (List.concat_map
                       (function
                         | Core.Value value -> viewed_temporaries builder value | Place _ -> [])
                       others)
            | None -> frontier)
        | _ -> frontier)
      frontier call.arguments
  in
  (* The callee may store a function value that it receives through an [own]
     parameter. *)
  let frontier =
    List.fold_left
      (fun frontier (position, (argument : Core.argument)) ->
        match argument with
        | Passed { mode = Own; value = Value ({ type_ = T.Function _; _ } as value); _ }
          when builder.stores_function call.callee position ->
            emit builder frontier (Pass_owned_function (views_of builder value)) value.origin
        | _ -> frontier)
      frontier
      (List.mapi (fun position argument -> (position, argument)) call.arguments)
  in
  (* A call of a lending method borrows its receiver until the statement
     ends. *)
  (match (call.lends, call.arguments) with
  | Some _, Passed { mode; value = Place receiver; _ } :: _ -> (
      match Place.of_core receiver with
      | Some borrowed ->
          builder.loans <-
            { borrowed; mode = (if mode = Mut then Mut else Read); duration = Rest_of_statement }
            :: builder.loans
      | None -> ())
  | _ -> ());
  frontier

(* Stores views in a place. None of them may be a view of a temporary, which
   is dropped when the statement ends. *)
and store_views builder frontier (place : Place.t) origin ~views ~temporaries =
  let frontier =
    List.fold_left
      (fun frontier (temporary : Core.expression) ->
        emit builder frontier (View_of_temporary (Some place)) temporary.origin)
      frontier temporaries
  in
  emit builder frontier (Store { place; views }) origin

(* Evaluates a call's arguments. An argument's [mut] borrow starts at the
   call, after every argument is evaluated, so the later arguments can still
   read the place. *)
and arguments builder frontier (call_arguments : Core.argument list) =
  let passed =
    List.filter_map
      (function Core.Passed { mode; value; _ } -> Some (mode, value) | Default -> None)
      call_arguments
  in
  let frontier =
    evaluate_in_order builder frontier passed
      ~evaluate:(fun frontier (mode, value) -> evaluate_operand builder frontier mode value)
      ~borrows:(fun (_, value) -> operand_borrows builder value)
  in
  List.fold_left
    (fun frontier (mode, value) ->
      if mode = T.Mut then borrow_mut builder frontier value else frontier)
    frontier passed

(* An operand: a place that is borrowed with the given mode, or a value. *)
and operand builder frontier (mode : T.mode) (core_operand : Core.operand) =
  let frontier = evaluate_operand builder frontier mode core_operand in
  if mode = Mut then borrow_mut builder frontier core_operand else frontier

(* Evaluates an operand. [borrow_mut] emits the [mut] borrow of the operand
   separately. *)
and evaluate_operand builder frontier (mode : T.mode) (core_operand : Core.operand) =
  match core_operand with
  | Place core_place -> (
      let frontier = place_subexpressions builder frontier core_place in
      match Place.of_core core_place with
      | Some place when mode <> Mut ->
          emit builder frontier (Read place) (Core_walk.place_origin core_place)
      | _ -> frontier)
  | Value value -> expression builder frontier value

(* The [mut] borrow of an operand. *)
and borrow_mut builder frontier (core_operand : Core.operand) =
  match core_operand with
  | Place core_place -> (
      let frontier = writes_through builder frontier core_place ~whole:true in
      match Place.of_core core_place with
      | Some place -> emit builder frontier (Mutate place) (Core_walk.place_origin core_place)
      | None -> frontier)
  | Value ({ kind = Slice _; _ } as slice) -> (
      match Place.of_slice slice with
      | Some place -> emit builder frontier (Mutate place) slice.origin
      | None -> frontier)
  | Value _ -> frontier

(* A mutation of a place writes through a slice if the path to the place
   goes through one. *)
and writes_through builder frontier (core_place : Core.place) ~whole =
  match
    Option.bind (Place.written_slice ~whole core_place) (fun slice ->
        Option.map (fun place -> (place, slice)) (Place.of_core slice))
  with
  | Some (place, slice) ->
      emit builder frontier (Write_through place) (Core_walk.place_origin slice)
  | None -> frontier

(* Evaluates the subexpressions of a place: its index keys, a lending call,
   and the value of a temporary. *)
and place_subexpressions builder frontier (core_place : Core.place) =
  match core_place with
  | Local _ | Constant _ -> frontier
  | Field { base; _ } -> place_subexpressions builder frontier base
  | Lent index -> (
      match (Place.storage_index index, index.kind) with
      | Some collection, Call { arguments = _ :: keys; _ } ->
          let frontier = place_subexpressions builder frontier collection in
          let added =
            add_operand_loans builder
              (List.map (fun (view : view) -> view.place) (views_of_borrow builder collection))
          in
          let frontier = arguments builder frontier keys in
          remove_loans builder added;
          frontier
      | _ -> expression builder frontier index)
  | Temporary value -> expression builder frontier value

(* A [Use]: the value is copied or moved out of the place. *)
and use builder frontier (node : Core.expression) (core_place : Core.place) ~returned =
  let frontier = place_subexpressions builder frontier core_place in
  match Place.of_core core_place with
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
      if Place.is_lent_part core_place && not (builder.plain node.type_) then
        emit builder frontier (Move_out_of_lent node.type_) node.origin
      else frontier

(* The function's return value. If it is a block, an [if], or a [match], its
   tail expressions are return values too. *)
and returned_value builder frontier (value : Core.expression) =
  match value.kind with
  | Block body -> returned_block builder frontier body
  | If { condition; then_; else_ = Some else_ } ->
      let after = expression builder frontier condition in
      returned_block builder after then_ @ returned_block builder after else_
  | Match { scrutinees; arms; _ } ->
      let after =
        evaluate_in_order builder frontier scrutinees
          ~evaluate:(fun frontier scrutinee -> operand builder frontier Read scrutinee)
          ~borrows:(operand_borrows builder)
      in
      arms_ builder after scrutinees arms ~body:(returned_block builder)
  | _ ->
      let frontier =
        match value.kind with
        | Use core_place -> use builder frontier value core_place ~returned:true
        | _ -> expression builder frontier value
      in
      if builder.is_view value.type_ then
        emit builder frontier (Return_view (views_of builder value)) value.origin
      else frontier

and returned_block builder frontier (body : Core.block) =
  let frontier = List.fold_left (statement builder) frontier body.statements in
  match body.value with Some value -> returned_value builder frontier value | None -> frontier

(* The points from which control leaves a Boolean expression with [true],
   and the points from which it leaves with [false]. A short-circuit
   operator evaluates its right operand from one of the two: [left && right]
   evaluates [right] only where [left] is [true]. So an operand has an edge
   to the operand after it and to the code after the whole expression, and a
   chain of operators has a number of edges linear in its length. *)
and condition builder frontier (node : Core.expression) : int list * int list =
  match node.kind with
  | And (left, right) ->
      let left_true, left_false = condition builder frontier left in
      let right_true, right_false = condition builder left_true right in
      (right_true, left_false @ right_false)
  | Or (left, right) ->
      let left_true, left_false = condition builder frontier left in
      let right_true, right_false = condition builder left_false right in
      (left_true @ right_true, right_false)
  | Implies (left, right) ->
      let left_true, left_false = condition builder frontier left in
      let right_true, right_false = condition builder left_true right in
      (left_false @ right_true, right_false)
  | Not inner ->
      let on_true, on_false = condition builder frontier inner in
      (on_false, on_true)
  | _ ->
      let after = expression builder frontier node in
      (after, after)

and block builder frontier (body : Core.block) =
  let frontier = List.fold_left (statement builder) frontier body.statements in
  match body.value with Some value -> expression builder frontier value | None -> frontier

(* A statement. The loans that lending calls start in the statement end with
   it. *)
and statement builder frontier (node : Core.statement) =
  let loans = builder.loans in
  let frontier = statement_and_yield_point builder frontier node in
  builder.loans <- loans;
  frontier

and statement_actions builder frontier (node : Core.statement) =
  match node.kind with
  | Let { pattern; value; else_ } -> let_ builder frontier node pattern value else_
  | Evaluate value -> expression builder frontier value
  | Assign { target; value } -> (
      let frontier = expression builder frontier value in
      let added = add_operand_loans builder (operand_borrows builder (Value value)) in
      let frontier = place_subexpressions builder frontier target in
      remove_loans builder added;
      let frontier = writes_through builder frontier target ~whole:false in
      match Place.of_core target with
      | Some place ->
          let frontier = emit builder frontier (Assign place) (Core_walk.place_origin target) in
          if builder.is_view value.type_ then
            store_views builder frontier place node.origin ~views:(views_of builder value)
              ~temporaries:(viewed_temporaries builder value)
          else frontier
      | None -> frontier)
  | Compound_assign { target; value } -> (
      let frontier = expression builder frontier value in
      let frontier = place_subexpressions builder frontier target in
      let frontier = writes_through builder frontier target ~whole:false in
      match Place.of_core target with
      | Some place ->
          let origin = Core_walk.place_origin target in
          emit builder (emit builder frontier (Read place) origin) (Assign place) origin
      | None -> frontier)
  | For { pattern; iteration; body; _ } ->
      let frontier, loan =
        match iteration with
        | Integer_range { start; stop; _ } ->
            (expression builder (expression builder frontier start) stop, None)
        | Yielding_call
            ({ kind = Call { arguments = Passed { mode; value = Place core_place; _ } :: _; _ }; _ }
             as call) ->
            ( expression builder frontier call,
              Option.map
                (fun borrowed : loan ->
                  { borrowed; mode = (if mode = Mut then Mut else Read); duration = Loop_body })
                (Place.of_core core_place) )
        | Yielding_call call -> (expression builder frontier call, None)
        | Cursor { cursor; _ } ->
            ( operand builder frontier Mut (Place cursor),
              Option.map
                (fun borrowed : loan -> { borrowed; mode = Read; duration = Loop_body })
                (Place.of_core cursor) )
      in
      (* The loop's pattern variables view the collection that the loop
         iterates over. A variable of a [Plain] type holds a copy of the
         element, so it has only the element's own views. *)
      let views =
        match iteration with
        | Integer_range _ -> []
        | Yielding_call call ->
            List.map
              (fun (view : view) ->
                if builder.plain pattern.type_ then { view with copied_out = true } else view)
              (views_of builder call)
        | Cursor { cursor; _ } -> views_of_copy builder cursor
      in
      loop builder frontier ~bound:(pattern_locals pattern) ~views ~loan ~condition:None body
        node.origin
        ~fork_join:
          (match node.kind with
          | For { mode = Parallel_loop; _ } -> Some "parallel"
          | For { mode = Concurrent_loop; _ } -> Some "concurrent"
          | _ -> None)
  | While { condition; body; _ } ->
      loop builder frontier ~bound:[] ~views:[] ~loan:None ~condition:(Some condition) body
        node.origin ~fork_join:None
  | Parallel branches | Concurrent branches ->
      let concurrent = match node.kind with Concurrent _ -> true | _ -> false in
      let frontier, ranges =
        List.fold_left
          (fun (frontier, ranges) branch ->
            let first = builder.count in
            let frontier = statement builder frontier branch in
            let limit = builder.count in
            let frontier =
              if concurrent then emit builder frontier (Task_end { first; limit }) branch.origin
              else frontier
            in
            (frontier, { first; limit } :: ranges))
          (frontier, []) branches
      in
      builder.fork_join_blocks <-
        { keyword = (if concurrent then "concurrent" else "parallel"); branches = List.rev ranges }
        :: builder.fork_join_blocks;
      frontier
  | Proof _ -> frontier
  | Assert { value; _ } -> expression builder frontier value
  | Yield { mode; part = Value { kind = Construct { fields; _ }; _ } as part } ->
      let frontier = construct builder frontier mode fields in
      let lent = Core_walk.lent_places part in
      if mode = Mut then
        let frontier =
          List.fold_left
            (fun frontier core_place -> borrow_mut builder frontier (Place core_place))
            frontier lent
        in
        (* Aliasing: the places that are lent [mut] to the yielded value
           must not overlap. *)
        let places =
          List.concat
            (List.mapi
               (fun position (core_place : Core.place) ->
                 match Place.of_core core_place with
                 | Some place ->
                     [ { place; mode; at = Core_walk.place_origin core_place; position } ]
                 | None -> [])
               lent)
        in
        if List.length places > 1 then
          emit builder frontier (Arguments { places; views = []; yielded = true }) node.origin
        else frontier
      else frontier
  | Yield { mode; part } -> operand builder frontier mode part

and statement_and_yield_point builder frontier (node : Core.statement) =
  let frontier = statement_actions builder frontier node in
  match node.kind with
  | Yield { mode; part } ->
      let views =
        if builder.is_view (operand_type part) then views_of_operand builder part else []
      in
      let lent = List.map Place.of_core (Core_walk.lent_places part) in
      emit builder frontier (Yield_point { mode; lent; views }) node.origin
  | _ -> frontier

(* A [let]: evaluates the value, then records the views of the locals that
   the pattern binds. *)
and let_ builder frontier (node : Core.statement) (pattern : Core.pattern) (value : Core.operand)
    else_ =
  let frontier = operand builder frontier Read value in
  Option.iter (fun else_ -> ignore (block builder frontier else_)) else_;
  let type_ = operand_type value in
  let is_var = match pattern.kind with Bind { is_var; _ } -> is_var | _ -> false in
  let lent_part =
    match value with Place core_place -> Place.is_lent_part core_place | Value _ -> false
  in
  let origin =
    match value with
    | Place core_place -> Core_walk.place_origin core_place
    | Value value -> value.origin
  in
  (* A [let] cannot bind a part that a lending call lent, because the loan
     ends with the statement. A [Plain] part is copied instead, unless it is
     a view: a copied view still borrows from the lender. *)
  let frontier =
    if (not is_var) && lent_part && ((not (builder.plain type_)) || builder.is_view type_) then
      emit builder frontier (Bind_lent_part type_) origin
    else frontier
  in
  let holds_views = builder.is_view type_ || match type_ with T.Cursor _ -> true | _ -> false in
  (* A local that is bound to a place aliases the place, so it views it. A
     local that is bound to a value of a view type has the value's views. A
     local that takes ownership of a moved value has no views. *)
  let views =
    match value with
    | Place core_place
      when holds_views || (Option.is_some (Place.of_core core_place) && not (builder.plain type_))
      ->
        views_of_borrow builder core_place
    | Value value when holds_views -> views_of builder value
    | Place _ | Value _ -> []
  in
  let frontier =
    if holds_views then
      List.fold_left
        (fun frontier (temporary : Core.expression) ->
          emit builder frontier (View_of_temporary None) temporary.origin)
        frontier
        (match value with Value value -> viewed_temporaries builder value | Place _ -> [])
    else frontier
  in
  let locals = pattern_locals pattern in
  let frontier = emit builder frontier (Bind locals) node.origin in
  if holds_views || views <> [] then
    emit builder frontier (Bind_views { locals; views }) node.origin
  else frontier

(* A loop. Every iteration passes through the head point. A [while] loop
   evaluates its condition after the head. Control leaves the loop from the
   head, from the condition, and from each [break]. A loop over a place
   borrows the place for the body. *)
and loop builder frontier ~bound ~views ~loan ~condition ~fork_join (body : Core.block) origin =
  match frontier with
  | [] -> []
  | _ ->
      let head = add builder (Bind bound) origin in
      link builder frontier head;
      (* A loop that borrows its collection [mut] may mutate the collection
         on every iteration. *)
      let stepped =
        match loan with
        | Some { borrowed; mode = Mut; _ } -> emit builder [ head ] (Mutate borrowed) origin
        | _ -> [ head ]
      in
      let breaks = ref [] and continues = ref [] in
      builder.loops <- (breaks, continues) :: builder.loops;
      let loans = builder.loans in
      let tested =
        match condition with
        | Some condition ->
            let tested = expression builder stepped condition in
            builder.loans <- loans;
            tested
        | None -> stepped
      in
      builder.loans <- Option.to_list loan @ loans;
      let entered =
        if bound = [] || views = [] then tested
        else emit builder tested (Bind_views { locals = bound; views }) origin
      in
      let first = builder.count in
      let body_end = block builder entered body in
      Option.iter
        (fun keyword ->
          builder.fork_join_loops <-
            { keyword; body = { first; limit = builder.count }; bound } :: builder.fork_join_loops)
        fork_join;
      builder.loans <- loans;
      builder.loops <- List.tl builder.loops;
      link builder (body_end @ !continues) head;
      let ended = tested @ !breaks in
      if bound = [] then ended else emit builder ended (Scope_end bound) origin

(* The graph of a definition, or [None] if the definition has no body to
   check: only a function, a test, and a law's proof have one. *)
let of_definition ~plain ~is_view ~holds_function ~stores_function (definition : Core.definition) :
    t option =
  let body =
    match definition with
    | Function { body = Some body; _ } -> Some (body, true)
    | Test body | Law_proof { body; _ } -> Some (body, false)
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
          fork_join_blocks = [];
          fork_join_loops = [];
          plain;
          is_view;
          holds_function;
          stores_function;
        }
      in
      let entry = add builder Enter 0 in
      let frontier = List.fold_left (statement builder) [ entry ] body.statements in
      let frontier =
        match body.value with
        | Some value when returns -> returned_value builder frontier value
        | Some value -> expression builder frontier value
        | None -> frontier
      in
      if returns then ignore (emit builder frontier Exit 0);
      {
        points = Array.init builder.count (Hashtbl.find builder.table);
        entries = entry :: List.rev builder.entries;
        fork_join_blocks = List.rev builder.fork_join_blocks;
        fork_join_loops = List.rev builder.fork_join_loops;
      })
    body
