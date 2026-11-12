(* Loans and views, checked on the control-flow graph of a core form. The
   check prevents dangling views, mutation of a borrowed place, and data
   races.

   A loan is live at the points that the graph marks with it. A view is
   stored in a holder: a local, or a place that outlives the function, such
   as a [mut] parameter. A forward dataflow analysis computes the views that
   each holder may store at each point. A backward liveness analysis
   computes the locals that are live after each point. A place cannot be
   mutated or moved while a live holder stores a view of it. *)

module T = Types
open Graph
open Context
open Moves

(* The views that each holder may store. A holder with an entry stores a
   value of a view type, even if the entry is empty. *)
type held_views = (Place.root * view list) list

let views_held_by (held_views : held_views) (holder : Place.root) = List.assoc_opt holder held_views

let add_views (held_views : held_views) holder views : held_views =
  let known = Option.value ~default:[] (views_held_by held_views holder) in
  let added = List.filter (fun view -> not (List.mem view known)) views in
  (holder, known @ added) :: List.remove_assoc holder held_views

(* Whether a local is an alias of another place: a [let] bound to a place, a
   pattern binding of a part of a place, or a loop variable bound to an
   element. A parameter is not an alias: the function does not know what the
   caller passed. *)
let aliases_place context (root : Place.root) =
  match root with
  | Local local ->
      local <> Self && (not (List.mem local context.parameters)) && kind context root <> Owned
  | Constant _ | Environment -> false

(* Expands views through the holders that they name, so that the result
   names the places that own the borrowed data.

   - A view that borrows a place: the place itself, and the views that the
     place's root stores.
   - A copy of a view stored in a place ([copied_out]): only the views that
     the place's root stores.
   - A view of an alias: the views of the alias. After [match self.user {
     Some(found) => ... }], a slice of [found] views [self.user].

   If the root has no entry, as for a parameter, the view is kept as it is.
   The place then represents whatever the stored view borrows. *)
let resolve context (held_views : held_views) (views : view list) : view list =
  List.concat_map
    (fun (view : view) ->
      match views_held_by held_views view.place.root with
      | Some known when view.copied_out || aliases_place context view.place.root -> known
      | Some known -> known @ [ view ]
      | None -> [ view ])
    views

(* Whether the viewed place is dropped when the function returns, so that a
   view of it would dangle in the caller: a local, a lambda's environment
   record, or an [own] parameter. A copy of a view that an [own] parameter
   stores is not: it borrows the caller's data, which outlives the function. *)
let lifetime_ends_at_return context (view : view) =
  match view.place.root with
  | Constant _ -> false
  | Environment -> true
  | Local local ->
      if local = Self || List.mem local context.parameters then
        kind context view.place.root = Owned && not view.copied_out
      else true

(* Whether the place outlives the function: a [mut] parameter, or [self] in
   a [mut self] method. The caller still owns it after the call. *)
let outlives_function context (place : Place.t) =
  kind context place.root = Borrowed_mut
  &&
  match place.root with
  | Local local -> List.mem local context.parameters
  | Constant _ | Environment -> false

let transfer context (point : point) (before : held_views) : held_views =
  match point.action with
  | Bind locals ->
      List.filter
        (fun (holder, _) -> not (List.exists (fun local -> holder = Place.Local local) locals))
        before
  | Bind_views { locals; views } ->
      let viewed = resolve context before views in
      List.fold_left
        (fun held_views holder ->
          (Place.Local holder, viewed) :: List.remove_assoc (Place.Local holder) held_views)
        before locals
  | Store { place; views } -> (
      match resolve context before views with
      | [] -> before
      | viewed -> add_views before place.root viewed)
  | Enter | Read _ | Move _ | Move_out_of_lent _ | Mutate _ | Assign _ | Scope_end _ | Task_end _
  | Yield_point _ | Exit | Return_view _ | View_of_temporary _ | Bind_lent_part _
  | Pass_owned_function _ | Write_through _ | Arguments _ ->
      before

(* The views that each holder may store before each point: a forward
   may-analysis. *)
let held_views_before context (graph : Graph.t) : held_views array =
  let count = Array.length graph.points in
  let before = Array.make count [] in
  let reached = Array.make count false in
  let pending = Queue.create () in
  List.iter
    (fun entry ->
      reached.(entry) <- true;
      Queue.add entry pending)
    graph.entries;
  while not (Queue.is_empty pending) do
    let index = Queue.pop pending in
    let after = transfer context graph.points.(index) before.(index) in
    List.iter
      (fun successor ->
        let known = before.(successor) in
        let merged =
          List.fold_left
            (fun held_views (holder, places) -> add_views held_views holder places)
            known after
        in
        let changed =
          List.exists
            (fun (holder, places) ->
              match views_held_by known holder with
              | Some existing -> List.exists (fun place -> not (List.mem place existing)) places
              | None -> true)
            after
        in
        if changed || not reached.(successor) then begin
          reached.(successor) <- true;
          before.(successor) <- merged;
          Queue.add successor pending
        end)
      graph.points.(index).successors
  done;
  before

(* Liveness: the locals that may be used after each point. A use of a local
   is a read, a move, a borrow, or an assignment of a place rooted at it. *)
let live_after (graph : Graph.t) : Core.local list array =
  let count = Array.length graph.points in
  let after = Array.make count [] in
  let uses (point : point) =
    match point.action with
    | Read place | Mutate place | Assign place | Move { place; _ } -> (
        match place.root with Local local -> [ local ] | Constant _ | Environment -> [])
    | _ -> []
  in
  let changed = ref true in
  while !changed do
    changed := false;
    for index = count - 1 downto 0 do
      let point = graph.points.(index) in
      let live =
        List.concat_map
          (fun successor ->
            let next = graph.points.(successor) in
            let bound = match next.action with Bind locals -> locals | _ -> [] in
            uses next @ List.filter (fun local -> not (List.mem local bound)) after.(successor))
          point.successors
      in
      let added = List.filter (fun local -> not (List.mem local after.(index))) live in
      if added <> [] then begin
        after.(index) <- List.sort_uniq compare (after.(index) @ added);
        changed := true
      end
    done
  done;
  after

let overlaps left right = Place.overlap left right <> Disjoint

(* The error message for a use of a place that a [mut] loan covers. [viewed]
   is true if the loan covers the place only because the borrowed place
   stores a view of it. *)
let mut_loan_message context (loan : loan) ~viewed (place : Place.t) =
  let borrowed = Printf.sprintf "`%s`" (show context loan.borrowed) in
  let borrowed, used =
    if viewed then
      let place = Printf.sprintf "`%s`" (show context place) in
      (Printf.sprintf "%s, which views %s," borrowed place, place)
    else (borrowed, "it")
  in
  match loan.duration with
  | Loop_body ->
      Printf.sprintf "%s is borrowed `mut` by the loop, so the loop body cannot use %s." borrowed
        used
  | Provide_body ->
      Printf.sprintf "%s is borrowed `mut` by the `provide` block, so its body cannot use %s."
        borrowed used
  | Rest_of_statement ->
      Printf.sprintf
        "%s is borrowed `mut` until this statement ends, so the statement cannot use %s again."
        borrowed used
  | Operand_evaluation ->
      Printf.sprintf "%s is borrowed `mut` by this expression, so the expression cannot use %s yet."
        borrowed used

(* The error message for a mutation of a place that a read-only loan covers. *)
let read_loan_message context (loan : loan) ~viewed (place : Place.t) ~verb =
  let place = show context place
  and borrowed = Printf.sprintf "`%s`" (show context loan.borrowed) in
  match loan.duration with
  | Loop_body ->
      Printf.sprintf "`%s` cannot %s while the loop iterates over %s." place verb
        (if viewed then borrowed ^ ", which views it" else "it")
  | Provide_body ->
      Printf.sprintf "`%s` cannot %s while the `provide` block borrows %s." place verb
        (if viewed then borrowed ^ ", which views it" else "it")
  | Rest_of_statement ->
      Printf.sprintf
        "`%s` cannot %s while a part of %s is lent, which lasts until this statement ends." place
        verb
        (if viewed then borrowed ^ ", which views it," else "it")
  | Operand_evaluation ->
      Printf.sprintf
        "`%s` cannot %s here, because %s was evaluated earlier in this expression and is used \
         later in it."
        place verb
        (if viewed then borrowed ^ ", which views it," else borrowed)

(* Why a task that starts at one of a method's [yield]s cannot keep the
   yielded value after the method resumes. *)
type task_hazard =
  | Yields_mut  (** The method yields [mut] borrows. *)
  | Borrows of string
      (** A yielded value borrows or views this place, which the method can mutate or drop when it
          resumes: a local, or a place inside a [mut] or [own] parameter. *)

(* Reports the errors of loans and views. Returns the first [task_hazard]
   of the definition's [yield]s, if it has one. *)
let check context (graph : Graph.t) : task_hazard option =
  let task_hazard = ref None in
  let before = held_views_before context graph in
  let after = live_after graph in
  (* Whether a loan covers a place: the loan borrows the place, or it
     borrows a holder that stores a view of the place. Returns [Some viewed]
     if it does, where [viewed] is true in the second case. *)
  let loan_coverage index (loan : loan) (place : Place.t) =
    if overlaps loan.borrowed place then Some false
    else if
      List.exists
        (fun (viewed : view) -> overlaps viewed.place place)
        (resolve context before.(index) [ { place = loan.borrowed; copied_out = false } ])
    then Some true
    else None
  in
  (* The loans that cover a place, oldest first, each with [viewed]. *)
  let covering index (point : point) (place : Place.t) =
    List.rev
      (List.filter_map
         (fun loan -> Option.map (fun viewed -> (loan, viewed)) (loan_coverage index loan place))
         point.loans)
  in
  let is_mut ((loan : loan), _) = loan.mode = Mut in
  (* Reports a use of a place that a [mut] loan covers. *)
  let check_use index (point : point) (place : Place.t) =
    match List.find_opt is_mut (covering index point place) with
    | Some (loan, viewed) ->
        report context Conflicting_loan (span context point.origin)
          (mut_loan_message context loan ~viewed place)
    | None -> ()
  in
  (* Reports a mutation or a move of a place that a loan covers, or that a
     live holder stores a view of. One mutation gets one report. *)
  let check_mutation index (point : point) (place : Place.t) ~verb =
    let at = span context point.origin in
    let covering = covering index point place in
    match (List.find_opt is_mut covering, covering) with
    | Some (loan, viewed), _ ->
        report context Conflicting_loan at (mut_loan_message context loan ~viewed place)
    | None, (loan, viewed) :: _ ->
        report context Changed_while_viewed at (read_loan_message context loan ~viewed place ~verb)
    | None, [] ->
        List.iter
          (fun ((holder : Place.root), viewed) ->
            let in_use =
              match holder with
              | Local local when not (outlives_function context { root = holder; steps = [] }) ->
                  List.mem local after.(index)
              | Local _ | Constant _ | Environment -> true
            in
            if in_use && List.exists (fun (viewed : view) -> overlaps viewed.place place) viewed
            then
              report context Changed_while_viewed at
                (Printf.sprintf "`%s` cannot %s while `%s`, which views it, is still in use."
                   (show context place) verb (show_root context holder)))
          before.(index)
  in
  Array.iteri
    (fun index (point : point) ->
      let at = span context point.origin in
      match point.action with
      | Read place -> check_use index point place
      | Mutate place ->
          check_use index point place;
          check_mutation index point place ~verb:"be borrowed `mut`"
      | Assign place -> check_mutation index point place ~verb:"be assigned"
      | Move { place; type_; returned; captured; _ } -> (
          check_use index point place;
          match verdict context place ~type_ ~returned ~captured with
          | Moves -> check_mutation index point place ~verb:"be moved"
          | Reads | Refused _ -> ())
      | Arguments { places; views; yielded } ->
          (* Aliasing: two places that one call borrows cannot overlap if
             either is borrowed [mut]. *)
          List.iteri
            (fun first_index (first : borrowed_argument) ->
              List.iteri
                (fun second_index (second : borrowed_argument) ->
                  if second_index > first_index && (first.mode = Mut || second.mode = Mut) then
                    let exclusive, also =
                      if first.mode = Mut then (first, second) else (second, first)
                    in
                    match Place.overlap first.place second.place with
                    | Overlapping ->
                        report context Conflicting_loan (with_mark context second.at)
                          (Printf.sprintf
                             (if yielded then
                                format_of_string
                                  "`%s` is lent `mut` to the yielded value, so `%s` cannot be lent \
                                   to it too."
                              else
                                "`%s` is borrowed `mut` by this call, so the call cannot also use \
                                 `%s`.")
                             (show context exclusive.place) (show context also.place))
                    | Maybe_disjoint (first_element, second_element) ->
                        context.must_be_disjoint <-
                          (first_element, second_element) :: context.must_be_disjoint
                    | Disjoint -> ())
                places)
            places;
          (* Aliasing: a view argument cannot view a place that the call
             borrows [mut], because the callee could mutate the place while
             it reads the view. Two parts of one collection may be disjoint,
             which is left to the prover as a [Disjoint] obligation, as for
             two places. *)
          List.iter
            (fun (position, viewed, view_at) ->
              let viewed = resolve context before.(index) viewed in
              List.iter
                (fun (passed : borrowed_argument) ->
                  if passed.position <> position && passed.mode = Mut then begin
                    let overlaps =
                      List.map
                        (fun (viewed : view) -> Place.overlap viewed.place passed.place)
                        viewed
                    in
                    if List.mem Place.Overlapping overlaps then
                      report context Conflicting_loan (with_mark context view_at)
                        (Printf.sprintf
                           "`%s` is borrowed `mut` by this call, so the call cannot also take a \
                            view of it."
                           (show context passed.place))
                    else
                      List.iter
                        (function
                          | Place.Maybe_disjoint (first, second) ->
                              context.must_be_disjoint <-
                                (first, second) :: context.must_be_disjoint
                          | Overlapping | Disjoint -> ())
                        overlaps
                  end)
                places)
            views
      | View_of_temporary holder ->
          report context Views_temporary at
            (match holder with
            | None ->
                "This temporary is dropped at the end of the statement, but the statement binds a \
                 view of it, which would dangle. Bind the temporary to a name first, so that it \
                 outlives the view."
            (* A synthetic local, such as the list that a list literal
               builds, has no name in the source. *)
            | Some { root = Local (Synthetic _); _ } ->
                "This temporary is dropped at the end of the statement, but the collection built \
                 here may store a view of it, which would dangle. Bind the temporary to a name \
                 first, so that it outlives the view."
            | Some place ->
                Printf.sprintf
                  "This temporary is dropped at the end of the statement, but `%s` may store a \
                   view of it, which would dangle. Bind the temporary to a name first, so that it \
                   outlives the view."
                  (show_root context place.root))
      | Bind_lent_part type_ ->
          report context Keeps_lent_part at
            ~fixes:
              (if copyable context type_ then
                 [
                   Diagnostic.fix "Copy it."
                     [ Diagnostic.insert (Syntax.Span.zero_width at.stop) ".copy()" ];
                 ]
               else [])
            "This part is lent only until the statement ends, so it cannot be bound to a name. Use \
             it in this statement, or copy it."
      | Pass_owned_function views -> (
          (* The callee may store the function, so the function must capture
             nothing. A function value that this function does not own, such
             as a read-only parameter, may be a capturing lambda. *)
          match
            List.find_opt
              (fun (viewed : view) ->
                match viewed.place.root with
                | Environment -> true
                | Constant _ -> false
                | Local _ -> kind context viewed.place.root <> Owned)
              (resolve context before.(index) views)
          with
          | Some { place = { root = Environment; _ }; _ } ->
              report context View_escapes at
                "This lambda captures local variables, and the callee may store a function that it \
                 takes through an `own` parameter, so the lambda could outlive them. Pass a \
                 function that captures nothing."
          | Some viewed ->
              report context View_escapes at
                (Printf.sprintf
                   "`%s` is not owned here, so it may be a capturing lambda, and the callee may \
                    store a function that it takes through an `own` parameter. Pass a function \
                    that captures nothing."
                   (show context viewed.place))
          | None -> ())
      | Return_view views -> (
          match
            List.find_opt (lifetime_ends_at_return context) (resolve context before.(index) views)
          with
          | Some { place = { root = Environment; _ }; _ } ->
              report context View_escapes at
                "This returns a capturing lambda. A lambda's captured variables live in the \
                 enclosing function's stack frame, so the returned lambda would dangle. Return a \
                 record that stores the captured values, with a method that does the work."
          | Some local ->
              report context View_escapes at
                (Printf.sprintf
                   "This returns a view of `%s`, which is dropped when the function returns, so \
                    the view would dangle. A function can return a view only of its parameters."
                   (show_root context local.place.root))
          | None ->
              (* A caller reaches a capability's implementation only through
                 the capability, so the caller's ownership check cannot
                 track a view of the implementation's state. The next call
                 could mutate that state and invalidate the view. *)
              if
                context.implements_capability
                && List.exists
                     (fun (view : view) -> view.place.root = Local Self && not view.copied_out)
                     (resolve context before.(index) views)
              then
                report context View_crosses_capability at
                  "This returns a view of the capability implementation's own state. The caller \
                   cannot see the implementation, so nothing stops the next call from mutating \
                   that state while the view is in use. Return a copy.")
      | Store { place; views } -> (
          if outlives_function context place then
            let resolved = resolve context before.(index) views in
            (* The caller assumes that a [mut] argument stores only the
               views that the call was passed as view arguments. So the
               function cannot store there a view of a borrowed parameter
               that is not a view, or a view of the place itself. *)
            let is_self_reference (view : view) =
              view.place.root = place.root && not view.copied_out
            in
            let views_borrowed_parameter (view : view) =
              match view.place.root with
              | Local local when local = Self || List.mem local context.parameters -> (
                  match Hashtbl.find_opt context.types local with
                  | Some type_ -> not (is_view context type_)
                  | None -> false)
              | Local _ | Constant _ | Environment -> false
            in
            (* The caller of a capability's method cannot see the
               implementation, so the caller's ownership check cannot track
               a view argument that the implementation stores. So the
               implementation stores no view argument. *)
            let stores_argument_view (view : view) =
              context.implements_capability && place.root = Local Self
              &&
              match view.place.root with
              | Local local -> local <> Self && List.mem local context.parameters
              | Constant _ | Environment -> false
            in
            match List.find_opt (lifetime_ends_at_return context) resolved with
            | Some { place = { root = Environment; _ }; _ } ->
                report context View_escapes at
                  (Printf.sprintf
                     "This stores a capturing lambda in `%s`, which outlives this function. A \
                      lambda's captured variables live in the enclosing function's stack frame, so \
                      the stored lambda would dangle. Store a function that captures nothing."
                     (show_root context place.root))
            | Some local ->
                report context View_escapes at
                  (Printf.sprintf
                     "This stores a view of `%s` in `%s`, which outlives this function, so the \
                      view would dangle when `%s` is dropped. A `mut` parameter can store only \
                      views that the function received as arguments."
                     (show_root context local.place.root)
                     (show_root context place.root)
                     (show_root context local.place.root))
            | None -> (
                match
                  ( List.find_opt stores_argument_view resolved,
                    List.find_opt is_self_reference resolved,
                    List.find_opt views_borrowed_parameter resolved )
                with
                | Some stored_view, _, _ ->
                    report context View_crosses_capability at
                      (Printf.sprintf
                         "This stores a view of `%s` in a capability implementation. The caller \
                          cannot see the implementation, so it could mutate or drop what the view \
                          borrows while the implementation still stores the view. Store a copy."
                         (show_root context stored_view.place.root))
                | None, Some _, _ ->
                    report context Self_referential at
                      (Printf.sprintf
                         "This stores a view of a part of `%s` in `%s` itself, which makes it \
                          self-referential. The caller does not know about the view, so it could \
                          mutate that part and invalidate the view."
                         (show_root context place.root) (show_root context place.root))
                | None, None, Some parameter ->
                    let parameter = show_root context parameter.place.root in
                    report context View_escapes at
                      (Printf.sprintf
                         "This stores a view of `%s` in `%s`, which outlives this function, but \
                          `%s` is only borrowed for the call, and the caller does not expect it to \
                          stay borrowed afterwards. Take `%s` as a view type, such as a `Slice`, \
                          to store a view of it."
                         parameter (show_root context place.root) parameter parameter)
                | None, None, None -> ()))
      | Write_through slice -> (
          (* Writing through a slice mutates the places that the slice
             views, so each of them must be mutable. A slice that is stored
             in a field is read-only, whatever the mode of the record: the
             record's mode does not say whether the viewed place is mutable.
             A slice parameter is writable if its mode is [mut], which the
             type checker checks. *)
          let mutable_root (root : Place.root) =
            match root with
            | Constant _ | Environment -> false
            | Local local -> (
                match kind context root with
                | Borrowed_mut -> true
                | Owned -> List.mem local context.mutable_locals
                | Borrowed -> false)
          in
          match slice with
          | { steps = _ :: _; _ } ->
              report context Read_only_view at
                (Printf.sprintf
                   "`%s` is a slice stored in a field, so it is read-only. Mutate the collection \
                    that it views instead."
                   (show context slice))
          | { root = Local local; _ } when List.mem local context.parameters -> ()
          | _ -> (
              match
                List.find_opt
                  (fun (viewed : view) ->
                    viewed.place <> slice && not (mutable_root viewed.place.root))
                  (resolve context before.(index) [ { place = slice; copied_out = true } ])
              with
              | Some viewed ->
                  report context Read_only_view at
                    (Printf.sprintf
                       "`%s` views `%s`, which is read-only here, so `%s` cannot be written \
                        through."
                       (show context slice) (show context viewed.place) (show context slice))
              | None -> ()))
      | Yield_point { mode; lent; views } -> (
          (* A task can keep a borrow or a view only of a place that the
             method cannot mutate or drop: a place inside a read-only
             parameter, or a constant. *)
          (if !task_hazard = None then
             let safe (view : view) =
               match view.place.root with
               | Constant _ -> true
               | Environment -> false
               | Local local ->
                   (local = Self || List.mem local context.parameters)
                   && kind context view.place.root = Borrowed
             in
             let borrowed =
               List.concat_map
                 (function
                   | Some place -> resolve context before.(index) [ { place; copied_out = false } ]
                   | None -> [])
                 lent
             in
             task_hazard :=
               if mode = Mut then Some Yields_mut
               else
                 match
                   List.find_opt
                     (fun view -> not (safe view))
                     (borrowed @ resolve context before.(index) views)
                 with
                 | Some view -> Some (Borrows (show context view.place))
                 | None when List.mem None lent -> Some (Borrows "a part that a lending call lends")
                 | None -> None);
          (* The caller may store a yielded view, so a method can yield a
             view only of its parameters. *)
          match
            List.find_opt (lifetime_ends_at_return context) (resolve context before.(index) views)
          with
          | Some { place = { root = Environment; _ }; _ } ->
              report context View_escapes at
                "This yields a capturing lambda. A lambda's captured variables live in this \
                 method's stack frame, and the caller may store the lambda, so it could dangle. \
                 Yield a function that captures nothing."
          | Some local ->
              report context View_escapes at
                (Printf.sprintf
                   "This yields a view of `%s`, which is local to the method. The caller may store \
                    the view, and it would dangle when the method returns. Yield `%s` itself, or a \
                    copy."
                   (show_root context local.place.root)
                   (show_root context local.place.root))
          | None -> ())
      | Enter | Move_out_of_lent _ | Bind _ | Scope_end _ | Task_end _ | Exit | Bind_views _ -> ())
    graph.points;
  (* The places that a range of points mutates, and the places that it uses. *)
  let effects (range : range) =
    let changes = ref [] and uses = ref [] in
    for index = range.first to range.limit - 1 do
      let point = graph.points.(index) in
      (* A use of a view uses the places that it views, and a write through
         a slice mutates the places that the slice views. *)
      let viewed place =
        List.map
          (fun (view : view) -> view.place)
          (resolve context before.(index) [ { place; copied_out = true } ])
      in
      match point.action with
      | Read place -> uses := (place :: viewed place) @ !uses
      | Mutate place ->
          uses := (place :: viewed place) @ !uses;
          changes := (place, point.origin) :: !changes
      | Write_through place ->
          changes := List.map (fun viewed -> (viewed, point.origin)) (viewed place) @ !changes
      | Assign place -> changes := (place, point.origin) :: !changes
      | Move { place; type_; returned; captured; _ } -> (
          uses := place :: !uses;
          match verdict context place ~type_ ~returned ~captured with
          | Moves -> changes := (place, point.origin) :: !changes
          | Reads | Refused _ -> ())
      | _ -> ()
    done;
    (!changes, !uses)
  in
  (* Data races between the branches of a [parallel] or [concurrent] block:
     a place that one branch mutates must not overlap a place that another
     branch uses. Two elements of one collection may be disjoint, which is
     left to the prover as a [Disjoint] obligation. *)
  List.iter
    (fun ({ keyword; branches } : fork_join_block) ->
      let branches = List.map effects branches in
      List.iteri
        (fun index (changes, _) ->
          List.iteri
            (fun other (other_changes, other_uses) ->
              if other <> index then (
                let used = other_uses @ List.map fst other_changes in
                List.iter
                  (fun (place, origin) ->
                    if List.exists (fun other -> Place.overlap other place = Overlapping) used then
                      report context Data_race (span context origin)
                        (Printf.sprintf
                           "Data race: one branch of this `%s` block mutates `%s`, and another \
                            branch uses it."
                           keyword (show context place));
                    if other > index then
                      List.iter
                        (fun other ->
                          match Place.overlap place other with
                          | Maybe_disjoint (first, second) ->
                              context.must_be_disjoint <-
                                (first, second) :: context.must_be_disjoint
                          | Overlapping | Disjoint -> ())
                        used)
                  changes;
                if other > index then
                  (* The other branch's mutations against this branch's
                     uses. *)
                  let _, uses = List.nth branches index in
                  List.iter
                    (fun (place, _) ->
                      List.iter
                        (fun used ->
                          match Place.overlap place used with
                          | Maybe_disjoint (first, second) ->
                              context.must_be_disjoint <-
                                (first, second) :: context.must_be_disjoint
                          | Overlapping | Disjoint -> ())
                        uses)
                    other_changes))
            branches)
        branches)
    graph.fork_join_blocks;
  (* Data races between the iterations of a [parallel for] or [concurrent
     for]: the body can mutate only the locals of one iteration, which are
     the loop's pattern variables and the locals that the body binds. *)
  List.iter
    (fun ({ keyword; body = range; bound } : fork_join_loop) ->
      let bound = ref bound in
      for index = range.first to range.limit - 1 do
        match graph.points.(index).action with Bind locals -> bound := locals @ !bound | _ -> ()
      done;
      List.iter
        (fun ((place : Place.t), origin) ->
          let outside =
            match place.root with
            | Constant _ | Environment | Local Self -> true
            | Local local -> not (List.mem local !bound)
          in
          if outside then
            report context Data_race (span context origin)
              (Printf.sprintf
                 "Data race: the iterations of a `%s for` run at the same time, so the body can \
                  mutate only its own element and its own locals."
                 keyword))
        (fst (effects range)))
    graph.fork_join_loops;
  !task_hazard
