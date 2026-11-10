(* Loans and views, checked on the control-flow graph of a core form.

   A loan is in force at the points that the graph marks with it. A view is
   held by a local, or by a place that the caller keeps. A forward analysis
   finds what each holder may view at each point, and a backward analysis
   finds which locals are still used after each point. A place may not be
   changed while a holder that views it is still used. *)

module T = Types
open Graph
open Context
open Moves

(* What each holder may view. A holder with an entry is known to hold a
   view, even if the entry is empty. *)
type holdings = (Place.root * view list) list

let held (holdings : holdings) (holder : Place.root) = List.assoc_opt holder holdings

let hold (holdings : holdings) holder views : holdings =
  let known = Option.value ~default:[] (held holdings holder) in
  let added = List.filter (fun view -> not (List.mem view known)) views in
  (holder, known @ added) :: List.remove_assoc holder holdings

(* Whether a name refers to a place that is not its own: a name that a
   [let] binds to a place, that a pattern binds to a part of a place, or
   that a loop binds to an element. A parameter is not such a name: what
   the caller gave it is all that the function knows. *)
let refers_elsewhere context (root : Place.root) =
  match root with
  | Local local ->
      local <> Self && (not (List.mem local context.parameters)) && kind context root <> Owned
  | Constant _ | Environment -> false

(* What a value views, given the places it names. A value that refers to a
   place views the place and what the place's root is known to view. A
   value taken out of a place views only what the root is known to view,
   and so does a value that refers to a name that itself refers elsewhere:
   a slice of [found], after [match self.user { Some(found) => ... }], views
   [self.user]. If nothing is known of the root, as for a parameter, the
   place stands for what was taken out of it. *)
let resolve context (holdings : holdings) (views : view list) : view list =
  List.concat_map
    (fun (view : view) ->
      match held holdings view.place.root with
      | Some known when view.taken || refers_elsewhere context view.place.root -> known
      | Some known -> known @ [ view ]
      | None -> [ view ])
    views

(* Whether what is viewed is gone when the function returns, so that
   nothing the caller keeps may view it: a local, the environment of a
   lambda, and a parameter or [self] that the function owns. A value taken
   out of an owned parameter is a view that the parameter held, which views
   what the caller has. *)
let ends_with_function context (view : view) =
  match view.place.root with
  | Constant _ -> false
  | Environment -> true
  | Local local ->
      if local = Self || List.mem local context.parameters then
        kind context view.place.root = Owned && not view.taken
      else true

(* Whether the caller keeps the place after the function returns: a [mut]
   parameter, or [self] in a [mut self] method. *)
let kept_by_caller context (place : Place.t) =
  kind context place.root = Mut_access
  &&
  match place.root with
  | Local local -> List.mem local context.parameters
  | Constant _ | Environment -> false

let transfer context (point : point) (before : holdings) : holdings =
  match point.action with
  | Bind locals ->
      List.filter
        (fun (holder, _) -> not (List.exists (fun local -> holder = Place.Local local) locals))
        before
  | Hold { holders; views } ->
      let viewed = resolve context before views in
      List.fold_left
        (fun holdings holder ->
          (Place.Local holder, viewed) :: List.remove_assoc (Place.Local holder) holdings)
        before holders
  | Store { place; views } -> (
      match resolve context before views with
      | [] -> before
      | viewed -> hold before place.root viewed)
  | Enter | Read _ | Move _ | Take_lent _ | Mutate _ | Assign _ | Ends _ | Task_end _ | Suspend _
  | Exit | Return_view _ | Views_temporary _ | Keeps_lent_part _ | Gives_function _
  | Write_through _ | Arguments _ ->
      before

(* What each holder may view before each point. *)
let holdings_before context (graph : Graph.t) : holdings array =
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
          List.fold_left (fun holdings (holder, places) -> hold holdings holder places) known after
        in
        let changed =
          List.exists
            (fun (holder, places) ->
              match held known holder with
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

(* The locals that are used after each point. A local is used where a
   place rooted at it is read, moved, borrowed, or assigned. *)
let used_after (graph : Graph.t) : Core.local list array =
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

let overlaps left right = Place.overlap left right <> Apart

(* Why a place cannot be used: a loan that is [mut] covers it. [viewed] is
   true if the loan covers the place only because what is lent views it. *)
let lent_mut_message context (loan : loan) ~viewed (place : Place.t) =
  let lent = Printf.sprintf "`%s`" (show context loan.lent) in
  let lent, used =
    if viewed then
      let place = Printf.sprintf "`%s`" (show context place) in
      (Printf.sprintf "%s, which views %s," lent place, place)
    else (lent, "it")
  in
  match loan.lender with
  | To_loop -> Printf.sprintf "%s is lent `mut` to the loop, so its body cannot use %s." lent used
  | To_provide ->
      Printf.sprintf "%s is lent `mut` to the `provide` block, so its body cannot use %s." lent used
  | To_statement ->
      Printf.sprintf
        "%s is lent `mut` for the rest of this statement, so the statement cannot use %s again."
        lent used
  | To_operand ->
      Printf.sprintf "%s is lent `mut` to this expression, so the expression cannot use %s yet."
        lent used

(* Why a place cannot be changed: a read-only loan covers it. *)
let lent_message context (loan : loan) ~viewed (place : Place.t) ~what =
  let place = show context place and lent = Printf.sprintf "`%s`" (show context loan.lent) in
  match loan.lender with
  | To_loop ->
      Printf.sprintf "`%s` cannot %s while the loop goes over %s." place what
        (if viewed then lent ^ ", which views it" else "it")
  | To_provide ->
      Printf.sprintf "`%s` cannot %s while the `provide` block is given %s." place what
        (if viewed then lent ^ ", which views it" else "it")
  | To_statement ->
      Printf.sprintf "`%s` cannot %s while a part of %s is lent, which lasts this statement." place
        what
        (if viewed then lent ^ ", which views it," else "it")
  | To_operand ->
      Printf.sprintf
        "`%s` cannot %s here, because %s was evaluated earlier in this expression and is used \
         later in it."
        place what
        (if viewed then lent ^ ", which views it," else lent)

let check context (graph : Graph.t) =
  let before = holdings_before context graph in
  let after = used_after graph in
  (* Whether a loan covers a place: the loan lends the place, or it lends a
     view of the place. [Some viewed] if it does, where [viewed] is true in
     the second case. *)
  let covers index (loan : loan) (place : Place.t) =
    if overlaps loan.lent place then Some false
    else if
      List.exists
        (fun (viewed : view) -> overlaps viewed.place place)
        (resolve context before.(index) [ { place = loan.lent; taken = false } ])
    then Some true
    else None
  in
  (* The loans that cover a place, oldest first, each with [viewed]. *)
  let covering index (point : point) (place : Place.t) =
    List.rev
      (List.filter_map
         (fun loan -> Option.map (fun viewed -> (loan, viewed)) (covers index loan place))
         point.loans)
  in
  let is_mut ((loan : loan), _) = loan.mode = Mut in
  (* A use of a place that is lent [mut]. *)
  let used index (point : point) (place : Place.t) =
    match List.find_opt is_mut (covering index point place) with
    | Some (loan, viewed) ->
        report context Conflicting_loan (span context point.origin)
          (lent_mut_message context loan ~viewed place)
    | None -> ()
  in
  (* A change to a place that is lent, or that a holder still in use
     views. One change gets one report. *)
  let changed index (point : point) (place : Place.t) ~what =
    let at = span context point.origin in
    let covering = covering index point place in
    match (List.find_opt is_mut covering, covering) with
    | Some (loan, viewed), _ ->
        report context Conflicting_loan at (lent_mut_message context loan ~viewed place)
    | None, (loan, viewed) :: _ ->
        report context Changed_while_viewed at (lent_message context loan ~viewed place ~what)
    | None, [] ->
        List.iter
          (fun ((holder : Place.root), viewed) ->
            let in_use =
              match holder with
              | Local local when not (kept_by_caller context { root = holder; steps = [] }) ->
                  List.mem local after.(index)
              | Local _ | Constant _ | Environment -> true
            in
            if in_use && List.exists (fun (viewed : view) -> overlaps viewed.place place) viewed
            then
              report context Changed_while_viewed at
                (Printf.sprintf "`%s` cannot %s while `%s`, which views it, is still in use."
                   (show context place) what (show_root context holder)))
          before.(index)
  in
  Array.iteri
    (fun index (point : point) ->
      let at = span context point.origin in
      match point.action with
      | Read place -> used index point place
      | Mutate place ->
          used index point place;
          changed index point place ~what:"be lent `mut`"
      | Assign place -> changed index point place ~what:"change"
      | Move { place; type_; returned; captured; _ } -> (
          used index point place;
          match verdict context place ~type_ ~returned ~captured with
          | Moves -> changed index point place ~what:"be moved"
          | Reads | Refused _ -> ())
      | Arguments { places; views; yielded } ->
          (* Two places that one call borrows may not overlap if one of
             them is borrowed [mut]. *)
          List.iteri
            (fun first_index (first : passed) ->
              List.iteri
                (fun second_index (second : passed) ->
                  if second_index > first_index && (first.mode = Mut || second.mode = Mut) then
                    let exclusive, also =
                      if first.mode = Mut then (first, second) else (second, first)
                    in
                    match Place.overlap first.place second.place with
                    | Overlap ->
                        report context Conflicting_loan
                          (with_mark context (span context second.at))
                          (Printf.sprintf
                             (if yielded then
                                format_of_string
                                  "`%s` is lent `mut` to the value that is yielded, so the value \
                                   cannot be lent `%s` too."
                              else
                                "`%s` is lent `mut` to this call, so the call cannot use `%s` too.")
                             (show context exclusive.place) (show context also.place))
                    | Maybe_apart (first_element, second_element) ->
                        context.disjoint <- (first_element, second_element) :: context.disjoint
                    | Apart -> ())
                places)
            places;
          (* A view passed to the call may not view a place that the call
             borrows [mut]: the callee would hold the view and change what
             it views. Two parts of one collection may be different
             elements, which the prover decides, as for two places. *)
          List.iter
            (fun (position, viewed, view_at) ->
              let viewed = resolve context before.(index) viewed in
              List.iter
                (fun (passed : passed) ->
                  if passed.position <> position && passed.mode = Mut then begin
                    let overlaps =
                      List.map
                        (fun (viewed : view) -> Place.overlap viewed.place passed.place)
                        viewed
                    in
                    if List.mem Place.Overlap overlaps then
                      report context Conflicting_loan
                        (with_mark context (span context view_at))
                        (Printf.sprintf
                           "`%s` is lent `mut` to this call, so the call cannot be given a view of \
                            it too."
                           (show context passed.place))
                    else
                      List.iter
                        (function
                          | Place.Maybe_apart (first, second) ->
                              context.disjoint <- (first, second) :: context.disjoint
                          | Overlap | Apart -> ())
                        overlaps
                  end)
                places)
            views
      | Views_temporary holder ->
          report context Views_temporary at
            (match holder with
            | None ->
                "This value is dropped at the end of the statement, but what the statement binds \
                 still views it. Bind it to a name first, so it lives as long as the view."
            (* A local that the compiler made, such as the list that a list
               literal builds, has no name that the source shows. *)
            | Some { root = Local (Synthetic _); _ } ->
                "This value is dropped at the end of the statement, but the collection that is \
                 built here may still view it. Bind it to a name first, so it lives as long as the \
                 view."
            | Some place ->
                Printf.sprintf
                  "This value is dropped at the end of the statement, but `%s` may still view it. \
                   Bind it to a name first, so it lives as long as the view."
                  (show_root context place.root))
      | Keeps_lent_part type_ ->
          report context Keeps_lent_part at
            ~fixes:
              (if copyable context type_ then
                 [ Diagnostic.fix "Copy it." [ Diagnostic.insert at.stop ".copy()" ] ]
               else [])
            "This part is lent only for this statement, so a name cannot keep it. Use it in this \
             statement, or copy it."
      | Gives_function views -> (
          (* Only a function that captures nothing may be kept. A function
             value that is not owned here may be a lambda that captures. *)
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
                "This lambda captures, and an `own` parameter may keep the function it is given \
                 after this function returns. Only a function that captures nothing can be given \
                 to an `own` parameter."
          | Some viewed ->
              report context View_escapes at
                (Printf.sprintf
                   "`%s` is not owned here, so it may be a lambda that captures, and an `own` \
                    parameter may keep the function it is given. Only a function that captures \
                    nothing can be given to an `own` parameter."
                   (show context viewed.place))
          | None -> ())
      | Return_view views -> (
          match
            List.find_opt (ends_with_function context) (resolve context before.(index) views)
          with
          | Some { place = { root = Environment; _ }; _ } ->
              report context View_escapes at
                "This returns a lambda that captures. What a lambda captures is kept in the \
                 function that the lambda is written in, so the lambda would outlive it. Only a \
                 function that captures nothing can be returned. Return a record that holds what \
                 the lambda needs instead, with a method that does the work."
          | Some local ->
              report context View_escapes at
                (Printf.sprintf
                   "This returns a view of `%s`, which is local to the function, so it would \
                    outlive it. A function returns views only of its parameters."
                   (show_root context local.place.root))
          | None ->
              (* A capability's callers cannot see its implementation, so a
                 method returns no view of the implementation's own parts:
                 the next call could change them. *)
              if
                context.implements_capability
                && List.exists
                     (fun (view : view) -> view.place.root = Local Self && not view.taken)
                     (resolve context before.(index) views)
              then
                report context View_crosses_capability at
                  "This returns a view of a part of an implementation of a capability. Code that \
                   calls the capability cannot see its implementation, and the next call could \
                   change that part. Return a copy instead.")
      | Store { place; views } -> (
          if kept_by_caller context place then
            let resolved = resolve context before.(index) views in
            (* The caller assumes that what it keeps views only what the
               function was given as a view. So the function cannot put
               there a view of a parameter that it was only lent, or a view
               of the place itself. *)
            let of_itself (view : view) = view.place.root = place.root && not view.taken in
            let only_lent (view : view) =
              match view.place.root with
              | Local local when local = Self || List.mem local context.parameters -> (
                  match Hashtbl.find_opt context.types local with
                  | Some type_ -> not (is_view context type_)
                  | None -> false)
              | Local _ | Constant _ | Environment -> false
            in
            (* A capability's callers cannot see its implementation, so the
               implementation keeps no view that a method is given. *)
            let given_to_implementation (view : view) =
              context.implements_capability && place.root = Local Self
              &&
              match view.place.root with
              | Local local -> local <> Self && List.mem local context.parameters
              | Constant _ | Environment -> false
            in
            match List.find_opt (ends_with_function context) resolved with
            | Some { place = { root = Environment; _ }; _ } ->
                report context View_escapes at
                  (Printf.sprintf
                     "This puts a lambda that captures in `%s`, which the caller keeps. What a \
                      lambda captures is kept in the function that the lambda is written in, so \
                      the lambda would outlive it. Only a function that captures nothing can be \
                      kept."
                     (show_root context place.root))
            | Some local ->
                report context View_escapes at
                  (Printf.sprintf
                     "This puts a view of `%s` in `%s`, which the caller keeps, so the view would \
                      outlive `%s`. What the caller keeps views only what reached the function \
                      through its parameters."
                     (show_root context local.place.root)
                     (show_root context place.root)
                     (show_root context local.place.root))
            | None -> (
                match
                  ( List.find_opt given_to_implementation resolved,
                    List.find_opt of_itself resolved,
                    List.find_opt only_lent resolved )
                with
                | Some given, _, _ ->
                    report context View_crosses_capability at
                      (Printf.sprintf
                         "This keeps a view of `%s` in an implementation of a capability. Code \
                          that calls the capability cannot see its implementation, so it could \
                          change or drop what is viewed. Keep a copy instead."
                         (show_root context given.place.root))
                | None, Some _, _ ->
                    report context Self_referential at
                      (Printf.sprintf
                         "This puts a view of a part of `%s` in `%s` itself. A value cannot hold a \
                          view of its own parts: the caller would not know that changing the part \
                          ends the view."
                         (show_root context place.root) (show_root context place.root))
                | None, None, Some lent ->
                    let lent = show_root context lent.place.root in
                    report context View_escapes at
                      (Printf.sprintf
                         "This puts a view of `%s` in `%s`, which the caller keeps, but `%s` is \
                          only lent to this function. A function keeps only the views that it is \
                          given. Take `%s` as a view type, such as a `Slice`, to keep a view of \
                          it."
                         lent (show_root context place.root) lent lent)
                | None, None, None -> ()))
      | Write_through slice -> (
          (* Writing through a slice changes what the slice views, so every
             place it views must be mutable. A slice held in a field is
             read-only, whatever the mode of its holder: the holder's mode
             says nothing about what the field views. A slice parameter is
             writable if its mode is [mut], which the type checker checks. *)
          let mutable_root (root : Place.root) =
            match root with
            | Constant _ | Environment -> false
            | Local local -> (
                match kind context root with
                | Mut_access -> true
                | Owned -> List.mem local context.variables
                | Viewing -> false)
          in
          match slice with
          | { steps = _ :: _; _ } ->
              report context Read_only_view at
                (Printf.sprintf
                   "`%s` is a slice held in a field, so nothing can be changed through it. Change \
                    the collection it views instead."
                   (show context slice))
          | { root = Local local; _ } when List.mem local context.parameters -> ()
          | _ -> (
              match
                List.find_opt
                  (fun (viewed : view) ->
                    viewed.place <> slice && not (mutable_root viewed.place.root))
                  (resolve context before.(index) [ { place = slice; taken = true } ])
              with
              | Some viewed ->
                  report context Read_only_view at
                    (Printf.sprintf
                       "`%s` views `%s`, which is read-only here, so nothing can be changed \
                        through `%s`."
                       (show context slice) (show context viewed.place) (show context slice))
              | None -> ()))
      | Suspend views -> (
          (* The caller may keep a view that it is given, so a method gives
             views only of what reached it through its parameters. *)
          match
            List.find_opt (ends_with_function context) (resolve context before.(index) views)
          with
          | Some { place = { root = Environment; _ }; _ } ->
              report context View_escapes at
                "This yields a lambda that captures. What a lambda captures is kept in the method \
                 that the lambda is written in, and the caller may keep what it is given. Only a \
                 function that captures nothing can be yielded."
          | Some local ->
              report context View_escapes at
                (Printf.sprintf
                   "This yields a view of `%s`, which is local to the method. The caller may keep \
                    a view that it is given, so a method yields views only of what reached it \
                    through its parameters. Yield `%s` itself, or a copy of what is viewed."
                   (show_root context local.place.root)
                   (show_root context local.place.root))
          | None -> ())
      | Enter | Take_lent _ | Bind _ | Ends _ | Task_end _ | Exit | Hold _ -> ())
    graph.points;
  (* What a stretch of code changes and uses. *)
  let effects (range : range) =
    let changes = ref [] and uses = ref [] in
    for index = range.first to range.limit - 1 do
      let point = graph.points.(index) in
      (* A use of a view is a use of what it views, and a write through a
         slice changes what the slice views. *)
      let viewed place =
        List.map
          (fun (view : view) -> view.place)
          (resolve context before.(index) [ { place; taken = true } ])
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
  (* The branches of a [parallel] or [concurrent] block run at the same
     time. A place that one branch changes must not overlap a place that
     another branch uses. Two elements of one collection may be different:
     the prover decides. *)
  List.iter
    (fun ({ keyword; branches } : simultaneous_block) ->
      let branches = List.map effects branches in
      List.iteri
        (fun index (changes, _) ->
          List.iteri
            (fun other (other_changes, other_uses) ->
              if other <> index then (
                let used = other_uses @ List.map fst other_changes in
                List.iter
                  (fun (place, origin) ->
                    if List.exists (fun other -> Place.overlap other place = Overlap) used then
                      report context Data_race (span context origin)
                        (Printf.sprintf
                           "One branch of this `%s` block changes `%s`, which another branch uses."
                           keyword (show context place));
                    if other > index then
                      List.iter
                        (fun other ->
                          match Place.overlap place other with
                          | Maybe_apart (first, second) ->
                              context.disjoint <- (first, second) :: context.disjoint
                          | Overlap | Apart -> ())
                        used)
                  changes;
                if other > index then
                  (* The other branch's changes against this branch's reads. *)
                  let _, uses = List.nth branches index in
                  List.iter
                    (fun (place, _) ->
                      List.iter
                        (fun used ->
                          match Place.overlap place used with
                          | Maybe_apart (first, second) ->
                              context.disjoint <- (first, second) :: context.disjoint
                          | Overlap | Apart -> ())
                        uses)
                    other_changes))
            branches)
        branches)
    graph.simultaneous_blocks;
  (* Each iteration of a [parallel for] or [concurrent for] runs at the same
     time as the others, so the body may change only what belongs to one
     iteration: the locals that the pattern binds and the locals bound in
     the body. *)
  List.iter
    (fun ({ keyword; body = range; bound } : simultaneous_loop) ->
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
              (Printf.sprintf "A `%s for` may change only its own element and its own locals."
                 keyword))
        (fst (effects range)))
    graph.simultaneous_loops
