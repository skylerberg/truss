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
type holdings = (Place.root * Place.t list) list

let held (holdings : holdings) (holder : Place.root) = List.assoc_opt holder holdings

let hold (holdings : holdings) holder places : holdings =
  let known = Option.value ~default:[] (held holdings holder) in
  let added = List.filter (fun place -> not (List.mem place known)) places in
  (holder, known @ added) :: List.remove_assoc holder holdings

let local_type context local = Hashtbl.find_opt context.types local

(* Whether a root has a value of its own that a view of it refers to. A
   local that is itself a view, or that only views another place, has
   none: a value read from it views what the local views. *)
let has_own_value context (root : Place.root) =
  match root with
  | Constant _ | Local Self -> true
  | Local local -> (
      List.mem local context.parameters
      || kind context root = Owned
         &&
         match local_type context local with
         | Some type_ -> not (is_view context type_)
         | None -> true)

(* The places that a value views, given the places it names. *)
let resolve context (holdings : holdings) (places : Place.t list) : Place.t list =
  List.concat_map
    (fun (place : Place.t) ->
      match held holdings place.root with
      | Some viewed when not (has_own_value context place.root) -> viewed
      | known -> Option.value ~default:[] known @ [ place ])
    places

(* Whether a place is gone when the function returns, so that nothing the
   caller keeps may view it: a local, and a parameter or [self] that the
   function owns. An owned view stands for what it views, which the caller
   has. *)
let ends_with_function context (place : Place.t) =
  match place.root with
  | Constant _ -> false
  | Local local ->
      let owned =
        kind context place.root = Owned
        &&
        match local_type context local with
        | Some type_ -> not (is_view context type_)
        | None -> true
      in
      if local = Self || List.mem local context.parameters then owned else true

(* Whether the caller keeps the place after the function returns: a [mut]
   parameter, or [self] in a [mut self] method. *)
let kept_by_caller context (place : Place.t) =
  kind context place.root = Mut_access
  && match place.root with Local local -> List.mem local context.parameters | Constant _ -> false

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
  | Enter | Read _ | Move _ | Take_lent _ | Mutate _ | Assign _ | Exit | Return_view _
  | Views_temporary _ | Keeps_lent_part _ | Write_through _ | Arguments _ ->
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
        match place.root with Local local -> [ local ] | Constant _ -> [])
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

let lent_mut_message context (loan : loan) =
  let place = show context loan.lent in
  match loan.lender with
  | To_loop -> Printf.sprintf "`%s` is lent `mut` to the loop, so its body cannot use it." place
  | To_statement ->
      Printf.sprintf
        "`%s` is lent `mut` for the rest of this statement, so the statement cannot use it again."
        place

let overlaps left right = Place.overlap left right <> Apart

let check context (graph : Graph.t) =
  let before = holdings_before context graph in
  let after = used_after graph in
  (* A use of a place that is lent [mut]. *)
  let used (point : point) (place : Place.t) =
    List.iter
      (fun (loan : loan) ->
        if loan.mode = Mut && overlaps loan.lent place then
          report context Conflicting_loan (span context point.origin)
            (lent_mut_message context loan))
      point.loans
  in
  (* A change to a place that is lent, or that a holder still in use
     views. *)
  let changed index (point : point) (place : Place.t) ~what =
    let at = span context point.origin in
    List.iter
      (fun (loan : loan) ->
        if overlaps loan.lent place then
          if loan.mode = Mut then report context Conflicting_loan at (lent_mut_message context loan)
          else
            report context Changed_while_viewed at
              (Printf.sprintf
                 (match loan.lender with
                 | To_loop -> format_of_string "`%s` cannot %s while the loop goes over it."
                 | To_statement ->
                     "`%s` cannot %s while a part of it is lent, which lasts this statement.")
                 (show context place) what))
      point.loans;
    List.iter
      (fun ((holder : Place.root), viewed) ->
        let in_use =
          match holder with
          | Local local when not (kept_by_caller context { root = holder; steps = [] }) ->
              List.mem local after.(index)
          | Local _ | Constant _ -> true
        in
        if in_use && List.exists (fun viewed -> overlaps viewed place) viewed then
          report context Changed_while_viewed at
            (Printf.sprintf "`%s` cannot %s while `%s`, which views it, is still in use."
               (show context place) what (show_root context holder)))
      before.(index)
  in
  Array.iteri
    (fun index (point : point) ->
      let at = span context point.origin in
      match point.action with
      | Read place -> used point place
      | Mutate place ->
          used point place;
          changed index point place ~what:"be lent `mut`"
      | Assign place -> changed index point place ~what:"change"
      | Move { place; type_; returned; captured; _ } -> (
          used point place;
          match verdict context place ~type_ ~returned ~captured with
          | Moves -> changed index point place ~what:"be moved"
          | Reads | Refused _ -> ())
      | Arguments { places; lent } ->
          (* Two places passed to one call may not overlap if one of them
             is borrowed [mut] or moved. *)
          let given : T.mode -> string = function Mut -> "lent `mut`" | _ -> "moved" in
          List.iteri
            (fun first_index (first : passed) ->
              List.iteri
                (fun second_index (second : passed) ->
                  if second_index > first_index && (first.mode <> Read || second.mode <> Read) then
                    let exclusive, also =
                      if first.mode <> Read then (first, second) else (second, first)
                    in
                    match Place.overlap first.place second.place with
                    | Overlap ->
                        report context Conflicting_loan
                          (with_mark context (span context second.at))
                          (Printf.sprintf
                             "`%s` is %s to this call, so the call cannot use `%s` too."
                             (show context exclusive.place) (given exclusive.mode)
                             (show context also.place))
                    | Maybe_apart (first_element, second_element) ->
                        context.disjoint <- (first_element, second_element) :: context.disjoint
                    | Apart -> ())
                places)
            places;
          (* A part that a call lends lends its whole place, so an
             argument before the part may not overlap that place if either
             is [mut]. *)
          List.iter
            (fun (position, lender, lent_mode, lent_at) ->
              List.iter
                (fun (passed : passed) ->
                  if
                    passed.position < position
                    && (passed.mode <> Read || lent_mode <> T.Read)
                    && overlaps passed.place lender
                  then
                    report context Conflicting_loan
                      (with_mark context (span context lent_at))
                      (Printf.sprintf
                         "This call is given `%s`, and a part that `%s` lends, and one of them is \
                          `mut`. A place is lent whole, for the rest of the statement, when a part \
                          of it is lent."
                         (show context passed.place) (show context lender)))
                places)
            lent
      | Views_temporary holder ->
          report context Views_temporary at
            (match holder with
            | None ->
                "This value is dropped at the end of the statement, but what the statement binds \
                 still views it. Bind it to a name first, so it lives as long as the view."
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
      | Return_view views -> (
          match
            List.find_opt (ends_with_function context) (resolve context before.(index) views)
          with
          | Some local ->
              report context Returns_local_view at
                (Printf.sprintf
                   "This returns a view of `%s`, which is local to the function, so it would \
                    outlive it. A function returns views only of its parameters."
                   (show_root context local.root))
          | None -> ())
      | Store { place; views } -> (
          if kept_by_caller context place then
            match
              List.find_opt (ends_with_function context) (resolve context before.(index) views)
            with
            | Some local ->
                report context Stores_local_view at
                  (Printf.sprintf
                     "This puts a view of `%s` in `%s`, which the caller keeps, so the view would \
                      outlive `%s`. What the caller keeps views only what reached the function \
                      through its parameters."
                     (show_root context local.root) (show_root context place.root)
                     (show_root context local.root))
            | None -> ())
      | Write_through slice -> (
          (* Writing through a slice changes what the slice views, so every
             place it views must be mutable. A slice held in a field is
             read-only, whatever the mode of its holder: the holder's mode
             says nothing about what the field views. A slice parameter is
             writable if its mode is [mut], which the type checker checks. *)
          let mutable_root (root : Place.root) =
            match root with
            | Constant _ -> false
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
                  (fun (viewed : Place.t) -> viewed <> slice && not (mutable_root viewed.root))
                  (resolve context before.(index) [ slice ])
              with
              | Some viewed ->
                  report context Read_only_view at
                    (Printf.sprintf
                       "`%s` views `%s`, which is read-only here, so nothing can be changed \
                        through `%s`."
                       (show context slice) (show context viewed) (show context slice))
              | None -> ()))
      | Enter | Take_lent _ | Bind _ | Exit | Hold _ -> ())
    graph.points;
  (* What a stretch of code changes and uses, for [parallel]. *)
  let effects (range : range) =
    let changes = ref [] and uses = ref [] in
    for index = range.first to range.limit - 1 do
      let point = graph.points.(index) in
      match point.action with
      | Read place -> uses := place :: !uses
      | Mutate place ->
          uses := place :: !uses;
          changes := (place, point.origin) :: !changes
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
  (* The branches of a [parallel] block run at the same time. A place that
     one branch changes must not overlap a place that another branch uses.
     Two elements of one collection may be different: the prover decides. *)
  List.iter
    (fun branches ->
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
                      report context Parallel_conflict (span context origin)
                        (Printf.sprintf
                           "One branch of this `parallel` block changes `%s`, which another branch \
                            uses."
                           (show context place));
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
    graph.parallel_blocks;
  (* Each iteration of a [parallel for] runs at the same time as the
     others, so the body may change only what belongs to one iteration: the
     locals that the pattern binds and the locals bound in the body. *)
  List.iter
    (fun ((range : range), own) ->
      let bound = ref own in
      for index = range.first to range.limit - 1 do
        match graph.points.(index).action with Bind locals -> bound := locals @ !bound | _ -> ()
      done;
      List.iter
        (fun ((place : Place.t), origin) ->
          let outside =
            match place.root with
            | Constant _ | Local Self -> true
            | Local local -> not (List.mem local !bound)
          in
          if outside then
            report context Parallel_conflict (span context origin)
              "A `parallel for` may change only its own element and its own locals.")
        (fst (effects range)))
    graph.parallel_loops
