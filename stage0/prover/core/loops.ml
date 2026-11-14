(* Loops: invariants, measures, and costs, at the head, after each
   iteration, and at the exit. *)

open Core
open State
open Facts
open Contracts
open Validity
open Operations
open Models
open Lambdas
open Intrinsics
open Laws
open Amounts
open Calls
open Values

(* Loops' costs. A loop's [cost] clause about a counter bounds the loop's
   cost so far at its head, on entry and after each iteration, and after
   the loop the loop costs the clause's bound, as a call with that bound
   would. Any other counter is bounded by the iterations so far times a
   per-iteration bound, [per], which is inferred from the body's cost and
   then proven of each iteration.

   Where the values a loop mutates hold potential, which amortized callees
   spend and save, a second bound, [per_held], bounds the loop's cost so far
   plus the potential it holds. That sum telescopes when each iteration
   spends potential that earlier ones saved. Both bounds are assumed at the
   head. The assumption is sound even before the bound is inferred, since
   each run of the loop has a last iteration. Only the bound an iteration's
   cost needs is inferred and proven. [held] maps a frame to the potential
   of the values the loop mutates. *)
let loop_costs context frame (clauses : Mir.loop_clause list) ~held =
  List.map
    (fun (counter : Costs.counter) ->
      let entry =
        match List.assoc_opt counter frame.spent with Some term -> term | None -> Costs.zero
      in
      let written =
        List.find_map
          (fun (clause : Mir.loop_clause) ->
            match clause with
            | Cost cost
              when same_resource cost ~locals:frame.locals counter
                   && counting_of cost = counter.counting ->
                Some cost
            | _ -> None)
          clauses
      in
      let rule =
        match written with
        | Some cost -> Clause_bound cost
        | None ->
            Per_iteration
              {
                per = fresh context frame "per" Logic.Int;
                per_held =
                  Option.map (fun held -> (fresh context frame "per" Logic.Int, held frame)) held;
              }
      in
      {
        counter;
        entry;
        rule;
        held;
        held_on_entry = Option.map (fun held -> held frame) held;
        gained_at_head =
          (match (rule, held) with
          | Clause_bound _, Some _ when counter.counting <> Exactly ->
              Some (fresh context frame "gained" Logic.Int)
          | _ -> None);
        counts_potential = false;
      })
    context.counters

(* That a loop's [cost] clause bounds the loop's cost so far, at [at]. *)
let loop_clause_holds context (at : frame) (counter : Costs.counter) (cost : Mir.cost) ~since =
  let amount =
    match cost.bound with
    | Order_of amount | At_most amount | Exactly amount ->
        snd (specification_value context { at with checking = false } amount)
    | Finite -> Costs.zero
  in
  match counter.counting with
  | Units -> Costs.at_most since (Costs.bound amount)
  | Exactly -> Logic.equal since amount
  | At_most -> Costs.at_most since amount

(* The potential that the values a loop mutates have gained since its
   entry, where the loop's [cost] clause counts it. An iteration that calls
   an amortized callee spends or saves potential, so its clause bounds the
   cost so far plus the potential gained: that sum telescopes where the cost
   alone does not. *)
let potential_gained (cost : loop_cost) (at : frame) =
  match (cost.held, cost.held_on_entry) with
  | Some held, Some on_entry when cost.counts_potential -> Costs.minus (held at) on_entry
  | _ -> Costs.zero

let spent_at (frame : frame) key =
  match List.assoc_opt key frame.spent with Some spent_term -> spent_term | None -> Costs.zero

(* A counter's bounded term at the head and where the loop is left:
   its value, plus the potential the loop holds there, for [per_held]. *)
let counted_with ~(counter : Costs.counter) ~at ~bound =
  if counter.counting = Exactly then Logic.equal at bound else Costs.at_most at bound

(* The head of a loop: each counter takes a fresh value, within its
   clause, or within its iterations so far times its bounds on one. *)
let loop_head context head costs ~iterations =
  let iterations = Option.value iterations ~default:Costs.zero in
  let head =
    {
      head with
      spent = List.map (fun cost -> (cost.counter, fresh context head "spent" Logic.Int)) costs;
    }
  in
  List.iter
    (fun cost ->
      let at_head = spent_at head cost.counter in
      match cost.rule with
      | Clause_bound written ->
          assume context head
            (loop_clause_holds context head cost.counter written
               ~since:
                 (Costs.plus (Costs.minus at_head cost.entry)
                    (Option.value cost.gained_at_head ~default:Costs.zero)))
      | Per_iteration { per; per_held } -> (
          assume context head
            (counted_with ~counter:cost.counter ~at:at_head
               ~bound:(Costs.plus cost.entry (Costs.times iterations per)));
          match (per_held, cost.held) with
          | Some (per_held, on_entry), Some held ->
              assume context head
                (counted_with ~counter:cost.counter
                   ~at:(Costs.plus at_head (held head))
                   ~bound:
                     (Costs.plus (Costs.plus cost.entry on_entry) (Costs.times iterations per_held)))
          | _ -> ()))
    costs;
  head

(* Each [cost] clause on entry to the loop, when nothing is spent yet. *)
let loop_entry context frame costs =
  List.iter
    (fun cost ->
      match cost.rule with
      | Clause_bound written ->
          (* The bound is well defined, as every specification must be. *)
          (match written.bound with
          | Order_of amount | At_most amount | Exactly amount ->
              ignore (specification_value context frame amount)
          | Finite -> ());
          oblige context frame Cost
            (span_of frame.source written.origin)
            (Printf.sprintf "The loop's `%s` may not hold on entry to the loop."
               (quote frame.source written.origin))
            (loop_clause_holds context frame cost.counter written ~since:Costs.zero)
      | Per_iteration _ -> ())
    costs

(* After the body: each per-iteration bound is inferred from the costs of
   the iterations that completed, and every iteration, completed or exited
   by [break], is proven to be within its counter's bound. An iteration that
   spends or saves potential is bounded with the potential the loop
   holds. *)
let loop_iterations context loop_at head costs ~mark ~facts ~ends ~breaks =
  let span = span_of head.source loop_at in
  List.iter
    (fun cost ->
      match cost.rule with
      | Clause_bound written_cost ->
          (* The clause counts the potential gained where an iteration spends
             or saves potential, which decides what it counted at the head. *)
          cost.counts_potential <-
            Option.is_some cost.gained_at_head
            && List.exists
                 (fun (frame : frame) ->
                   mentions_potential
                     (Costs.since ~start:(spent_at head cost.counter) (spent_at frame cost.counter)))
                 (ends @ breaks);
          Option.iter
            (fun gained -> fact context head (Logic.equal gained (potential_gained cost head)))
            cost.gained_at_head;
          List.iter
            (fun (frame, when_) ->
              oblige context frame Cost
                (span_of frame.source written_cost.origin)
                (Printf.sprintf "The loop's `%s` may not hold %s."
                   (quote frame.source written_cost.origin)
                   when_)
                (loop_clause_holds context frame cost.counter written_cost
                   ~since:
                     (Costs.plus
                        (Costs.minus (spent_at frame cost.counter) cost.entry)
                        (potential_gained cost frame))))
            (List.map (fun exit_frame -> (exit_frame, "after an iteration")) ends
            @ List.map (fun exit_frame -> (exit_frame, "where the loop is left")) breaks)
      | Per_iteration { per; per_held } -> (
          let frames = ends @ breaks in
          let plain (frame : frame) =
            Costs.since ~start:(spent_at head cost.counter) (spent_at frame cost.counter)
          in
          let held_rule =
            match (per_held, cost.held) with
            | Some (per_held, _), Some held
              when List.exists (fun exit_frame -> mentions_potential (plain exit_frame)) frames ->
                [
                  ( per_held,
                    fun (frame : frame) ->
                      Costs.normalize
                        (Costs.plus (plain frame) (Costs.minus (held frame) (held head))) );
                ]
            | _ -> []
          in
          let facts = facts @ List.map (fun (frame : frame) -> frame.condition) frames in
          let bounded (per, spent_in) =
            let spent = List.map spent_in frames in
            let most =
              match spent with
              | [] -> Costs.zero
              | first :: rest -> List.fold_left Costs.larger first rest
            in
            Option.map
              (fun bound -> (per, spent, bound))
              (Costs.bound_on ~varies:(mentions_fresh_after context mark) ~facts most)
          in
          match List.find_map bounded (held_rule @ [ (per, plain) ]) with
          | Some (per, spent, bound) ->
              fact context head (Logic.equal per bound);
              List.iter2
                (fun (frame : frame) spent ->
                  oblige context frame Cost span
                    "The prover cannot show that this iteration of the loop costs no more than the \
                     per-iteration bound it inferred from the values the loop does not mutate: \
                     give the loop a `cost` clause."
                    (counted_with ~counter:cost.counter ~at:spent ~bound:per))
                frames spent
          | None ->
              oblige context head Cost span
                "The prover cannot bound the cost of one iteration of this loop by the values the \
                 loop does not mutate, so it cannot count the loop's cost: give the loop a `cost` \
                 clause."
                (Logic.Boolean false)))
    costs

let loop_exit context (exit_ : frame) costs ~iterations ~most =
  let iterations = Option.value iterations ~default:Costs.zero in
  let spent =
    List.map
      (fun cost ->
        let at = spent_at exit_ cost.counter in
        match cost.rule with
        | Clause_bound written ->
            let amount =
              match written.bound with
              | Order_of amount | At_most amount | Exactly amount ->
                  snd (specification_value context { exit_ with checking = false } amount)
              | Finite -> Costs.zero
            in
            let counted =
              match cost.counter.counting with
              | Units -> Costs.units amount
              | At_most -> bounded_amount context exit_ amount
              | Exactly -> amount
            in
            (* The clause bounds the cost with the potential gained, so the
               cost is the bound less that potential. *)
            (cost.counter, Costs.minus (Costs.plus cost.entry counted) (potential_gained cost exit_))
        | Per_iteration { per; per_held } ->
            let bounded ~at ~start per =
              if cost.counter.counting <> Exactly then
                List.iter
                  (fun most ->
                    fact context exit_
                      Logic.(
                        conjunction
                          [
                            Costs.at_most at (Costs.plus start (Costs.times iterations per));
                            Operation ("<=", [ int 0; iterations ]);
                            Operation ("<=", [ iterations; most ]);
                            Operation ("<=", [ int 0; per ]);
                          ]
                        ==> Costs.at_most at (Costs.plus start (Costs.times most per))))
                  most
            in
            bounded ~at ~start:cost.entry per;
            (match (per_held, cost.held) with
            | Some (per_held, on_entry), Some held ->
                bounded
                  ~at:(Costs.plus at (held exit_))
                  ~start:(Costs.plus cost.entry on_entry) per_held
            | _ -> ());
            (cost.counter, at))
      costs
  in
  { exit_ with spent }

(* The potential held by the values of some locals, in a frame, or nothing
   when none of their types can hold any. *)
let held_by context (frame : frame) (changed : changed) =
  let typed =
    List.filter_map
      (fun id -> Option.map (fun ty -> (`Local id, ty)) (local_type context frame id))
      changed.changed_locals
    @
    match (changed.changes_self, frame.self_type) with
    | true, Some ty -> [ (`Self, ty) ]
    | _ -> []
  in
  if not (List.exists (fun (_, ty) -> has_potential context ty) typed) then None
  else
    Some
      (fun (frame : frame) ->
        List.fold_left
          (fun total (place, ty) ->
            match (place, frame.self) with
            | `Local id, _ -> (
                match Locals.find_opt id frame.locals with
                | Some term -> Costs.plus total (potential context frame ty term)
                | None -> total)
            | `Self, Some self -> Costs.plus total (potential context frame ty self)
            | `Self, None -> total)
          Costs.zero typed)

(* An [assert ... by bit_vector], proven in a query of its own: for every
   value of the integers and booleans it names, with its bitwise
   operations defined exactly. It holds of every value, so it holds of the
   values it is asserted of, and the caller assumes it. *)
let bit_vector_assertion context frame (formula : Mir.formula) =
  (* The locals the assertion names are the parameters of its formula. *)
  let named =
    List.map
      (fun parameter ->
        match formula.locals.(parameter) with
        | { kind = Source { local; _ }; type_; _ } -> (local, type_)
        | { kind = Temporary | Lent _; _ } -> bug "an assertion's formula that takes no local")
      formula.parameters
  in
  let saved_facts = context.facts and saved_decisions = context.decisions in
  let saved_stated = Hashtbl.copy context.stated in
  context.facts <- [];
  context.decisions <- [];
  let isolated =
    { frame with condition = Logic.Boolean true; bound = []; binders = []; checking = false }
  in
  let isolated =
    List.fold_left
      (fun (inside : frame) (local, ty) ->
        let symbol = fresh context inside "asserted" (sort_of context ty) in
        assume context inside (in_range ty symbol);
        match local with
        | Core.Self -> { inside with self = Some symbol }
        | _ -> { inside with locals = Locals.add local symbol inside.locals })
      isolated named
  in
  let _, term = context.formula_term isolated formula ~arguments:[] in
  let obligation =
    make_obligation context { isolated with checking = true } Assertion
      (span_of frame.source formula.origin)
      (Printf.sprintf "`%s` may not hold for every value of the variables it names."
         (quote frame.source formula.origin))
      term
  in
  context.obligations <- { obligation with query = exactly obligation.query } :: context.obligations;
  context.facts <- saved_facts;
  context.decisions <- saved_decisions;
  Hashtbl.reset context.stated;
  Hashtbl.iter (Hashtbl.replace context.stated) saved_stated

(* Statements and blocks *)

(* An [assert] of [term], the condition written at [origin]: an obligation,
   or where it is proven by bit vectors or in a test, an assumption. *)
let assertion context frame ~origin ~bit_vector term =
  (match bit_vector with
  | Some asserted when not (is_test context) -> bit_vector_assertion context frame asserted
  | _ -> ());
  if is_test context || bit_vector <> None then assume context frame term
  else
    oblige context frame Assertion (span_of frame.source origin)
      (Printf.sprintf "`%s` may not hold." (quote frame.source origin))
      term

(* The part a lending method lends, where its body gives it: the part meets
   the clauses about it, and a [mut] part comes back as the caller left it,
   which is any value of its type. [handed] is the part's value, [lends]
   says whether it lends places, and [write_back] writes the caller's
   changes to it back to them. *)
let lend_part context frame origin (mode : Types.mode) ~handed ~lends ~write_back =
  let span = span_of frame.source origin in
  match (context.yielded_part, context.yield_ensures, frame.yielded_so_far) with
  | Some part_type, Some (each, _), Some before ->
      List.iter
        (fun (clause : Mir.formula) ->
          let _, term =
            specification_value context
              { frame with result = Some handed; yielded = Some before }
              clause
          in
          oblige context frame Ensures
            (span_of frame.source clause.origin)
            (Printf.sprintf "`%s` may not hold for the part lent here."
               (quote frame.source clause.origin))
            term)
        each;
      check_valid context frame span part_type handed ~deep:true ~when_:"for the part lent here";
      (* The caller's changes to a part lent [mut] are written to each lent
         place. *)
      let frame, part_after =
        if mode = Types.Mut && lends then (
          let part_after = arrive context frame "lent" part_type in
          context.lent_back <- (part_type, handed, part_after) :: context.lent_back;
          (write_back frame part_after, part_after))
        else (frame, handed)
      in
      Some { frame with yielded_so_far = Some (appended context frame part_type before part_after) }
  | _ -> unsupported span "a lent part outside a lending method's body"

(* That one sequence is another with the element at [index] replaced by
   [part]. *)
let replaced context frame element ~before ~after index part =
  let length sequence = sequence_length context element sequence in
  let at = element_at context element in
  let limit = fresh_name context "index" in
  assume context frame
    (Logic.conjunction
       [ Logic.equal (length after) (length before); Logic.equal (at after index) part ]);
  assume context frame
    (Logic.forall
       ( [ (limit, Logic.Int) ],
         Logic.(
           Operation ("<=", [ int 0; Symbol limit ])
           &&& Operation ("<", [ Symbol limit; length before ])
           &&& not_ (equal (Symbol limit) index)
           ==> equal (at after (Symbol limit)) (at before (Symbol limit))) ))

(* A storage whose element at [index] is [part], and which is otherwise the
   one it was. *)
let storage_updated context frame element storage index part =
  let storage_type =
    Types.Named { path = Intrinsic.builtin_path Storage; arguments = [ Types.Type element ] }
  in
  let updated = arrive context frame "changed" storage_type in
  replaced context frame element
    ~before:(buffer_model context Storage element storage)
    ~after:(buffer_model context Storage element updated)
    index part;
  assume context frame
    (Logic.equal
       (buffer_capacity context element updated)
       (buffer_capacity context element storage));
  updated

(* An array whose element at [index] is [part], and which is otherwise the
   one it was. *)
let array_updated context frame (array_type : Types.ty) array index part =
  match array_type with
  | Types.Named { arguments = Types.Type element :: _; _ } ->
      let updated = arrive context frame "changed" array_type in
      replaced context frame element
        ~before:(array_model context frame array_type array)
        ~after:(array_model context frame array_type updated)
        index part;
      updated
  | _ -> raise (Foreign_unsupported (Printf.sprintf "the elements of `%s`" (Types.show array_type)))

let element_written_back context frame ~(operation : Intrinsic.operation) ~type_arguments
    ~(receiver : passed_place) ~receiver_type index final =
  let element () =
    match type_arguments with
    | Types.Type element :: _ -> substituted context frame element
    | _ -> bug "an element's lend with no element type"
  in
  match operation with
  | Storage_at_mut ->
      receiver.write frame
        (storage_updated context frame (element ()) (receiver.read frame) index final)
  | Array_at_mut ->
      receiver.write frame
        (array_updated context frame receiver_type (receiver.read frame) index final)
  | View_at_mut ->
      let element = element () in
      let updated = arrive context frame "changed" receiver_type in
      replaced context frame element
        ~before:(buffer_model context View element (receiver.read frame))
        ~after:(buffer_model context View element updated)
        index final;
      receiver.write frame updated
  | _ -> bug "a lend of an element by an operation that lends none"

(* A record, or a variant's value, of [ty], with one field's value
   replaced. *)
let field_replaced context ty variant field whole new_value =
  match Option.bind (constructors context ty) (List.assoc_opt variant) with
  | Some fields ->
      Logic.Apply
        ( constructor_name ty variant,
          List.map
            (fun (name, _) ->
              if name = field then new_value else selected context ty variant name whole)
            fields )
  | None -> raise (Foreign_unsupported (Printf.sprintf "the fields of `%s`" (Types.show ty)))

let havoc context frame (changed : changed) =
  let frame =
    List.fold_left
      (fun frame local ->
        let ty =
          match local_type context frame local with Some ty -> ty | None -> Types.Integer
        in
        { frame with locals = Locals.add local (arrive context frame "loop" ty) frame.locals })
      frame changed.changed_locals
  in
  match (changed.changes_self, frame.self_type) with
  | true, Some ty -> { frame with self = Some (arrive context frame "loop" ty) }
  | _ -> frame

(* Validity is an invariant of every loop: each value the loop mutates
   that is valid on entry is valid at the head of each iteration, so each
   iteration must keep it valid. A value that is not valid on entry, as
   [self] may not be in a private method that updates it, is not held to
   it. *)
let preserved_validity context (entry : frame) (changed : changed) =
  let obligation name ty before read =
    match validity context entry ~assuming:false ~deep:true ty before with
    | Logic.Boolean true -> None
    | valid -> Some (name, ty, valid, read)
  in
  List.filter_map
    (fun local ->
      match (local_type context entry local, Locals.find_opt local entry.locals) with
      | Some ty, Some before ->
          obligation
            (Option.value (Hashtbl.find_opt context.local_names local) ~default:"a local")
            ty before
            (fun (at : frame) -> Locals.find_opt local at.locals)
      | _ -> None)
    changed.changed_locals
  @
  match (changed.changes_self, entry.self, entry.self_type) with
  | true, Some before, Some ty ->
      Option.to_list (obligation "self" ty before (fun (at : frame) -> at.self))
  | _ -> []

let assume_preserved_validity context head preserved =
  List.iter
    (fun (_, ty, valid_on_entry, read) ->
      match read head with
      | Some term ->
          assume context head
            (Logic.( ==> ) valid_on_entry (validity context head ~assuming:true ~deep:true ty term))
      | None -> ())
    preserved

let check_preserved_validity context end_ span preserved =
  List.iter
    (fun (name, ty, valid_on_entry, read) ->
      match read end_ with
      | Some term ->
          oblige context end_ Invariant span
            (Printf.sprintf "The invariant of `%s` may not hold for `%s` after an iteration."
               (Types.show ty) name)
            (Logic.( ==> ) valid_on_entry
               (validity context end_ ~assuming:false ~deep:true ty term))
      | None -> ())
    preserved

let check_invariants context frame clauses ~when_ =
  List.iter
    (fun (invariant : Mir.formula) ->
      let _, term = specification_value context frame invariant in
      oblige context frame Invariant
        (span_of frame.source invariant.origin)
        (Printf.sprintf "The loop invariant `%s` may not hold %s."
           (quote frame.source invariant.origin)
           when_)
        term)
    (invariants clauses)

let assume_invariants context frame clauses =
  List.iter
    (fun (invariant : Mir.formula) ->
      let _, term = specification_value context { frame with checking = false } invariant in
      assume context frame term)
    (invariants clauses)

let measures_of (clauses : Mir.loop_clause list) =
  List.find_map (function Mir.Decreases measures -> Some measures | _ -> None) clauses

(* The start of a loop, from the frame before it and [entry], the frame its
   invariants are checked in on entry. *)
let enter_loop ?holds context frame ~entry clauses ~changed =
  let holds = Option.value holds ~default:changed in
  let costs = loop_costs context frame clauses ~held:(held_by context frame holds) in
  loop_entry context entry costs;
  let fresh_mark = context.fresh and facts_mark = List.length context.facts in
  let preserved = preserved_validity context frame changed in
  let head = havoc context frame changed in
  assume_preserved_validity context head preserved;
  { loop_costs = costs; fresh_mark; facts_mark; preserved; havocked = head }

(* The frame after a loop, from the frames that leave it, without the
   locals declared inside it. *)
let leave_loop context frame frames =
  Option.map (end_scope ~outer:frame) (join_frames context frames)

let end_iterations context frame loop_at clauses (start : loop_start) ~head ~inside ~ends ~breaks
    ~with_through =
  loop_iterations context loop_at head start.loop_costs ~mark:start.fresh_mark
    ~facts:(facts_since context start.facts_mark @ [ inside.condition ])
    ~ends:(List.map with_through ends) ~breaks:(List.map with_through breaks);
  List.iter
    (fun (end_ : frame) ->
      check_invariants context (with_through end_) clauses ~when_:"after an iteration";
      check_preserved_validity context end_ (span_of frame.source loop_at) start.preserved)
    ends

(* A ghost count of a loop's iterations so far, when the loop counts a
   cost by them. *)
let iterations_so_far context head costs =
  if
    List.exists
      (fun (cost : loop_cost) ->
        match cost.rule with Per_iteration _ -> true | Clause_bound _ -> false)
      costs
  then begin
    let iterations = fresh context head "iterations" Logic.Int in
    assume context head (Logic.Operation ("<=", [ Logic.int 0; iterations ]));
    Some iterations
  end
  else None

let one_step (counter : Costs.counter) =
  match counter.resource with Time -> Logic.int 1 | _ -> Costs.zero

(* What a loop that reads the elements of a collection knows of [yielded],
   the elements of the [count] iterations before: each is the value of the
   collection's [element] at its position, which [element_at] reads from
   [call], so each meets that method's postcondition. Where the collection
   has a model that is a sequence of its elements, [yielded] is compared
   with the model, so that [yielded] is the model once the loop has been
   lent every element. *)
let elements_so_far context head ~element ~collection ~count yielded element_at =
  let symbol = fresh_name context "position" in
  let position = Logic.Symbol symbol in
  let premise =
    Logic.(Operation ("<=", [ int 0; position ]) &&& Operation ("<", [ position; count ]))
  in
  (match sequence_at context element yielded position with
  | Some earlier ->
      let _, same, with_facts =
        under_binder context
          { head with bound = symbol :: head.bound; checking = false }
          symbol Logic.Int premise
          (fun inner -> Option.map (Logic.equal earlier) (element_at inner position))
      in
      Option.iter
        (fun same ->
          assume context head
            (with_facts (Logic.forall ([ (symbol, Logic.Int) ], Logic.( ==> ) premise same))))
        same
  | None -> ());
  match collection with
  | Some read ->
      let collection_type, collected = read head in
      let model_type =
        substituted context head
          (Projection
             {
               base = collection_type;
               trait = { trait = Well_known.path Model; trait_arguments = []; associated = [] };
               name = "Value";
             })
      in
      if model_type = sequence_type element then
        Option.iter
          (extensional context head model_type yielded)
          (model_of context collection_type collected ~element)
  | None -> ()

(* A [for] loop that receives values one at a time from a cursor it pulls.
   [start] is the values received before an iteration, at the head, and
   [receive] is the value an iteration receives, with the [ensures] of the
   cursor's [next] for it assumed. [holds] is the values whose potential
   the loop holds, among those it mutates. *)
let receiving_loop ?(each_iteration = fun ~head:_ ~ends:_ -> ()) ?(most = []) ~(driven : driven)
    context frame ~element_type ~changed ~holds ~start ~receive =
  let clauses = driven.loop_clauses in
  let entry = { frame with yielded = Some (empty_parts context frame element_type) } in
  check_invariants context entry clauses ~when_:"on entry to the loop";
  let loop = enter_loop ~holds context frame ~entry clauses ~changed in
  let costs = loop.loop_costs and head = driven.bindings loop.havocked in
  let before = start head in
  let iterations = sequence_length context element_type before in
  let head =
    loop_head context { head with yielded = Some before } costs ~iterations:(Some iterations)
  in
  assume_invariants context head clauses;
  let ended_mark = List.length context.facts in
  let received = receive head before in
  let through = received.through in
  let inside = received.advance (restrict head received.has_another) in
  let inside = { (spend context inside one_step) with yielded = frame.yielded } in
  let ends, breaks = driven.run_body inside received.element in
  each_iteration ~head ~ends;
  let with_through (exit_frame : frame) = { exit_frame with yielded = Some through } in
  end_iterations context frame driven.loop_at clauses loop ~head ~inside ~ends ~breaks ~with_through;
  let ended = received.advance (restrict head (Logic.not_ received.has_another)) in
  let varies = mentions_fresh_after context loop.fresh_mark in
  let ended_facts = facts_since context ended_mark @ facts_since context loop.facts_mark in
  let exit_ =
    loop_exit context
      { ended with yielded = Some before }
      costs ~iterations:(Some iterations)
      ~most:(most @ Costs.upper_bounds ~varies ~facts:ended_facts iterations)
  in
  let left =
    List.map
      (fun (exit_frame : frame) ->
        loop_exit context (with_through exit_frame) costs
          ~iterations:(Some (Costs.plus iterations (Logic.int 1)))
          ~most:
            (most
            @ Costs.upper_bounds ~varies ~facts:ended_facts
                (sequence_length context element_type through)))
      breaks
  in
  leave_loop context frame
    (List.map
       (fun (exit_frame : frame) -> { exit_frame with yielded = frame.yielded })
       (exit_ :: left))

(* A [for] loop over a value of a type's own [Cursor]: each iteration
   calls its [next] by the [impl]'s contract, and the loop ends at [None].
   Such a cursor promises no end, so in a function that must end, the loop
   needs a [decreases] clause, which each iteration decreases. *)
let own_cursor_loop ~(driven : driven) context frame (cursor_access : passed_place)
    (next : Invocation.callee) ~cursor_type =
  let span = span_of frame.source driven.loop_at in
  let clauses = driven.loop_clauses in
  ignore (cursor_access.read frame);
  let element_type = substituted context frame driven.element_type in
  let trait, evidence =
    match next with
    | Trait_method { trait; evidence = Impl _ as evidence; _ } -> (trait, evidence)
    | _ ->
        unsupported span "a loop over `%s`, whose `Cursor` the prover cannot find"
          (Types.show cursor_type)
  in
  (* The [impl]'s own generic parameters, as the cursor's type instantiates
     them: its [next] is read with them. *)
  let impl, impl_arguments =
    match evidence with
    | Impl { impl; arguments } ->
        ( impl,
          List.map
            (fun (parameter, argument) ->
              (parameter, Types.substitute_argument frame.substitution argument))
            arguments )
    | _ -> bug "a cursor's evidence is not an impl"
  in
  let contract =
    match
      method_contract ?reading_package:(reading_package context) context.database trait "next" Mut
        evidence
    with
    | Some contract -> contract
    | None ->
        unsupported span "a loop over `%s`, whose `next` the prover cannot read"
          (Types.show cursor_type)
  in
  let path = Path.Method { owner = impl; name = "next"; receiver = Mut } in
  let option_type = Types.Named { path = option_path; arguments = [ Types.Type element_type ] } in
  let invocation : Invocation.t = { callee = next; lends = None; uses = Types.no_capabilities } in
  let pulling : Invocation.site =
    { id = driven.loop_at; origin = driven.loop_at; type_ = option_type }
  in
  let measures = measures_of clauses in
  if context.terminates && not (signature_terminates context path) then
    oblige context frame Termination span
      (Printf.sprintf "This loop may not end: `%s`'s `next` has no `time` clause."
         (Types.show cursor_type))
      (Logic.Boolean false);
  if context.terminates && measures = None then
    oblige context frame Termination span
      "This loop may not end: a cursor of a type's own promises no end, so give the loop a \
       `decreases` clause."
      (Logic.Boolean false);
  let measured (at : frame) =
    Option.map
      (List.map (fun measure ->
           snd (specification_value context { at with checking = false } measure)))
      measures
  in
  (* A loop that must end and has one measure runs no more iterations than
     the measure's value on entry, since each iteration makes the measure
     smaller and it never goes below zero. *)
  let entry_measure =
    if context.terminates then match measured frame with Some [ entry ] -> Some entry | _ -> None
    else None
  in
  (* The loop holds the potential of the values its body mutates, and of
     the cursor only where its [next] is amortized. A [next] that is not
     amortized neither spends nor saves the cursor's potential, so counting
     it would leave each iteration's cost depending on a value the loop
     changes. *)
  let is_amortized =
    List.exists
      (fun (part : part) -> List.exists (fun (cost : Mir.cost) -> cost.amortized) part.costs)
      contract.parts
  in
  let holds = if is_amortized then driven.changed_in frame else driven.changed_by_body frame in
  receiving_loop ~driven context frame ~element_type ~changed:(driven.changed_in frame) ~holds
    ~most:(Option.to_list entry_measure)
    ~each_iteration:(fun ~head ~ends ->
      (* The pull is part of the iteration, so the measure is compared from
         the head, before it. *)
      if context.terminates then
        match measured head with
        | Some before ->
            List.iter
              (fun (end_ : frame) ->
                match measured end_ with
                | Some after ->
                    oblige context end_ Termination span "This loop's measure may not decrease."
                      (lexicographically_less before after)
                | None -> ())
              ends
        | None -> ())
    ~start:(fun head ->
      let before = some_parts context head element_type in
      (match (entry_measure, measured head) with
      | Some entry, Some [ now ] ->
          assume context head
            Logic.(
              Operation
                ("<=", [ Costs.plus (sequence_length context element_type before) now; entry ])
              &&& Operation ("<=", [ sequence_length context element_type before; entry ]))
      | _ -> ());
      before)
    ~receive:(fun head before ->
      let cursor = cursor_access.read head in
      let havoc_mut (frame : frame) =
        cursor_access.write frame (arrive context frame "changed" cursor_type)
      in
      let after, pulled =
        contract_call ~lent_final:None context head pulling invocation path contract
          [
            {
              position = 0;
              mode = Types.Mut;
              shape = Other;
              origin = None;
              passed_place = Some cursor_access;
              type_ = cursor_type;
              term = cursor;
            };
          ]
          ~havoc_mut
          ~substitution_of:(fun _ ->
            impl_arguments
            @ [ ({ Types.owner = cursor_trait; name = "Self" }, Types.Type cursor_type) ])
          ~instance:[ type_key cursor_type ]
      in
      let has_another = Logic.Is (constructor_name option_type (Some "Some"), pulled) in
      let element = Logic.Apply (selector_name option_type (Some "Some") "value", [ pulled ]) in
      let inside = restrict after has_another in
      assume_valid context inside element_type element;
      {
        has_another;
        element;
        through = appended context inside element_type before element;
        advance =
          (fun (frame : frame) ->
            let now = cursor_access.read after in
            { (cursor_access.write frame now) with spent = after.spent });
      })

let loop_over ~(driven : driven) context frame =
  let clauses = driven.loop_clauses in
  match driven.looped with
  | Over_range { low; high; inclusive } ->
      (* In a loop over the elements of a collection, [yielded] holds the
         elements. Where the loop reads them, each is the value of the
         collection's [element] at its position. Where the loop mutates
         them, the prover knows them by their number alone. *)
      let element =
        substituted context frame (Option.value driven.lent_element ~default:driven.element_type)
      in
      let over_positions = Option.is_some driven.lent_element in
      let element_at (at : frame) position =
        Option.map
          (fun call -> snd (specification_value context (driven.bind_element at position) call))
          driven.element_call
      in
      let outer_yielded = frame.yielded in
      (* In the loop's clauses, the pattern names the next index: [low] plus
         the iterations so far. *)
      let at_index (exit_frame : frame) next = driven.bind_element exit_frame next in
      let entry = at_index { frame with yielded = Some (empty_parts context frame element) } low in
      check_invariants context entry clauses ~when_:"on entry to the loop";
      let start = enter_loop context frame ~entry clauses ~changed:(driven.changed_in frame) in
      let costs = start.loop_costs and head = driven.bindings start.havocked in
      (* The [n]th iteration, from 0, has the index [low + n]. *)
      let count =
        Costs.normalize
          (if inclusive then Costs.plus (Costs.minus high low) (Logic.int 1)
           else Costs.minus high low)
      in
      let iterations = fresh context head "iterations" Logic.Int in
      assume context head
        Logic.(
          Operation ("<=", [ int 0; iterations ])
          &&& Operation ("<=", [ iterations; Costs.at_least_zero count ]));
      (* [yielded] is the indexes so far, from [low] up. *)
      let before = some_parts context head element in
      assume context head (Logic.equal (sequence_length context element before) iterations);
      (let position = fresh_name context "index" in
       match
         if over_positions then None else sequence_at context element before (Logic.Symbol position)
       with
       | Some yielded_index ->
           assume context head
             (Logic.forall
                ( [ (position, Logic.Int) ],
                  Logic.(
                    Operation ("<=", [ int 0; Symbol position ])
                    &&& Operation ("<", [ Symbol position; iterations ])
                    ==> equal yielded_index (Operation ("+", [ low; Symbol position ]))) ))
       | None -> ());
      Option.iter
        (fun _ ->
          elements_so_far context head ~element ~collection:driven.collection ~count:iterations
            before element_at)
        driven.element_call;
      let index = Costs.plus low iterations in
      let head =
        loop_head context
          (at_index { head with yielded = Some before } index)
          costs ~iterations:(Some iterations)
      in
      assume_invariants context head clauses;
      (* A loop that mutates the elements of a collection keeps their number,
         which is the loop's stop: each iteration's [element] must. *)
      let keeps_count (at : frame) =
        Option.map
          (fun kept -> Logic.equal (snd (specification_value context at kept)) high)
          driven.kept_count
      in
      Option.iter (assume context head) (keeps_count { head with checking = false });
      let inside = restrict head (Logic.Operation ("<", [ iterations; count ])) in
      let through =
        appended context inside element before
          (if over_positions then
             match element_at { inside with checking = false } index with
             | Some lent -> lent
             | None -> arrive context inside "element" element
           else index)
      in
      let inside = { inside with yielded = outer_yielded } in
      let inside = spend context inside one_step in
      let ends, breaks = driven.run_body inside index in
      let with_through (exit_frame : frame) =
        at_index { exit_frame with yielded = Some through } (Costs.plus index (Logic.int 1))
      in
      end_iterations context frame driven.loop_at clauses start ~head ~inside ~ends ~breaks
        ~with_through;
      List.iter
        (fun (end_ : frame) ->
          Option.iter
            (oblige context end_ Invariant
               (span_of frame.source driven.loop_at)
               "An iteration of this loop may change how many elements the collection has. The \
                collection's `element(mut self)` must leave its `count` as it was.")
            (keeps_count end_))
        ends;
      let most = [ Costs.at_least_zero count ] in
      let exit_ =
        loop_exit context
          (restrict head (Logic.Operation (">=", [ iterations; count ])))
          costs ~iterations:(Some iterations) ~most
      in
      let left =
        List.map
          (fun (exit_frame : frame) ->
            loop_exit context (with_through exit_frame) costs
              ~iterations:(Some (Costs.plus iterations (Logic.int 1)))
              ~most)
          breaks
      in
      leave_loop context frame
        (List.map
           (fun (exit_frame : frame) -> { exit_frame with yielded = outer_yielded })
           (exit_ :: left))
  | Over_cursor { cursor; cursor_type; next } ->
      own_cursor_loop ~driven context frame cursor next ~cursor_type

let for_ ~(driven : driven) context frame = loop_over ~driven context frame
