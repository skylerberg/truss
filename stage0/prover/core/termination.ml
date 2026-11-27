let is_datatype ty =
  match Types.strip_view ty with Named _ as ty -> Types.find_builtin ty = None | _ -> false

let list_entry_values (entry : State.frame) (parameters : Mir.parameter list) =
  List.concat
    (List.mapi
       (fun position (parameter : Mir.parameter) ->
         let found =
           match parameter.local with
           | Self -> (
               match (entry.old_self, entry.self_type) with
               | Some value, Some type_ -> Some (value, type_)
               | _ -> None)
           | local -> (
               match
                 ( Locals.find_opt (Core_local local) entry.old_locals,
                   Encoding.find_local_type entry (Core_local local) )
               with
               | Some value, Some type_ -> Some (value, type_)
               | _ -> None)
         in
         match found with Some (value, type_) -> [ { State.position; type_; value } ] | None -> [])
       parameters)

let holds_inductive_type (environment : State.environment) ty =
  environment.inductive_heads <> []
  &&
  match
    Mir.Size_change.classify_holding environment.lookups.interface
      ~heads:environment.inductive_heads ty
  with
  | Whole | Within -> true
  | Absent | Consumed | Out_of_reach _ -> false

let find_induction_bound (frame : State.frame) (values : State.ranked_value list) =
  match
    List.filter_map
      (fun (value : State.ranked_value) ->
        if holds_inductive_type frame.environment value.type_ then
          Some
            (Models.rank frame.environment frame.query (Types.erase_views value.type_) value.value)
        else None)
      values
  with
  | [] -> None
  | first :: rest -> Some (List.fold_left Logic.larger first rest)

let read_induction_bound (frame : State.frame) =
  Option.bind frame.definition_entry (fun (entry : State.definition_entry) -> entry.induction_bound)

let is_in_proof_group (environment : State.environment) path =
  List.exists (Path.equal path) (environment.lookups.list_proof_group environment.node)

let makes_inductive_values (environment : State.environment) ~generics ~substitution
    (assumptions : Mir.Call_edges.assumption list) =
  let lookups : Mir.Call_edges.lookups =
    { interface = environment.lookups.interface; mir = environment.lookups.mir }
  in
  let holds = holds_inductive_type environment in
  List.exists
    (fun (generic : Types.generic) ->
      match Types.find_argument generic.generic substitution with
      | Some (Type argument) when holds argument ->
          Option.is_some (Mir.Size_change.find_value_maker lookups generics generic.generic)
      | Some _ | None -> false)
    generics
  || List.exists
       (fun (assumption : Mir.Call_edges.assumption) ->
         holds (fst assumption.assumed)
         &&
         match
           ( assumption.parameter,
             Interface.Definition.find_impl_interface environment.lookups.interface
               assumption.assumer )
         with
         | Some parameter, Some impl ->
             Option.is_some (Mir.Size_change.find_value_maker lookups impl.impl_generics parameter)
         | None, _ | _, None -> true)
       assumptions

let rank_against_bound (frame : State.frame) ty value ~is_strict ~bound =
  let rank = Models.rank frame.environment frame.query (Types.erase_views ty) value in
  if is_strict then Logic.less rank bound else Logic.less_equal rank bound

let find_law_induction_premise (frame : State.frame) (clauses : State.clauses) ~substitution ~inputs
    =
  let environment = frame.environment in
  if environment.inductive_heads = [] then Some (Logic.Boolean true)
  else
    let interface = environment.lookups.interface in
    let generics =
      match Interface.Impls.read_signature interface clauses.callee.definition with
      | Some signature -> signature.generics
      | None -> []
    in
    let impls, assumptions =
      Mir.Call_edges.list_impls_of_bounds interface
        (Interface.Impls.list_required_bounds generics substitution)
    in
    let assumes_group_laws = List.exists (Cycles.is_in_proof_cycle environment) impls in
    if not (assumes_group_laws || is_in_proof_group environment clauses.callee.definition) then
      Some (Logic.Boolean true)
    else if
      assumes_group_laws && makes_inductive_values environment ~generics ~substitution assumptions
    then None
    else
      Option.bind (read_induction_bound frame) (fun bound ->
          let compared =
            List.map2
              (fun (parameter : Mir.parameter) input ->
                let ty = Types.substitute_erased substitution parameter.type_ in
                match
                  ( Mir.Size_change.classify_holding interface ~heads:environment.inductive_heads ty,
                    assumes_group_laws )
                with
                | Whole, true -> Some (rank_against_bound frame ty input ~is_strict:true ~bound)
                | (Whole | Within), _ ->
                    Some (rank_against_bound frame ty input ~is_strict:false ~bound)
                | Out_of_reach _, true -> None
                | (Absent | Consumed), _ | Out_of_reach _, false -> Some (Logic.Boolean true))
              clauses.parameters inputs
          in
          if List.mem None compared then None
          else Some (Logic.conjunction (List.filter_map Fun.id compared)))

let enter_definition (start : State.frame) ~parameters =
  let at_entry = { start with makes_obligations = false } in
  let values = list_entry_values start parameters in
  {
    start with
    definition_entry =
      Some
        {
          entry_measures =
            List.map
              (fun measure -> snd (Validity.read_specification at_entry measure))
              start.environment.measures;
          entry_ranks =
            List.filter (fun (value : State.ranked_value) -> is_datatype value.type_) values;
          induction_bound = find_induction_bound start values;
        };
  }

let read_entry (frame : State.frame) =
  match frame.definition_entry with
  | Some entry -> entry
  | None -> Facts.raise_bug "a recursive call is compared before the definition is entered"

let reached_calls : (Core.origin * Path.t) list ref Private_state.key =
  Private_state.make_key (fun () -> ref [])

let makes_size_change_obligations (frame : State.frame) =
  frame.terminates && frame.makes_obligations && frame.environment.measures = []

let oblige_call_without_decrease (frame : State.frame) location (call : Mir.Size_change.call) =
  Obligations.oblige frame location
    (Recursion_without_smaller_part
       {
         call =
           {
             at = location;
             callee =
               (match call.passage with
               | Direct_call | Function_value _ -> Some call.callee
               | Dictionary _ -> None);
           };
         passage = call.passage;
         is_self_call = Path.equal call.callee frame.environment.node;
       })
    (Logic.Boolean false)

let check_size_change (frame : State.frame) location ~origin ~callee =
  if makes_size_change_obligations frame then
    match
      List.find_opt
        (fun (call : Mir.Size_change.call) -> call.origin = origin && Path.equal call.callee callee)
        (Lazy.force frame.environment.termination).calls_without_decrease
    with
    | Some call ->
        let reached = Private_state.read frame.environment.memos reached_calls in
        reached := (origin, callee) :: !reached;
        oblige_call_without_decrease frame location call
    | None -> ()

let is_rejected_at_its_call (environment : State.environment) (call : Mir.Size_change.call) =
  match environment.lookups.mir.find_form_origin call.callee with
  | Some ((Derived _ | Inherited _), _) -> true
  | Some (Written _, _) | None -> false

let reject_unreached_calls_without_decrease (frame : State.frame) =
  let environment = frame.environment in
  if makes_size_change_obligations frame then begin
    let reached = !(Private_state.read environment.memos reached_calls) in
    List.iter
      (fun (call : Mir.Size_change.call) ->
        if
          (not (List.mem (call.origin, call.callee) reached))
          && not (is_rejected_at_its_call environment call)
        then oblige_call_without_decrease frame (Facts.locate frame call.origin) call)
      (Lazy.force environment.termination).calls_without_decrease
  end

let rec pair_measures before after =
  match (before, after) with
  | entry :: before, called :: after ->
      let rest_before, rest_after = pair_measures before after in
      (entry :: rest_before, called :: rest_after)
  | _ -> ([], [])

let compare_measures (frame : State.frame) ~(callee_entry : State.frame) callee_measures =
  let after =
    List.map (fun measure -> snd (Validity.read_specification callee_entry measure)) callee_measures
  in
  let before, after = pair_measures (read_entry frame).entry_measures after in
  Logic.decreases_lexicographically before after

let check_recursive_call (frame : State.frame) location ~origin ~path (clauses : State.clauses)
    ~is_self_call ~(callee_entry : State.frame) =
  match (frame.environment.measures, clauses.decreases) with
  | [], [] -> check_size_change frame location ~origin ~callee:path
  | _ :: _, (_ :: _ as callee_measures) ->
      Obligations.oblige frame location
        (Measure_may_not_decrease
           {
             call = { at = location; callee = None };
             measures =
               List.map
                 (fun (measure : Mir.formula) -> Facts.quote frame.source measure.origin)
                 frame.environment.measures;
           })
        (compare_measures frame ~callee_entry callee_measures)
  | ([], _ :: _ | _ :: _, []) when callee_entry.terminates ->
      Obligations.oblige frame location
        (Recursion_may_not_end { call = { at = location; callee = Some path }; is_self_call })
        (Logic.Boolean false)
  | [], _ :: _ | _ :: _, [] -> ()

let compute_rank (frame : State.frame) (ranks : State.ranked_value list)
    (component : Mir.Size_change.component) =
  match component with
  | Level level -> Some (Logic.int level)
  | Largest_rank positions -> (
      let found =
        List.map
          (fun position ->
            List.find_opt (fun (rank : State.ranked_value) -> rank.position = position) ranks)
          positions
      in
      if List.exists Option.is_none found then None
      else
        match
          List.map
            (fun (rank : State.ranked_value) ->
              Models.rank frame.environment frame.query (Types.erase_views rank.type_) rank.value)
            (List.filter_map Fun.id found)
        with
        | [] -> Some (Logic.int 0)
        | first :: rest -> Some (Logic.add (Logic.int 1) (List.fold_left Logic.larger first rest)))

let rec compare_ranks before after =
  match (before, after) with
  | Logic.Integer earlier :: before, Logic.Integer later :: after ->
      if Z.lt later earlier then Some (Logic.Boolean true)
      else if Z.gt later earlier then None
      else compare_ranks before after
  | [], [] -> None
  | before, after -> Some (Logic.decreases_lexicographically before after)

let find_ranked_premise (frame : State.frame) (clauses : State.clauses) ~callee
    ~(callee_entry : State.frame) ~argument_at =
  let compute path ranks ranking =
    Option.bind
      (Option.map snd (List.find_opt (fun (member, _) -> Path.equal member path) ranking))
      (fun components ->
        let computed = List.map (compute_rank frame ranks) components in
        if List.exists Option.is_none computed then None else Some (List.filter_map Fun.id computed))
  in
  let callee_ranks =
    List.concat
      (List.mapi
         (fun position (parameter : Mir.parameter) ->
           let type_ = Encoding.substitute_type callee_entry parameter.type_ in
           if is_datatype type_ then [ { State.position; type_; value = argument_at position } ]
           else [])
         clauses.parameters)
  in
  Option.bind (Lazy.force frame.environment.termination).ranking (fun ranking ->
      match
        ( compute frame.environment.node (read_entry frame).entry_ranks ranking,
          compute callee callee_ranks ranking )
      with
      | Some before, Some after -> compare_ranks before after
      | _ -> None)

let find_induction_premise (frame : State.frame) (clauses : State.clauses) ~callee
    ~(callee_entry : State.frame) ~argument_at =
  match (frame.environment.measures, clauses.decreases) with
  | [], [] when callee_entry.terminates ->
      find_ranked_premise frame clauses ~callee ~callee_entry ~argument_at
  | _ :: _, (_ :: _ as callee_measures) ->
      Some (compare_measures frame ~callee_entry callee_measures)
  | [], _ | _, [] -> None

let find_recursive_callee (frame : State.frame) location group_member =
  let reject target impl =
    Obligations.oblige frame location
      (Recursion_through_impl { call = { at = location; callee = Some target }; impl })
      (Logic.Boolean false);
    None
  in
  match group_member with
  | Some target when frame.makes_obligations -> (
      match frame.environment.lookups.mir.find_form_origin target with
      | Some (Derived _, _) when frame.terminates -> reject target Derives
      | Some (Inherited _, _) when frame.terminates -> reject target Inherits
      | Some ((Written _ | Derived _ | Inherited _), _) | None -> Some target)
  | Some _ | None -> None

let reject_uncompared_recursion (frame : State.frame) location recursive_callee =
  if frame.terminates then
    Option.iter
      (fun callee ->
        Obligations.oblige frame location
          (Uncompared_recursion { call = { at = location; callee = Some callee } })
          (Logic.Boolean false))
      recursive_callee

let reject_recursion_through_higher_order_argument (frame : State.frame) location
    (statement : Mir.statement) =
  let environment = frame.environment in
  let reject recursion =
    Obligations.oblige frame location (Recursion_through_argument recursion) (Logic.Boolean false)
  in
  let reject_passing (argument : Mir.Call_edges.higher_order_argument) code =
    let recursive =
      List.filter
        (fun target ->
          Cycles.is_in_recursion_group environment target
          &&
          match argument with
          | Handler -> true
          | Dictionary | Function_value _ -> environment.measures <> [])
        code
    in
    (match argument with
    | Dictionary | Function_value _ ->
        List.iter
          (fun callee ->
            check_size_change frame location ~origin:(Mir.Call_edges.locate_call statement) ~callee)
          code
    | Handler -> ());
    (match argument with
    | Function_value path when List.exists (Path.equal path) recursive ->
        reject (Function_value path)
    | Function_value _ | Dictionary | Handler -> ());
    List.iter
      (fun owner ->
        reject
          (match argument with
          | Dictionary -> Dictionary_through_call { call = { at = location; callee = None }; owner }
          | Function_value path -> Dictionary_through_name { path; owner }
          | Handler -> Handler owner))
      (List.sort_uniq Path.compare
         (List.filter_map
            (fun (node : Path.t) -> match node with Method { owner; _ } -> Some owner | _ -> None)
            recursive))
  in
  if frame.terminates && frame.makes_obligations then
    List.iter
      (fun (edge : Mir.Call_edges.edge) ->
        match edge with Calls _ -> () | Passes { argument; code } -> reject_passing argument code)
      (Mir.Call_edges.list_statement_edges environment.lookups.interface frame.substitution
         statement)

type loop_measure = { read : State.frame -> Logic.term list; at_head : Logic.term list }

let find_written_measures (clauses : Mir.loop_clause list) =
  List.find_map (function Mir.Decreases measures -> Some measures | _ -> None) clauses

let read_measures (at : State.frame) measures =
  List.map
    (fun measure -> snd (Validity.read_specification { at with makes_obligations = false } measure))
    measures

let make_comparison_measure (head : State.frame) measure_operands =
  match measure_operands with
  | Some (comparison, read_operands) when head.terminates ->
      Some
        (fun (at : State.frame) ->
          let left, right =
            read_operands { (Counters.stop_counting at) with makes_obligations = false }
          in
          let distance from into = Logic.subtract into from in
          let through distance = Logic.add distance (Logic.int 1) in
          match (comparison : Language.Comparison.t) with
          | Less -> [ distance left right ]
          | Less_equal -> [ through (distance left right) ]
          | Greater -> [ distance right left ]
          | Greater_equal -> [ through (distance right left) ]
          | Equal | Not_equal -> Facts.raise_bug "an equality gives a loop its measure")
  | Some _ | None -> None

let read_loop_measure ?implicit (clauses : Mir.loop_clause list) ~(head : State.frame) =
  let read =
    match find_written_measures clauses with
    | Some written -> Some (fun at -> read_measures at written)
    | None -> implicit
  in
  Option.map (fun read -> { read; at_head = read head }) read

let require_measure (frame : State.frame) ~loop ~is_measured =
  if frame.terminates && not is_measured then
    Facts.raise_bug "%s has no measure in a body that terminates" loop

let check_loop_measure (frame : State.frame) location measure =
  Option.iter
    (fun measure ->
      Obligations.oblige frame location Loop_measure_may_not_decrease
        (Logic.decreases_lexicographically measure.at_head (measure.read frame)))
    measure
