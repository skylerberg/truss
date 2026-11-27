let is_datatype ty = match ty with Types.Named _ -> Types.find_builtin ty = None | _ -> false

let enter_definition (start : State.frame) =
  let at_entry = { start with makes_obligations = false } in
  {
    start with
    definition_entry =
      Some
        {
          entry_frame = start;
          entry_measures =
            List.map
              (fun measure -> snd (Validity.read_specification at_entry measure))
              start.environment.measures;
        };
  }

let read_entry (frame : State.frame) =
  match frame.definition_entry with
  | Some entry -> entry
  | None -> Facts.raise_bug "a recursive call is compared before the definition is entered"

let list_structural_parameters (entry : State.frame) (clauses : State.clauses) =
  List.concat
    (List.mapi
       (fun index (parameter : Mir.parameter) ->
         match parameter.local with
         | Self -> (
             match (entry.old_self, entry.self_type) with
             | Some value, Some ty when is_datatype ty -> [ (parameter, ty, value, index) ]
             | _ -> [])
         | local -> (
             match
               ( Locals.find_opt (Core_local local) entry.old_locals,
                 Encoding.find_local_type entry (Core_local local) )
             with
             | Some value, Some ty when is_datatype ty -> [ (parameter, ty, value, index) ]
             | _ -> []))
       clauses.parameters)

type decrease =
  | Smaller_measures of Logic.term
  | Smaller_part of { compared : string list; smaller : Logic.term }
  | Unmeasured
  | Uncompared

let rec pair_measures before after =
  match (before, after) with
  | entry :: before, called :: after ->
      let rest_before, rest_after = pair_measures before after in
      (entry :: rest_before, called :: rest_after)
  | _ -> ([], [])

let compare_with_entry (frame : State.frame) (clauses : State.clauses) ~is_self_call
    ~(callee_entry : State.frame) ~argument_at =
  match (frame.environment.measures, clauses.decreases) with
  | [], [] when callee_entry.terminates && is_self_call -> (
      let entry = (read_entry frame).entry_frame in
      let is_passed_at_its_type ((parameter : Mir.parameter), ty, _, _) =
        Types.equal
          (Encoding.substitute_type entry ty)
          (Encoding.substitute_type callee_entry parameter.type_)
      in
      match List.filter is_passed_at_its_type (list_structural_parameters entry clauses) with
      | [] -> Unmeasured
      | parts ->
          let before =
            List.map
              (fun (_, ty, value, _) -> Models.rank frame.environment frame.query ty value)
              parts
          in
          let after =
            List.map
              (fun (_, ty, _, index) ->
                Models.rank frame.environment frame.query ty (argument_at index))
              parts
          in
          Smaller_part
            {
              compared =
                List.map (fun (parameter, _, _, _) -> Facts.read_parameter_name parameter) parts;
              smaller = Logic.decreases_lexicographically before after;
            })
  | ([], _ | _, []) when callee_entry.terminates -> Unmeasured
  | _ :: _, (_ :: _ as callee_measures) ->
      let after =
        List.map
          (fun measure -> snd (Validity.read_specification callee_entry measure))
          callee_measures
      in
      let before, after = pair_measures (read_entry frame).entry_measures after in
      Smaller_measures (Logic.decreases_lexicographically before after)
  | [], _ | _, [] -> Uncompared

let check_recursive_call (frame : State.frame) location ~path (clauses : State.clauses)
    ~is_self_call ~callee_entry ~argument_at =
  match compare_with_entry frame clauses ~is_self_call ~callee_entry ~argument_at with
  | Smaller_part { compared; smaller } ->
      Obligations.oblige frame location
        (Recursion_not_on_part { call = { at = location; callee = Some path }; compared })
        smaller
  | Unmeasured ->
      Obligations.oblige frame location
        (Recursion_may_not_end { call = { at = location; callee = Some path }; is_self_call })
        (Logic.Boolean false)
  | Smaller_measures smaller ->
      Obligations.oblige frame location
        (Measure_may_not_decrease
           {
             call = { at = location; callee = None };
             measures =
               List.map
                 (fun (measure : Mir.formula) -> Facts.quote frame.source measure.origin)
                 frame.environment.measures;
           })
        smaller
  | Uncompared -> ()

let find_induction_premise (frame : State.frame) (clauses : State.clauses) ~is_self_call
    ~callee_entry ~argument_at =
  match compare_with_entry frame clauses ~is_self_call ~callee_entry ~argument_at with
  | Smaller_measures smaller | Smaller_part { smaller; _ } -> Some smaller
  | Unmeasured | Uncompared -> None

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

let reject_recursion_through_supplied_code (frame : State.frame) location
    (statement : Mir.statement) =
  let reject supplied =
    Obligations.oblige frame location (Recursion_through_supply supplied) (Logic.Boolean false)
  in
  let reject_supply (supplier : Mir.Call_edges.supplier) code =
    let recursive = List.filter (Cycles.is_in_recursion_group frame.environment) code in
    (match supplier with
    | Named_function path when List.exists (Path.equal path) recursive ->
        reject (Named_function path)
    | Named_function _ | Call | Provide -> ());
    List.iter
      (fun owner ->
        reject
          (match supplier with
          | Call -> Bound_through_call { call = { at = location; callee = None }; owner }
          | Named_function path -> Bound_through_name { path; owner }
          | Provide -> Provided owner))
      (List.sort_uniq Path.compare
         (List.filter_map
            (fun (node : Path.t) -> match node with Method { owner; _ } -> Some owner | _ -> None)
            recursive))
  in
  if frame.terminates && frame.makes_obligations then
    List.iter
      (fun (edge : Mir.Call_edges.edge) ->
        match edge with Calls _ -> () | Supplies { supplier; code } -> reject_supply supplier code)
      (Mir.Call_edges.list_statement_edges frame.environment.lookups.interface frame.substitution
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
