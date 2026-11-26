let is_datatype ty = match ty with Types.Named _ -> Types.find_builtin ty = None | _ -> false

let enter_definition (context : State.context) (start : State.frame) =
  let at_entry = { start with makes_obligations = false } in
  context.definition_entry <-
    Some
      {
        entry_frame = start;
        entry_measures =
          List.map
            (fun measure -> snd (Validity.read_specification context at_entry measure))
            context.measures;
      }

let read_entry (context : State.context) =
  match context.definition_entry with
  | Some entry -> entry
  | None -> Facts.raise_bug "a recursive call is compared before the definition is entered"

let list_structural_parameters context (entry : State.frame) (clauses : State.clauses) =
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
                 Facts.find_local_type context entry (Core_local local) )
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

let compare_with_entry (context : State.context) (clauses : State.clauses) ~is_self_call
    ~callee_entry ~argument_at =
  match (context.measures, clauses.decreases) with
  | [], [] when context.terminates && is_self_call -> (
      match list_structural_parameters context (read_entry context).entry_frame clauses with
      | [] -> Unmeasured
      | parts ->
          let before = List.map (fun (_, ty, value, _) -> Models.rank context ty value) parts in
          let after =
            List.map (fun (_, ty, _, index) -> Models.rank context ty (argument_at index)) parts
          in
          Smaller_part
            {
              compared =
                List.map (fun (parameter, _, _, _) -> Facts.read_parameter_name parameter) parts;
              smaller = Logic.decreases_lexicographically before after;
            })
  | ([], _ | _, []) when context.terminates -> Unmeasured
  | _ :: _, (_ :: _ as callee_measures) ->
      let after =
        List.map
          (fun measure -> snd (Validity.read_specification context callee_entry measure))
          callee_measures
      in
      let before, after = pair_measures (read_entry context).entry_measures after in
      Smaller_measures (Logic.decreases_lexicographically before after)
  | [], _ | _, [] -> Uncompared

let check_recursive_call (context : State.context) (frame : State.frame) location ~path
    (clauses : State.clauses) ~is_self_call ~callee_entry ~argument_at =
  match compare_with_entry context clauses ~is_self_call ~callee_entry ~argument_at with
  | Smaller_part { compared; smaller } ->
      Facts.oblige context frame location
        (Recursion_not_on_part { call = { at = location; callee = Some path }; compared })
        smaller
  | Unmeasured ->
      Facts.oblige context frame location
        (Recursion_may_not_end { call = { at = location; callee = Some path }; is_self_call })
        (Logic.Boolean false)
  | Smaller_measures smaller ->
      Facts.oblige context frame location
        (Measure_may_not_decrease
           {
             call = { at = location; callee = None };
             measures =
               List.map
                 (fun (measure : Mir.formula) -> Facts.quote frame.source measure.origin)
                 context.measures;
           })
        smaller
  | Uncompared -> ()

let find_induction_premise context (clauses : State.clauses) ~is_self_call ~callee_entry
    ~argument_at =
  match compare_with_entry context clauses ~is_self_call ~callee_entry ~argument_at with
  | Smaller_measures smaller | Smaller_part { smaller; _ } -> Some smaller
  | Unmeasured | Uncompared -> None
