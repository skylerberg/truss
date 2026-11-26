type decision = Always | In_run of Types.condition | Elsewhere

let implies (lookups : Lookups.t) ~current premise conclusion =
  Interface.Impls.implies_condition lookups.interface
    ~list_bounds:(Encoding.list_definition_bounds lookups ~current ~condition:[])
    premise conclusion

let may_panic_for_every_value lookups ~current ~condition (uses : Types.capability_set) =
  Types.has_capability (Built_in Panic) uses
  ||
  match Types.find_unless (Built_in Panic) uses with
  | Some unless -> not (implies lookups ~current condition unless)
  | None -> false

let may_panic lookups ~current ~condition (uses : Types.capability_set) =
  may_panic_for_every_value lookups ~current ~condition uses
  || Types.has_capability (Capability_unless_values (Built_in Panic)) uses

let decide (context : State.context) ~substitution (holds_when : Types.condition) =
  match holds_when with
  | [] -> Always
  | _ -> (
      match
        Interface.Impls.decide_condition context.environment.lookups.interface
          ~list_bounds:
            (Encoding.list_definition_bounds context.environment.lookups
               ~current:context.environment.current ~condition:[])
          (Types.substitute_condition substitution holds_when)
      with
      | None -> Elsewhere
      | Some [] -> Always
      | Some undecided ->
          if
            implies context.environment.lookups ~current:context.environment.current
              context.environment.condition undecided
          then In_run undecided
          else begin
            if
              context.environment.condition = []
              && not (List.mem undecided context.skipped_conditions)
            then context.skipped_conditions <- undecided :: context.skipped_conditions;
            Elsewhere
          end)

let holds_here (context : State.context) ?(substitution = Types.no_substitution) holds_when =
  match decide context ~substitution holds_when with
  | Always | In_run _ -> true
  | Elsewhere -> false

let find_obligation_condition = function
  | Always -> Some []
  | In_run undecided -> Some undecided
  | Elsewhere -> None

let keep_holding (context : State.context) ~substitution (clauses : State.clauses) =
  let decide holds_when = find_obligation_condition (decide context ~substitution holds_when) in
  let keep (clause : Mir.formula) =
    Option.map (fun holds_when -> { clause with holds_when }) (decide clause.holds_when)
  in
  {
    clauses with
    requires =
      List.filter_map
        (fun (requirement : Mir.requirement) ->
          Option.map (fun clause -> { requirement with clause }) (keep requirement.clause))
        clauses.requires;
    ensures = List.filter_map keep clauses.ensures;
    decreases = List.filter_map keep clauses.decreases;
    costs =
      List.filter_map
        (fun (cost : Mir.cost) ->
          Option.map (fun holds_when -> { cost with holds_when }) (decide cost.holds_when))
        clauses.costs;
  }
