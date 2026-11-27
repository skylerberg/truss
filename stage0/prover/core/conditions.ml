type decision = Always | In_run of Types.condition | Elsewhere

let implies (lookups : Lookups.t) ~current premise conclusion =
  Interface.Impls.implies_condition lookups.interface
    ~list_bounds:(Encoding.list_definition_bounds lookups ~current ~condition:[])
    premise conclusion

let may_use_for_every_value lookups ~current ~condition capability (uses : Types.capability_set) =
  Types.has_capability capability uses
  ||
  match Types.find_unless capability uses with
  | Some unless -> not (implies lookups ~current condition unless)
  | None -> false

let decide_available lookups ~current ~condition (uses : Types.capability_set) =
  Types.make_capability_set
    (List.filter
       (function
         | Types.Capability_unless { unless; _ } -> not (implies lookups ~current condition unless)
         | _ -> true)
       (Types.list_capabilities uses))

type state = { mutable undecided : Types.condition list }

let state = Private_state.make_key (fun () -> { undecided = [] })
let list_undecided query = (Query.read_state query state).undecided

let decide (environment : State.environment) (query : Query.t) ~substitution
    (holds_when : Types.condition) =
  match holds_when with
  | [] -> Always
  | _ -> (
      match
        Interface.Impls.decide_condition environment.lookups.interface
          ~list_bounds:
            (Encoding.list_definition_bounds environment.lookups ~current:environment.current
               ~condition:[])
          (Types.substitute_condition substitution holds_when)
      with
      | None -> Elsewhere
      | Some [] -> Always
      | Some undecided ->
          if
            implies environment.lookups ~current:environment.current environment.condition undecided
          then In_run undecided
          else begin
            let state = Query.read_state query state in
            if environment.condition = [] && not (List.mem undecided state.undecided) then
              state.undecided <- undecided :: state.undecided;
            Elsewhere
          end)

let holds_here (environment : State.environment) (query : Query.t)
    ?(substitution = Types.no_substitution) holds_when =
  match decide environment query ~substitution holds_when with
  | Always | In_run _ -> true
  | Elsewhere -> false

let find_obligation_condition = function
  | Always -> Some []
  | In_run undecided -> Some undecided
  | Elsewhere -> None

let keep_holding (environment : State.environment) (query : Query.t) ~substitution
    (clauses : State.clauses) =
  let decide holds_when =
    find_obligation_condition (decide environment query ~substitution holds_when)
  in
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
