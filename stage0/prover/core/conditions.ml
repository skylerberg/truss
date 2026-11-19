type decision = Always | In_run of Types.condition | Elsewhere

let implies (lookups : Lookups.t) ~current premise conclusion =
  Interface.Impls.implies_condition lookups.interface
    ~list_bounds:(Facts.list_definition_bounds lookups ~current ~condition:[])
    premise conclusion

let may_panic lookups ~current ~condition (uses : Types.capability_set) =
  Types.has_capability (Built_in Panic) uses
  ||
  match Types.find_unless (Built_in Panic) uses with
  | Some unless -> not (implies lookups ~current condition unless)
  | None -> false

let decide (context : State.context) ~substitution (holds_when : Types.condition) =
  match holds_when with
  | [] -> Always
  | _ -> (
      match
        Interface.Impls.decide_condition context.lookups.interface
          ~list_bounds:
            (Facts.list_definition_bounds context.lookups ~current:context.current ~condition:[])
          (Types.substitute_condition substitution holds_when)
      with
      | None -> Elsewhere
      | Some [] -> Always
      | Some undecided ->
          if implies context.lookups ~current:context.current context.condition undecided then
            In_run undecided
          else begin
            if context.condition = [] && not (List.mem undecided context.skipped_conditions) then
              context.skipped_conditions <- undecided :: context.skipped_conditions;
            Elsewhere
          end)

let holds_here context ?(substitution = Types.no_substitution) holds_when =
  match decide context ~substitution holds_when with
  | Always | In_run _ -> true
  | Elsewhere -> false

let find_obligation_condition = function
  | Always -> Some []
  | In_run undecided -> Some undecided
  | Elsewhere -> None

let with_obligation_condition (context : State.context) condition run =
  let outer = context.obligation_condition in
  context.obligation_condition <- condition;
  Fun.protect ~finally:(fun () -> context.obligation_condition <- outer) run
