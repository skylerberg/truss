let zero = Logic.Integer Z.zero

type target = Through of Logic.term | Capability of Path.t | Capability_method of Path.t * string
type resource = Metric of Language.Metric.t | Calls of target
type counting = Units | At_most | Exactly
type counter = { resource : resource; counting : counting; amortized : bool }
type counted = No_potential | Potential_change | Potential_growth
type charge = { amount : Logic.term; counted : counted }

let make_counted_charge (counter : counter) amount =
  { amount; counted = (if counter.amortized then Potential_change else No_potential) }

let least_amount = function
  | Metric Time -> Logic.Integer Z.one
  | Metric (Allocations | Allocated_bytes) | Calls _ -> zero

let make_operand_counter (metric : Language.Metric.t) =
  {
    resource = Metric metric;
    counting = (match metric with Time -> Units | Allocations | Allocated_bytes -> At_most);
    amortized = false;
  }

let classify_counting (cost : Mir.cost) : counting =
  match cost.bound with Order_of _ -> Units | At_most _ -> At_most | Exactly _ -> Exactly

let find_resource (cost : Mir.cost) ~locals : resource option =
  match cost.resource with
  | Metric metric -> Some (Metric metric)
  | Calls (Function_parameter local) ->
      Option.map (fun term -> Calls (Through term)) (Locals.find_opt (Core_local local) locals)
  | Calls (Capability path) -> Some (Calls (Capability path))
  | Calls (Capability_method (path, name)) -> Some (Calls (Capability_method (path, name)))

let covers ~(clause : target) ~(counter : target) =
  match (clause, counter) with
  | Capability path, Capability_method (owner, _) -> Path.equal path owner
  | Through left, Through right -> left = right
  | Capability left, Capability right -> Path.equal left right
  | Capability_method (left, left_method), Capability_method (right, right_method) ->
      Path.equal left right && left_method = right_method
  | _ -> false

let is_same_resource (cost : Mir.cost) ~locals (counter : counter) =
  match (cost.resource, counter.resource) with
  | Metric bounded, Metric counted -> bounded = counted
  | Calls _, Calls counted -> (
      match find_resource cost ~locals with
      | Some (Calls target) -> covers ~clause:target ~counter:counted
      | _ -> false)
  | _ -> false

let make_conditional_amount condition amount =
  match condition with
  | Logic.Boolean true -> amount
  | Logic.Boolean false -> zero
  | condition -> Logic.ite condition amount zero

let list_stated_bounds (costs : Types.cost list) (metric : Language.Metric.t) ~amortized =
  List.filter_map
    (fun (cost : Types.cost) ->
      if cost.resource = Types.Metric metric && cost.amortized = amortized then Some cost.bound
      else None)
    costs

let states_no_allocation costs =
  List.exists
    (function
      | Types.No_more_than limit | Exactly_cost limit -> Z.equal limit Z.zero | Order_of -> false)
    (list_stated_bounds costs Allocations ~amortized:false)

let find_stated_operand costs metric =
  let counting = (make_operand_counter metric).counting in
  List.find_map
    (fun (bound : Types.cost_bound) ->
      match (counting, bound) with
      | Units, Order_of -> Some (Logic.Integer Z.one)
      | At_most, (No_more_than limit | Exactly_cost limit) -> Some (Logic.Integer limit)
      | (Units | At_most | Exactly), (Order_of | No_more_than _ | Exactly_cost _) -> None)
    (list_stated_bounds costs metric ~amortized:false)

let bound bound_function =
  Logic.add
    (Logic.multiply (Logic.Integer (Z.shift_left Z.one 17)) bound_function)
    (Logic.Integer (Z.shift_left Z.one 16))

let units amount = Logic.add (Logic.at_least_zero amount) (Logic.int 1)

let reduce_constants amount =
  let sums, constant = Logic.linearize amount in
  let factor =
    List.fold_left (fun factor (_, coefficient) -> Z.gcd factor coefficient) Z.zero sums
  in
  if Z.leq factor Z.one && Z.leq (Z.abs constant) Z.one then amount
  else
    Logic.combine_linear
      ( List.map (fun (atom, coefficient) -> (atom, Z.divexact coefficient factor)) sums,
        Z.of_int (Z.sign constant) )

let rec since ~start total =
  match total with
  | Logic.Operation (Ite, [ condition; left; right ]) ->
      Logic.ite condition (since ~start left) (since ~start right)
  | _ -> Logic.normalize_linear (Logic.subtract total start)

let credit_symbol = Logic.Symbol.Variable { label = "cost.credit"; numbers = [] }

type polarity = Grows | Shrinks | Both

let flip = function Grows -> Shrinks | Shrinks -> Grows | Both -> Both

let rec rewrite_choices_as_most = function
  | Logic.Operation (Ite, [ _; left; right ]) ->
      Logic.Apply
        (Logic.Symbol.Cost_most, [ rewrite_choices_as_most left; rewrite_choices_as_most right ])
  | Logic.Apply (name, arguments) -> Logic.Apply (name, List.map rewrite_choices_as_most arguments)
  | Logic.Operation (operator, arguments) ->
      Logic.Operation (operator, List.map rewrite_choices_as_most arguments)
  | Logic.Is (constructor, argument) -> Logic.Is (constructor, rewrite_choices_as_most argument)
  | other -> other

let rec rewrite_most_as_choices = function
  | Logic.Apply (Logic.Symbol.Cost_most, [ left; right ]) ->
      Logic.larger (rewrite_most_as_choices left) (rewrite_most_as_choices right)
  | Logic.Apply (name, arguments) -> Logic.Apply (name, List.map rewrite_most_as_choices arguments)
  | Logic.Operation (operator, arguments) ->
      Logic.Operation (operator, List.map rewrite_most_as_choices arguments)
  | Logic.Is (constructor, argument) -> Logic.Is (constructor, rewrite_most_as_choices argument)
  | other -> other

let list_varying_parts varies term =
  let parts = ref [] in
  let add part polarity =
    match List.assoc_opt part !parts with
    | None -> parts := !parts @ [ (part, polarity) ]
    | Some existing when existing = polarity -> ()
    | Some _ ->
        parts :=
          List.map
            (fun (existing_part, existing_polarity) ->
              if existing_part = part then (existing_part, Both)
              else (existing_part, existing_polarity))
            !parts
  in
  let rec walk polarity term =
    if varies term then
      match term with
      | Logic.Operation (Add, arguments) -> List.iter (walk polarity) arguments
      | Logic.Operation (Negate, [ inner ]) -> walk (flip polarity) inner
      | Logic.Operation (Subtract, first :: rest) ->
          walk polarity first;
          List.iter (walk (flip polarity)) rest
      | Logic.Operation (Multiply, [ Logic.Integer factor; inner ])
      | Logic.Operation (Multiply, [ inner; Logic.Integer factor ]) ->
          walk (if Z.sign factor >= 0 then polarity else flip polarity) inner
      | Logic.Operation (Multiply, arguments)
      | Logic.Apply
          ( (Logic.Symbol.Cost_most | Logic.Symbol.Integer_log | Logic.Symbol.Integer_power),
            arguments ) ->
          List.iter (walk polarity) arguments
      | Logic.Apply (symbol, arguments) when symbol = credit_symbol ->
          List.iter (walk polarity) arguments
      | _ -> add term polarity
  in
  walk Grows term;
  !parts

let grows_with ~varies term =
  List.exists
    (fun (_, polarity) -> polarity <> Shrinks)
    (list_varying_parts varies (rewrite_choices_as_most term))

let rec list_comparisons fact =
  match fact with
  | Logic.Operation (And, parts) -> List.concat_map list_comparisons parts
  | Logic.Operation (Implies, [ _; conclusion ]) -> list_comparisons conclusion
  | Logic.Operation ((Less_equal | Less), [ left; right ]) -> [ (left, right) ]
  | Logic.Operation ((Greater_equal | Greater), [ left; right ]) -> [ (right, left) ]
  | Logic.Operation (Equal, [ left; right ]) -> [ (left, right); (right, left) ]
  | _ -> []

let is_type_end = function
  | Logic.Integer value ->
      List.exists
        (fun bits ->
          let power = Z.shift_left Z.one bits in
          Z.equal value (Z.pred power)
          || Z.equal value (Z.pred (Z.shift_right power 1))
          || Z.equal value (Z.neg (Z.shift_right power 1)))
        [ 8; 16; 32; 64 ]
      || List.exists
           (fun (_, high) -> Z.equal value high)
           (Types.list_value_ranges (Types.make_builtin Character))
  | _ -> false

let find_part_bound ~varies ~facts part polarity =
  let candidates =
    List.filter_map
      (fun (smaller, larger) ->
        match polarity with
        | Grows when smaller = part && larger <> part -> Some larger
        | Shrinks when larger = part && smaller <> part -> Some smaller
        | _ -> None)
      (List.concat_map list_comparisons facts)
  in
  let rank candidate = if varies candidate then 2 else if is_type_end candidate then 1 else 0 in
  match List.stable_sort (fun left right -> compare (rank left) (rank right)) candidates with
  | best :: _ -> Some best
  | [] -> None

let find_cost_bound ~varies ~facts cost =
  let rec find_bound_within_depth depth cost =
    if not (varies cost) then Some cost
    else if depth = 0 then None
    else
      let parts = list_varying_parts varies cost in
      let replaced =
        List.find_map
          (fun (part, polarity) ->
            if polarity = Both then None
            else
              match find_part_bound ~varies ~facts part polarity with
              | Some bound ->
                  Some
                    (Logic.normalize_linear
                       (Logic.replace ~from:part ~into:(rewrite_choices_as_most bound) cost))
              | None -> None)
          parts
      in
      match replaced with
      | Some next when next <> cost -> find_bound_within_depth (depth - 1) next
      | _ -> None
  in
  Option.map rewrite_most_as_choices
    (find_bound_within_depth 12 (Logic.normalize_linear (rewrite_choices_as_most cost)))

let list_unbounded_parts ~varies ~facts cost =
  let rec list_within_depth depth cost =
    List.concat_map
      (fun (part, polarity) ->
        let bound =
          if depth = 0 || polarity = Both then None
          else
            Option.map
              (fun bound -> if polarity = Shrinks then Logic.negate bound else bound)
              (find_part_bound ~varies ~facts part polarity)
        in
        match bound with
        | None -> [ part ]
        | Some bound -> (
            match
              list_within_depth (depth - 1) (Logic.normalize_linear (rewrite_choices_as_most bound))
            with
            | [] -> []
            | parts -> part :: parts))
      (list_varying_parts varies cost)
  in
  List.fold_left
    (fun parts part -> if List.mem part parts then parts else parts @ [ part ])
    []
    (list_within_depth 12 (Logic.normalize_linear (rewrite_choices_as_most cost)))

let mentions_part ~part amount =
  let rec holds term = term = part || List.exists holds (Logic.list_arguments term) in
  holds (Logic.normalize_linear (rewrite_choices_as_most amount))

let list_upper_bounds ~varies ~facts term =
  List.filter_map
    (fun (smaller, larger) -> if smaller = term && not (varies larger) then Some larger else None)
    (List.concat_map list_comparisons facts)

let rec is_potential = function
  | Logic.Apply (symbol, [ credited ]) when symbol = credit_symbol -> is_potential credited
  | Logic.Apply ((Logic.Symbol.Potential _ | Logic.Symbol.Slack _), _) -> true
  | Logic.Apply (_, arguments) ->
      List.exists
        (function Logic.Symbol (Logic.Symbol.Potential_measure _) -> true | _ -> false)
        arguments
  | _ -> false

let mentions_potential term =
  let rec walk term =
    is_potential term
    ||
    match term with
    | Logic.Forall (_, _, body) | Logic.Exists (_, body) -> walk body
    | term -> List.exists walk (Logic.list_arguments term)
  in
  walk term

let rec list_potentials term =
  if is_potential term then [ term ]
  else List.concat_map list_potentials (Logic.list_arguments term)

let rec take_potential_as_zero term =
  if is_potential term then Logic.Integer Z.zero
  else Logic.map_arguments take_potential_as_zero term

let find_shared_potential_summands
    (values : (Logic.term * (Logic.term * Logic.term) list * Logic.term) list) =
  let joined_terms = List.concat_map (fun (_, renamings, _) -> List.map snd renamings) values in
  let linear =
    List.map (fun (on, renamings, amount) -> (on, renamings, Logic.linearize amount)) values
  in
  let find_coefficient sums atom = Option.value (List.assoc_opt atom sums) ~default:Z.zero in
  let joined_atoms =
    List.fold_left
      (fun atoms (_, _, (sums, _)) ->
        List.fold_left
          (fun atoms (atom, _) ->
            if
              is_potential atom
              && List.exists (fun joined -> mentions_part ~part:joined atom) joined_terms
              && not (List.mem atom atoms)
            then atoms @ [ atom ]
            else atoms)
          atoms sums)
      [] linear
  in
  let align linear atom =
    match
      List.find_map
        (fun (_, _, (sums, _)) ->
          let coefficient = find_coefficient sums atom in
          if Z.equal coefficient Z.zero then None else Some coefficient)
        linear
    with
    | None -> linear
    | Some target ->
        List.map
          (fun (on, renamings, (sums, constant)) ->
            let difference = Z.sub target (find_coefficient sums atom) in
            if Z.equal difference Z.zero then (on, renamings, (sums, constant))
            else
              let on_path =
                List.fold_left
                  (fun atom (incoming, joined) -> Logic.replace ~from:joined ~into:incoming atom)
                  atom renamings
              in
              ( on,
                renamings,
                Logic.linearize
                  (Logic.add
                     (Logic.combine_linear (sums, constant))
                     (Logic.multiply (Logic.Integer difference) (Logic.subtract atom on_path))) ))
          linear
  in
  let is_misaligned atom =
    match linear with
    | (_, _, (first_sums, _)) :: rest ->
        let coefficient = find_coefficient first_sums atom in
        List.exists
          (fun (_, _, (sums, _)) -> not (Z.equal (find_coefficient sums atom) coefficient))
          rest
    | [] -> false
  in
  match List.filter is_misaligned joined_atoms with
  | [] -> None
  | misaligned ->
      let aligned = List.fold_left align linear misaligned in
      let shared =
        match aligned with
        | (_, _, (first_sums, _)) :: rest ->
            List.filter
              (fun (atom, coefficient) ->
                is_potential atom
                && List.for_all
                     (fun (_, _, (sums, _)) ->
                       match List.assoc_opt atom sums with
                       | Some other -> Z.equal other coefficient
                       | None -> false)
                     rest)
              first_sums
        | [] -> []
      in
      Some
        ( Logic.combine_linear (shared, Z.zero),
          List.map
            (fun (on, _, (sums, constant)) ->
              ( on,
                Logic.combine_linear
                  (List.filter (fun (atom, _) -> not (List.mem_assoc atom shared)) sums, constant)
              ))
            aligned )

let join_spent spent ~paths ~name =
  List.map
    (fun (counter, term) ->
      let values =
        List.map
          (fun (on, renamings, spent_on_path) ->
            ( on,
              renamings,
              List.fold_left
                (fun amount (from, into) -> Logic.replace ~from ~into amount)
                (Option.value (List.assoc_opt counter spent_on_path) ~default:term)
                renamings ))
          paths
      in
      let choose_amount values =
        match List.rev values with
        | (_, last) :: earlier ->
            List.fold_left (fun otherwise (on, value) -> Logic.ite on value otherwise) last earlier
        | [] -> term
      in
      let name_amount amount = if mentions_potential amount then amount else name amount in
      match values with
      | (_, _, first_value) :: rest
        when List.for_all (fun (_, _, other) -> other == first_value || other = first_value) rest ->
          (counter, first_value)
      | _ -> (
          match find_shared_potential_summands values with
          | None ->
              ( counter,
                name_amount (choose_amount (List.map (fun (on, _, value) -> (on, value)) values)) )
          | Some (shared, (_, first_rest) :: others)
            when List.for_all (fun (_, other) -> other = first_rest) others ->
              (counter, Logic.add shared first_rest)
          | Some (shared, rests) -> (counter, Logic.add shared (name_amount (choose_amount rests)))))
    spent
