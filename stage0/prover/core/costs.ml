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

let list_stated_bounds (costs : Types.cost list) (metric : Language.Metric.t) ~amortized =
  List.filter_map
    (fun (cost : Types.cost) ->
      if cost.resource = Types.Metric metric && cost.amortized = amortized then Some cost.bound
      else None)
    costs

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

let plus left right =
  match (left, right) with
  | Logic.Integer x, Logic.Integer y -> Logic.Integer (Z.add x y)
  | (Logic.Integer x, other | other, Logic.Integer x) when Z.equal x Z.zero -> other
  | _ -> Logic.add left right

let minus left right =
  match (left, right) with
  | Logic.Integer x, Logic.Integer y -> Logic.Integer (Z.sub x y)
  | other, Logic.Integer x when Z.equal x Z.zero -> other
  | _ when left = right -> zero
  | _ -> Logic.subtract left right

let times left right =
  match (left, right) with
  | Logic.Integer x, Logic.Integer y -> Logic.Integer (Z.mul x y)
  | (Logic.Integer x, other | other, Logic.Integer x) when Z.equal x Z.one -> other
  | (Logic.Integer x, _ | _, Logic.Integer x) when Z.equal x Z.zero -> zero
  | _ -> Logic.multiply left right

let at_least_zero term =
  match term with
  | Logic.Integer value -> Logic.Integer (Z.max value Z.zero)
  | _ -> Logic.ite (Logic.greater_equal term zero) term zero

let larger left right =
  match (left, right) with
  | Logic.Integer x, Logic.Integer y -> Logic.Integer (Z.max x y)
  | _ when left = right -> left
  | _ -> Logic.ite (Logic.greater_equal left right) left right

let units amount = plus (at_least_zero amount) (Logic.int 1)

let combine (sums, constant) =
  let scale (atom, sum_coefficient) = times (Logic.Integer sum_coefficient) atom in
  let positive = List.filter (fun (_, sum_coefficient) -> Z.sign sum_coefficient > 0) sums in
  let negative =
    List.filter_map
      (fun (atom, sum_coefficient) ->
        if Z.sign sum_coefficient < 0 then Some (atom, Z.neg sum_coefficient) else None)
      sums
  in
  let total = List.fold_left (fun total entry -> plus total (scale entry)) zero positive in
  let total =
    if Z.sign constant >= 0 then plus total (Logic.Integer constant)
    else minus total (Logic.Integer (Z.neg constant))
  in
  List.fold_left (fun total entry -> minus total (scale entry)) total negative

let rec linearize term =
  let rec add_scaled coefficient term (sums, constant) =
    match term with
    | Logic.Integer value -> (sums, Z.add constant (Z.mul coefficient value))
    | Logic.Operation (Add, arguments) ->
        List.fold_left
          (fun sums_and_constant argument -> add_scaled coefficient argument sums_and_constant)
          (sums, constant) arguments
    | Logic.Operation (Negate, [ inner ]) -> add_scaled (Z.neg coefficient) inner (sums, constant)
    | Logic.Operation (Subtract, first :: rest) ->
        List.fold_left
          (fun sums_and_constant argument ->
            add_scaled (Z.neg coefficient) argument sums_and_constant)
          (add_scaled coefficient first (sums, constant))
          rest
    | Logic.Operation (Multiply, [ Logic.Integer factor; inner ])
    | Logic.Operation (Multiply, [ inner; Logic.Integer factor ]) ->
        add_scaled (Z.mul coefficient factor) inner (sums, constant)
    | other -> (
        match normalize_node other with
        | Logic.Operation (Add, _) as sum -> add_scaled coefficient sum (sums, constant)
        | other -> add_atom coefficient other (sums, constant))
  and add_atom coefficient other (sums, constant) =
    let rec add = function
      | [] -> [ (other, coefficient) ]
      | (atom, sum_coefficient) :: rest when atom = other ->
          (atom, Z.add sum_coefficient coefficient) :: rest
      | entry :: rest -> entry :: add rest
    in
    (add sums, constant)
  and normalize_node = function
    | Logic.Apply (Logic.Symbol.Cost_most, [ left; right ]) -> (
        let left = normalize left and right = normalize right in
        let rec list_summands coefficient = function
          | Logic.Operation (Add, parts) -> List.concat_map (list_summands coefficient) parts
          | Logic.Operation (Negate, [ inner ]) -> list_summands (Z.neg coefficient) inner
          | Logic.Operation (Subtract, first :: rest) ->
              list_summands coefficient first
              @ List.concat_map (list_summands (Z.neg coefficient)) rest
          | Logic.Operation (Multiply, [ Logic.Integer factor; inner ]) ->
              list_summands (Z.mul coefficient factor) inner
          | Logic.Integer _ -> []
          | other -> [ (other, coefficient) ]
        in
        match
          List.filter
            (fun part -> List.mem part (list_summands Z.one right))
            (list_summands Z.one left)
        with
        | [] -> Logic.Apply (Logic.Symbol.Cost_most, [ left; right ])
        | common ->
            let shared =
              List.fold_left
                (fun total (atom, coefficient) ->
                  plus total (times (Logic.Integer coefficient) atom))
                zero common
            in
            Logic.add shared
              (Logic.Apply
                 ( Logic.Symbol.Cost_most,
                   [ normalize (minus left shared); normalize (minus right shared) ] )))
    | Logic.Apply (name, arguments) -> Logic.Apply (name, List.map normalize arguments)
    | Logic.Is (constructor, argument) -> Logic.Is (constructor, normalize argument)
    | Logic.Operation (operator, arguments) ->
        Logic.Operation (operator, List.map normalize arguments)
    | other -> other
  in
  let sums, constant = add_scaled Z.one term ([], Z.zero) in
  (List.filter (fun (_, sum_coefficient) -> not (Z.equal sum_coefficient Z.zero)) sums, constant)

and normalize term = combine (linearize term)

let reduce_constants amount =
  let sums, constant = linearize amount in
  let factor =
    List.fold_left (fun factor (_, coefficient) -> Z.gcd factor coefficient) Z.zero sums
  in
  if Z.leq factor Z.one && Z.leq (Z.abs constant) Z.one then amount
  else
    combine
      ( List.map (fun (atom, coefficient) -> (atom, Z.divexact coefficient factor)) sums,
        Z.of_int (Z.sign constant) )

let rec since ~start total =
  match total with
  | Logic.Operation (Ite, [ condition; left; right ]) ->
      Logic.ite condition (since ~start left) (since ~start right)
  | _ -> normalize (minus total start)

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
      larger (rewrite_most_as_choices left) (rewrite_most_as_choices right)
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
          ((Logic.Symbol.Cost_most | Logic.Symbol.Cost_log | Logic.Symbol.Cost_power), arguments) ->
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
      || Z.equal value (Z.of_int 0x10FFFF)
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
                    (normalize
                       (Logic.replace ~from:part ~into:(rewrite_choices_as_most bound) cost))
              | None -> None)
          parts
      in
      match replaced with
      | Some next when next <> cost -> find_bound_within_depth (depth - 1) next
      | _ -> None
  in
  Option.map rewrite_most_as_choices
    (find_bound_within_depth 12 (normalize (rewrite_choices_as_most cost)))

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
            match list_within_depth (depth - 1) (normalize (rewrite_choices_as_most bound)) with
            | [] -> []
            | parts -> part :: parts))
      (list_varying_parts varies cost)
  in
  List.fold_left
    (fun parts part -> if List.mem part parts then parts else parts @ [ part ])
    []
    (list_within_depth 12 (normalize (rewrite_choices_as_most cost)))

let mentions_part ~part amount =
  let rec holds term = term = part || List.exists holds (Logic.list_arguments term) in
  holds (normalize (rewrite_choices_as_most amount))

let list_upper_bounds ~varies ~facts term =
  List.filter_map
    (fun (smaller, larger) -> if smaller = term && not (varies larger) then Some larger else None)
    (List.concat_map list_comparisons facts)
