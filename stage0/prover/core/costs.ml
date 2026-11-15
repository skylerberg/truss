module Symbol = Logic.Symbol

let zero = Logic.Integer Z.zero

type target = Through of Logic.term | Capability of Path.t | Capability_method of Path.t * string
type resource = Time | Allocations | Allocated_bytes | Calls of target
type counting = Units | At_most | Exactly
type counter = { resource : resource; counting : counting; amortized : bool }

let bound bound_function =
  Logic.Operation
    ( "+",
      [
        Logic.Operation ("*", [ Logic.Integer (Z.shift_left Z.one 17); bound_function ]);
        Logic.Integer (Z.shift_left Z.one 16);
      ] )

let plus left right =
  match (left, right) with
  | Logic.Integer x, Logic.Integer y -> Logic.Integer (Z.add x y)
  | (Logic.Integer x, other | other, Logic.Integer x) when Z.equal x Z.zero -> other
  | _ -> Logic.Operation ("+", [ left; right ])

let minus left right =
  match (left, right) with
  | Logic.Integer x, Logic.Integer y -> Logic.Integer (Z.sub x y)
  | other, Logic.Integer x when Z.equal x Z.zero -> other
  | _ when left = right -> zero
  | _ -> Logic.Operation ("-", [ left; right ])

let times left right =
  match (left, right) with
  | Logic.Integer x, Logic.Integer y -> Logic.Integer (Z.mul x y)
  | (Logic.Integer x, other | other, Logic.Integer x) when Z.equal x Z.one -> other
  | (Logic.Integer x, _ | _, Logic.Integer x) when Z.equal x Z.zero -> zero
  | _ -> Logic.Operation ("*", [ left; right ])

let at_most left right = Logic.Operation ("<=", [ left; right ])

let at_least_zero term =
  match term with
  | Logic.Integer value -> Logic.Integer (Z.max value Z.zero)
  | _ -> Logic.ite (Logic.Operation (">=", [ term; zero ])) term zero

let larger left right =
  match (left, right) with
  | Logic.Integer x, Logic.Integer y -> Logic.Integer (Z.max x y)
  | _ when left = right -> left
  | _ -> Logic.ite (Logic.Operation (">=", [ left; right ])) left right

let units amount = plus (at_least_zero amount) (Logic.int 1)

let rec normalize term =
  let rec linear coefficient term (sums, constant) =
    match term with
    | Logic.Integer value -> (sums, Z.add constant (Z.mul coefficient value))
    | Logic.Operation ("+", arguments) ->
        List.fold_left
          (fun sums_and_constant argument -> linear coefficient argument sums_and_constant)
          (sums, constant) arguments
    | Logic.Operation ("-", [ inner ]) -> linear (Z.neg coefficient) inner (sums, constant)
    | Logic.Operation ("-", first :: rest) ->
        List.fold_left
          (fun sums_and_constant argument -> linear (Z.neg coefficient) argument sums_and_constant)
          (linear coefficient first (sums, constant))
          rest
    | Logic.Operation ("*", [ Logic.Integer factor; inner ])
    | Logic.Operation ("*", [ inner; Logic.Integer factor ]) ->
        linear (Z.mul coefficient factor) inner (sums, constant)
    | other -> (
        match inner other with
        | Logic.Operation ("+", _) as sum -> linear coefficient sum (sums, constant)
        | other -> add_atom coefficient other (sums, constant))
  and add_atom coefficient other (sums, constant) =
    let rec add = function
      | [] -> [ (other, coefficient) ]
      | (atom, sum_coefficient) :: rest when atom = other ->
          (atom, Z.add sum_coefficient coefficient) :: rest
      | entry :: rest -> entry :: add rest
    in
    (add sums, constant)
  and inner = function
    | Logic.Apply (Symbol.Cost_most, [ left; right ]) -> (
        let left = normalize left and right = normalize right in
        let rec summands coefficient = function
          | Logic.Operation ("+", parts) -> List.concat_map (summands coefficient) parts
          | Logic.Operation ("-", [ inner ]) -> summands (Z.neg coefficient) inner
          | Logic.Operation ("-", first :: rest) ->
              summands coefficient first @ List.concat_map (summands (Z.neg coefficient)) rest
          | Logic.Operation ("*", [ Logic.Integer factor; inner ]) ->
              summands (Z.mul coefficient factor) inner
          | Logic.Integer _ -> []
          | other -> [ (other, coefficient) ]
        in
        match
          List.filter (fun part -> List.mem part (summands Z.one right)) (summands Z.one left)
        with
        | [] -> Logic.Apply (Symbol.Cost_most, [ left; right ])
        | common ->
            let shared =
              List.fold_left
                (fun total (atom, coefficient) ->
                  plus total (times (Logic.Integer coefficient) atom))
                zero common
            in
            Logic.Operation
              ( "+",
                [
                  shared;
                  Logic.Apply
                    ( Symbol.Cost_most,
                      [ normalize (minus left shared); normalize (minus right shared) ] );
                ] ))
    | Logic.Apply (name, arguments) -> Logic.Apply (name, List.map normalize arguments)
    | Logic.Is (constructor, argument) -> Logic.Is (constructor, normalize argument)
    | Logic.Operation (name, arguments) when not (List.mem name [ "+"; "-" ]) ->
        Logic.Operation (name, List.map normalize arguments)
    | other -> other
  in
  let sums, constant = linear Z.one term ([], Z.zero) in
  let sums = List.filter (fun (_, sum_coefficient) -> not (Z.equal sum_coefficient Z.zero)) sums in
  let scaled (atom, sum_coefficient) = times (Logic.Integer sum_coefficient) atom in
  let positive = List.filter (fun (_, sum_coefficient) -> Z.sign sum_coefficient > 0) sums in
  let negative =
    List.filter_map
      (fun (atom, sum_coefficient) ->
        if Z.sign sum_coefficient < 0 then Some (atom, Z.neg sum_coefficient) else None)
      sums
  in
  let total = List.fold_left (fun total entry -> plus total (scaled entry)) zero positive in
  let total =
    if Z.sign constant >= 0 then plus total (Logic.Integer constant)
    else minus total (Logic.Integer (Z.neg constant))
  in
  List.fold_left (fun total entry -> minus total (scaled entry)) total negative

let rec since ~start total =
  match total with
  | Logic.Operation ("ite", [ condition; left; right ]) ->
      Logic.ite condition (since ~start left) (since ~start right)
  | _ -> normalize (minus total start)

type polarity = Grows | Shrinks | Both

let flip = function Grows -> Shrinks | Shrinks -> Grows | Both -> Both

let rec choices_as_most = function
  | Logic.Operation ("ite", [ _; left; right ]) ->
      Logic.Apply (Symbol.Cost_most, [ choices_as_most left; choices_as_most right ])
  | Logic.Apply (name, arguments) -> Logic.Apply (name, List.map choices_as_most arguments)
  | Logic.Operation (name, arguments) -> Logic.Operation (name, List.map choices_as_most arguments)
  | Logic.Is (constructor, argument) -> Logic.Is (constructor, choices_as_most argument)
  | other -> other

let rec most_as_choices = function
  | Logic.Apply (Symbol.Cost_most, [ left; right ]) ->
      larger (most_as_choices left) (most_as_choices right)
  | Logic.Apply (name, arguments) -> Logic.Apply (name, List.map most_as_choices arguments)
  | Logic.Operation (name, arguments) -> Logic.Operation (name, List.map most_as_choices arguments)
  | Logic.Is (constructor, argument) -> Logic.Is (constructor, most_as_choices argument)
  | other -> other

let varying_parts varies term =
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
      | Logic.Operation ("+", arguments) -> List.iter (walk polarity) arguments
      | Logic.Operation ("-", [ inner ]) -> walk (flip polarity) inner
      | Logic.Operation ("-", first :: rest) ->
          walk polarity first;
          List.iter (walk (flip polarity)) rest
      | Logic.Operation ("*", [ Logic.Integer factor; inner ])
      | Logic.Operation ("*", [ inner; Logic.Integer factor ]) ->
          walk (if Z.sign factor >= 0 then polarity else flip polarity) inner
      | Logic.Operation ("*", arguments)
      | Logic.Apply ((Symbol.Cost_most | Symbol.Cost_log | Symbol.Cost_power), arguments) ->
          List.iter (walk polarity) arguments
      | _ -> add term polarity
  in
  walk Grows term;
  !parts

let rec comparisons fact =
  match fact with
  | Logic.Operation ("and", parts) -> List.concat_map comparisons parts
  | Logic.Operation ("=>", [ _; conclusion ]) -> comparisons conclusion
  | Logic.Operation (("<=" | "<"), [ left; right ]) -> [ (left, right) ]
  | Logic.Operation ((">=" | ">"), [ left; right ]) -> [ (right, left) ]
  | Logic.Operation ("=", [ left; right ]) -> [ (left, right); (right, left) ]
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

let bound_of ~varies ~facts part polarity =
  let candidates =
    List.filter_map
      (fun (smaller, larger) ->
        match polarity with
        | Grows when smaller = part && larger <> part -> Some larger
        | Shrinks when larger = part && smaller <> part -> Some smaller
        | _ -> None)
      (List.concat_map comparisons facts)
  in
  let rank candidate = if varies candidate then 2 else if is_type_end candidate then 1 else 0 in
  match List.stable_sort (fun left right -> compare (rank left) (rank right)) candidates with
  | best :: _ -> Some best
  | [] -> None

let bound_on ~varies ~facts cost =
  let rec bound_within_depth depth cost =
    if not (varies cost) then Some cost
    else if depth = 0 then None
    else
      let parts = varying_parts varies cost in
      let replaced =
        List.find_map
          (fun (part, polarity) ->
            if polarity = Both then None
            else
              match bound_of ~varies ~facts part polarity with
              | Some bound ->
                  Some (normalize (Logic.replace ~from:part ~into:(choices_as_most bound) cost))
              | None -> None)
          parts
      in
      match replaced with
      | Some next when next <> cost -> bound_within_depth (depth - 1) next
      | _ -> None
  in
  Option.map most_as_choices (bound_within_depth 12 (normalize (choices_as_most cost)))

let upper_bounds ~varies ~facts term =
  List.filter_map
    (fun (smaller, larger) -> if smaller = term && not (varies larger) then Some larger else None)
    (List.concat_map comparisons facts)
