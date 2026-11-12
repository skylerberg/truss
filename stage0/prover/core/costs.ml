(* Cost bounds: a counter's resource, its way of counting, and the constants an [O(...)]
   bound is proven with. *)
module Symbol = Logic.Symbol

let zero = Logic.Integer Z.zero

(* The target of a [calls(...)] clause: calls through a function value,
   which is its term in the definition proven, or calls of a capability's
   methods, or of one of them. *)
type target = Through of Logic.term | Capability of Path.t | Capability_method of Path.t * string
type resource = Time | Allocations | Allocated_bytes | Calls of target

(* A counter counts in units, for an [O(...)] bound, or exactly, for a bound
   written with [<=] or [==]. In units, each callee's [O(g)] counts as
   [g + 1] and each step as one, which is within a constant factor of the
   real cost; exactly, each callee counts its exact bound,
   and one with only an [O(...)] bound is not known. A loop without a
   [cost] clause is counted as its iterations times a bound on each, which
   for [==] must be every iteration's exact cost. *)
type counting = Units | At_most | Exactly

(* An amortized bound has a counter of its own, so that a definition with a
   plain and an amortized bound on one resource counts each callee by the
   clause of its kind. *)
type counter = { resource : resource; counting : counting; amortized : bool }

(* Whether a [calls] clause about [clause] bounds the calls a counter about
   [counter] counts: the same target, or a whole capability for one of its
   methods, which bounds it from above. *)
let covers ~clause ~counter =
  match (clause, counter) with
  | Capability path, Capability_method (owner, _) -> Path.equal path owner
  | Through left, Through right -> left = right
  | Capability left, Capability right -> Path.equal left right
  | Capability_method (left, left_method), Capability_method (right, right_method) ->
      Path.equal left right && left_method = right_method
  | _ -> false

(* The constants of one [O(...)] bound: two symbols, which each query that
   mentions them pins to one pair from the list, tried in order. *)
type constants = {
  factor : Logic.symbol;
  addend : Logic.symbol;
  mutable pairs : (Z.t * Z.t) list;
      (** Cut to the first when the bound is assumed of another function in a cycle, which is proven
          with that pair. *)
}

let pairs = [ (Z.shift_left Z.one 17, Z.shift_left Z.one 16); (Z.shift_left Z.one 17, Z.zero) ]

let constants group =
  { factor = Symbol.Cost_factor group; addend = Symbol.Cost_addend group; pairs }

(* [c * f + d]. *)
let bound constants bound_function =
  Logic.Operation
    ( "+",
      [
        Logic.Operation ("*", [ Logic.Symbol constants.factor; bound_function ]);
        Logic.Symbol constants.addend;
      ] )

let pin constants (factor, addend) =
  Logic.(
    equal (Symbol constants.factor) (Integer factor)
    &&& equal (Symbol constants.addend) (Integer addend))

let plus left right =
  match (left, right) with
  | Logic.Integer left_value, Logic.Integer right_value ->
      Logic.Integer (Z.add left_value right_value)
  | (Logic.Integer left_value, other | other, Logic.Integer left_value)
    when Z.equal left_value Z.zero ->
      other
  | _ -> Logic.Operation ("+", [ left; right ])

let minus left right =
  match (left, right) with
  | Logic.Integer left_value, Logic.Integer right_value ->
      Logic.Integer (Z.sub left_value right_value)
  | other, Logic.Integer left_value when Z.equal left_value Z.zero -> other
  | _ when left = right -> zero
  | _ -> Logic.Operation ("-", [ left; right ])

let times left right =
  match (left, right) with
  | Logic.Integer left_value, Logic.Integer right_value ->
      Logic.Integer (Z.mul left_value right_value)
  | (Logic.Integer left_value, other | other, Logic.Integer left_value)
    when Z.equal left_value Z.one ->
      other
  | (Logic.Integer left_value, _ | _, Logic.Integer left_value) when Z.equal left_value Z.zero ->
      zero
  | _ -> Logic.Operation ("*", [ left; right ])

let at_most left right = Logic.Operation ("<=", [ left; right ])

let at_least_zero term =
  match term with
  | Logic.Integer value -> Logic.Integer (Z.max value Z.zero)
  | _ -> Logic.ite (Logic.Operation (">=", [ term; zero ])) term zero

let larger left right =
  match (left, right) with
  | Logic.Integer left_value, Logic.Integer right_value ->
      Logic.Integer (Z.max left_value right_value)
  | _ when left = right -> left
  | _ -> Logic.ite (Logic.Operation (">=", [ left; right ])) left right

(* A callee's [O(g)], in units. *)
let units amount = plus (at_least_zero amount) (Logic.int 1)

(* [log] and [power]: [log(n)] rounds log2(n + 1) up, so [log(0)] is 0,
   and [power(b, e)] is [b] to the [e]. *)

(* The facts about [log(n)]: it is 0 at and below 0, at least 0 and at
   most [n], and one more than [log(n / 2)] from 1 up, which is exact since
   [log] rounds up. The halving is stated once, not again for [n / 2], so
   no fact makes the solver unfold [log] forever. *)
let log_facts number ~halving =
  let log number = Logic.Apply (Symbol.Cost_log, [ number ]) in
  let basic =
    Logic.(
      Operation ("<=", [ int 0; log number ])
      &&& (Operation ("<=", [ number; int 0 ]) ==> equal (log number) (int 0))
      &&& (Operation (">=", [ number; int 0 ]) ==> Operation ("<=", [ log number; number ])))
  in
  if halving then
    let half = Logic.Operation ("div", [ number; Logic.int 2 ]) in
    ( [
        basic;
        Logic.(
          Operation (">=", [ number; int 1 ])
          ==> equal (log number) (Operation ("+", [ log half; int 1 ])));
      ],
      Some half )
  else ([ basic ], None)

(* [log] grows with its argument, between two terms it is applied to. *)
let log_order left right =
  let log number = Logic.Apply (Symbol.Cost_log, [ number ]) in
  Logic.(
    Operation ("<=", [ left; right ])
    ==> Operation ("<=", [ log left; log right ])
    &&& (Operation ("<=", [ right; left ]) ==> Operation ("<=", [ log right; log left ])))

(* The facts about [power(b, e)]: 1 at 0, and at least 1, and above [e],
   for a base of at least 1 or 2; and, as a step stated once, [b] times
   [power(b, e - 1)] from 1 up, with [e - 1]. *)
let power_facts base exponent =
  let power exponent = Logic.Apply (Symbol.Cost_power, [ base; exponent ]) in
  let previous = Logic.Operation ("-", [ exponent; Logic.int 1 ]) in
  ( Logic.
      [
        equal exponent (int 0) ==> equal (power exponent) (int 1);
        Operation (">=", [ base; int 1 ])
        &&& Operation (">=", [ exponent; int 0 ])
        ==> Operation (">=", [ power exponent; int 1 ]);
        Operation (">=", [ base; int 2 ])
        &&& Operation (">=", [ exponent; int 0 ])
        ==> Operation (">", [ power exponent; exponent ]);
      ],
    ( Logic.(
        Operation (">=", [ exponent; int 1 ])
        ==> equal (power exponent) (Operation ("*", [ base; power previous ]))),
      previous ) )

let power_order base left right =
  let power exponent = Logic.Apply (Symbol.Cost_power, [ base; exponent ]) in
  Logic.(
    Operation (">=", [ base; int 1 ])
    ==> (Operation ("<=", [ left; right ])
        ==> Operation ("<=", [ power left; power right ])
        &&& (Operation ("<=", [ right; left ]) ==> Operation ("<=", [ power right; power left ]))))

(* Arithmetic in a normal form: a sum of terms, each times an integer,
   plus an integer, with the terms in the order they first appear. So
   [(k + a) - k] is [a], which separates a loop's cost in one iteration
   from its cost before. *)
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
        (* A term both choices add is moved outside the larger of them. *)
        let left = normalize left
        and right = normalize right in
        (* Each summand with its coefficient, so that a term both choices
           take away is shared as one both add is. *)
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

(* The cost since [start], of a counter that is now [total]: a sum
   that began at [start], or a choice between such sums where paths
   joined. *)
let rec since ~start total =
  match total with
  | Logic.Operation ("ite", [ condition; left; right ]) ->
      Logic.ite condition (since ~start left) (since ~start right)
  | _ -> normalize (minus total start)

(* Finding a bound for one iteration of a loop, or one call of a lambda.

   [cost] is one iteration's cost, a term over values the loop changes,
   which [varies] tells, and values it does not. The bound replaces each
   part of [cost] that varies with a bound on it from [facts]: an upper
   bound where [cost] grows with the part, and a lower bound where it
   shrinks, until nothing in it varies. The result is only a guess; the
   prover shows that each iteration spends no more than it, so a wrong
   guess is never unsound, only unproven. *)

type polarity = Grows | Shrinks | Both

let flip = function Grows -> Shrinks | Shrinks -> Grows | Both -> Both

(* Each choice, [ite], becomes the larger of its branches, which is above
   it whichever is taken. *)
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

(* The parts of a term that vary, each with how the term changes with it.
   Sums, differences, products, the larger of two, [log], and [power] are
   followed; any other term that varies is a part as a whole. *)
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

(* Each comparison in a fact, as [(smaller, larger)]. *)
let rec comparisons fact =
  match fact with
  | Logic.Operation ("and", parts) -> List.concat_map comparisons parts
  | Logic.Operation ("=>", [ _; conclusion ]) -> comparisons conclusion
  | Logic.Operation (("<=" | "<"), [ left; right ]) -> [ (left, right) ]
  | Logic.Operation ((">=" | ">"), [ left; right ]) -> [ (right, left) ]
  | Logic.Operation ("=", [ left; right ]) -> [ (left, right); (right, left) ]
  | _ -> []

(* A literal at the end of a built-in integer type's range, which every
   value of the type is known to be within: a bound, but too loose to
   help, so the last one chosen. *)
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

(* Facts' upper bounds on a term, for the number of a loop's iterations. *)
let upper_bounds ~varies ~facts term =
  List.filter_map
    (fun (smaller, larger) -> if smaller = term && not (varies larger) then Some larger else None)
    (List.concat_map comparisons facts)
