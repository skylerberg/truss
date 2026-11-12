(* Cost bounds: what a counter counts, how, and the constants an [O(...)]
   bound is proven with. The proof program that increases the counters is
   [Translate]'s. *)

module L = Logic
module S = Logic.Symbol

let zero = L.Integer Z.zero

(* What a [calls(...)] clause counts: calls through a function value,
   which is its term in the definition proven, or calls of a capability's
   methods, or of one of them. *)
type target = Through of L.term | Capability of Path.t | Capability_method of Path.t * string
type resource = Time | Allocations | Allocated_bytes | Calls of target

(* A counter counts in units, for an [O(...)] bound, or exactly, for a bound
   written with [<=] or [==]. In units, each callee's [O(g)] counts as
   [g + 1] and each step as one, which is within a constant factor of what
   is really spent; exactly, each callee counts what its exact bound says,
   and one with only an [O(...)] bound is not known. A loop without a
   [cost] clause is counted as its iterations times a bound on each, which
   for [==] must be what every iteration spends. *)
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
  | Through a, Through b -> a = b
  | Capability a, Capability b -> Path.equal a b
  | Capability_method (a, m), Capability_method (b, n) -> Path.equal a b && m = n
  | _ -> false

(* The constants of one [O(...)] bound: two symbols, which each query that
   mentions them pins to one pair from the list, tried in order. *)
type constants = {
  factor : L.symbol;
  addend : L.symbol;
  mutable pairs : (Z.t * Z.t) list;
      (** Cut to the first when the bound is assumed of another function in a cycle, which is proven
          with that pair. *)
}

let pairs = [ (Z.shift_left Z.one 17, Z.shift_left Z.one 16); (Z.shift_left Z.one 17, Z.zero) ]
let constants group = { factor = S.Cost_factor group; addend = S.Cost_addend group; pairs }

(* [c * f + d]. *)
let bound constants f =
  L.Operation
    ("+", [ L.Operation ("*", [ L.Symbol constants.factor; f ]); L.Symbol constants.addend ])

let pin constants (factor, addend) =
  L.(
    equal (Symbol constants.factor) (Integer factor)
    &&& equal (Symbol constants.addend) (Integer addend))

let plus a b =
  match (a, b) with
  | L.Integer x, L.Integer y -> L.Integer (Z.add x y)
  | (L.Integer x, other | other, L.Integer x) when Z.equal x Z.zero -> other
  | _ -> L.Operation ("+", [ a; b ])

let minus a b =
  match (a, b) with
  | L.Integer x, L.Integer y -> L.Integer (Z.sub x y)
  | other, L.Integer x when Z.equal x Z.zero -> other
  | _ when a = b -> zero
  | _ -> L.Operation ("-", [ a; b ])

let times a b =
  match (a, b) with
  | L.Integer x, L.Integer y -> L.Integer (Z.mul x y)
  | (L.Integer x, other | other, L.Integer x) when Z.equal x Z.one -> other
  | (L.Integer x, _ | _, L.Integer x) when Z.equal x Z.zero -> zero
  | _ -> L.Operation ("*", [ a; b ])

let at_most a b = L.Operation ("<=", [ a; b ])

let at_least_zero term =
  match term with
  | L.Integer value -> L.Integer (Z.max value Z.zero)
  | _ -> L.ite (L.Operation (">=", [ term; zero ])) term zero

let larger a b =
  match (a, b) with
  | L.Integer x, L.Integer y -> L.Integer (Z.max x y)
  | _ when a = b -> a
  | _ -> L.ite (L.Operation (">=", [ a; b ])) a b

(* A callee's [O(g)], in units. *)
let units g = plus (at_least_zero g) (L.int 1)

(* [log] and [power]: [log(n)] rounds log2(n + 1) up, so [log(0)] is 0,
   and [power(b, e)] is [b] to the [e]. *)

(* What is known of [log(n)]: it is 0 at and below 0, at least 0 and at
   most [n], and one more than [log(n / 2)] from 1 up, which is exact since
   [log] rounds up. The halving is stated once, not again for [n / 2], so
   no fact makes the solver unfold [log] forever. *)
let log_facts n ~halving =
  let log n = L.Apply (S.Cost_log, [ n ]) in
  let basic =
    L.(
      Operation ("<=", [ int 0; log n ])
      &&& (Operation ("<=", [ n; int 0 ]) ==> equal (log n) (int 0))
      &&& (Operation (">=", [ n; int 0 ]) ==> Operation ("<=", [ log n; n ])))
  in
  if halving then
    let half = L.Operation ("div", [ n; L.int 2 ]) in
    ( [
        basic;
        L.(Operation (">=", [ n; int 1 ]) ==> equal (log n) (Operation ("+", [ log half; int 1 ])));
      ],
      Some half )
  else ([ basic ], None)

(* [log] grows with its argument, between two terms it is applied to. *)
let log_order a b =
  let log n = L.Apply (S.Cost_log, [ n ]) in
  L.(
    Operation ("<=", [ a; b ])
    ==> Operation ("<=", [ log a; log b ])
    &&& (Operation ("<=", [ b; a ]) ==> Operation ("<=", [ log b; log a ])))

(* What is known of [power(b, e)]: 1 at 0, and at least 1, and above [e],
   for a base of at least 1 or 2; and, as a step stated once, [b] times
   [power(b, e - 1)] from 1 up, with [e - 1]. *)
let power_facts base exponent =
  let power e = L.Apply (S.Cost_power, [ base; e ]) in
  let previous = L.Operation ("-", [ exponent; L.int 1 ]) in
  ( L.
      [
        equal exponent (int 0) ==> equal (power exponent) (int 1);
        Operation (">=", [ base; int 1 ])
        &&& Operation (">=", [ exponent; int 0 ])
        ==> Operation (">=", [ power exponent; int 1 ]);
        Operation (">=", [ base; int 2 ])
        &&& Operation (">=", [ exponent; int 0 ])
        ==> Operation (">", [ power exponent; exponent ]);
      ],
    ( L.(
        Operation (">=", [ exponent; int 1 ])
        ==> equal (power exponent) (Operation ("*", [ base; power previous ]))),
      previous ) )

let power_order base a b =
  let power e = L.Apply (S.Cost_power, [ base; e ]) in
  L.(
    Operation (">=", [ base; int 1 ])
    ==> (Operation ("<=", [ a; b ])
        ==> Operation ("<=", [ power a; power b ])
        &&& (Operation ("<=", [ b; a ]) ==> Operation ("<=", [ power b; power a ]))))

(* Arithmetic in a normal form: a sum of terms, each times an integer,
   plus an integer, with the terms in the order they first appear. So
   [(k + a) - k] is [a], which is how what a loop spent in one iteration
   is told from what it had spent before. *)
let rec normalize term =
  let rec linear coefficient term (sums, constant) =
    match term with
    | L.Integer value -> (sums, Z.add constant (Z.mul coefficient value))
    | L.Operation ("+", arguments) ->
        List.fold_left
          (fun sums_and_constant argument -> linear coefficient argument sums_and_constant)
          (sums, constant) arguments
    | L.Operation ("-", [ inner ]) -> linear (Z.neg coefficient) inner (sums, constant)
    | L.Operation ("-", first :: rest) ->
        List.fold_left
          (fun sums_and_constant argument -> linear (Z.neg coefficient) argument sums_and_constant)
          (linear coefficient first (sums, constant))
          rest
    | L.Operation ("*", [ L.Integer k; inner ]) | L.Operation ("*", [ inner; L.Integer k ]) ->
        linear (Z.mul coefficient k) inner (sums, constant)
    | other -> (
        match inner other with
        | L.Operation ("+", _) as sum -> linear coefficient sum (sums, constant)
        | other -> add_atom coefficient other (sums, constant))
  and add_atom coefficient other (sums, constant) =
    let rec add = function
      | [] -> [ (other, coefficient) ]
      | (atom, c) :: rest when atom = other -> (atom, Z.add c coefficient) :: rest
      | entry :: rest -> entry :: add rest
    in
    (add sums, constant)
  and inner = function
    | L.Apply (S.Cost_most, [ a; b ]) -> (
        (* What both choices add is outside the larger of them. *)
        let a = normalize a
        and b = normalize b in
        (* Each summand with its coefficient, so that a term both choices
           take away is shared as one both add is. *)
        let rec summands coefficient = function
          | L.Operation ("+", parts) -> List.concat_map (summands coefficient) parts
          | L.Operation ("-", [ inner ]) -> summands (Z.neg coefficient) inner
          | L.Operation ("-", first :: rest) ->
              summands coefficient first @ List.concat_map (summands (Z.neg coefficient)) rest
          | L.Operation ("*", [ L.Integer k; inner ]) -> summands (Z.mul coefficient k) inner
          | L.Integer _ -> []
          | other -> [ (other, coefficient) ]
        in
        match List.filter (fun part -> List.mem part (summands Z.one b)) (summands Z.one a) with
        | [] -> L.Apply (S.Cost_most, [ a; b ])
        | common ->
            let shared =
              List.fold_left
                (fun total (atom, coefficient) -> plus total (times (L.Integer coefficient) atom))
                zero common
            in
            L.Operation
              ( "+",
                [
                  shared;
                  L.Apply (S.Cost_most, [ normalize (minus a shared); normalize (minus b shared) ]);
                ] ))
    | L.Apply (name, arguments) -> L.Apply (name, List.map normalize arguments)
    | L.Is (constructor, argument) -> L.Is (constructor, normalize argument)
    | L.Operation (name, arguments) when not (List.mem name [ "+"; "-" ]) ->
        L.Operation (name, List.map normalize arguments)
    | other -> other
  in
  let sums, constant = linear Z.one term ([], Z.zero) in
  let sums = List.filter (fun (_, c) -> not (Z.equal c Z.zero)) sums in
  let scaled (atom, c) = times (L.Integer c) atom in
  let positive = List.filter (fun (_, c) -> Z.sign c > 0) sums in
  let negative =
    List.filter_map (fun (atom, c) -> if Z.sign c < 0 then Some (atom, Z.neg c) else None) sums
  in
  let total = List.fold_left (fun total entry -> plus total (scaled entry)) zero positive in
  let total =
    if Z.sign constant >= 0 then plus total (L.Integer constant)
    else minus total (L.Integer (Z.neg constant))
  in
  List.fold_left (fun total entry -> minus total (scaled entry)) total negative

(* What was spent since [start], of a counter that is now [total]: a sum
   that began at [start], or a choice between such sums where paths
   joined. *)
let rec since ~start total =
  match total with
  | L.Operation ("ite", [ condition; a; b ]) -> L.ite condition (since ~start a) (since ~start b)
  | _ -> normalize (minus total start)

(* Finding a bound for one iteration of a loop, or one call of a lambda.

   [cost] is what one iteration spent, a term over values the loop changes,
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
  | L.Operation ("ite", [ _; a; b ]) ->
      L.Apply (S.Cost_most, [ choices_as_most a; choices_as_most b ])
  | L.Apply (name, arguments) -> L.Apply (name, List.map choices_as_most arguments)
  | L.Operation (name, arguments) -> L.Operation (name, List.map choices_as_most arguments)
  | L.Is (constructor, argument) -> L.Is (constructor, choices_as_most argument)
  | other -> other

let rec most_as_choices = function
  | L.Apply (S.Cost_most, [ a; b ]) -> larger (most_as_choices a) (most_as_choices b)
  | L.Apply (name, arguments) -> L.Apply (name, List.map most_as_choices arguments)
  | L.Operation (name, arguments) -> L.Operation (name, List.map most_as_choices arguments)
  | L.Is (constructor, argument) -> L.Is (constructor, most_as_choices argument)
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
    | Some _ -> parts := List.map (fun (p, q) -> if p = part then (p, Both) else (p, q)) !parts
  in
  let rec walk polarity term =
    if varies term then
      match term with
      | L.Operation ("+", arguments) -> List.iter (walk polarity) arguments
      | L.Operation ("-", [ inner ]) -> walk (flip polarity) inner
      | L.Operation ("-", first :: rest) ->
          walk polarity first;
          List.iter (walk (flip polarity)) rest
      | L.Operation ("*", [ L.Integer k; inner ]) | L.Operation ("*", [ inner; L.Integer k ]) ->
          walk (if Z.sign k >= 0 then polarity else flip polarity) inner
      | L.Operation ("*", arguments) | L.Apply ((S.Cost_most | S.Cost_log | S.Cost_power), arguments)
        ->
          List.iter (walk polarity) arguments
      | _ -> add term polarity
  in
  walk Grows term;
  !parts

(* Each comparison in a fact, as [(smaller, larger)]. *)
let rec comparisons fact =
  match fact with
  | L.Operation ("and", parts) -> List.concat_map comparisons parts
  | L.Operation ("=>", [ _; conclusion ]) -> comparisons conclusion
  | L.Operation (("<=" | "<"), [ a; b ]) -> [ (a, b) ]
  | L.Operation ((">=" | ">"), [ a; b ]) -> [ (b, a) ]
  | L.Operation ("=", [ a; b ]) -> [ (a, b); (b, a) ]
  | _ -> []

(* A literal at the end of a built-in integer type's range, which every
   value of the type is known to be within: a bound, but too loose to
   help, so the last one chosen. *)
let is_type_end = function
  | L.Integer value ->
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
  match List.stable_sort (fun a b -> compare (rank a) (rank b)) candidates with
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
                  Some (normalize (L.replace ~from:part ~into:(choices_as_most bound) cost))
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
