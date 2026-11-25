module Hash_map = Map.Make (Int)

type held = { condition : Logic.term; conjunct : Logic.term }
type t = { newest_first : Logic.term list; count : int; held : held list Hash_map.t }

let empty = { newest_first = []; count = 0; held = Hash_map.empty }

let rec list_conjuncts = function
  | Logic.Operation (And, parts) -> List.concat_map list_conjuncts parts
  | term -> [ term ]

let add fact facts =
  let condition, stated =
    match fact with
    | Logic.Operation (Implies, [ condition; stated ]) -> (condition, stated)
    | stated -> (Logic.Boolean true, stated)
  in
  {
    newest_first = fact :: facts.newest_first;
    count = facts.count + 1;
    held =
      List.fold_left
        (fun held conjunct ->
          Hash_map.update (Logic.hash_term conjunct)
            (fun alike -> Some ({ condition; conjunct } :: Option.value alike ~default:[]))
            held)
        facts.held (list_conjuncts stated);
  }

let count facts = facts.count
let list_oldest_first facts = List.rev facts.newest_first
let list_newest_since facts ~count = List.take (facts.count - count) facts.newest_first

let rec encloses condition ~inner =
  condition == inner
  ||
  match inner with
  | Logic.Operation (And, [ outer; _ ]) -> encloses condition ~inner:outer
  | _ -> false

let is_held facts ~under conjunct =
  match Hash_map.find_opt (Logic.hash_term conjunct) facts.held with
  | Some alike ->
      List.exists
        (fun held ->
          (held.condition = Logic.Boolean true || encloses held.condition ~inner:under)
          && held.conjunct = conjunct)
        alike
  | None -> false

let holds facts ~under goal = List.for_all (is_held facts ~under) (list_conjuncts goal)
