type clause = Catalog.Prover.quoted * Logic.term

type t = {
  list_requires : Logic.term list -> clause list;
  list_ensures :
    entries:Logic.term list -> exits:Logic.term list -> result:Logic.term -> clause list;
  has_ensures : bool;
}

let assume_requires (frame : State.frame) specification entries =
  Facts.restrict frame (Logic.conjunction (List.map snd (specification.list_requires entries)))

let oblige_each (frame : State.frame) location clauses ~describe =
  List.iter (fun (clause, term) -> Obligations.oblige frame location (describe clause) term) clauses

let oblige_requires frame location specification entries ~describe =
  let required = specification.list_requires entries in
  oblige_each frame location required ~describe;
  Logic.conjunction (List.map snd required)

let assume_ensures (frame : State.frame) specification ~entries ~exits ~result =
  List.iter
    (fun (_, term) -> Facts.assume frame term)
    (specification.list_ensures ~entries ~exits ~result)

let refine (frame : State.frame) location ~by refined entries ~havoc ~describe_ensures =
  let at_call = assume_requires frame refined entries in
  let executed =
    Option.map
      (fun (specify, describe) ->
        let by = specify at_call in
        let required = oblige_requires at_call location by entries ~describe in
        (by, Facts.restrict_unless_proven at_call required))
      by
  in
  if refined.has_ensures then begin
    let exits, result = havoc () in
    Option.iter (fun (by, returned) -> assume_ensures returned by ~entries ~exits ~result) executed;
    oblige_each at_call location
      (refined.list_ensures ~entries ~exits ~result)
      ~describe:describe_ensures
  end
