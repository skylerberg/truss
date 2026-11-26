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
  oblige_each frame location (specification.list_requires entries) ~describe

let assume_ensures (frame : State.frame) specification ~entries ~exits ~result =
  List.iter
    (fun (_, term) -> Facts.assume frame term)
    (specification.list_ensures ~entries ~exits ~result)

let oblige_ensures frame location specification ~entries ~exits ~result ~describe =
  oblige_each frame location (specification.list_ensures ~entries ~exits ~result) ~describe

let refine (frame : State.frame) location ~by refined entries ~havoc ~describe_ensures =
  let at_call = assume_requires frame refined entries in
  let by = Option.map (fun (specify, describe) -> (specify at_call, describe)) by in
  Option.iter (fun (by, describe) -> oblige_requires at_call location by entries ~describe) by;
  if refined.has_ensures then begin
    let exits, result = havoc () in
    Option.iter (fun (by, _) -> assume_ensures at_call by ~entries ~exits ~result) by;
    oblige_ensures at_call location refined ~entries ~exits ~result ~describe:describe_ensures
  end
