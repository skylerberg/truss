(* The words of a [cost] clause. The lexer reads them as names, and the
   parser recognizes them by their spelling where a clause expects them. See
   GRAMMAR.md, "Keywords". *)

type t = Amortized | Time | Allocations | Allocated_bytes | Calls | O | Finite | Potential

(* The one place each word is spelled. A test checks the list against
   GRAMMAR.md. *)
let spellings =
  [
    ("amortized", Amortized);
    ("time", Time);
    ("allocations", Allocations);
    ("allocated_bytes", Allocated_bytes);
    ("calls", Calls);
    ("O", O);
    ("finite", Finite);
    ("potential", Potential);
  ]

let spelling word = fst (List.find (fun (_, candidate) -> candidate = word) spellings)

(* The word a token spells: a name, uppercase only for [O]. *)
let of_token (kind : Token.kind) =
  match kind with Lower text | Upper text -> List.assoc_opt text spellings | _ -> None

let resources = [ Time; Allocations; Allocated_bytes; Calls ]
