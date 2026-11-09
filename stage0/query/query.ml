(* The compiler stages' view of the code database. See query.mli. *)

type context = Incremental.context
type subject = Incremental.subject = { path : Path.t; part : string option }
type ('key, 'value) input = ('key, 'value) Incremental.input
type ('key, 'value) query = ('key, 'value) Incremental.query

type phase =
  | Syntax
  | Declarations
  | Resolution
  | Interfaces
  | Bodies
  | Checks
  | Diagnostics
  | Lowering
  | Linking
  | Recursion
  | Keys

(* Inputs are before every phase. *)
let rank = function
  | Syntax -> 1
  | Declarations -> 2
  | Resolution -> 3
  | Interfaces -> 4
  | Bodies -> 5
  | Checks -> 6
  | Diagnostics -> 7
  | Lowering -> 8
  | Linking -> 9
  | Recursion -> 10
  | Keys -> 11

let phase_name = function
  | Syntax -> "syntax"
  | Declarations -> "declarations"
  | Resolution -> "resolution"
  | Interfaces -> "interfaces"
  | Bodies -> "bodies"
  | Checks -> "checks"
  | Diagnostics -> "diagnostics"
  | Lowering -> "lowering"
  | Linking -> "linking"
  | Recursion -> "recursion"
  | Keys -> "keys"

let input = Incremental.input

let query ~name ~show ~phase ?saved ?equal ?about compute =
  Incremental.query ~name ~show ~phase:(rank phase) ?saved ?equal ?about compute

let find = Incremental.read

let get context input key =
  match Incremental.read context input key with Some value -> value | None -> raise Not_found

let demand = Incremental.demand

exception Cycle = Incremental.Cycle
