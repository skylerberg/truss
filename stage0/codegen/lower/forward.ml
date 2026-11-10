(* Forward references that tie lowering's mutually recursive parts
   together: [Calls], [Values], and [Matching] call through them to the
   parts after them, [Expressions] and [Statements], which [Lower] sets
   them to. *)

open Lowering
module S = Syntax

let block_into : (state -> S.block -> Lir.place option -> unit) ref =
  ref (fun _ -> Definitions.bug "block_into is not set")

let branch : (state -> S.expression -> yes:Lir.block -> no:Lir.block -> unit) ref =
  ref (fun _ -> Definitions.bug "branch is not set")

let expression : (state -> S.expression -> Lir.place) ref =
  ref (fun _ -> Definitions.bug "expression is not set")

let if_ :
    (state ->
    condition:S.expression ->
    then_:S.block ->
    else_:S.else_branch option ->
    Lir.place option ->
    unit)
    ref =
  ref (fun _ -> Definitions.bug "if_ is not set")

let into : (state -> S.expression -> Lir.place -> unit) ref =
  ref (fun _ -> Definitions.bug "into is not set")

let match_ :
    (state -> scrutinees:S.expression list -> arms:S.arm list -> Lir.place option -> unit) ref =
  ref (fun _ -> Definitions.bug "match_ is not set")

let operand : (state -> S.expression -> Lir.operand) ref =
  ref (fun _ -> Definitions.bug "operand is not set")

let operator : (state -> S.expression -> S.expression list -> Lir.place -> unit) ref =
  ref (fun _ -> Definitions.bug "operator is not set")

let place_expression : (state -> S.expression -> Lir.place option) ref =
  ref (fun _ -> Definitions.bug "place_expression is not set")

let statement : (state -> S.statement -> unit) ref =
  ref (fun _ -> Definitions.bug "statement is not set")
