(* Forward references that tie lowering's mutually recursive parts
   together: [Calls], [Values], and [Matching] call through them to the
   parts after them, [Expressions] and [Statements], which [Lower] sets
   them to. See lower.ml. *)

open Lowering
module S = Syntax

let block_into : (state -> S.block -> Lir.place option -> unit) ref =
  ref (fun _ -> invalid_arg "Lower: block_into is not set")

let branch : (state -> S.expression -> yes:Lir.block -> no:Lir.block -> unit) ref =
  ref (fun _ -> invalid_arg "Lower: branch is not set")

let expression : (state -> S.expression -> Lir.place) ref =
  ref (fun _ -> invalid_arg "Lower: expression is not set")

let if_ :
    (state ->
    condition:S.expression ->
    then_:S.block ->
    else_:S.else_branch option ->
    Lir.place option ->
    unit)
    ref =
  ref (fun _ -> invalid_arg "Lower: if_ is not set")

let into : (state -> S.expression -> Lir.place -> unit) ref =
  ref (fun _ -> invalid_arg "Lower: into is not set")

let match_ :
    (state -> scrutinees:S.expression list -> arms:S.arm list -> Lir.place option -> unit) ref =
  ref (fun _ -> invalid_arg "Lower: match_ is not set")

let operand : (state -> S.expression -> Lir.operand) ref =
  ref (fun _ -> invalid_arg "Lower: operand is not set")

let operator : (state -> S.expression -> S.expression list -> Lir.place -> unit) ref =
  ref (fun _ -> invalid_arg "Lower: operator is not set")

let place_expression : (state -> S.expression -> Lir.place option) ref =
  ref (fun _ -> invalid_arg "Lower: place_expression is not set")

let statement : (state -> S.statement -> unit) ref =
  ref (fun _ -> invalid_arg "Lower: statement is not set")
