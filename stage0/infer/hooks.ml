(* The entry points of checking that its parts call across files.
   Checking an expression is one recursive whole, split into files by what
   each part checks; each part calls the parts after it through these, and
   [Expressions], which every caller of checking reaches, sets them when it
   is linked. *)

open Syntax
module T = Types
open State

let not_set name _ = failwith ("Hooks." ^ name ^ " was not set")

let expression_hook : (state -> env -> ?expected:T.ty -> expression -> T.ty) ref =
  ref (fun _ _ ?expected:_ -> not_set "expression")

let check_hook : (state -> env -> expression -> T.ty -> unit) ref =
  ref (fun _ _ _ -> not_set "check")

let expression state env ?expected value = !expression_hook state env ?expected value
let check state env value expected = !check_hook state env value expected
