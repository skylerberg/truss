(* The entry points of parsing that an earlier part calls in a later one:
   a clause's expressions, and an expression's blocks and statements.
   [Parse_statement], which the parser of definitions reaches, sets them. *)

open Syntax

let not_set name _ = failwith ("Parse_hooks." ^ name ^ " was not set")

let expression_hook : (?open_range:bool -> Cursor.t -> expression) ref =
  ref (fun ?open_range:_ -> not_set "expression")

let block_hook : (Cursor.t -> block) ref = ref (not_set "block")
let body_hook : (Cursor.t -> block) ref = ref (not_set "body")
let body_opening_hook : (Cursor.t -> unit) ref = ref (not_set "body_opening")
let statement_hook : (Cursor.t -> statement) ref = ref (not_set "statement")
let expression ?open_range cursor = !expression_hook ?open_range cursor
let block cursor = !block_hook cursor
let body cursor = !body_hook cursor
let body_opening cursor = !body_opening_hook cursor
let statement cursor = !statement_hook cursor
