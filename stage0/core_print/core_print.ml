(* Prints the core form as text, for tests and debugging. A local is
   printed with the name it was declared with. *)

open Core
module T = Types

type names = (local, string) Hashtbl.t

let local (names : names) (found : local) =
  match (found, Hashtbl.find_opt names found) with
  | _, Some name -> name
  | Self, None -> "self"
  | Named id, None -> Printf.sprintf "local#%d" id
  | Synthetic number, None -> Printf.sprintf "synthetic#%d" number

let mode : T.mode -> string = function Read -> "" | Mut -> "mut " | Own -> "own "
let list show items = String.concat ", " (List.map show items)
let type_arguments = function [] -> "" | arguments -> "[" ^ list T.show_argument arguments ^ "]"

let comparison = function
  | Equal -> "=="
  | Not_equal -> "!="
  | Less -> "<"
  | Less_equal -> "<="
  | Greater -> ">"
  | Greater_equal -> ">="

let evidence = function Impl { impl; _ } -> Path.show impl | Bound -> "a bound" | Dynamic -> "any"

let rec expression names (node : expression) =
  let expression = expression names and place = place names and operand = operand names in
  match node.kind with
  | Integer number -> Z.to_string number
  | Float number -> Printf.sprintf "%h" number
  | Boolean value -> string_of_bool value
  | String text -> Printf.sprintf "%S" text
  | Interpolated { pieces; _ } ->
      "interpolated("
      ^ list
          (function
            | Text text -> Printf.sprintf "%S" text
            | Displayed { value; display } ->
                Printf.sprintf "%s through %s" (operand value) (callee names display))
          pieces
      ^ ")"
  | Template { literals; call } ->
      Printf.sprintf "template(%s) call %s" (list (Printf.sprintf "%S") literals) (expression call)
  | Use found -> place found
  | Copy given -> "copy(" ^ operand given ^ ")"
  | Function_value { path; type_arguments = arguments } ->
      "fn " ^ Path.show path ^ type_arguments arguments
  | Value_parameter parameter -> parameter.name
  | Lambda { parameters; captures; body; _ } ->
      Printf.sprintf "lambda(%s)%s %s"
        (list (pattern names) parameters)
        (match captures with
        | [] -> ""
        | captures ->
            " capturing " ^ list (fun (capture : capture) -> local names capture.local) captures)
        (block names body)
  | Construct { variant; fields } ->
      Printf.sprintf "%s%s(%s)" (T.show node.type_)
        (match variant with Some variant -> "." ^ variant | None -> "")
        (list
           (fun (name, given) ->
             name ^ ": " ^ match given with Some given -> operand given | None -> "default")
           fields)
  | Collection_literal { elements; construction = how } ->
      Printf.sprintf "%s[%s]" (construction how) (list expression elements)
  | Map_literal { entries } ->
      Printf.sprintf "%s[%s]" (construction Specification_only)
        (list (fun (key, value) -> expression key ^ ": " ^ expression value) entries)
  | Record_update { base; updates } ->
      Printf.sprintf "%s with (%s)" (expression base)
        (list (fun (path, value) -> String.concat "." path ^ ": " ^ expression value) updates)
  | Slice { call; _ } -> "slice " ^ expression call
  | Call made -> call names made
  | Operator { operation; arguments } ->
      Printf.sprintf "%s(%s)" (Intrinsic.operation_name operation) (list expression arguments)
  | Compare { comparison = written; left; right } ->
      Printf.sprintf "(%s %s %s)" (expression left) (comparison written) (expression right)
  | Not inner -> "!" ^ expression inner
  | And (left, right) -> Printf.sprintf "(%s && %s)" (expression left) (expression right)
  | Or (left, right) -> Printf.sprintf "(%s || %s)" (expression left) (expression right)
  | Implies (left, right) -> Printf.sprintf "(%s ==> %s)" (expression left) (expression right)
  | Matches { value; pattern = matched } ->
      Printf.sprintf "(%s is %s)" (operand value) (pattern names matched)
  | Cursor_next cursor -> "cursor_next(" ^ place cursor ^ ")"
  | Convert { conversion; value } ->
      Printf.sprintf "%s(%s)"
        (match conversion with
        | Widen -> "widen"
        | To_integer -> "to_integer"
        | From_integer -> "from_integer")
        (expression value)
  | To_any { value; trait; evidence = found } ->
      Printf.sprintf "any %s(%s by %s)" (T.show_trait trait) (expression value) (evidence found)
  | If { condition; then_; else_ } ->
      Printf.sprintf "if %s %s%s" (expression condition) (block names then_)
        (match else_ with Some else_ -> " else " ^ block names else_ | None -> "")
  | Match { scrutinees; arms; guards_exhaustive } ->
      Printf.sprintf "match %s {%s }%s" (list operand scrutinees)
        (String.concat ""
           (List.map
              (fun (arm : arm) ->
                Printf.sprintf " %s%s => %s"
                  (list (pattern names) arm.patterns)
                  (match arm.guard with Some guard -> " if " ^ expression guard | None -> "")
                  (block names arm.body))
              arms))
        (if guards_exhaustive then " guards exhaustive" else "")
  | Block body -> block names body
  | Provide { implementations; body } ->
      Printf.sprintf "provide %s %s"
        (list
           (fun (implementation : implementation) ->
             mode implementation.mode ^ operand implementation.value)
           implementations)
        (block names body)
  | Return value -> (
      match value with Some value -> "return " ^ expression value | None -> "return")
  | Break -> "break"
  | Continue -> "continue"
  | Leaving { tasks; exit } ->
      Printf.sprintf "leaving %s { %s }"
        (String.concat ", "
           (List.map
              (function
                | Branch { block; index } -> Printf.sprintf "branch %d of #%d" index block
                | Iteration { loop } -> Printf.sprintf "an iteration of #%d" loop)
              tasks))
        (expression exit)
  | Todo -> "todo"
  | Unreachable -> "unreachable"
  | Echo inner -> "echo " ^ expression inner
  | Result -> "result"
  | Old inner -> "old(" ^ expression inner ^ ")"
  | Current_target -> "current_target"
  | Quantified { quantifier; binder = bound; body } ->
      Printf.sprintf "%s %s { %s }"
        (match quantifier with Forall -> "forall" | Exists -> "exists")
        (match bound with
        | Over_type { name; type_; _ } -> name ^ ": " ^ T.show type_
        | Over_range { pattern = matched; start; stop; inclusive } ->
            Printf.sprintf "%s in %s%s%s" (pattern names matched) (expression start)
              (if inclusive then "..=" else "..")
              (expression stop)
        | Over_collection { pattern = matched; collection } ->
            Printf.sprintf "%s in %s" (pattern names matched) (expression collection)
        | Over_each { pattern = matched; call } ->
            Printf.sprintf "%s in yielding_call %s" (pattern names matched) (expression call))
        (expression body)
  | Yielded -> "yielded"
  | Finished -> "finished"
  | Identical (left, right) ->
      Printf.sprintf "identical(%s, %s)" (expression left) (expression right)
  | Method_time method_ -> Printf.sprintf "time(%s)" (callee names method_)
  | Specification_function { function_; arguments } ->
      Printf.sprintf "%s(%s)"
        (match function_ with Log -> "log" | Power -> "power" | Time -> "time" | Calls -> "calls")
        (list expression arguments)

and construction = function Array -> "array" | Specification_only -> "specification_only"

and callee names = function
  | Function { path; type_arguments = arguments } -> Path.show path ^ type_arguments arguments
  | Trait_method { trait; name; self_type; evidence = found; _ } ->
      Printf.sprintf "%s.%s for %s by %s" (T.show_trait trait) name (T.show self_type)
        (evidence found)
  | Capability_method { capability; name } -> Path.show capability ^ "." ^ name
  | Intrinsic { operation; _ } -> "intrinsic::" ^ Intrinsic.operation_name operation
  | Indirect function_value -> "(" ^ operand names function_value ^ ")"

and call names (call : call) =
  Printf.sprintf "%s(%s)%s" (callee names call.callee)
    (list
       (function
         | Passed { mode = passed; value } -> mode passed ^ operand names value
         | Default -> "default")
       call.arguments)
    (match call.lends with
    | Some Mut -> " lends mut"
    | Some Own -> " lends own"
    | Some Read -> " lends"
    | None -> "")

and operand names = function
  | Place found -> "place " ^ place names found
  | Value value -> expression names value

and place names = function
  | Local { local = found; _ } -> local names found
  | Constant { path; _ } -> Path.show path
  | Field { base; field; _ } -> Printf.sprintf "%s.%s" (place names base) field
  | Lent call -> "lent " ^ expression names call
  | Temporary value -> "temporary " ^ expression names value

and block names (body : block) =
  let parts =
    List.map (statement names) body.statements
    @ match body.value with Some value -> [ expression names value ] | None -> []
  in
  Printf.sprintf "{ %s }%s" (String.concat "; " parts) (if body.diverges then " diverges" else "")

and statement names (node : statement) =
  match node.kind with
  | Let { pattern = bound; value; else_ } ->
      Printf.sprintf "let %s = %s%s" (pattern names bound) (operand names value)
        (match else_ with Some else_ -> " else " ^ block names else_ | None -> "")
  | Evaluate value -> expression names value
  | Assign { target; value } ->
      Printf.sprintf "%s = %s" (place names target) (expression names value)
  | Compound_assign { target; value } ->
      Printf.sprintf "compound_assign %s = %s" (place names target) (expression names value)
  | For { pattern = bound; iteration; clauses; body; mode } ->
      Printf.sprintf "%sfor %s in %s%s %s"
        (match mode with
        | Sequential -> ""
        | Parallel_loop -> "parallel "
        | Concurrent_loop -> Printf.sprintf "concurrent #%d " node.origin)
        (pattern names bound)
        (match iteration with
        | Integer_range { start; stop; inclusive } ->
            Printf.sprintf "integer_range %s%s%s" (expression names start)
              (if inclusive then "..=" else "..")
              (expression names stop)
        | Yielding_call call -> "yielding_call " ^ expression names call
        | Cursor { cursor; next } ->
            Printf.sprintf "cursor %s%s" (place names cursor)
              (match next with Some next -> " by " ^ callee names next | None -> ""))
        (loop_clauses names clauses) (block names body)
  | While { condition; clauses; body } ->
      Printf.sprintf "while %s%s %s" (expression names condition) (loop_clauses names clauses)
        (block names body)
  | Parallel branches ->
      "parallel { " ^ String.concat "; " (List.map (statement names) branches) ^ " }"
  | Concurrent branches ->
      Printf.sprintf "concurrent #%d { %s }" node.origin
        (String.concat "; " (List.map (statement names) branches))
  | Proof body -> "proof " ^ block names body
  | Assert found -> "assert " ^ condition names found
  | Yield { mode = lent; part } -> "yield " ^ mode lent ^ operand names part

and condition names (condition : condition) =
  expression names condition.value ^ if condition.executable then "" else " (not executable)"

and loop_clauses names clauses =
  String.concat ""
    (List.map
       (function
         | Invariant value -> " invariant " ^ expression names value
         | Decreases measures -> " decreases " ^ list (expression names) measures
         | Cost spent -> " " ^ cost names spent)
       clauses)

and cost names (spent : cost) =
  Printf.sprintf "cost%s %s %s"
    (if spent.amortized then " amortized" else "")
    (match spent.resource with
    | Time -> "time"
    | Allocations -> "allocations"
    | Allocated_bytes -> "allocated_bytes"
    | Calls (Function_parameter found) -> "calls(" ^ local names found ^ ")"
    | Calls (Capability path) -> "calls(" ^ Path.show path ^ ")"
    | Calls (Capability_method (path, method_)) ->
        Printf.sprintf "calls(%s.%s)" (Path.show path) method_)
    (match spent.bound with
    | Finite -> "finite"
    | Order_of value -> "O(" ^ expression names value ^ ")"
    | At_most value -> "<= " ^ expression names value
    | Exactly value -> "== " ^ expression names value)

and pattern names (node : pattern) =
  match node.kind with
  | Wildcard -> "_"
  | Bind { local = bound; mutable_; mode = held; _ } ->
      (if mutable_ then "var " else "") ^ mode held ^ local names bound
  | Variant { variant; fields } -> (
      match fields with
      | [] -> variant
      | fields -> variant ^ "(" ^ pattern_fields names fields ^ ")")
  | Record fields -> "(" ^ pattern_fields names fields ^ ")"
  | Literal value -> expression names value
  | Range { start; stop; inclusive } ->
      Printf.sprintf "%s%s%s" (expression names start)
        (if inclusive then "..=" else "..")
        (expression names stop)
  | Equal_to { value; _ } -> "equal to " ^ expression names value
  | Alternatives alternatives -> String.concat " | " (List.map (pattern names) alternatives)

and pattern_fields names fields =
  list (fun (name, inner) -> name ^ ": " ^ pattern names inner) fields

(* The names of all locals in a definition: its parameters and every
   pattern binding. *)
let names_of (definition : definition) : names =
  let names = Hashtbl.create 16 in
  let parameter (written : parameter) =
    Hashtbl.replace names written.local written.name;
    Option.iter
      (fun (contract : callback_contract) ->
        List.iter (fun (input, name) -> Hashtbl.replace names input name) contract.inputs)
      written.callback_contract
  in
  (match definition with
  | Function { parameters; _ } -> List.iter parameter parameters
  | Trait laws -> List.iter (fun (written : law) -> List.iter parameter written.parameters) laws
  | Type _ | Constant _ | Test _ | Law_proof _ | Empty -> ());
  Core_walk.definition
    {
      Core_walk.ignore_all with
      pattern =
        (fun (node : pattern) ->
          match node.kind with
          | Bind { local = bound; name; _ } -> Hashtbl.replace names bound name
          | _ -> ());
      expression =
        (fun (node : expression) ->
          match node.kind with
          | Quantified { binder = Over_type { local = bound; name; _ }; _ } ->
              Hashtbl.replace names bound name
          | _ -> ());
    }
    definition;
  names

let parameter names (written : parameter) =
  Printf.sprintf "%s%s: %s%s" (mode written.mode) written.name (T.show written.type_)
    (match written.default with Some value -> " = " ^ expression names value | None -> "")

let definition (definition : definition) =
  let names = names_of definition in
  let lines =
    match definition with
    | Function { parameters; contract; body } -> (
        [ "fn(" ^ list (parameter names) parameters ^ ")" ]
        @ List.map (fun found -> "requires " ^ condition names found) contract.requires
        @ List.map (fun value -> "ensures " ^ expression names value) contract.ensures
        @ (match contract.decreases with
          | [] -> []
          | measures -> [ "decreases " ^ list (expression names) measures ])
        @ List.map (cost names) contract.costs
        @ match body with Some body -> [ block names body ] | None -> [])
    | Type { defaults; invariants; potential } -> (
        List.map
          (fun (variant, name, value) ->
            Printf.sprintf "default %s%s = %s"
              (match variant with Some variant -> variant ^ "." | None -> "")
              name (expression names value))
          defaults
        @ List.map (fun value -> "invariant " ^ expression names value) invariants
        @
        match potential with
        | Some value -> [ "potential " ^ expression names value ]
        | None -> [])
    | Trait laws ->
        List.concat_map
          (fun (written : law) ->
            [ Printf.sprintf "law %s(%s)" written.name (list (parameter names) written.parameters) ]
            @ List.map (fun value -> "requires " ^ expression names value) written.requires
            @ [ block names written.body ])
          laws
    | Constant value -> [ expression names value ]
    | Test body -> [ "test " ^ block names body ]
    | Law_proof body -> [ "proof " ^ block names body ]
    | Empty -> []
  in
  String.concat "\n" lines

let show (form : t) = definition form.definition
