(* The core form as text, for tests and for looking at what checking
   built. A local is shown by the name that binds it. *)

open Core
module T = Types

type names = (local, string) Hashtbl.t

let local (names : names) (found : local) =
  match (found, Hashtbl.find_opt names found) with
  | _, Some name -> name
  | Self, None -> "self"
  | Bound id, None -> Printf.sprintf "local#%d" id
  | Made number, None -> Printf.sprintf "made#%d" number

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
                Printf.sprintf "%s through %s" (expression value) (callee names display))
          pieces
      ^ ")"
  | Template { from_template; template } ->
      Printf.sprintf "%s(%s)" (callee names from_template) (expression template)
  | Use found -> place found
  | Copy given -> "copy(" ^ operand given ^ ")"
  | Function_value { path; type_arguments = arguments } ->
      "fn " ^ Path.show path ^ type_arguments arguments
  | Constant path -> Path.show path
  | Generic_value parameter -> parameter.name
  | Lambda { parameters; captures; body; _ } ->
      Printf.sprintf "lambda(%s)%s %s"
        (list (pattern names) parameters)
        (match captures with [] -> "" | captures -> " capturing " ^ list (local names) captures)
        (block names body)
  | Construct { variant; fields } ->
      Printf.sprintf "%s%s(%s)" (T.show node.type_)
        (match variant with Some variant -> "." ^ variant | None -> "")
        (list
           (fun (name, given) ->
             name ^ ": " ^ match given with Some given -> expression given | None -> "default")
           fields)
  | Collection { elements; built } ->
      Printf.sprintf "%s[%s]" (collection built) (list expression elements)
  | Entries { entries; built } ->
      Printf.sprintf "%s[%s]" (collection built)
        (list (fun (key, value) -> expression key ^ ": " ^ expression value) entries)
  | Updated { base; updates } ->
      Printf.sprintf "%s with (%s)" (expression base)
        (list (fun (path, value) -> String.concat "." path ^ ": " ^ expression value) updates)
  | Slice { base; start; stop; inclusive } ->
      let end_ = function Some value -> expression value | None -> "" in
      Printf.sprintf "%s[%s%s%s]" (place base) (end_ start)
        (if inclusive then "..=" else "..")
        (end_ stop)
  | Call made -> call names made
  | Operator { operation; arguments } ->
      Printf.sprintf "%s(%s)" (Intrinsic.operation_name operation) (list expression arguments)
  | Compare { comparison = written; left; right } ->
      Printf.sprintf "(%s %s %s)" (expression left) (comparison written) (expression right)
  | Not inner -> "!" ^ expression inner
  | Both (left, right) -> Printf.sprintf "(%s && %s)" (expression left) (expression right)
  | Either (left, right) -> Printf.sprintf "(%s || %s)" (expression left) (expression right)
  | Implies (left, right) -> Printf.sprintf "(%s ==> %s)" (expression left) (expression right)
  | Matches { value; pattern = matched } ->
      Printf.sprintf "(%s is %s)" (operand value) (pattern names matched)
  | Next cursor -> "next(" ^ place cursor ^ ")"
  | Convert { conversion; value } ->
      Printf.sprintf "%s(%s)"
        (match conversion with
        | View view -> "view through " ^ callee names view
        | Widen -> "widen"
        | To_integer -> "to_integer"
        | From_integer -> "from_integer")
        (expression value)
  | Any { value; trait; evidence = found } ->
      Printf.sprintf "any %s(%s by %s)" (T.show_trait trait) (expression value) (evidence found)
  | If { condition; then_; else_ } ->
      Printf.sprintf "if %s %s%s" (expression condition) (block names then_)
        (match else_ with Some else_ -> " else " ^ block names else_ | None -> "")
  | Match { scrutinees; arms; guards_cover } ->
      Printf.sprintf "match %s {%s }%s" (list operand scrutinees)
        (String.concat ""
           (List.map
              (fun (arm : arm) ->
                Printf.sprintf " %s%s => %s"
                  (list (pattern names) arm.patterns)
                  (match arm.guard with Some guard -> " if " ^ expression guard | None -> "")
                  (block names arm.body))
              arms))
        (if guards_cover then " guards cover" else "")
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
  | Todo -> "todo"
  | Unreachable -> "unreachable"
  | Echo inner -> "echo " ^ expression inner
  | Result -> "result"
  | Old inner -> "old(" ^ expression inner ^ ")"
  | Updating -> "updating"
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
            Printf.sprintf "%s in %s" (pattern names matched) (expression collection))
        (expression body)
  | Yielded -> "yielded"
  | Finished -> "finished"
  | Identical (left, right) ->
      Printf.sprintf "identical(%s, %s)" (expression left) (expression right)
  | Measure { function_; arguments } ->
      Printf.sprintf "%s(%s)"
        (match function_ with Log -> "log" | Power -> "power" | Time -> "time" | Calls -> "calls")
        (list expression arguments)

and collection = function
  | Array -> "array"
  | From_storage _ -> "list"
  | Inserted _ -> "inserted"
  | Modelled -> "modelled"

and callee names = function
  | Function { path; type_arguments = arguments } -> Path.show path ^ type_arguments arguments
  | Trait_method { trait; name; self_type; evidence = found; _ } ->
      Printf.sprintf "%s.%s for %s by %s" (T.show_trait trait) name (T.show self_type)
        (evidence found)
  | Capability_method { capability; name } -> Path.show capability ^ "." ^ name
  | Intrinsic { operation; _ } -> "intrinsic::" ^ Intrinsic.operation_name operation
  | Value function_ -> "(" ^ expression names function_ ^ ")"

and call names (made : call) =
  Printf.sprintf "%s(%s)%s" (callee names made.callee)
    (list
       (function
         | Passed { mode = passed; value } -> mode passed ^ operand names value
         | Default -> "default")
       made.arguments)
    (match made.lends with
    | Some Mut -> " lends mut"
    | Some Own -> " lends own"
    | Some Read -> " lends"
    | None -> "")

and operand names = function
  | Place found -> "place " ^ place names found
  | Value value -> expression names value

and place names = function
  | Local found -> local names found
  | Field { base; field; _ } -> Printf.sprintf "%s.%s" (place names base) field
  | Lent lending -> "lent " ^ expression names lending
  | Temporary value -> "temporary " ^ expression names value

and block names (body : block) =
  let parts =
    List.map (statement names) body.statements
    @ match body.value with Some value -> [ expression names value ] | None -> []
  in
  Printf.sprintf "{ %s }%s" (String.concat "; " parts) (if body.ends then "" else " never ends")

and statement names (node : statement) =
  match node.kind with
  | Let { pattern = bound; value; otherwise } ->
      Printf.sprintf "let %s = %s%s" (pattern names bound) (operand names value)
        (match otherwise with Some otherwise -> " else " ^ block names otherwise | None -> "")
  | Evaluate value -> expression names value
  | Assign { target; value } ->
      Printf.sprintf "%s = %s" (place names target) (expression names value)
  | Update { target; value } ->
      Printf.sprintf "update %s = %s" (place names target) (expression names value)
  | For { pattern = bound; drive = over; clauses; body; parallel } ->
      Printf.sprintf "%sfor %s in %s%s %s"
        (if parallel then "parallel " else "")
        (pattern names bound)
        (match over with
        | Count { start; stop; inclusive } ->
            Printf.sprintf "count %s%s%s" (expression names start)
              (if inclusive then "..=" else "..")
              (expression names stop)
        | Each each -> "each " ^ expression names each
        | Pull { cursor; next } ->
            Printf.sprintf "pull %s%s" (expression names cursor)
              (match next with Some next -> " by " ^ callee names next | None -> ""))
        (loop_clauses names clauses) (block names body)
  | While { condition; clauses; body } ->
      Printf.sprintf "while %s%s %s" (expression names condition) (loop_clauses names clauses)
        (block names body)
  | Parallel branches ->
      "parallel { " ^ String.concat "; " (List.map (statement names) branches) ^ " }"
  | Proof body -> "proof " ^ block names body
  | Assert condition -> "assert " ^ clause names condition
  | Yield { mode = lent; part } -> "yield " ^ mode lent ^ operand names part

and clause names (condition : clause) =
  expression names condition.value ^ if condition.runs then "" else " (not run)"

and loop_clauses names clauses =
  String.concat ""
    (List.map
       (function
         | Invariant value -> " invariant " ^ expression names value
         | Decreases measures -> " decreases " ^ list (expression names) measures
         | Cost spent -> " " ^ cost names spent)
       clauses)

and cost names (spent : cost) =
  Printf.sprintf "cost%s %s"
    (if spent.amortized then " amortized" else "")
    (match spent.bound with
    | Finite -> "finite"
    | Order_of value -> "O(" ^ expression names value ^ ")"
    | At_most value -> "<= " ^ expression names value
    | Exactly value -> "== " ^ expression names value)

and pattern names (node : pattern) =
  match node.kind with
  | Anything -> "_"
  | Bind { local = bound; mutable_; mode = held; _ } ->
      (if mutable_ then "var " else "") ^ mode held ^ local names bound
  | Variant { variant; fields } -> (
      match fields with
      | [] -> variant
      | fields -> variant ^ "(" ^ pattern_fields names fields ^ ")")
  | Record fields -> "(" ^ pattern_fields names fields ^ ")"
  | Literal value -> expression names value
  | Within { start; stop; inclusive } ->
      Printf.sprintf "%s%s%s" (expression names start)
        (if inclusive then "..=" else "..")
        (expression names stop)
  | Equals { value; _ } -> "equal to " ^ expression names value
  | Alternatives alternatives -> String.concat " | " (List.map (pattern names) alternatives)

and pattern_fields names fields =
  list (fun (name, inner) -> name ^ ": " ^ pattern names inner) fields

(* The names of a definition's locals: its parameters and everything a
   pattern binds. *)
let names_of (parts : parts) : names =
  let names = Hashtbl.create 16 in
  let parameter (written : parameter) =
    Hashtbl.replace names written.local written.name;
    Option.iter
      (fun (accepted : accepts) ->
        List.iter (fun (input, name) -> Hashtbl.replace names input name) accepted.inputs)
      written.accepts
  in
  (match parts with
  | Function { parameters; _ } -> List.iter parameter parameters
  | Trait laws -> List.iter (fun (written : law) -> List.iter parameter written.parameters) laws
  | Type _ | Constant _ | Test _ | Law_proof _ | Nothing -> ());
  Core_walk.parts
    {
      Core_walk.nothing with
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
    parts;
  names

let parameter names (written : parameter) =
  Printf.sprintf "%s%s: %s%s" (mode written.mode) written.name (T.show written.type_)
    (match written.default with Some value -> " = " ^ expression names value | None -> "")

let parts (parts : parts) =
  let names = names_of parts in
  let lines =
    match parts with
    | Function { parameters; contract; body } -> (
        [ "fn(" ^ list (parameter names) parameters ^ ")" ]
        @ List.map (fun condition -> "requires " ^ clause names condition) contract.requires
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
    | Nothing -> []
  in
  String.concat "\n" lines

let show (form : t) = parts form.parts
