(* The solver's logic, and the canonical text of a query. See PROVER.md,
   "The canonical form". *)

type sort = Int | Bool | Uninterpreted of string

type term =
  | Symbol of string
  | Integer of Z.t
  | Boolean of bool
  | Apply of string * term list
  | Forall of (string * sort) list * term
  | Exists of (string * sort) list * term

type declaration = Constant of string * sort | Function of string * sort list * sort
type query = { declarations : declaration list; facts : term list; goal : term }

(* Building terms *)

let int value = Integer (Z.of_int value)

let ( &&& ) left right =
  match (left, right) with
  | Boolean true, other | other, Boolean true -> other
  | Boolean false, _ | _, Boolean false -> Boolean false
  | _ -> Apply ("and", [ left; right ])

let ( ||| ) left right =
  match (left, right) with
  | Boolean false, other | other, Boolean false -> other
  | Boolean true, _ | _, Boolean true -> Boolean true
  | _ -> Apply ("or", [ left; right ])

let ( ==> ) premise conclusion =
  match (premise, conclusion) with
  | Boolean true, other -> other
  | Boolean false, _ | _, Boolean true -> Boolean true
  | _ -> Apply ("=>", [ premise; conclusion ])

let not_ = function
  | Boolean value -> Boolean (not value)
  | Apply ("not", [ inner ]) -> inner
  | other -> Apply ("not", [ other ])

let equal left right = if left = right then Boolean true else Apply ("=", [ left; right ])

let ite condition then_ else_ =
  match condition with
  | Boolean true -> then_
  | Boolean false -> else_
  | _ -> if then_ = else_ then then_ else Apply ("ite", [ condition; then_; else_ ])

let conjunction terms = List.fold_left ( &&& ) (Boolean true) terms
let disjunction terms = List.fold_left ( ||| ) (Boolean false) terms
let zero = Integer Z.zero
let negate value = Apply ("-", [ value ])

(* SMT-LIB's [div] and [mod] round so that the remainder is never
   negative. Truss rounds toward zero, which agrees with them when both
   operands are at or above zero, so each sign is handled by negating. *)
let truncated_divide left right =
  let ge0 value = Apply (">=", [ value; zero ]) in
  let div a b = Apply ("div", [ a; b ]) in
  ite (ge0 left)
    (ite (ge0 right) (div left right) (negate (div left (negate right))))
    (ite (ge0 right) (negate (div (negate left) right)) (div (negate left) (negate right)))

let truncated_remainder left right =
  Apply ("-", [ left; Apply ("*", [ right; truncated_divide left right ]) ])

let rec mentions symbols = function
  | Symbol name -> List.mem name symbols
  | Integer _ | Boolean _ -> false
  | Apply (name, arguments) -> List.mem name symbols || List.exists (mentions symbols) arguments
  | Forall (bound, body) | Exists (bound, body) ->
      let shadowed = List.map fst bound in
      mentions (List.filter (fun symbol -> not (List.mem symbol shadowed)) symbols) body

(* Canonical text *)

(* Numbering: every declared symbol and every uninterpreted sort is named
   by the order of its first appearance in a walk of the facts, in order,
   and then the goal. Bound variables are named by their depth and
   position, so a quantifier's text does not depend on what its variables
   were called. *)
type numbering = {
  declared : (string, declaration) Hashtbl.t;
  symbol_names : (string, string) Hashtbl.t;
  mutable symbol_order : string list;  (** Reversed. *)
  sort_names : (string, string) Hashtbl.t;
  mutable sort_order : string list;  (** Reversed. *)
}

let sort_name numbering = function
  | Int -> "Int"
  | Bool -> "Bool"
  | Uninterpreted name -> (
      match Hashtbl.find_opt numbering.sort_names name with
      | Some canonical -> canonical
      | None ->
          let canonical = Printf.sprintf "S%d" (Hashtbl.length numbering.sort_names) in
          Hashtbl.replace numbering.sort_names name canonical;
          numbering.sort_order <- name :: numbering.sort_order;
          canonical)

let symbol_name numbering name =
  match Hashtbl.find_opt numbering.symbol_names name with
  | Some canonical -> Some canonical
  | None -> (
      match Hashtbl.find_opt numbering.declared name with
      | None -> None
      | Some declaration ->
          let canonical = Printf.sprintf "x%d" (Hashtbl.length numbering.symbol_names) in
          Hashtbl.replace numbering.symbol_names name canonical;
          numbering.symbol_order <- name :: numbering.symbol_order;
          (* The sorts a declaration mentions are numbered with it. *)
          (match declaration with
          | Constant (_, sort) -> ignore (sort_name numbering sort)
          | Function (_, inputs, output) ->
              List.iter (fun sort -> ignore (sort_name numbering sort)) inputs;
              ignore (sort_name numbering output));
          Some canonical)

let integer_text value =
  if Z.sign value < 0 then Printf.sprintf "(- %s)" (Z.to_string (Z.neg value))
  else Z.to_string value

let rec print numbering bound buffer term =
  let add = Buffer.add_string buffer in
  match term with
  | Symbol name -> (
      match List.assoc_opt name bound with
      | Some canonical -> add canonical
      | None -> (
          match symbol_name numbering name with
          | Some canonical -> add canonical
          | None -> invalid_arg ("Logic.text: undeclared symbol " ^ name)))
  | Integer value -> add (integer_text value)
  | Boolean value -> add (if value then "true" else "false")
  | Apply (name, []) -> (
      match symbol_name numbering name with Some canonical -> add canonical | None -> add name)
  | Apply (name, arguments) ->
      add "(";
      (match symbol_name numbering name with Some canonical -> add canonical | None -> add name);
      List.iter
        (fun argument ->
          add " ";
          print numbering bound buffer argument)
        arguments;
      add ")"
  | Forall (variables, body) -> quantifier numbering bound buffer "forall" variables body
  | Exists (variables, body) -> quantifier numbering bound buffer "exists" variables body

and quantifier numbering bound buffer word variables body =
  let add = Buffer.add_string buffer in
  let depth = List.length bound in
  let named =
    List.mapi
      (fun index (name, sort) -> (name, Printf.sprintf "b%d" (depth + index), sort))
      variables
  in
  add "(";
  add word;
  add " (";
  List.iteri
    (fun index (_, canonical, sort) ->
      if index > 0 then add " ";
      add (Printf.sprintf "(%s %s)" canonical (sort_name numbering sort)))
    named;
  add ") ";
  print numbering
    (List.map (fun (name, canonical, _) -> (name, canonical)) named @ bound)
    buffer body;
  add ")"

let numbering query =
  let declared = Hashtbl.create 64 in
  List.iter
    (fun declaration ->
      let name = match declaration with Constant (name, _) | Function (name, _, _) -> name in
      Hashtbl.replace declared name declaration)
    query.declarations;
  {
    declared;
    symbol_names = Hashtbl.create 64;
    symbol_order = [];
    sort_names = Hashtbl.create 8;
    sort_order = [];
  }

let render query =
  let numbering = numbering query in
  let assertion term =
    let buffer = Buffer.create 128 in
    Buffer.add_string buffer "(assert ";
    print numbering [] buffer term;
    Buffer.add_string buffer ")\n";
    Buffer.contents buffer
  in
  let assertions = List.map assertion query.facts @ [ assertion (not_ query.goal) ] in
  let sorts =
    List.rev_map
      (fun name -> Printf.sprintf "(declare-sort %s 0)\n" (Hashtbl.find numbering.sort_names name))
      numbering.sort_order
  in
  let declarations =
    List.rev_map
      (fun name ->
        let canonical = Hashtbl.find numbering.symbol_names name in
        match Hashtbl.find numbering.declared name with
        | Constant (_, sort) ->
            Printf.sprintf "(declare-fun %s () %s)\n" canonical (sort_name numbering sort)
        | Function (_, inputs, output) ->
            Printf.sprintf "(declare-fun %s (%s) %s)\n" canonical
              (String.concat " " (List.map (sort_name numbering) inputs))
              (sort_name numbering output))
      numbering.symbol_order
  in
  (String.concat "" (sorts @ declarations @ assertions) ^ "(check-sat)\n", numbering)

let text query = fst (render query)

let symbols query =
  let _, numbering = render query in
  List.rev_map (fun name -> (name, Hashtbl.find numbering.symbol_names name)) numbering.symbol_order

let hash text = "smt1-blake3-" ^ Blake3.to_hex (Blake3.hash text)

let show_term term =
  let rec show = function
    | Symbol name -> name
    | Integer value -> integer_text value
    | Boolean value -> if value then "true" else "false"
    | Apply (name, []) -> name
    | Apply (name, arguments) -> "(" ^ String.concat " " (name :: List.map show arguments) ^ ")"
    | Forall (bound, body) -> binder "forall" bound body
    | Exists (bound, body) -> binder "exists" bound body
  and binder word bound body =
    let sort = function Int -> "Int" | Bool -> "Bool" | Uninterpreted name -> name in
    Printf.sprintf "(%s (%s) %s)" word
      (String.concat " " (List.map (fun (name, s) -> Printf.sprintf "(%s %s)" name (sort s)) bound))
      (show body)
  in
  show term
