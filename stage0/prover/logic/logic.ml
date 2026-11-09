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

type declaration =
  | Constant of string * sort
  | Function of string * sort list * sort
  | Datatype of string * (string * (string * sort) list) list

let tester constructor = "is?" ^ constructor

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

(* Numbering: every declared symbol and every sort is named by the order
   of its first appearance in a walk of the facts, in order, and then the
   goal. A datatype's constructors, selectors, and testers are named after
   its sort and their positions. Bound variables are named by their depth
   and position, so a quantifier's text does not depend on what its
   variables were called. *)
type numbering = {
  declared : (string, declaration) Hashtbl.t;
  datatypes : (string, (string * (string * sort) list) list) Hashtbl.t;
  member_of : (string, string * string) Hashtbl.t;
      (** Each constructor, selector, and tester: its datatype and its canonical suffix. *)
  symbol_names : (string, string) Hashtbl.t;
  mutable symbol_order : string list;  (** Reversed. *)
  sort_names : (string, string) Hashtbl.t;
  mutable sort_order : string list;  (** Reversed. *)
}

let rec sort_name numbering = function
  | Int -> "Int"
  | Bool -> "Bool"
  | Uninterpreted name -> (
      match Hashtbl.find_opt numbering.sort_names name with
      | Some canonical -> canonical
      | None ->
          let canonical = Printf.sprintf "S%d" (Hashtbl.length numbering.sort_names) in
          Hashtbl.replace numbering.sort_names name canonical;
          numbering.sort_order <- name :: numbering.sort_order;
          (* A datatype's fields' sorts are numbered with it. *)
          (match Hashtbl.find_opt numbering.datatypes name with
          | Some constructors ->
              List.iter
                (fun (_, fields) ->
                  List.iter (fun (_, sort) -> ignore (sort_name numbering sort)) fields)
                constructors
          | None -> ());
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
              ignore (sort_name numbering output)
          | Datatype _ -> ());
          Some canonical)

(* A function's name in the text: a datatype's member, a declared symbol,
   or one of SMT-LIB's own. *)
let function_name numbering name =
  match Hashtbl.find_opt numbering.member_of name with
  | Some (datatype, suffix) ->
      let canonical = sort_name numbering (Uninterpreted datatype) ^ suffix in
      if String.length name > 3 && String.sub name 0 3 = "is?" then
        Printf.sprintf "(_ is %s)" canonical
      else canonical
  | None -> ( match symbol_name numbering name with Some canonical -> canonical | None -> name)

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
          match Hashtbl.find_opt numbering.member_of name with
          | Some _ -> add (function_name numbering name)
          | None -> (
              match symbol_name numbering name with
              | Some canonical -> add canonical
              | None -> invalid_arg ("Logic.text: undeclared symbol " ^ name))))
  | Integer value -> add (integer_text value)
  | Boolean value -> add (if value then "true" else "false")
  | Apply (name, []) -> add (function_name numbering name)
  | Apply (name, arguments) ->
      add "(";
      add (function_name numbering name);
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
  let datatypes = Hashtbl.create 8 in
  let member_of = Hashtbl.create 32 in
  List.iter
    (fun declaration ->
      match declaration with
      | Constant (name, _) | Function (name, _, _) -> Hashtbl.replace declared name declaration
      | Datatype (name, constructors) ->
          Hashtbl.replace datatypes name constructors;
          List.iteri
            (fun index (constructor, fields) ->
              let suffix = Printf.sprintf "_c%d" index in
              Hashtbl.replace member_of constructor (name, suffix);
              Hashtbl.replace member_of (tester constructor) (name, suffix);
              List.iteri
                (fun field (selector, _) ->
                  Hashtbl.replace member_of selector (name, Printf.sprintf "%s_f%d" suffix field))
                fields)
            constructors)
    query.declarations;
  {
    declared;
    datatypes;
    member_of;
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
              (sort_name numbering output)
        | Datatype _ -> "")
      numbering.symbol_order
  in
  (* Every datatype goes in one block, so that datatypes may refer to each
     other; every other sort is declared on its own. Sorts are listed only
     once the walk above has numbered them all. *)
  let sort_order = List.rev numbering.sort_order in
  let sorts =
    List.filter_map
      (fun name ->
        if Hashtbl.mem numbering.datatypes name then None
        else Some (Printf.sprintf "(declare-sort %s 0)\n" (Hashtbl.find numbering.sort_names name)))
      sort_order
  in
  let datatypes = List.filter (Hashtbl.mem numbering.datatypes) sort_order in
  let datatype_block =
    match datatypes with
    | [] -> []
    | _ ->
        let heads =
          List.map
            (fun name -> Printf.sprintf "(%s 0)" (Hashtbl.find numbering.sort_names name))
            datatypes
        in
        let body name =
          let sort = Hashtbl.find numbering.sort_names name in
          let constructors =
            List.mapi
              (fun index (_, fields) ->
                let constructor = Printf.sprintf "%s_c%d" sort index in
                let fields =
                  List.mapi
                    (fun field (_, field_sort) ->
                      Printf.sprintf " (%s_f%d %s)" constructor field
                        (sort_name numbering field_sort))
                    fields
                in
                "(" ^ constructor ^ String.concat "" fields ^ ")")
              (Hashtbl.find numbering.datatypes name)
          in
          "(" ^ String.concat " " constructors ^ ")"
        in
        [
          Printf.sprintf "(declare-datatypes (%s) (%s))\n" (String.concat " " heads)
            (String.concat " " (List.map body datatypes));
        ]
  in
  ( String.concat "" (sorts @ datatype_block @ declarations @ assertions) ^ "(check-sat)\n",
    numbering )

let text query = fst (render query)

let symbols query =
  let _, numbering = render query in
  List.rev_map (fun name -> (name, Hashtbl.find numbering.symbol_names name)) numbering.symbol_order

let members query =
  let _, numbering = render query in
  Hashtbl.fold
    (fun name (datatype, suffix) found ->
      if String.length name > 3 && String.sub name 0 3 = "is?" then found
      else
        match Hashtbl.find_opt numbering.sort_names datatype with
        | Some sort -> (sort ^ suffix, name) :: found
        | None -> found)
    numbering.member_of []
  |> List.sort compare

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
