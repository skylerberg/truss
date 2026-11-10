(* The solver's logic, and the canonical text of a query. *)

type sort = Int | Bool | Float of int * int | Uninterpreted of string

type term =
  | Symbol of string
  | Integer of Z.t
  | Boolean of bool
  | Bits of int * Z.t
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
  | Integer _ | Boolean _ | Bits _ -> false
  | Apply (name, arguments) -> List.mem name symbols || List.exists (mentions symbols) arguments
  | Forall (bound, body) | Exists (bound, body) ->
      let shadowed = List.map fst bound in
      mentions (List.filter (fun symbol -> not (List.mem symbol shadowed)) symbols) body

(* Each occurrence of a term, outside the quantifiers that bind its
   symbols, replaced. *)
let rec replace ~from ~into term =
  if term = from then into
  else
    match term with
    | Symbol _ | Integer _ | Boolean _ | Bits _ -> term
    | Apply (name, arguments) -> Apply (name, List.map (replace ~from ~into) arguments)
    | Forall (bound, body) ->
        if mentions (List.map fst bound) from then term else Forall (bound, replace ~from ~into body)
    | Exists (bound, body) ->
        if mentions (List.map fst bound) from then term else Exists (bound, replace ~from ~into body)

(* Triggers *)

(* The terms that make the solver use a quantified statement, as Dafny
   chooses them: sets of applications of the query's own functions that
   together name every bound variable, each variable as an argument and not
   under arithmetic, since the solver matches a trigger by its shape. An
   application that contains another with the same variables is left out
   for the smaller one, and so is one that the statement's own body would
   match with a larger term, which would use the statement again and again,
   unless nothing else is left. An equation that defines a function on its
   left side is triggered by that side alone. With no trigger, the solver
   chooses its own. *)
let triggers ~triggering variables body =
  let names = List.map fst variables in
  let rec usable = function
    | Symbol _ | Integer _ | Boolean _ | Bits _ -> true
    | Apply (name, arguments) ->
        if triggering name then List.for_all usable arguments
        else not (mentions names (Apply (name, arguments)))
    | (Forall _ | Exists _) as term -> not (mentions names term)
  in
  let candidate = function
    | Apply (name, _ :: _) as term -> triggering name && mentions names term && usable term
    | _ -> false
  in
  let applications = ref [] in
  let rec walk term =
    match term with
    | Apply (_, arguments) ->
        if not (List.mem term !applications) then applications := term :: !applications;
        List.iter walk arguments
    | Forall _ | Exists _ | Symbol _ | Integer _ | Boolean _ | Bits _ -> ()
  in
  walk body;
  let applications = List.rev !applications in
  let covers term = List.filter (fun name -> mentions [ name ] term) names in
  let rec within inner term =
    inner <> term
    &&
    match term with
    | Apply (_, arguments) ->
        List.exists (fun argument -> argument = inner || within inner argument) arguments
    | _ -> false
  in
  (* Whether [pattern] matches [term], binding its bound variables. *)
  let rec matching bindings pattern term =
    match (pattern, bindings) with
    | _, None -> None
    | Symbol name, Some found when List.mem name names -> (
        match List.assoc_opt name found with
        | Some bound -> if bound = term then bindings else None
        | None -> Some ((name, term) :: found))
    | Apply (name, arguments), _ -> (
        match term with
        | Apply (other, others) when name = other && List.length arguments = List.length others ->
            List.fold_left2 matching bindings arguments others
        | _ -> None)
    | _ -> if pattern = term then bindings else None
  in
  let loops trigger =
    List.exists
      (fun term ->
        term <> trigger
        &&
        match matching (Some []) trigger term with
        | Some bindings ->
            List.exists (fun (name, bound) -> bound <> Symbol name && mentions names bound) bindings
        | None -> false)
      applications
  in
  let rec conclusion = function Apply ("=>", [ _; inner ]) -> conclusion inner | term -> term in
  match conclusion body with
  | Apply ("=", [ (Apply _ as defined); _ ]) when candidate defined && covers defined = names ->
      [ [ defined ] ]
  | _ -> (
      let candidates = List.filter candidate applications in
      let candidates =
        List.filter
          (fun term ->
            not
              (List.exists
                 (fun inner -> within inner term && covers inner = covers term)
                 candidates))
          candidates
      in
      let chosen candidates =
        match List.filter (fun term -> covers term = names) candidates with
        | _ :: _ as whole -> List.map (fun term -> [ term ]) whole
        | [] ->
            List.concat_map
              (fun first ->
                List.filter_map
                  (fun second ->
                    if
                      first < second
                      && List.for_all
                           (fun name -> List.mem name (covers first @ covers second))
                           names
                    then Some [ first; second ]
                    else None)
                  candidates)
              candidates
      in
      match chosen (List.filter (fun term -> not (loops term)) candidates) with
      | [] -> chosen candidates
      | found -> found)

(* The functions a trigger may apply: a declared function or a datatype's
   constructor or selector. *)
let triggering_in declarations =
  let functions = Hashtbl.create 64 in
  List.iter
    (function
      | Function (name, _, _) -> Hashtbl.replace functions name ()
      | Datatype (_, constructors) ->
          List.iter
            (fun (constructor, fields) ->
              Hashtbl.replace functions constructor ();
              List.iter (fun (selector, _) -> Hashtbl.replace functions selector ()) fields)
            constructors
      | Constant _ -> ())
    declarations;
  Hashtbl.mem functions

(* Pruning *)

(* The declared symbols a term mentions. A datatype's constructors and
   selectors are shared vocabulary, like SMT-LIB's own operations, so they
   connect nothing. *)
let declared_symbols declared term =
  let found = ref [] in
  let rec walk bound = function
    | Symbol name ->
        if (not (List.mem name bound)) && Hashtbl.mem declared name then found := name :: !found
    | Integer _ | Boolean _ | Bits _ -> ()
    | Apply (name, arguments) ->
        if Hashtbl.mem declared name then found := name :: !found;
        List.iter (walk bound) arguments
    | Forall (variables, body) | Exists (variables, body) ->
        walk (List.map fst variables @ bound) body
  in
  walk [] term;
  !found

let prune query =
  let declared = Hashtbl.create 64 in
  List.iter
    (function
      | Constant (name, _) | Function (name, _, _) -> Hashtbl.replace declared name ()
      | Datatype _ -> ())
    query.declarations;
  let reached = Hashtbl.create 64 in
  let reach symbols = List.iter (fun symbol -> Hashtbl.replace reached symbol ()) symbols in
  reach (declared_symbols declared query.goal);
  let triggering = triggering_in query.declarations in
  (* A quantified fact can be used only where terms of the shape of one of
     its triggers are, so it waits until each symbol of one of them is
     kept. A fact under a path's condition is read through it. *)
  let rec needs fact symbols =
    match fact with
    | Apply ("=>", [ _; (Forall _ as inner) ]) -> needs inner symbols
    | Forall (variables, body) -> (
        match triggers ~triggering variables body with
        | [] -> fun () -> List.exists (Hashtbl.mem reached) symbols
        | triggers ->
            let triggers = List.map (List.concat_map (declared_symbols declared)) triggers in
            fun () ->
              List.exists (fun trigger -> List.for_all (Hashtbl.mem reached) trigger) triggers)
    | _ -> fun () -> List.exists (Hashtbl.mem reached) symbols
  in
  let facts =
    Array.of_list
      (List.map
         (fun fact ->
           let symbols = declared_symbols declared fact in
           (symbols, needs fact symbols))
         query.facts)
  in
  let kept = Array.make (Array.length facts) false in
  let changed = ref true in
  while !changed do
    changed := false;
    Array.iteri
      (fun index (symbols, ready) ->
        if (not kept.(index)) && ready () then begin
          kept.(index) <- true;
          reach symbols;
          changed := true
        end)
      facts
  done;
  { query with facts = List.filteri (fun index _ -> kept.(index)) query.facts }

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
  triggering : string -> bool;
  symbol_names : (string, string) Hashtbl.t;
  mutable symbol_order : string list;  (** Reversed. *)
  sort_names : (string, string) Hashtbl.t;
  mutable sort_order : string list;  (** Reversed. *)
}

let rec sort_name numbering = function
  | Int -> "Int"
  | Bool -> "Bool"
  | Float (exponent, significand) -> Printf.sprintf "(_ FloatingPoint %d %d)" exponent significand
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

(* A bit-vector literal, most significant bit first. *)
let bits_text width value =
  "#b" ^ String.init width (fun index -> if Z.testbit value (width - 1 - index) then '1' else '0')

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
  | Bits (width, value) -> add (bits_text width value)
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
  let bound = List.map (fun (name, canonical, _) -> (name, canonical)) named @ bound in
  match triggers ~triggering:numbering.triggering variables body with
  | [] ->
      print numbering bound buffer body;
      add ")"
  | triggers ->
      add "(! ";
      print numbering bound buffer body;
      List.iter
        (fun trigger ->
          add " :pattern (";
          List.iteri
            (fun index term ->
              if index > 0 then add " ";
              print numbering bound buffer term)
            trigger;
          add ")")
        triggers;
      add "))"

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
    triggering = triggering_in query.declarations;
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
    (fun datatype constructors found ->
      match Hashtbl.find_opt numbering.sort_names datatype with
      | Some sort ->
          List.mapi
            (fun index (constructor, fields) ->
              (Printf.sprintf "%s_c%d" sort index, (constructor, List.map fst fields)))
            constructors
          @ found
      | None -> found)
    numbering.datatypes []
  |> List.sort compare

let hash text = "smt1-blake3-" ^ Blake3.to_hex (Blake3.hash text)

let show_term term =
  let rec show = function
    | Symbol name -> name
    | Integer value -> integer_text value
    | Boolean value -> if value then "true" else "false"
    | Bits (width, value) -> bits_text width value
    | Apply (name, []) -> name
    | Apply (name, arguments) -> "(" ^ String.concat " " (name :: List.map show arguments) ^ ")"
    | Forall (bound, body) -> binder "forall" bound body
    | Exists (bound, body) -> binder "exists" bound body
  and binder word bound body =
    let sort = function
      | Int -> "Int"
      | Bool -> "Bool"
      | Float (exponent, significand) ->
          Printf.sprintf "(_ FloatingPoint %d %d)" exponent significand
      | Uninterpreted name -> name
    in
    Printf.sprintf "(%s (%s) %s)" word
      (String.concat " " (List.map (fun (name, s) -> Printf.sprintf "(%s %s)" name (sort s)) bound))
      (show body)
  in
  show term
