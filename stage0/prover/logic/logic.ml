(* The solver's logic, and the canonical text of a query. *)

type sort = Int | Bool | Float of int * int | Uninterpreted of string

module Symbol = struct
  type 'term t =
    | Variable of { label : string; numbers : int list }
    | Function of { callee : Path.t; instance : string list }
    | Function_value of { callee : Path.t; instance : string list }
    | Constant of Path.t
    | Generic_value of { owner : Path.t; name : string }
    | Literal of { type_key : string; text : string }
    | Argument of 'term
    | Lambda of { sorts : sort list; definition : 'term }
    | Over of 'term t
    | Constructor of { type_key : string; type_name : string; variant : string option }
    | Field of { type_key : string; variant : string option; field : string }
    | Unit
    | Apply of sort list
    | Equal of string
    | Valid of string
    | Rank of string
    | Capacity of string
    | Model of string
    | Slack of string
    | Potential of string
    | Potential_measure of string
    | Cursor_yielded of string
    | Cursor_ended of string
    | Block_bytes of { type_key : string; variant : string option }
    | Time of sort
    | Method_time of { method_ : Path.t; self_type : string }
    | Opaque_operation of { operation : string; type_key : string; integer : (int * bool) option }
    | Bit_count of { count : string; width : int }
    | System of string
    | Libc_number of string
    | Handle_descriptor
    | Compare_bytes_order
    | Cost_most
    | Cost_log
    | Cost_power
    | Reached of int
    | Condition of int
end

type term =
  | Symbol of symbol
  | Integer of Z.t
  | Boolean of bool
  | Bits of int * Z.t
  | Apply of symbol * term list
  | Is of symbol * term
  | Operation of string * term list
  | Forall of (symbol * sort) list * term
  | Exists of (symbol * sort) list * term

and symbol = term Symbol.t

type declaration =
  | Constant of symbol * sort
  | Function of symbol * sort list * sort
  | Datatype of string * (symbol * (symbol * sort) list) list

type query = { declarations : declaration list; facts : term list; goal : term }

(* A bit-vector literal, most significant bit first. *)
let bits_text width value =
  "#b" ^ String.init width (fun index -> if Z.testbit value (width - 1 - index) then '1' else '0')

let integer_text value =
  if Z.sign value < 0 then Printf.sprintf "(- %s)" (Z.to_string (Z.neg value))
  else Z.to_string value

let sort_text = function
  | Int -> "Int"
  | Bool -> "Bool"
  | Float (exponent, significand) -> Printf.sprintf "Float%d_%d" exponent significand
  | Uninterpreted name -> name

let instance_text = function [] -> "" | keys -> "[" ^ String.concat ", " keys ^ "]"
let variant_text = Option.value ~default:"record"

let rec show_symbol : symbol -> string = function
  | Variable { label; numbers } -> String.concat "." (label :: List.map string_of_int numbers)
  | Function { callee; instance } -> "function." ^ Path.show callee ^ instance_text instance
  | Function_value { callee; instance } -> "named." ^ Path.show callee ^ instance_text instance
  | Constant path -> "constant." ^ Path.show path
  | Generic_value { owner; name } -> Printf.sprintf "generic.%s.%s" (Path.show owner) name
  | Literal { type_key; text } -> Printf.sprintf "literal.%s.%S" type_key text
  | Argument term -> "argument(" ^ show_term term ^ ")"
  | Lambda { definition; _ } -> "lambda(" ^ show_term definition ^ ")"
  | Over symbol -> show_symbol symbol ^ ".over"
  | Constructor { type_key; variant; _ } -> "constructor." ^ type_key ^ "." ^ variant_text variant
  | Field { type_key; variant; field } ->
      "field." ^ type_key ^ "." ^ variant_text variant ^ "." ^ field
  | Unit -> "Unit.unit"
  | Apply sorts -> String.concat "." ("apply" :: List.map sort_text sorts)
  | Equal type_key -> "equal." ^ type_key
  | Valid type_key -> "valid." ^ type_key
  | Rank type_key -> "rank." ^ type_key
  | Capacity type_key -> "capacity." ^ type_key
  | Model type_key -> "model." ^ type_key
  | Slack type_key -> "slack." ^ type_key
  | Potential type_key -> "potential." ^ type_key
  | Potential_measure type_key -> "potential.measure." ^ type_key
  | Cursor_yielded type_key -> "cursor.yielded." ^ type_key
  | Cursor_ended type_key -> "cursor.ended." ^ type_key
  | Block_bytes { type_key; variant } -> "bytes." ^ type_key ^ "." ^ variant_text variant
  | Time sort -> "time." ^ sort_text sort
  | Method_time { method_; self_type } ->
      Printf.sprintf "time.method.%s[%s]" (Path.show method_) self_type
  | Opaque_operation { operation; type_key; _ } ->
      Printf.sprintf "operation.%s.%s" operation type_key
  | Bit_count { count; width } -> Printf.sprintf "bits.%s.%d" count width
  | System operation -> "system." ^ operation
  | Libc_number number -> "libc.number." ^ number
  | Handle_descriptor -> "handle.descriptor"
  | Compare_bytes_order -> "compare_bytes.order"
  | Cost_most -> "cost.most"
  | Cost_log -> "cost.log"
  | Cost_power -> "cost.power"
  | Reached index -> Printf.sprintf "reached.%d" index
  | Condition index -> Printf.sprintf "condition.%d" index

and show_term term =
  let rec show = function
    | Symbol name -> show_symbol name
    | Integer value -> integer_text value
    | Boolean value -> if value then "true" else "false"
    | Bits (width, value) -> bits_text width value
    | Apply (name, arguments) -> applied (show_symbol name) arguments
    | Operation (name, arguments) -> applied name arguments
    | Is (constructor, argument) ->
        applied (Printf.sprintf "(_ is %s)" (show_symbol constructor)) [ argument ]
    | Forall (bound, body) -> binder "forall" bound body
    | Exists (bound, body) -> binder "exists" bound body
  and applied head = function
    | [] -> head
    | arguments -> "(" ^ String.concat " " (head :: List.map show arguments) ^ ")"
  and binder word bound body =
    let sort = function
      | Int -> "Int"
      | Bool -> "Bool"
      | Float (exponent, significand) ->
          Printf.sprintf "(_ FloatingPoint %d %d)" exponent significand
      | Uninterpreted name -> name
    in
    Printf.sprintf "(%s (%s) %s)" word
      (String.concat " "
         (List.map
            (fun (name, bound_sort) ->
              Printf.sprintf "(%s %s)" (show_symbol name) (sort bound_sort))
            bound))
      (show body)
  in
  show term

let arguments = function
  | Apply (_, arguments) | Operation (_, arguments) -> arguments
  | Is (_, argument) -> [ argument ]
  | Symbol _ | Integer _ | Boolean _ | Bits _ | Forall _ | Exists _ -> []

let map_arguments transform = function
  | Apply (name, arguments) -> Apply (name, List.map transform arguments)
  | Operation (name, arguments) -> Operation (name, List.map transform arguments)
  | Is (constructor, argument) -> Is (constructor, transform argument)
  | (Symbol _ | Integer _ | Boolean _ | Bits _ | Forall _ | Exists _) as term -> term

let int value = Integer (Z.of_int value)

let ( &&& ) left right =
  match (left, right) with
  | Boolean true, other | other, Boolean true -> other
  | Boolean false, _ | _, Boolean false -> Boolean false
  | _ -> Operation ("and", [ left; right ])

let ( ||| ) left right =
  match (left, right) with
  | Boolean false, other | other, Boolean false -> other
  | Boolean true, _ | _, Boolean true -> Boolean true
  | _ -> Operation ("or", [ left; right ])

let ( ==> ) premise conclusion =
  match (premise, conclusion) with
  | Boolean true, other -> other
  | Boolean false, _ | _, Boolean true -> Boolean true
  | _ -> Operation ("=>", [ premise; conclusion ])

let not_ = function
  | Boolean value -> Boolean (not value)
  | Operation ("not", [ inner ]) -> inner
  | other -> Operation ("not", [ other ])

let equal left right = if left = right then Boolean true else Operation ("=", [ left; right ])

let ite condition then_ else_ =
  match condition with
  | Boolean true -> then_
  | Boolean false -> else_
  | _ -> if then_ = else_ then then_ else Operation ("ite", [ condition; then_; else_ ])

let conjunction terms = List.fold_left ( &&& ) (Boolean true) terms
let disjunction terms = List.fold_left ( ||| ) (Boolean false) terms
let zero = Integer Z.zero
let negate value = Operation ("-", [ value ])

(* SMT-LIB's [div] and [mod] round so that the remainder is never
   negative. Truss rounds toward zero, which agrees with them when both
   operands are at or above zero, so each sign is handled by negating. *)
let truncated_divide left right =
  let ge0 value = Operation (">=", [ value; zero ]) in
  let div dividend divisor = Operation ("div", [ dividend; divisor ]) in
  ite (ge0 left)
    (ite (ge0 right) (div left right) (negate (div left (negate right))))
    (ite (ge0 right) (negate (div (negate left) right)) (div (negate left) (negate right)))

let truncated_remainder left right =
  Operation ("-", [ left; Operation ("*", [ right; truncated_divide left right ]) ])

let rec mentions symbols = function
  | Symbol name -> List.mem name symbols
  | Integer _ | Boolean _ | Bits _ -> false
  | Apply (name, arguments) -> List.mem name symbols || List.exists (mentions symbols) arguments
  | Operation (_, arguments) -> List.exists (mentions symbols) arguments
  | Is (_, argument) -> mentions symbols argument
  | Forall (bound, body) | Exists (bound, body) ->
      let shadowed = List.map fst bound in
      mentions (List.filter (fun symbol -> not (List.mem symbol shadowed)) symbols) body

let rec free_symbols = function
  | Symbol name -> [ name ]
  | Integer _ | Boolean _ | Bits _ -> []
  | Apply (_, arguments) | Operation (_, arguments) -> List.concat_map free_symbols arguments
  | Is (_, argument) -> free_symbols argument
  | Forall (bound, body) | Exists (bound, body) ->
      List.filter (fun name -> not (List.mem_assoc name bound)) (free_symbols body)

let rec quantified = function
  | Forall _ | Exists _ -> true
  | Symbol _ | Integer _ | Boolean _ | Bits _ -> false
  | Apply (_, arguments) | Operation (_, arguments) -> List.exists quantified arguments
  | Is (_, argument) -> quantified argument

(* Each occurrence of a term, outside the quantifiers that bind its
   symbols, replaced. *)
let rec replace ~from ~into term =
  if term = from then into
  else
    match term with
    | Symbol _ | Integer _ | Boolean _ | Bits _ -> term
    | Apply (name, arguments) -> Apply (name, List.map (replace ~from ~into) arguments)
    | Operation (name, arguments) -> Operation (name, List.map (replace ~from ~into) arguments)
    | Is (constructor, argument) -> Is (constructor, replace ~from ~into argument)
    | Forall (bound, body) ->
        if mentions (List.map fst bound) from then term else Forall (bound, replace ~from ~into body)
    | Exists (bound, body) ->
        if mentions (List.map fst bound) from then term else Exists (bound, replace ~from ~into body)

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
    | Apply (name, arguments) when triggering name -> List.for_all usable arguments
    | (Apply _ | Operation _ | Is _ | Forall _ | Exists _) as term -> not (mentions names term)
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
    | Operation (_, arguments) -> List.iter walk arguments
    | Is (_, argument) -> walk argument
    | Forall _ | Exists _ | Symbol _ | Integer _ | Boolean _ | Bits _ -> ()
  in
  walk body;
  let applications = List.rev !applications in
  let bound_names_in term = List.filter (fun name -> mentions [ name ] term) names in
  let rec is_proper_subterm inner term =
    inner <> term
    &&
    match term with
    | Apply (_, arguments) | Operation (_, arguments) ->
        List.exists (fun argument -> argument = inner || is_proper_subterm inner argument) arguments
    | Is (_, argument) -> argument = inner || is_proper_subterm inner argument
    | _ -> false
  in
  (* Whether [pattern] matches [term], binding its bound variables. *)
  let rec matching bindings pattern term =
    match (pattern, bindings) with
    | _, None -> None
    | Symbol name, Some matched when List.mem name names -> (
        match List.assoc_opt name matched with
        | Some bound -> if bound = term then bindings else None
        | None -> Some ((name, term) :: matched))
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
  let rec conclusion = function
    | Operation ("=>", [ _; inner ]) -> conclusion inner
    | term -> term
  in
  match conclusion body with
  | Operation ("=", [ (Apply _ as defined); _ ])
    when candidate defined && bound_names_in defined = names ->
      [ [ defined ] ]
  | _ -> (
      let candidates = List.filter candidate applications in
      let candidates =
        List.filter
          (fun term ->
            not
              (List.exists
                 (fun inner ->
                   is_proper_subterm inner term && bound_names_in inner = bound_names_in term)
                 candidates))
          candidates
      in
      let covering_triggers candidates =
        match List.filter (fun term -> bound_names_in term = names) candidates with
        | _ :: _ as whole -> List.map (fun term -> [ term ]) whole
        | [] ->
            List.concat_map
              (fun first ->
                List.filter_map
                  (fun second ->
                    if
                      first < second
                      && List.for_all
                           (fun name ->
                             List.mem name (bound_names_in first @ bound_names_in second))
                           names
                    then Some [ first; second ]
                    else None)
                  candidates)
              candidates
      in
      match covering_triggers (List.filter (fun term -> not (loops term)) candidates) with
      | [] -> covering_triggers candidates
      | triggers -> triggers)

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

(* Whether a fact of a query is quantified with no trigger, so the solver
   chooses its own way to use it, or none. A fact under a path's condition
   is read through it. *)
let untriggered query =
  let triggering = triggering_in query.declarations in
  let rec without = function
    | Operation ("=>", [ _; inner ]) -> without inner
    | Forall (variables, body) -> triggers ~triggering variables body = []
    | _ -> false
  in
  List.exists without query.facts

(* The declared symbols a term mentions. A datatype's constructors and
   selectors are shared vocabulary, like SMT-LIB's own operations, so they
   connect nothing. *)
let declared_symbols declared term =
  let symbols = ref [] in
  let rec walk bound = function
    | Symbol name ->
        if (not (List.mem name bound)) && Hashtbl.mem declared name then symbols := name :: !symbols
    | Integer _ | Boolean _ | Bits _ -> ()
    | Apply (name, arguments) ->
        if Hashtbl.mem declared name then symbols := name :: !symbols;
        List.iter (walk bound) arguments
    | Operation (_, arguments) -> List.iter (walk bound) arguments
    | Is (_, argument) -> walk bound argument
    | Forall (variables, body) | Exists (variables, body) ->
        walk (List.map fst variables @ bound) body
  in
  walk [] term;
  !symbols

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
    | Operation ("=>", [ _; (Forall _ as inner) ]) -> needs inner symbols
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
  let is_needed = Array.make (Array.length facts) false in
  let changed = ref true in
  while !changed do
    changed := false;
    Array.iteri
      (fun index (symbols, ready) ->
        if (not is_needed.(index)) && ready () then begin
          is_needed.(index) <- true;
          reach symbols;
          changed := true
        end)
      facts
  done;
  { query with facts = List.filteri (fun index _ -> is_needed.(index)) query.facts }

(* Numbering: every declared symbol and every sort is named by the order
   of its first appearance in a walk of the facts, in order, and then the
   goal. A datatype's constructors and selectors are named after
   its sort and their positions. Bound variables are named by their depth
   and position, so a quantifier's text does not depend on what its
   variables were called. *)
type numbering = {
  declared : (symbol, declaration) Hashtbl.t;
  datatypes : (string, (symbol * (symbol * sort) list) list) Hashtbl.t;
  member_of : (symbol, string * string) Hashtbl.t;
      (** Each constructor and selector: its datatype and its canonical suffix. *)
  triggering : symbol -> bool;
  symbol_names : (symbol, string) Hashtbl.t;
  symbol_order : symbol Dynarray.t;
  sort_names : (string, string) Hashtbl.t;
  sort_order : string Dynarray.t;
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
          Dynarray.add_last numbering.sort_order name;
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
          Dynarray.add_last numbering.symbol_order name;
          (* The sorts a declaration mentions are numbered with it. *)
          (match declaration with
          | Constant (_, sort) -> ignore (sort_name numbering sort)
          | Function (_, inputs, output) ->
              List.iter (fun sort -> ignore (sort_name numbering sort)) inputs;
              ignore (sort_name numbering output)
          | Datatype _ -> ());
          Some canonical)

let member_name numbering name =
  Option.map
    (fun (datatype, suffix) -> sort_name numbering (Uninterpreted datatype) ^ suffix)
    (Hashtbl.find_opt numbering.member_of name)

(* A function's name in the text: a datatype's member or a declared symbol. *)
let function_name numbering name =
  match member_name numbering name with
  | Some canonical -> canonical
  | None -> (
      match symbol_name numbering name with
      | Some canonical -> canonical
      | None -> invalid_arg ("Logic.text: undeclared symbol " ^ show_symbol name))

let rec print numbering bound buffer term =
  let add = Buffer.add_string buffer in
  match term with
  | Symbol name -> (
      match List.assoc_opt name bound with
      | Some canonical -> add canonical
      | None -> add (function_name numbering name))
  | Integer value -> add (integer_text value)
  | Boolean value -> add (if value then "true" else "false")
  | Bits (width, value) -> add (bits_text width value)
  | Apply (name, arguments) ->
      application numbering bound buffer (function_name numbering name) arguments
  | Operation (name, arguments) -> application numbering bound buffer name arguments
  | Is (constructor, argument) ->
      application numbering bound buffer
        (Printf.sprintf "(_ is %s)" (function_name numbering constructor))
        [ argument ]
  | Forall (variables, body) -> quantifier numbering bound buffer "forall" variables body
  | Exists (variables, body) -> quantifier numbering bound buffer "exists" variables body

and application numbering bound buffer head = function
  | [] -> Buffer.add_string buffer head
  | arguments ->
      Buffer.add_string buffer "(";
      Buffer.add_string buffer head;
      List.iter
        (fun argument ->
          Buffer.add_string buffer " ";
          print numbering bound buffer argument)
        arguments;
      Buffer.add_string buffer ")"

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
    symbol_order = Dynarray.create ();
    sort_names = Hashtbl.create 8;
    sort_order = Dynarray.create ();
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
    List.map
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
      (Dynarray.to_list numbering.symbol_order)
  in
  (* Every datatype goes in one block, so that datatypes may refer to each
     other; every other sort is declared on its own. Sorts are listed only
     once the walk above has numbered them all. *)
  let sort_order = Dynarray.to_list numbering.sort_order in
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

let term_text query term =
  let _, numbering = render query in
  (* A symbol the query declares but its text does not mention has no
     canonical name, and the solver would not know it. *)
  let rec named = function
    | Symbol name -> Hashtbl.mem numbering.symbol_names name
    | Integer _ | Boolean _ | Bits _ -> true
    | Apply (name, arguments) ->
        (Hashtbl.mem numbering.member_of name || Hashtbl.mem numbering.symbol_names name)
        && List.for_all named arguments
    | Operation (_, arguments) -> List.for_all named arguments
    | Is (constructor, argument) -> Hashtbl.mem numbering.member_of constructor && named argument
    | Forall _ | Exists _ -> false
  in
  if named term then begin
    let buffer = Buffer.create 64 in
    print numbering [] buffer term;
    Some (Buffer.contents buffer)
  end
  else None

let symbols query =
  let _, numbering = render query in
  List.map
    (fun name -> (name, Hashtbl.find numbering.symbol_names name))
    (Dynarray.to_list numbering.symbol_order)

let members query =
  let _, numbering = render query in
  Hashtbl.fold
    (fun datatype constructors entries ->
      match Hashtbl.find_opt numbering.sort_names datatype with
      | Some sort ->
          List.mapi
            (fun index (constructor, fields) ->
              (Printf.sprintf "%s_c%d" sort index, (constructor, List.map fst fields)))
            constructors
          @ entries
      | None -> entries)
    numbering.datatypes []
  |> List.sort compare

let hash text = "smt1-blake3-" ^ Blake3.hex_digest text
