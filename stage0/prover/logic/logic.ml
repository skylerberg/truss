type sort = Int | Bool | Float of int * int | Type_sort of Types.ty | Function_sort of int

module Symbol = struct
  type 'term t =
    | Variable of { label : string; numbers : int list }
    | Function of { callee : Path.t; instance : Types.argument list }
    | Limited of { callee : Path.t; instance : Types.argument list }
    | Function_value of { callee : Path.t; instance : Types.argument list }
    | Constant of Path.t
    | Generic_value of { owner : Path.t; name : string }
    | Text_literal of { type_ : Types.ty; text : string }
    | Named_term of 'term
    | Lambda of { sorts : sort list; definition : 'term }
    | Lifted of 'term t
    | Constructor of { type_ : Types.ty; variant : string option }
    | Field of { type_ : Types.ty; variant : string option; field : string }
    | Unit
    | Apply of sort list
    | Equal of Types.ty
    | Valid of Types.ty
    | Rank of Types.ty
    | Capacity of Types.ty
    | Model of Types.ty
    | Slack of Types.ty
    | Potential of Types.ty
    | Potential_measure of Types.ty
    | Block_bytes of { type_ : Types.ty; variant : string option }
    | Time of sort
    | Method_time of {
        method_ : Path.t;
        trait_arguments : Types.argument list;
        self_type : Types.ty;
      }
    | Opaque_operation of {
        operation : Intrinsic.operation;
        type_ : Types.ty;
        integer : (int * bool) option;
      }
    | Bit_count of { count : Intrinsic.operation; width : int }
    | System of Intrinsic.operation
    | Libc_number of Libc.number
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
  | Forall of (symbol * sort) list * term list * term
  | Exists of (symbol * sort) list * term

and symbol = term Symbol.t

type declaration =
  | Constant of symbol * sort
  | Function of symbol * sort list * sort
  | Datatype of Types.ty * (symbol * (symbol * sort) list) list

type query = { declarations : declaration list; facts : term list; goal : term }

module Sort_table = Hashtbl.Make (Structural_key.Make (struct
  type t = sort
end))

module Symbol_table = Hashtbl.Make (Structural_key.Make (struct
  type t = symbol
end))

module Term_table = Hashtbl.Make (Structural_key.Make (struct
  type t = term
end))

let show_bits width value =
  "#b" ^ String.init width (fun index -> if Z.testbit value (width - 1 - index) then '1' else '0')

let show_integer value =
  if Z.sign value < 0 then Printf.sprintf "(- %s)" (Z.to_string (Z.neg value))
  else Z.to_string value

let show_sort = function
  | Int -> "Int"
  | Bool -> "Bool"
  | Float (exponent, significand) -> Printf.sprintf "Float%d_%d" exponent significand
  | Type_sort ty -> Types.show ty
  | Function_sort arity -> Printf.sprintf "function/%d" arity

let instance_text = function
  | [] -> ""
  | arguments -> "[" ^ String.concat ", " (List.map Types.show_argument arguments) ^ "]"

let variant_text = Option.value ~default:"record"

let rec show_symbol : symbol -> string = function
  | Variable { label; numbers } -> String.concat "." (label :: List.map string_of_int numbers)
  | Function { callee; instance } -> "function." ^ Path.show callee ^ instance_text instance
  | Limited { callee; instance } -> "limited." ^ Path.show callee ^ instance_text instance
  | Function_value { callee; instance } -> "named." ^ Path.show callee ^ instance_text instance
  | Constant path -> "constant." ^ Path.show path
  | Generic_value { owner; name } -> Printf.sprintf "generic.%s.%s" (Path.show owner) name
  | Text_literal { type_; text } -> Printf.sprintf "text_literal.%s.%S" (Types.show type_) text
  | Named_term term -> "named_term(" ^ show_term term ^ ")"
  | Lambda { definition; _ } -> "lambda(" ^ show_term definition ^ ")"
  | Lifted symbol -> show_symbol symbol ^ ".lifted"
  | Constructor { type_; variant } -> "constructor." ^ Types.show type_ ^ "." ^ variant_text variant
  | Field { type_; variant; field } ->
      "field." ^ Types.show type_ ^ "." ^ variant_text variant ^ "." ^ field
  | Unit -> "Unit.unit"
  | Apply sorts -> String.concat "." ("apply" :: List.map show_sort sorts)
  | Equal ty -> "equal." ^ Types.show ty
  | Valid ty -> "valid." ^ Types.show ty
  | Rank ty -> "rank." ^ Types.show ty
  | Capacity ty -> "capacity." ^ Types.show ty
  | Model ty -> "model." ^ Types.show ty
  | Slack ty -> "slack." ^ Types.show ty
  | Potential ty -> "potential." ^ Types.show ty
  | Potential_measure ty -> "potential.measure." ^ Types.show ty
  | Block_bytes { type_; variant } -> "bytes." ^ Types.show type_ ^ "." ^ variant_text variant
  | Time sort -> "time." ^ show_sort sort
  | Method_time { method_; trait_arguments; self_type } ->
      Printf.sprintf "time.method.%s%s[%s]" (Path.show method_) (instance_text trait_arguments)
        (Types.show self_type)
  | Opaque_operation { operation; type_; _ } ->
      Printf.sprintf "operation.%s.%s" (Intrinsic.operation_name operation) (Types.show type_)
  | Bit_count { count; width } -> Printf.sprintf "bits.%s.%d" (Intrinsic.operation_name count) width
  | System operation -> "system." ^ Intrinsic.operation_name operation
  | Libc_number number -> "libc.number." ^ Libc.number_name number
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
    | Integer value -> show_integer value
    | Boolean value -> if value then "true" else "false"
    | Bits (width, value) -> show_bits width value
    | Apply (name, arguments) -> applied (show_symbol name) arguments
    | Operation (name, arguments) -> applied name arguments
    | Is (constructor, argument) ->
        applied (Printf.sprintf "(_ is %s)" (show_symbol constructor)) [ argument ]
    | Forall (bound, _, body) -> binder "forall" bound body
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
      | (Type_sort _ | Function_sort _) as sort -> show_sort sort
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
  | Forall (bound, _, body) | Exists (bound, body) ->
      let shadowed = List.map fst bound in
      mentions (List.filter (fun symbol -> not (List.mem symbol shadowed)) symbols) body

let rec list_free_constants = function
  | Symbol name -> [ name ]
  | Integer _ | Boolean _ | Bits _ -> []
  | Apply (_, arguments) | Operation (_, arguments) -> List.concat_map list_free_constants arguments
  | Is (_, argument) -> list_free_constants argument
  | Forall (bound, _, body) | Exists (bound, body) ->
      List.filter (fun name -> not (List.mem_assoc name bound)) (list_free_constants body)

let rec has_quantifier = function
  | Forall _ | Exists _ -> true
  | Symbol _ | Integer _ | Boolean _ | Bits _ -> false
  | Apply (_, arguments) | Operation (_, arguments) -> List.exists has_quantifier arguments
  | Is (_, argument) -> has_quantifier argument

let rec replace ~from ~into term =
  if term = from then into
  else
    match term with
    | Symbol _ | Integer _ | Boolean _ | Bits _ -> term
    | Apply (name, arguments) -> Apply (name, List.map (replace ~from ~into) arguments)
    | Operation (name, arguments) -> Operation (name, List.map (replace ~from ~into) arguments)
    | Is (constructor, argument) -> Is (constructor, replace ~from ~into argument)
    | Forall (bound, trigger, body) ->
        if mentions (List.map fst bound) from then term
        else Forall (bound, List.map (replace ~from ~into) trigger, replace ~from ~into body)
    | Exists (bound, body) ->
        if mentions (List.map fst bound) from then term else Exists (bound, replace ~from ~into body)

let rec substitute substitution term =
  match term with
  | Symbol name -> ( match List.assoc_opt name substitution with Some into -> into | None -> term)
  | Integer _ | Boolean _ | Bits _ -> term
  | Apply (name, arguments) -> Apply (name, List.map (substitute substitution) arguments)
  | Operation (name, arguments) -> Operation (name, List.map (substitute substitution) arguments)
  | Is (constructor, argument) -> Is (constructor, substitute substitution argument)
  | Forall (bound, trigger, body) ->
      let inner = remove_bound bound substitution in
      Forall (bound, List.map (substitute inner) trigger, substitute inner body)
  | Exists (bound, body) -> Exists (bound, substitute (remove_bound bound substitution) body)

and remove_bound bound substitution =
  List.filter (fun (name, _) -> not (List.mem_assoc name bound)) substitution

let list_triggers ~triggering variables body =
  let names = List.map fst variables in
  let rec is_trigger_term = function
    | Symbol _ | Integer _ | Boolean _ | Bits _ -> true
    | Apply (name, arguments) when triggering name -> List.for_all is_trigger_term arguments
    | (Apply _ | Operation _ | Is _ | Forall _ | Exists _) as term -> not (mentions names term)
  in
  let candidate = function
    | Apply (name, _ :: _) as term -> triggering name && mentions names term && is_trigger_term term
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
  let makes_matching_loop trigger =
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
  let names_every_variable term = candidate term && bound_names_in term = names in
  match conclusion body with
  | Operation ("=", [ (Apply _ as defined); other ])
    when names_every_variable defined && not (names_every_variable other) ->
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
      let with_same_functions trigger =
        let function_of = function Apply (name, _) -> Some name | _ -> None in
        let functions = List.map function_of trigger in
        trigger
        @ List.filter
            (fun term -> (not (List.mem term trigger)) && List.mem (function_of term) functions)
            candidates
        |> List.sort compare
      in
      let covering_triggers candidates =
        match List.filter (fun term -> bound_names_in term = names) candidates with
        | _ :: _ as covering -> List.map (fun term -> [ term ]) covering
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
                    then Some (with_same_functions [ first; second ])
                    else None)
                  candidates)
              candidates
            |> List.sort_uniq compare
      in
      match
        covering_triggers (List.filter (fun term -> not (makes_matching_loop term)) candidates)
      with
      | [] -> covering_triggers candidates
      | triggers -> triggers)

let forall ?(trigger = []) (variables, body) =
  match variables with [] -> body | _ -> Forall (variables, trigger, body)

let choose_triggers ~triggering variables trigger body =
  match trigger with [] -> list_triggers ~triggering variables body | terms -> [ terms ]

let make_triggering_test declarations =
  let functions = Symbol_table.create 64 in
  List.iter
    (function
      | Function (name, _, _) -> Symbol_table.replace functions name ()
      | Datatype (_, constructors) ->
          List.iter
            (fun (constructor, fields) ->
              Symbol_table.replace functions constructor ();
              List.iter (fun (selector, _) -> Symbol_table.replace functions selector ()) fields)
            constructors
      | Constant _ -> ())
    declarations;
  Symbol_table.mem functions

let has_untriggered_fact query =
  let triggering = make_triggering_test query.declarations in
  let rec without = function
    | Operation ("=>", [ _; inner ]) -> without inner
    | Forall (variables, trigger, body) -> choose_triggers ~triggering variables trigger body = []
    | _ -> false
  in
  List.exists without query.facts

let list_declared_symbols declared term =
  let symbols = ref [] in
  let rec walk bound = function
    | Symbol name ->
        if (not (List.mem name bound)) && Symbol_table.mem declared name then
          symbols := name :: !symbols
    | Integer _ | Boolean _ | Bits _ -> ()
    | Apply (name, arguments) ->
        if Symbol_table.mem declared name then symbols := name :: !symbols;
        List.iter (walk bound) arguments
    | Operation (_, arguments) -> List.iter (walk bound) arguments
    | Is (_, argument) -> walk bound argument
    | Forall (variables, _, body) | Exists (variables, body) ->
        walk (List.map fst variables @ bound) body
  in
  walk [] term;
  !symbols

let prune query =
  let declared = Symbol_table.create 64 in
  List.iter
    (function
      | Constant (name, _) | Function (name, _, _) -> Symbol_table.replace declared name ()
      | Datatype _ -> ())
    query.declarations;
  let reached = Symbol_table.create 64 in
  let reach symbols = List.iter (fun symbol -> Symbol_table.replace reached symbol ()) symbols in
  reach (list_declared_symbols declared query.goal);
  let triggering = make_triggering_test query.declarations in
  let rec needs fact symbols =
    match fact with
    | Operation ("=>", [ _; (Forall _ as inner) ]) -> needs inner symbols
    | Forall (variables, trigger, body) -> (
        match choose_triggers ~triggering variables trigger body with
        | [] -> fun () -> List.exists (Symbol_table.mem reached) symbols
        | triggers ->
            let triggers = List.map (List.concat_map (list_declared_symbols declared)) triggers in
            fun () ->
              List.exists (fun trigger -> List.for_all (Symbol_table.mem reached) trigger) triggers)
    | _ -> fun () -> List.exists (Symbol_table.mem reached) symbols
  in
  let distinct =
    let seen = Term_table.create 64 in
    List.filter
      (fun fact ->
        let is_new = not (Term_table.mem seen fact) in
        Term_table.replace seen fact ();
        is_new)
      query.facts
  in
  let query = { query with facts = distinct } in
  let facts =
    Array.of_list
      (List.map
         (fun fact ->
           let symbols = list_declared_symbols declared fact in
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

type numbering = {
  declared : declaration Symbol_table.t;
  datatypes : (symbol * (symbol * sort) list) list Sort_table.t;
  member_of : (sort * string) Symbol_table.t;
  triggering : symbol -> bool;
  symbol_names : string Symbol_table.t;
  symbol_order : symbol Dynarray.t;
  sort_names : string Sort_table.t;
  sort_order : sort Dynarray.t;
}

let rec render_sort_name numbering = function
  | Int -> "Int"
  | Bool -> "Bool"
  | Float (exponent, significand) -> Printf.sprintf "(_ FloatingPoint %d %d)" exponent significand
  | (Type_sort _ | Function_sort _) as sort -> (
      match Sort_table.find_opt numbering.sort_names sort with
      | Some canonical -> canonical
      | None ->
          let canonical = Printf.sprintf "S%d" (Sort_table.length numbering.sort_names) in
          Sort_table.replace numbering.sort_names sort canonical;
          Dynarray.add_last numbering.sort_order sort;
          (match Sort_table.find_opt numbering.datatypes sort with
          | Some constructors ->
              List.iter
                (fun (_, fields) ->
                  List.iter (fun (_, sort) -> ignore (render_sort_name numbering sort)) fields)
                constructors
          | None -> ());
          canonical)

let render_symbol_name numbering name =
  match Symbol_table.find_opt numbering.symbol_names name with
  | Some canonical -> Some canonical
  | None -> (
      match Symbol_table.find_opt numbering.declared name with
      | None -> None
      | Some declaration ->
          let canonical = Printf.sprintf "x%d" (Symbol_table.length numbering.symbol_names) in
          Symbol_table.replace numbering.symbol_names name canonical;
          Dynarray.add_last numbering.symbol_order name;
          (match declaration with
          | Constant (_, sort) -> ignore (render_sort_name numbering sort)
          | Function (_, inputs, output) ->
              List.iter (fun sort -> ignore (render_sort_name numbering sort)) inputs;
              ignore (render_sort_name numbering output)
          | Datatype _ -> ());
          Some canonical)

let render_member_name numbering name =
  Option.map
    (fun (datatype, suffix) -> render_sort_name numbering datatype ^ suffix)
    (Symbol_table.find_opt numbering.member_of name)

let render_function_name numbering name =
  match render_member_name numbering name with
  | Some canonical -> canonical
  | None -> (
      match render_symbol_name numbering name with
      | Some canonical -> canonical
      | None -> invalid_arg ("Logic.text: undeclared symbol " ^ show_symbol name))

let rec print numbering bound buffer term =
  let add = Buffer.add_string buffer in
  match term with
  | Symbol name -> (
      match List.assoc_opt name bound with
      | Some canonical -> add canonical
      | None -> add (render_function_name numbering name))
  | Integer value -> add (show_integer value)
  | Boolean value -> add (if value then "true" else "false")
  | Bits (width, value) -> add (show_bits width value)
  | Apply (name, arguments) ->
      render_application numbering bound buffer (render_function_name numbering name) arguments
  | Operation (name, arguments) -> render_application numbering bound buffer name arguments
  | Is (constructor, argument) ->
      render_application numbering bound buffer
        (Printf.sprintf "(_ is %s)" (render_function_name numbering constructor))
        [ argument ]
  | Forall (variables, trigger, body) ->
      render_quantifier numbering bound buffer "forall" variables trigger body
  | Exists (variables, body) -> render_quantifier numbering bound buffer "exists" variables [] body

and render_application numbering bound buffer head = function
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

and render_quantifier numbering bound buffer word variables trigger body =
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
      add (Printf.sprintf "(%s %s)" canonical (render_sort_name numbering sort)))
    named;
  add ") ";
  let bound = List.map (fun (name, canonical, _) -> (name, canonical)) named @ bound in
  match choose_triggers ~triggering:numbering.triggering variables trigger body with
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

let number_symbols query =
  let declared = Symbol_table.create 64 in
  let datatypes = Sort_table.create 8 in
  let member_of = Symbol_table.create 32 in
  List.iter
    (fun declaration ->
      match declaration with
      | Constant (name, _) | Function (name, _, _) -> Symbol_table.replace declared name declaration
      | Datatype (ty, constructors) ->
          let sort = Type_sort ty in
          Sort_table.replace datatypes sort constructors;
          List.iteri
            (fun index (constructor, fields) ->
              let suffix = Printf.sprintf "_c%d" index in
              Symbol_table.replace member_of constructor (sort, suffix);
              List.iteri
                (fun field (selector, _) ->
                  Symbol_table.replace member_of selector
                    (sort, Printf.sprintf "%s_f%d" suffix field))
                fields)
            constructors)
    query.declarations;
  {
    declared;
    datatypes;
    member_of;
    triggering = make_triggering_test query.declarations;
    symbol_names = Symbol_table.create 64;
    symbol_order = Dynarray.create ();
    sort_names = Sort_table.create 8;
    sort_order = Dynarray.create ();
  }

type rendering = { text : string; numbering : numbering }

let render query =
  let numbering = number_symbols query in
  let assertion term =
    let buffer = Buffer.create 128 in
    Buffer.add_string buffer "(assert ";
    print numbering [] buffer term;
    Buffer.add_string buffer ")\n";
    Buffer.contents buffer
  in
  let negated_goal = assertion (not_ query.goal) in
  let assertions = List.map assertion query.facts @ [ negated_goal ] in
  let declarations =
    List.map
      (fun name ->
        let canonical = Symbol_table.find numbering.symbol_names name in
        match Symbol_table.find numbering.declared name with
        | Constant (_, sort) ->
            Printf.sprintf "(declare-fun %s () %s)\n" canonical (render_sort_name numbering sort)
        | Function (_, inputs, output) ->
            Printf.sprintf "(declare-fun %s (%s) %s)\n" canonical
              (String.concat " " (List.map (render_sort_name numbering) inputs))
              (render_sort_name numbering output)
        | Datatype _ -> "")
      (Dynarray.to_list numbering.symbol_order)
  in
  let sort_order = Dynarray.to_list numbering.sort_order in
  let sorts =
    List.filter_map
      (fun name ->
        if Sort_table.mem numbering.datatypes name then None
        else
          Some (Printf.sprintf "(declare-sort %s 0)\n" (Sort_table.find numbering.sort_names name)))
      sort_order
  in
  let datatypes = List.filter (Sort_table.mem numbering.datatypes) sort_order in
  let datatype_block =
    match datatypes with
    | [] -> []
    | _ ->
        let heads =
          List.map
            (fun name -> Printf.sprintf "(%s 0)" (Sort_table.find numbering.sort_names name))
            datatypes
        in
        let body name =
          let sort = Sort_table.find numbering.sort_names name in
          let constructors =
            List.mapi
              (fun index (_, fields) ->
                let constructor = Printf.sprintf "%s_c%d" sort index in
                let fields =
                  List.mapi
                    (fun field (_, field_sort) ->
                      Printf.sprintf " (%s_f%d %s)" constructor field
                        (render_sort_name numbering field_sort))
                    fields
                in
                "(" ^ constructor ^ String.concat "" fields ^ ")")
              (Sort_table.find numbering.datatypes name)
          in
          "(" ^ String.concat " " constructors ^ ")"
        in
        [
          Printf.sprintf "(declare-datatypes (%s) (%s))\n" (String.concat " " heads)
            (String.concat " " (List.map body datatypes));
        ]
  in
  {
    text = String.concat "" (sorts @ datatype_block @ declarations @ assertions) ^ "(check-sat)\n";
    numbering;
  }

let rendered_text rendering = rendering.text
let show_query query = (render query).text

let term_text { numbering; _ } term =
  let rec named = function
    | Symbol name -> Symbol_table.mem numbering.symbol_names name
    | Integer _ | Boolean _ | Bits _ -> true
    | Apply (name, arguments) ->
        (Symbol_table.mem numbering.member_of name || Symbol_table.mem numbering.symbol_names name)
        && List.for_all named arguments
    | Operation (_, arguments) -> List.for_all named arguments
    | Is (constructor, argument) ->
        Symbol_table.mem numbering.member_of constructor && named argument
    | Forall _ | Exists _ -> false
  in
  if named term then begin
    let buffer = Buffer.create 64 in
    print numbering [] buffer term;
    Some (Buffer.contents buffer)
  end
  else None

let symbols { numbering; _ } =
  List.map
    (fun name -> (name, Symbol_table.find numbering.symbol_names name))
    (Dynarray.to_list numbering.symbol_order)

let list_members query =
  let { numbering; _ } = render query in
  Sort_table.fold
    (fun datatype constructors entries ->
      match Sort_table.find_opt numbering.sort_names datatype with
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
