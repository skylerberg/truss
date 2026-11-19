type sort = Int | Bool | Float of int * int | Type_sort of Types.ty | Function_sort of int

module Symbol = struct
  type 'term t =
    | Variable of { label : string; numbers : int list }
    | Function of { callee : Path.t; type_arguments : Types.argument list }
    | Limited of { callee : Path.t; type_arguments : Types.argument list }
    | Function_value of { callee : Path.t; type_arguments : Types.argument list }
    | Constant of Path.t
    | Generic_value of { owner : Path.t; name : string }
    | Text_literal of { type_ : Types.ty; text : string }
    | Named_term of 'term
    | Lambda of { sorts : sort list; definition : 'term }
    | Lifted of 'term t
    | Unspecified of 'term t
    | Constructor of { type_ : Types.ty; variant : string option }
    | Field of { type_ : Types.ty; variant : string option; field : string }
    | Unit
    | Apply of sort list
    | Equal of Types.ty
    | Valid of Types.ty
    | Rank of Types.ty
    | Capacity of Types.ty
    | Owner_of_view of Types.ty
    | Model of Types.ty
    | Slack of Types.ty
    | Potential of Types.ty
    | Potential_measure of Types.ty
    | Block_bytes of { type_ : Types.ty; variant : string option }
    | Callback_cost of { metric : Language.Metric.t; sort : sort }
    | Method_cost of {
        metric : Language.Metric.t;
        method_ : Path.t;
        trait_arguments : Types.argument list;
        self_type : Types.ty;
      }
    | Opaque_operation of {
        operation : Intrinsic.scalar;
        type_ : Types.ty;
        integer : (int * bool) option;
      }
    | Bit_count of { count : Intrinsic.scalar; width : int }
    | System of Intrinsic.runtime
    | Libc_number of Libc.number
    | Handle_descriptor
    | Compare_bytes_order
    | Cost_most
    | Cost_log
    | Cost_power
    | Reached of int
    | Condition of int
end

type rounding_mode = Nearest_ties_to_even | Toward_positive | Toward_negative | Toward_zero

type operator =
  | Not
  | And
  | Or
  | Implies
  | Equal
  | Ite
  | Negate
  | Add
  | Subtract
  | Multiply
  | Div
  | Mod
  | Power
  | Less
  | Less_equal
  | Greater
  | Greater_equal
  | To_real
  | Int2bv of { width : int }
  | Bv2nat
  | Bvnot
  | Bvand
  | Bvor
  | Bvxor
  | Bvshl
  | Bvlshr
  | Bvashr
  | Bvsub
  | Concat
  | Extract of { high : int; low : int }
  | Fp
  | Fp_neg
  | Fp_add of rounding_mode
  | Fp_sub of rounding_mode
  | Fp_mul of rounding_mode
  | Fp_div of rounding_mode
  | Fp_fma of rounding_mode
  | Fp_sqrt of rounding_mode
  | Fp_round_to_integral of rounding_mode
  | Fp_eq
  | Fp_lt
  | Fp_leq
  | Fp_is_nan
  | To_fp of { exponent : int; significand : int; rounding_mode : rounding_mode option }
  | Fp_to_sbv of { width : int; rounding_mode : rounding_mode }
  | Fp_to_ubv of { width : int; rounding_mode : rounding_mode }

type term =
  | Symbol of symbol
  | Integer of Z.t
  | Boolean of bool
  | Bits of int * Z.t
  | Apply of symbol * term list
  | Is of symbol * term
  | Operation of operator * term list
  | Forall of (symbol * sort) list * term list * term
  | Exists of (symbol * sort) list * term

and symbol = term Symbol.t

type declaration =
  | Constant of symbol * sort
  | Function of symbol * sort list * sort
  | Definition of { symbol : symbol; parameters : (symbol * sort) list; result : sort; body : term }
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

let render_rounding_mode = function
  | Nearest_ties_to_even -> "RNE"
  | Toward_positive -> "RTP"
  | Toward_negative -> "RTN"
  | Toward_zero -> "RTZ"

let render_operator operator =
  let render_rounded name rounding_mode = name ^ " " ^ render_rounding_mode rounding_mode in
  match operator with
  | Not -> "not"
  | And -> "and"
  | Or -> "or"
  | Implies -> "=>"
  | Equal -> "="
  | Ite -> "ite"
  | Negate | Subtract -> "-"
  | Add -> "+"
  | Multiply -> "*"
  | Div -> "div"
  | Mod -> "mod"
  | Power -> "^"
  | Less -> "<"
  | Less_equal -> "<="
  | Greater -> ">"
  | Greater_equal -> ">="
  | To_real -> "to_real"
  | Int2bv { width } -> Printf.sprintf "(_ int2bv %d)" width
  | Bv2nat -> "bv2nat"
  | Bvnot -> "bvnot"
  | Bvand -> "bvand"
  | Bvor -> "bvor"
  | Bvxor -> "bvxor"
  | Bvshl -> "bvshl"
  | Bvlshr -> "bvlshr"
  | Bvashr -> "bvashr"
  | Bvsub -> "bvsub"
  | Concat -> "concat"
  | Extract { high; low } -> Printf.sprintf "(_ extract %d %d)" high low
  | Fp -> "fp"
  | Fp_neg -> "fp.neg"
  | Fp_add rounding_mode -> render_rounded "fp.add" rounding_mode
  | Fp_sub rounding_mode -> render_rounded "fp.sub" rounding_mode
  | Fp_mul rounding_mode -> render_rounded "fp.mul" rounding_mode
  | Fp_div rounding_mode -> render_rounded "fp.div" rounding_mode
  | Fp_fma rounding_mode -> render_rounded "fp.fma" rounding_mode
  | Fp_sqrt rounding_mode -> render_rounded "fp.sqrt" rounding_mode
  | Fp_round_to_integral rounding_mode -> render_rounded "fp.roundToIntegral" rounding_mode
  | Fp_eq -> "fp.eq"
  | Fp_lt -> "fp.lt"
  | Fp_leq -> "fp.leq"
  | Fp_is_nan -> "fp.isNaN"
  | To_fp { exponent; significand; rounding_mode } -> (
      let name = Printf.sprintf "(_ to_fp %d %d)" exponent significand in
      match rounding_mode with
      | Some rounding_mode -> render_rounded name rounding_mode
      | None -> name)
  | Fp_to_sbv { width; rounding_mode } ->
      render_rounded (Printf.sprintf "(_ fp.to_sbv %d)" width) rounding_mode
  | Fp_to_ubv { width; rounding_mode } ->
      render_rounded (Printf.sprintf "(_ fp.to_ubv %d)" width) rounding_mode

let show_type_arguments = function
  | [] -> ""
  | arguments -> "[" ^ String.concat ", " (List.map Types.show_argument arguments) ^ "]"

let show_variant = Option.value ~default:"record"

let rec show_symbol : symbol -> string = function
  | Variable { label; numbers } -> String.concat "." (label :: List.map string_of_int numbers)
  | Function { callee; type_arguments } ->
      "function." ^ Path.show callee ^ show_type_arguments type_arguments
  | Limited { callee; type_arguments } ->
      "limited." ^ Path.show callee ^ show_type_arguments type_arguments
  | Function_value { callee; type_arguments } ->
      "named." ^ Path.show callee ^ show_type_arguments type_arguments
  | Constant path -> "constant." ^ Path.show path
  | Generic_value { owner; name } -> Printf.sprintf "generic.%s.%s" (Path.show owner) name
  | Text_literal { type_; text } -> Printf.sprintf "text_literal.%s.%S" (Types.show type_) text
  | Named_term term -> "named_term(" ^ show_term term ^ ")"
  | Lambda { definition; _ } -> "lambda(" ^ show_term definition ^ ")"
  | Lifted symbol -> show_symbol symbol ^ ".lifted"
  | Unspecified symbol -> show_symbol symbol ^ ".unspecified"
  | Constructor { type_; variant } -> "constructor." ^ Types.show type_ ^ "." ^ show_variant variant
  | Field { type_; variant; field } ->
      "field." ^ Types.show type_ ^ "." ^ show_variant variant ^ "." ^ field
  | Unit -> "Unit.unit"
  | Apply sorts -> String.concat "." ("apply" :: List.map show_sort sorts)
  | Equal ty -> "equal." ^ Types.show ty
  | Valid ty -> "valid." ^ Types.show ty
  | Rank ty -> "rank." ^ Types.show ty
  | Capacity ty -> "capacity." ^ Types.show ty
  | Owner_of_view owner -> "owner_of_view." ^ Types.show owner
  | Model ty -> "model." ^ Types.show ty
  | Slack ty -> "slack." ^ Types.show ty
  | Potential ty -> "potential." ^ Types.show ty
  | Potential_measure ty -> "potential.measure." ^ Types.show ty
  | Block_bytes { type_; variant } -> "bytes." ^ Types.show type_ ^ "." ^ show_variant variant
  | Callback_cost { metric; sort } -> Language.Metric.show metric ^ "." ^ show_sort sort
  | Method_cost { metric; method_; trait_arguments; self_type } ->
      Printf.sprintf "%s.method.%s%s[%s]" (Language.Metric.show metric) (Path.show method_)
        (show_type_arguments trait_arguments)
        (Types.show self_type)
  | Opaque_operation { operation; type_; _ } ->
      Printf.sprintf "operation.%s.%s"
        (Intrinsic.show_operation (Scalar operation))
        (Types.show type_)
  | Bit_count { count; width } ->
      Printf.sprintf "bits.%s.%d" (Intrinsic.show_operation (Scalar count)) width
  | System operation -> "system." ^ Intrinsic.show_operation (Runtime operation)
  | Libc_number number -> "libc.number." ^ Libc.show_number number
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
    | Apply (name, arguments) -> show_applied (show_symbol name) arguments
    | Operation (operator, arguments) -> show_applied (render_operator operator) arguments
    | Is (constructor, argument) ->
        show_applied (Printf.sprintf "(_ is %s)" (show_symbol constructor)) [ argument ]
    | Forall (bound, _, body) -> show_binder "forall" bound body
    | Exists (bound, body) -> show_binder "exists" bound body
  and show_applied head = function
    | [] -> head
    | arguments -> "(" ^ String.concat " " (head :: List.map show arguments) ^ ")"
  and show_binder word bound body =
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

let list_arguments = function
  | Apply (_, arguments) | Operation (_, arguments) -> arguments
  | Is (_, argument) -> [ argument ]
  | Symbol _ | Integer _ | Boolean _ | Bits _ | Forall _ | Exists _ -> []

let map_arguments transform = function
  | Apply (name, arguments) -> Apply (name, List.map transform arguments)
  | Operation (operator, arguments) -> Operation (operator, List.map transform arguments)
  | Is (constructor, argument) -> Is (constructor, transform argument)
  | (Symbol _ | Integer _ | Boolean _ | Bits _ | Forall _ | Exists _) as term -> term

let int value = Integer (Z.of_int value)

let ( &&& ) left right =
  match (left, right) with
  | Boolean true, other | other, Boolean true -> other
  | Boolean false, _ | _, Boolean false -> Boolean false
  | _ -> Operation (And, [ left; right ])

let ( ||| ) left right =
  match (left, right) with
  | Boolean false, other | other, Boolean false -> other
  | Boolean true, _ | _, Boolean true -> Boolean true
  | _ -> Operation (Or, [ left; right ])

let ( ==> ) premise conclusion =
  match (premise, conclusion) with
  | Boolean true, other -> other
  | Boolean false, _ | _, Boolean true -> Boolean true
  | _ -> Operation (Implies, [ premise; conclusion ])

let not_ = function
  | Boolean value -> Boolean (not value)
  | Operation (Not, [ inner ]) -> inner
  | other -> Operation (Not, [ other ])

let equal left right = if left = right then Boolean true else Operation (Equal, [ left; right ])

let ite condition then_ else_ =
  match condition with
  | Boolean true -> then_
  | Boolean false -> else_
  | _ -> if then_ = else_ then then_ else Operation (Ite, [ condition; then_; else_ ])

let negate value = Operation (Negate, [ value ])
let add left right = Operation (Add, [ left; right ])
let subtract left right = Operation (Subtract, [ left; right ])
let multiply left right = Operation (Multiply, [ left; right ])
let less left right = Operation (Less, [ left; right ])
let less_equal left right = Operation (Less_equal, [ left; right ])
let greater left right = Operation (Greater, [ left; right ])
let greater_equal left right = Operation (Greater_equal, [ left; right ])
let conjunction terms = List.fold_left ( &&& ) (Boolean true) terms
let disjunction terms = List.fold_left ( ||| ) (Boolean false) terms

let truncated_divide left right =
  let is_nonnegative value = greater_equal value (Integer Z.zero) in
  let div dividend divisor = Operation (Div, [ dividend; divisor ]) in
  ite (is_nonnegative left)
    (ite (is_nonnegative right) (div left right) (negate (div left (negate right))))
    (ite (is_nonnegative right)
       (negate (div (negate left) right))
       (div (negate left) (negate right)))

let truncated_remainder left right = subtract left (multiply right (truncated_divide left right))

let integer_of_bits ~is_signed ~width bits =
  let unsigned = Operation (Bv2nat, [ bits ]) in
  if is_signed then
    ite
      (greater_equal unsigned (Integer (Z.shift_left Z.one (width - 1))))
      (subtract unsigned (Integer (Z.shift_left Z.one width)))
      unsigned
  else unsigned

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
    | Operation (operator, arguments) ->
        Operation (operator, List.map (replace ~from ~into) arguments)
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
  | Operation (operator, arguments) ->
      Operation (operator, List.map (substitute substitution) arguments)
  | Is (constructor, argument) -> Is (constructor, substitute substitution argument)
  | Forall (bound, trigger, body) ->
      let inner = remove_bound bound substitution in
      Forall (bound, List.map (substitute inner) trigger, substitute inner body)
  | Exists (bound, body) -> Exists (bound, substitute (remove_bound bound substitution) body)

and remove_bound bound substitution =
  List.filter (fun (name, _) -> not (List.mem_assoc name bound)) substitution

let list_triggers ~is_triggering variables body =
  let names = List.map fst variables in
  let rec is_trigger_term = function
    | Symbol _ | Integer _ | Boolean _ | Bits _ -> true
    | Apply (name, arguments) when is_triggering name -> List.for_all is_trigger_term arguments
    | (Apply _ | Operation _ | Is _ | Forall _ | Exists _) as term -> not (mentions names term)
  in
  let is_candidate = function
    | Apply (name, _ :: _) as term ->
        is_triggering name && mentions names term && is_trigger_term term
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
  let list_bound_names_in term = List.filter (fun name -> mentions [ name ] term) names in
  let rec is_proper_subterm inner term =
    inner <> term
    &&
    match term with
    | Apply (_, arguments) | Operation (_, arguments) ->
        List.exists (fun argument -> argument = inner || is_proper_subterm inner argument) arguments
    | Is (_, argument) -> argument = inner || is_proper_subterm inner argument
    | _ -> false
  in
  let rec find_matching bindings pattern term =
    match (pattern, bindings) with
    | _, None -> None
    | Symbol name, Some matched when List.mem name names -> (
        match List.assoc_opt name matched with
        | Some bound -> if bound = term then bindings else None
        | None -> Some ((name, term) :: matched))
    | Apply (name, arguments), _ -> (
        match term with
        | Apply (other, others) when name = other && List.length arguments = List.length others ->
            List.fold_left2 find_matching bindings arguments others
        | _ -> None)
    | _ -> if pattern = term then bindings else None
  in
  let makes_matching_loop trigger =
    List.exists
      (fun term ->
        term <> trigger
        &&
        match find_matching (Some []) trigger term with
        | Some bindings ->
            List.exists (fun (name, bound) -> bound <> Symbol name && mentions names bound) bindings
        | None -> false)
      applications
  in
  let rec extract_conclusion = function
    | Operation (Implies, [ _; inner ]) -> extract_conclusion inner
    | term -> term
  in
  let names_every_variable term = is_candidate term && list_bound_names_in term = names in
  match extract_conclusion body with
  | Operation (Equal, [ (Apply _ as defined); other ])
    when names_every_variable defined && not (names_every_variable other) ->
      [ [ defined ] ]
  | _ -> (
      let candidates = List.filter is_candidate applications in
      let candidates =
        List.filter
          (fun term ->
            not
              (List.exists
                 (fun inner ->
                   is_proper_subterm inner term
                   && list_bound_names_in inner = list_bound_names_in term)
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
      let list_covering_triggers candidates =
        match List.filter (fun term -> list_bound_names_in term = names) candidates with
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
                             List.mem name (list_bound_names_in first @ list_bound_names_in second))
                           names
                    then Some (with_same_functions [ first; second ])
                    else None)
                  candidates)
              candidates
            |> List.sort_uniq compare
      in
      match
        list_covering_triggers (List.filter (fun term -> not (makes_matching_loop term)) candidates)
      with
      | [] -> list_covering_triggers candidates
      | triggers -> triggers)

let forall ?(trigger = []) (variables, body) =
  match variables with [] -> body | _ -> Forall (variables, trigger, body)

let choose_triggers ~is_triggering variables trigger body =
  match trigger with [] -> list_triggers ~is_triggering variables body | terms -> [ terms ]

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
      | Constant _ | Definition _ -> ())
    declarations;
  List.iter
    (function
      | Definition { symbol; _ } -> Symbol_table.remove functions symbol
      | Constant _ | Function _ | Datatype _ -> ())
    declarations;
  Symbol_table.mem functions

let has_untriggered_fact query =
  let is_triggering = make_triggering_test query.declarations in
  let rec is_untriggered = function
    | Operation (Implies, [ _; inner ]) -> is_untriggered inner
    | Forall (variables, trigger, body) ->
        choose_triggers ~is_triggering variables trigger body = []
    | _ -> false
  in
  List.exists is_untriggered query.facts

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
  let bodies = Symbol_table.create 8 in
  List.iter
    (function
      | Constant (name, _) | Function (name, _, _) -> Symbol_table.replace declared name ()
      | Definition { symbol; body; _ } ->
          Symbol_table.replace declared symbol ();
          Symbol_table.replace bodies symbol body
      | Datatype _ -> ())
    query.declarations;
  let reached = Symbol_table.create 64 in
  let rec reach symbols =
    List.iter
      (fun symbol ->
        if not (Symbol_table.mem reached symbol) then begin
          Symbol_table.replace reached symbol ();
          Option.iter
            (fun body -> reach (list_declared_symbols declared body))
            (Symbol_table.find_opt bodies symbol)
        end)
      symbols
  in
  reach (list_declared_symbols declared query.goal);
  let is_triggering = make_triggering_test query.declarations in
  let rec needs fact symbols =
    match fact with
    | Operation (Implies, [ _; (Forall _ as inner) ]) -> needs inner symbols
    | Forall (variables, trigger, body) -> (
        match choose_triggers ~is_triggering variables trigger body with
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
      (fun index (symbols, is_ready) ->
        if (not is_needed.(index)) && is_ready () then begin
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
  is_triggering : symbol -> bool;
  symbol_names : string Symbol_table.t;
  symbol_order : symbol Dynarray.t;
  definition_bodies : string Symbol_table.t;
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

let rec render_symbol_name numbering name =
  match Symbol_table.find_opt numbering.symbol_names name with
  | Some canonical -> Some canonical
  | None -> (
      match Symbol_table.find_opt numbering.declared name with
      | None -> None
      | Some declaration ->
          let canonical = Printf.sprintf "x%d" (Symbol_table.length numbering.symbol_names) in
          Symbol_table.replace numbering.symbol_names name canonical;
          (match declaration with
          | Constant (_, sort) -> ignore (render_sort_name numbering sort)
          | Function (_, inputs, output) ->
              List.iter (fun sort -> ignore (render_sort_name numbering sort)) inputs;
              ignore (render_sort_name numbering output)
          | Definition { parameters; result; body; _ } ->
              List.iter (fun (_, sort) -> ignore (render_sort_name numbering sort)) parameters;
              ignore (render_sort_name numbering result);
              let buffer = Buffer.create 128 in
              print numbering
                (List.mapi
                   (fun index (parameter, _) -> (parameter, Printf.sprintf "b%d" index))
                   parameters)
                buffer body;
              Symbol_table.replace numbering.definition_bodies name (Buffer.contents buffer)
          | Datatype _ -> ());
          Dynarray.add_last numbering.symbol_order name;
          Some canonical)

and render_member_name numbering name =
  Option.map
    (fun (datatype, suffix) -> render_sort_name numbering datatype ^ suffix)
    (Symbol_table.find_opt numbering.member_of name)

and render_function_name numbering name =
  match render_member_name numbering name with
  | Some canonical -> canonical
  | None -> (
      match render_symbol_name numbering name with
      | Some canonical -> canonical
      | None -> invalid_arg ("Logic.text: undeclared symbol " ^ show_symbol name))

and print numbering bound buffer term =
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
  | Operation (operator, arguments) ->
      render_application numbering bound buffer (render_operator operator) arguments
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
  match choose_triggers ~is_triggering:numbering.is_triggering variables trigger body with
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
      | Constant (name, _) | Function (name, _, _) | Definition { symbol = name; _ } ->
          Symbol_table.replace declared name declaration
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
    is_triggering = make_triggering_test query.declarations;
    symbol_names = Symbol_table.create 64;
    symbol_order = Dynarray.create ();
    definition_bodies = Symbol_table.create 8;
    sort_names = Sort_table.create 8;
    sort_order = Dynarray.create ();
  }

type rendering = { text : string; numbering : numbering }

let render_cardinality_bound sort_name element_count =
  let elements = List.init element_count (Printf.sprintf "%s_e%d" sort_name) in
  String.concat ""
    (List.map (fun element -> Printf.sprintf "(declare-fun %s () %s)\n" element sort_name) elements)
  ^ Printf.sprintf "(assert (forall ((b0 %s)) (or%s)))\n" sort_name
      (String.concat "" (List.map (Printf.sprintf " (= b0 %s)") elements))

let render_with ~cardinality_bound query =
  let numbering = number_symbols query in
  let render_assertion term =
    let buffer = Buffer.create 128 in
    Buffer.add_string buffer "(assert ";
    print numbering [] buffer term;
    Buffer.add_string buffer ")\n";
    Buffer.contents buffer
  in
  let negated_goal = render_assertion (not_ query.goal) in
  let assertions = List.map render_assertion query.facts @ [ negated_goal ] in
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
        | Definition { parameters; result; _ } ->
            Printf.sprintf "(define-fun %s (%s) %s %s)\n" canonical
              (String.concat " "
                 (List.mapi
                    (fun index (_, sort) ->
                      Printf.sprintf "(b%d %s)" index (render_sort_name numbering sort))
                    parameters))
              (render_sort_name numbering result)
              (Symbol_table.find numbering.definition_bodies name)
        | Datatype _ -> "")
      (Dynarray.to_list numbering.symbol_order)
  in
  let sort_order = Dynarray.to_list numbering.sort_order in
  let uninterpreted_sorts =
    List.filter_map
      (fun name ->
        if Sort_table.mem numbering.datatypes name then None
        else Some (Sort_table.find numbering.sort_names name))
      sort_order
  in
  let sorts = List.map (Printf.sprintf "(declare-sort %s 0)\n") uninterpreted_sorts in
  let cardinality_bounds =
    match cardinality_bound with
    | None -> []
    | Some element_count ->
        List.map
          (fun sort_name -> render_cardinality_bound sort_name element_count)
          uninterpreted_sorts
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
        let render_body name =
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
            (String.concat " " (List.map render_body datatypes));
        ]
  in
  {
    text =
      String.concat "" (sorts @ datatype_block @ cardinality_bounds @ declarations @ assertions)
      ^ "(check-sat)\n";
    numbering;
  }

let render query = render_with ~cardinality_bound:None query
let rendered_text rendering = rendering.text
let show_query ?cardinality_bound query = (render_with ~cardinality_bound query).text

let has_uninterpreted_sort query =
  let { numbering; _ } = render query in
  Dynarray.exists (fun sort -> not (Sort_table.mem numbering.datatypes sort)) numbering.sort_order

let render_term { numbering; _ } term =
  let rec is_named = function
    | Symbol name -> Symbol_table.mem numbering.symbol_names name
    | Integer _ | Boolean _ | Bits _ -> true
    | Apply (name, arguments) ->
        (Symbol_table.mem numbering.member_of name || Symbol_table.mem numbering.symbol_names name)
        && List.for_all is_named arguments
    | Operation (_, arguments) -> List.for_all is_named arguments
    | Is (constructor, argument) ->
        Symbol_table.mem numbering.member_of constructor && is_named argument
    | Forall _ | Exists _ -> false
  in
  if is_named term then begin
    let buffer = Buffer.create 64 in
    print numbering [] buffer term;
    Some (Buffer.contents buffer)
  end
  else None

let list_symbols { numbering; _ } =
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

let hash text = "smt1-blake3-" ^ Blake3.hash_to_hex text
