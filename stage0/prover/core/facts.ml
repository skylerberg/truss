(* The operations on the state of a proof: declarations, facts, fresh
   symbols, obligations, the logic's sorts for types, and the join of paths. *)

open State

let variable ?(numbers = []) label = Symbol.Variable { label; numbers }

exception Unsupported of span * string

(* Something the prover cannot read in another definition's form, such as
   a callee's contract, whose span means nothing in this one. The nearest
   node of the definition being proven reports it, with its own span. *)
exception Foreign_unsupported of string

let unsupported span format =
  Printf.ksprintf (fun message -> raise (Unsupported (span, message))) format

let bug format = Compiler_bug.bug ~stage:"Prover" format

let home source =
  match source.key with Some key -> key | None -> bug "%s has no definition key" source.name

(* The formulas of [requires] clauses. *)
let clauses (requires : Mir.requirement list) =
  List.map (fun (requirement : Mir.requirement) -> requirement.clause) requires

let reading_package context = Some (Path.package context.current)

(* Symbols and facts *)

let declare context (declaration : Logic.declaration) =
  match declaration with
  | Constant (name, _) | Function (name, _, _) ->
      if not (Hashtbl.mem context.declared name) then begin
        Hashtbl.replace context.declared name ();
        context.declarations <- declaration :: context.declarations
      end
  | Datatype _ -> invalid_arg "Translate.declare: a datatype is declared by its sort"

(* A symbol for a value made at this point. Inside quantifiers it is a
   function of their bound symbols, since the value can differ for each of
   theirs. *)
(* Adds a fact. The fact is an argument, made before the list is read,
   since making it can add facts of its own: in
   [context.facts <- fact :: context.facts] the list is read first, and
   those facts are lost. *)
let add_fact context fact = context.facts <- fact :: context.facts

let value_symbol context frame name sort =
  match List.rev frame.binders with
  | [] ->
      declare context (Logic.Constant (name, sort));
      Logic.Symbol name
  | outermost_first ->
      declare context
        (Logic.Function (name, List.map (fun (_, sort, _) -> sort) outermost_first, sort));
      Logic.Apply (name, List.map (fun (bound, _, _) -> Logic.Symbol bound) outermost_first)

(* A name no other symbol of the query has, for a bound variable. *)
let fresh_name context label =
  context.fresh <- context.fresh + 1;
  variable label ~numbers:[ context.fresh ]

let fresh context frame label sort =
  let name = fresh_name context label in
  Hashtbl.replace context.fresh_order name context.fresh;
  value_symbol context frame name sort

(* Whether a term mentions a fresh symbol made after [mark]: a value a
   loop changes, or one made inside it. *)
let mentions_fresh_after context mark term =
  let is_fresh_after name =
    match Hashtbl.find_opt context.fresh_order name with
    | Some order -> order > mark
    | None -> false
  in
  let rec walk = function
    | Logic.Symbol name -> is_fresh_after name
    | Logic.Integer _ | Logic.Boolean _ | Logic.Bits _ -> false
    | Logic.Apply (name, arguments) -> is_fresh_after name || List.exists walk arguments
    | Logic.Operation (_, arguments) -> List.exists walk arguments
    | Logic.Is (_, argument) -> walk argument
    | Logic.Forall (_, _, body) | Logic.Exists (_, body) -> walk body
  in
  walk term

(* A statement made inside quantifiers, closed over them: true for every
   value of each bound symbol that its premise admits. [None] when it names
   a symbol bound by something other than a quantifier, such as a lambda's
   parameter, where it has no meaning outside. *)
let closed_over_binders frame term =
  let names = List.map (fun (name, _, _) -> name) frame.binders in
  if Logic.mentions (List.filter (fun name -> not (List.mem name names)) frame.bound) term then None
  else if not (Logic.mentions names term) then Some term
  else
    let outermost_first = List.rev frame.binders in
    Some
      (Logic.forall
         ( List.map (fun (name, sort, _) -> (name, sort)) outermost_first,
           Logic.( ==> )
             (Logic.conjunction (List.map (fun (_, _, premise) -> premise) outermost_first))
             term ))

let in_scope context frame term =
  let named = List.filter (fun name -> Logic.mentions [ name ] term) frame.bound in
  if List.for_all (fun name -> List.mem_assoc name context.scopes) named then
    match List.find_opt (fun (name, _) -> List.mem name named) context.scopes with
    | Some (_, facts) -> facts := term :: !facts
    | None -> ()

(* The facts of the quantifiers whose bound symbols are [names]. *)
let scope_facts context names =
  List.concat_map
    (fun (name, facts) -> if List.mem name names then List.rev !facts else [])
    context.scopes

let with_quantifier_facts ?(binders = []) context term =
  let stated bound fact =
    List.for_all
      (fun name -> List.mem name bound || not (Logic.mentions [ name ] fact))
      context.quantifier_symbols
  in
  let rec walk positive bound term =
    let facts symbols =
      let bound = List.map fst symbols @ bound in
      ( bound,
        List.filter (stated bound)
          (Option.value ~default:[] (Hashtbl.find_opt context.quantifier_facts term)) )
    in
    match term with
    | Logic.Forall (symbols, trigger, body) when positive ->
        let bound, facts = facts symbols in
        let body = walk positive bound body in
        Logic.Forall
          ( symbols,
            trigger,
            match facts with [] -> body | facts -> Logic.( ==> ) (Logic.conjunction facts) body )
    | Logic.Exists (symbols, body) when not positive ->
        let bound, facts = facts symbols in
        let body = walk positive bound body in
        Logic.Exists
          ( symbols,
            match facts with [] -> body | facts -> Logic.( &&& ) (Logic.conjunction facts) body )
    | Logic.Operation ((("and" | "or") as operator), parts) ->
        Logic.Operation (operator, List.map (walk positive bound) parts)
    | Logic.Operation ("=>", [ premise; conclusion ]) ->
        Logic.Operation ("=>", [ walk (not positive) bound premise; walk positive bound conclusion ])
    | Logic.Operation ("not", [ inner ]) ->
        Logic.Operation ("not", [ walk (not positive) bound inner ])
    | term -> term
  in
  walk true binders term

let fact context frame term =
  if not (Logic.mentions frame.bound term) then add_fact context term
  else in_scope context frame term

(* A fact is guarded by its path's condition, and kept with its
   quantifier where either names a bound symbol, as [fact] says. *)
let assume context frame term =
  match term with
  | Logic.Boolean true -> ()
  | _ ->
      let guarded = Logic.( ==> ) frame.condition term in
      if not (Logic.mentions frame.bound term || Logic.mentions frame.bound frame.condition) then
        add_fact context guarded
      else in_scope context frame guarded

(* An obligation is shown by its own query, and is a fact for the code
   after it. Inside a quantifier it is shown for each value the
   quantifier's premise admits, which is how a quantifier's body is shown
   to be well defined. *)
let add_requires context frame required =
  let text = Lazy.force frame.source.text in
  let brace =
    match Option.bind frame.source.key (Query.demand context.database Names.definition) with
    | Some { kind = Function { body; _ }; _ } when body.span.start < String.length text ->
        Some body.span.start
    | _ -> None
  in
  let edit =
    match brace with
    | Some at when at > 0 && text.[at - 1] = '\n' ->
        Some (Diagnostic.insert (Syntax.Span.zero_width at) ("  requires " ^ required ^ "\n"))
    | Some at when at > 0 && text.[at - 1] = ' ' ->
        Some (Diagnostic.replace (Syntax.Span.make (at - 1) at) ("\n  requires " ^ required ^ "\n"))
    | _ -> None
  in
  match edit with
  | Some edit -> [ Diagnostic.fix (Printf.sprintf "Add `requires %s`" required) [ edit ] ]
  | None -> []

(* A goal about the definition's parameters as they arrive, written as
   Truss: comparisons, logic, and arithmetic of parameters and literals,
   which a [requires] states exactly, since a specification's integers do
   not overflow. *)
let truss_of_goal context term =
  let name symbol =
    if List.mem symbol context.entry then
      match List.assoc_opt symbol context.values with Some name -> Some name | None -> Some "self"
    else None
  in
  let named = ref false in
  let all printed = if List.mem None printed then None else Some (List.filter_map Fun.id printed) in
  let rec atom = function
    | Logic.Symbol symbol ->
        let printed = name symbol in
        if printed <> None then named := true;
        printed
    | Logic.Integer value -> Some (Z.to_string value)
    | Logic.Boolean value -> Some (if value then "true" else "false")
    | _ -> None
  and value term = arithmetic 0 term
  and arithmetic level = function
    | Logic.Operation ((("+" | "*") as operator), (_ :: _ :: _ as parts)) ->
        let inner = if operator = "+" then 1 else 2 in
        Option.map
          (fun printed -> parenthesized level inner (String.concat (" " ^ operator ^ " ") printed))
          (all (List.map (arithmetic inner) parts))
    | Logic.Operation ("-", [ left; right ]) ->
        Option.map
          (fun printed -> parenthesized level 1 (String.concat " - " printed))
          (all [ arithmetic 1 left; arithmetic 2 right ])
    | Logic.Operation ("-", [ inner ]) ->
        Option.map (fun printed -> parenthesized level 3 ("-" ^ printed)) (arithmetic 3 inner)
    | Logic.Integer value when Z.sign value < 0 && level > 0 -> Some ("(" ^ Z.to_string value ^ ")")
    | term -> atom term
  and parenthesized level inner text = if inner < level then "(" ^ text ^ ")" else text
  and print = function
    | Logic.Operation ((("<" | "<=" | ">" | ">=" | "=") as operator), [ left; right ]) -> (
        match (value left, value right) with
        | Some left, Some right ->
            Some (Printf.sprintf "%s %s %s" left (if operator = "=" then "==" else operator) right)
        | _ -> None)
    | Logic.Operation ("and", parts) -> joined " && " parts
    | Logic.Operation ("or", parts) -> joined " || " parts
    | Logic.Operation ("not", [ inner ]) -> Option.map (Printf.sprintf "!(%s)") (print inner)
    | Logic.Operation ("=>", [ premise; conclusion ]) -> (
        match (print premise, print conclusion) with
        | Some premise, Some conclusion -> Some (Printf.sprintf "(%s) ==> (%s)" premise conclusion)
        | _ -> None)
    | term -> atom term
  and joined separator parts =
    Option.map
      (fun printed -> "(" ^ String.concat separator printed ^ ")")
      (all (List.map print parts))
  in
  let printed =
    match term with
    | Logic.Operation ("and", parts) ->
        Option.map (String.concat " && ") (all (List.map print parts))
    | Logic.Operation ("or", parts) ->
        Option.map (String.concat " || ") (all (List.map print parts))
    | term -> print term
  in
  if !named then printed else None

(* Bitwise operations, exactly: each defined as the operation on its
   operands' bits of their type's width, read back as an integer, which
   the solver decides by bit-blasting. *)
let bitwise_operations =
  [
    "and";
    "or";
    "xor";
    "complement";
    "shift_left";
    "shift_right";
    "rotate_left";
    "rotate_right";
    "swap_bytes";
  ]

let bitwise_of : Logic.symbol -> _ = function
  | Opaque_operation { operation; integer = Some (bits, signed); _ }
    when List.mem operation bitwise_operations ->
      Some (operation, bits, signed)
  | _ -> None

let exactly (query : Logic.query) =
  let bitwise_terms = ref [] in
  let rec walk bound = function
    | Logic.Apply (name, arguments) as term ->
        (if bitwise_of name <> None && not (List.mem_assoc term !bitwise_terms) then
           let named = List.filter (fun (symbol, _) -> Logic.mentions [ symbol ] term) bound in
           bitwise_terms := (term, named) :: !bitwise_terms);
        List.iter (walk bound) arguments
    | Logic.Forall (symbols, _, body) | Logic.Exists (symbols, body) -> walk (symbols @ bound) body
    | term -> List.iter (walk bound) (Logic.arguments term)
  in
  List.iter (walk []) (query.goal :: query.facts);
  let definition term =
    match term with
    | Logic.Apply (name, arguments) -> (
        match (bitwise_of name, arguments) with
        | Some (operation, bits, signed), first :: rest ->
            let bits_of value = Logic.Operation (Printf.sprintf "(_ int2bv %d)" bits, [ value ]) in
            let operand_bits = bits_of first in
            let result =
              match (operation, rest) with
              | "complement", _ -> Some (Logic.Operation ("bvnot", [ operand_bits ]))
              | "and", [ second_operand ] ->
                  Some (Logic.Operation ("bvand", [ operand_bits; bits_of second_operand ]))
              | "or", [ second_operand ] ->
                  Some (Logic.Operation ("bvor", [ operand_bits; bits_of second_operand ]))
              | "xor", [ second_operand ] ->
                  Some (Logic.Operation ("bvxor", [ operand_bits; bits_of second_operand ]))
              | "shift_left", [ second_operand ] ->
                  Some (Logic.Operation ("bvshl", [ operand_bits; bits_of second_operand ]))
              | "shift_right", [ second_operand ] ->
                  Some
                    (Logic.Operation
                       ( (if signed then "bvashr" else "bvlshr"),
                         [ operand_bits; bits_of second_operand ] ))
              | ("rotate_left" | "rotate_right"), [ second_operand ] ->
                  let by = bits_of (Logic.Operation ("mod", [ second_operand; Logic.int bits ])) in
                  let rest = Logic.Operation ("bvsub", [ bits_of (Logic.int bits); by ]) in
                  let towards, back =
                    if operation = "rotate_left" then ("bvshl", "bvlshr") else ("bvlshr", "bvshl")
                  in
                  Some
                    (Logic.Operation
                       ( "bvor",
                         [
                           Logic.Operation (towards, [ operand_bits; by ]);
                           Logic.Operation (back, [ operand_bits; rest ]);
                         ] ))
              | "swap_bytes", _ ->
                  let byte index =
                    Logic.Operation
                      ( Printf.sprintf "(_ extract %d %d)" ((8 * index) + 7) (8 * index),
                        [ operand_bits ] )
                  in
                  let bytes = List.init (bits / 8) byte in
                  Some
                    (List.fold_left
                       (fun swapped next -> Logic.Operation ("concat", [ swapped; next ]))
                       (List.hd bytes) (List.tl bytes))
              | _ -> None
            in
            Option.map
              (fun result ->
                let unsigned = Logic.Operation ("bv2nat", [ result ]) in
                let value =
                  if signed then
                    let half = Logic.Integer (Z.shift_left Z.one (bits - 1)) in
                    Logic.ite
                      (Logic.Operation (">=", [ unsigned; half ]))
                      (Logic.Operation ("-", [ unsigned; Logic.Integer (Z.shift_left Z.one bits) ]))
                      unsigned
                  else unsigned
                in
                Logic.equal term value)
              result
        | _ -> None)
    | _ -> None
  in
  (* A term under a quantifier that names its bound symbols is defined for
     each of their values. *)
  let defined (term, named) =
    Option.map
      (fun definition -> if named = [] then definition else Logic.forall (named, definition))
      (definition term)
  in
  { query with facts = query.facts @ List.filter_map defined (List.rev !bitwise_terms) }

let rec oblige ?evaluation ?cited ?(fixes = []) context frame code span message goal =
  match
    obligation_at ?evaluation context frame code span message
      (with_quantifier_facts
         ~binders:(List.map (fun (name, _, _) -> name) frame.binders)
         context goal)
  with
  | Some obligation ->
      (* Without a fix of its own, a goal about the parameters alone is
         offered as a [requires]. *)
      let fixes =
        match fixes with
        | [] when frame.source.key = Some context.home && frame.checking -> (
            let goal =
              match frame.condition with
              | Logic.Boolean true -> goal
              | condition -> Logic.( ==> ) condition goal
            in
            match truss_of_goal context goal with
            | Some required -> add_requires context frame required
            | None -> [])
        | fixes -> fixes
      in
      context.obligations <- { obligation with cited; fixes } :: context.obligations;
      assume context frame goal
  | None -> ()

(* An obligation made but not yet added, for one that is needed only if
   its goal is used. *)
and obligation_at ?evaluation context frame code span message goal =
  if not frame.checking then None
  else if not (Logic.mentions frame.bound goal || Logic.mentions frame.bound frame.condition) then
    Some (make_obligation ?evaluation context frame code span message goal)
  else
    let names = List.map (fun (name, _, _) -> name) frame.binders in
    let goal =
      match scope_facts context names with
      | [] -> goal
      | facts -> Logic.( ==> ) (Logic.conjunction facts) goal
    in
    match closed_over_binders frame (Logic.( ==> ) frame.condition goal) with
    | Some closed ->
        Some
          (make_obligation ?evaluation context
             { frame with condition = Logic.Boolean true }
             code span message closed)
    | None -> None

and make_obligation ?evaluation context frame code span message goal =
  let query =
    Logic.prune
      {
        declarations = List.rev context.declarations;
        facts = List.rev context.facts;
        goal = Logic.( ==> ) frame.condition goal;
      }
  in
  let known_calls =
    List.filter
      (fun (known : known_call) ->
        let mentioned term = occurs known.term term in
        mentioned query.goal || List.exists mentioned query.facts)
      context.known_calls
  in
  {
    code;
    span;
    message;
    cited = None;
    fixes = [];
    query;
    values = context.values;
    decisions = List.rev context.decisions;
    locals =
      Locals.fold
        (fun local term shown ->
          match (term, Hashtbl.find_opt context.local_names local) with
          | Logic.Symbol symbol, Some name
            when not (List.mem_assoc symbol context.values || List.mem_assoc symbol shown) ->
              (symbol, name) :: shown
          | _ -> shown)
        frame.locals
        (match frame.result with
        | Some (Logic.Symbol symbol) when not (List.mem_assoc symbol context.values) ->
            [ (symbol, "result") ]
        | _ -> []);
    evaluation;
    known_calls;
  }

(* Whether a term holds another. *)
and occurs part term =
  term = part
  ||
  match term with
  | Logic.Forall (_, _, body) | Logic.Exists (_, body) -> occurs part body
  | term -> List.exists (occurs part) (Logic.arguments term)

(* Where a node came from in its form's text, by its origin. *)
let span_of (source : source) origin =
  let spans = Lazy.force source.spans in
  if origin >= 0 && origin < Array.length spans then spans.(origin) else Syntax.Span.make 0 0

(* A node's source text, for messages. *)
let quote source origin =
  let span = span_of source origin in
  let text = Lazy.force source.text in
  if span.stop > span.start && span.stop <= String.length text then
    String.sub text span.start (span.stop - span.start)
  else "this expression"

(* Where a node of the form read here is. *)
let builtin ty = Types.builtin_of ty

let bounds (ty : Types.ty) =
  if Types.is_builtin Character ty then Some (Z.zero, Z.of_int 0x10FFFF) else Types.integer_range ty

let width (ty : Types.ty) = Option.map fst (Types.integer_bits ty)
let is_numeric (ty : Types.ty) = match ty with Types.Integer -> true | _ -> bounds ty <> None

(* A float type's widths in the solver's floating-point theory: its
   exponent's, and its significand's, with the hidden bit. *)
let float_format (ty : Types.ty) =
  match builtin ty with Some Float32 -> Some (8, 24) | Some Float64 -> Some (11, 53) | _ -> None

(* A float literal, bit for bit. *)
let float_literal (exponent, significand) value =
  let bits =
    if exponent = 8 then Z.extract (Z.of_int32 (Int32.bits_of_float value)) 0 32
    else Z.extract (Z.of_int64 (Int64.bits_of_float value)) 0 64
  in
  let fraction = significand - 1 in
  Logic.Operation
    ( "fp",
      [
        Logic.Bits (1, Z.extract bits (exponent + fraction) 1);
        Logic.Bits (exponent, Z.extract bits fraction exponent);
        Logic.Bits (fraction, Z.extract bits 0 fraction);
      ] )

(* IEEE 754 arithmetic, rounding to nearest with ties to even, and the
   lawful [==] and ordering of floats: every NaN is equal to every other
   and ordered after every number, and otherwise IEEE's, so [-0.0 == 0.0]. *)
let float_operation name left right =
  Logic.Operation (name, [ Logic.Operation ("RNE", []); left; right ])

let is_nan value = Logic.Operation ("fp.isNaN", [ value ])

let truncated value =
  Logic.Operation
    ( "fp.to_real",
      [ Logic.Operation ("fp.roundToIntegral", [ Logic.Operation ("RTZ", []); value ]) ] )

let float_equal left right =
  Logic.(Operation ("fp.eq", [ left; right ]) ||| (is_nan left &&& is_nan right))

let float_less left right =
  Logic.(not_ (is_nan left) &&& is_nan right ||| Operation ("fp.lt", [ left; right ]))

let is_bool ty = Types.is_builtin Bool ty

(* A type's name in the logic, unique across modules, as [Types.show] is not. *)
let rec type_key (ty : Types.ty) =
  match ty with
  | Named { path; arguments = [] } -> Path.show path
  | Named { path; arguments } ->
      Path.show path ^ "[" ^ String.concat ", " (List.map argument_key arguments) ^ "]"
  | _ -> Types.show ty

and argument_key = function
  | Types.Type ty -> type_key ty
  | argument -> Types.show_argument argument

let constructor_name (ty : Types.ty) variant =
  let type_name =
    match ty with Named { path = Top { name; _ }; _ } -> name | _ -> Types.show ty
  in
  Symbol.Constructor { type_key = type_key ty; type_name; variant }

let selector_name ty variant field = Symbol.Field { type_key = type_key ty; variant; field }
let is_standard_equal = Well_known.is Equal
let equal_trait = Well_known.path Equal

(* [frame] without the locals declared after [outer]: those of a block,
   an arm, or a loop end with it. *)
let end_scope ~(outer : frame) (frame : frame) =
  { frame with locals = Locals.filter (fun id _ -> Locals.mem id outer.locals) frame.locals }

(* A callee's generics paired with its type arguments, as the frame sees
   them. *)
let callee_substitution frame (signature : Types.signature) type_arguments =
  let rec pair (generics : Types.generic list) arguments =
    match (generics, arguments) with
    | generic :: generics, argument :: arguments ->
        (generic.generic, Types.substitute_argument frame.substitution argument)
        :: pair generics arguments
    | _ -> []
  in
  pair signature.generics type_arguments

(* A type's interface, when it is a type whose fields this package sees. *)
let visible_type context (ty : Types.ty) =
  match ty with
  | Named { path; arguments } when builtin ty = None -> (
      match Query.demand context.database Interface.Environment.interface path with
      | Some (Interface.Environment.Type_interface interface)
        when (not interface.opaque) || Path.package path = Path.package context.current ->
          let substitution =
            Option.value ~default:[] (Types.substitution_of interface.type_generics arguments)
          in
          Some (interface, substitution)
      | _ -> None)
  | _ -> None

(* A type's shape in the logic: its constructors, each with its variant's
   name, [None] for a record, and its fields, sorted by name so that
   reordering them changes no query. *)
let constructors context ty =
  match visible_type context ty with
  | Some (interface, substitution) -> (
      let fields (list : Types.field list) =
        List.sort compare
          (List.map
             (fun (field : Types.field) ->
               (field.field_name, Types.substitute substitution field.field_type))
             list)
      in
      match interface.shape with
      | Record list -> Some [ (None, fields list) ]
      | Sum variants ->
          Some
            (List.sort compare
               (List.map
                  (fun (variant : Types.variant) ->
                    ( Some variant.variant_name,
                      match variant.fields with Some list -> fields list | None -> [] ))
                  variants))
      | Todo_type | Builtin_type _ | Error_shape _ -> None)
  | None -> None

(* The fields of one constructor, in the order they are declared, which is
   how a call's arguments are numbered. *)
let declared_fields context ty variant =
  match visible_type context ty with
  | Some (interface, substitution) -> (
      let fields (list : Types.field list) =
        List.map
          (fun (field : Types.field) ->
            (field.field_name, Types.substitute substitution field.field_type))
          list
      in
      match (interface.shape, variant) with
      | Record list, None -> Some (fields list)
      | Sum variants, Some name -> (
          match
            List.find_opt (fun (variant : Types.variant) -> variant.variant_name = name) variants
          with
          | Some { fields = Some list; _ } -> Some (fields list)
          | Some { fields = None; _ } -> Some []
          | None -> None)
      | _ -> None)
  | None -> None

let rec sort_of context (ty : Types.ty) : Logic.sort =
  if is_numeric ty then Int
  else if is_bool ty then Bool
  else
    match (ty, float_format ty) with
    | _, Some (exponent, significand) -> Float (exponent, significand)
    | _ when Types.equal ty Types.unit ->
        (* One value, so any two are equal. *)
        if not (Hashtbl.mem context.datatypes "Unit") then begin
          Hashtbl.replace context.datatypes "Unit" ();
          context.declarations <-
            Logic.Datatype ("Unit", [ (Symbol.Unit, []) ]) :: context.declarations
        end;
        Uninterpreted "Unit"
    | Function function_type, _ ->
        (* One sort for each number of inputs, whatever the clauses, so a
           value keeps its sort where a function type is widened. *)
        Uninterpreted (Printf.sprintf "function/%d" (List.length function_type.inputs))
    | _ -> begin
        let name = type_key ty in
        (if not (Hashtbl.mem context.datatypes name) then
           match constructors context ty with
           | Some shape ->
               (* Marked first, so a recursive type's fields find it declared. *)
               Hashtbl.replace context.datatypes name ();
               let declaration =
                 Logic.Datatype
                   ( name,
                     List.map
                       (fun (variant, fields) ->
                         ( constructor_name ty variant,
                           List.map
                             (fun (field, field_type) ->
                               (selector_name ty variant field, sort_of context field_type))
                             fields ))
                       shape )
               in
               context.declarations <- declaration :: context.declarations
           | None -> ());
        Uninterpreted name
      end

(* Whether [==] on a type is the solver's equality: built in with identity
   semantics, or derived from fields that all are. *)
let rec structural context ?(seen = []) (ty : Types.ty) =
  if is_numeric ty || is_bool ty || Types.is_builtin Character ty || Types.equal ty Types.unit then
    true
  else if List.exists (Types.equal ty) seen then true
  else
    match (visible_type context ty, constructors context ty) with
    | Some (interface, _), Some shape ->
        List.exists is_standard_equal interface.derives
        && List.for_all
             (fun (_, fields) ->
               List.for_all
                 (fun (_, field_type) -> structural context ~seen:(ty :: seen) field_type)
                 fields)
             shape
    | _ -> false

(* Whether a term is a value of a type: within its bounds, and for a
   [Character], a Unicode scalar value, so never a surrogate. *)
(* The size of a built-in scalar on the 64-bit targets the address space
   is taken from. A type of another size, which may be zero, has none. *)
let scalar_bytes element : int option =
  match Types.builtin_of element with
  | Some (Int8 | UInt8 | Bool) -> Some 1
  | Some (Int16 | UInt16) -> Some 2
  | Some (Int32 | UInt32 | Float32 | Character) -> Some 4
  | Some (Int64 | UInt64 | USize | ISize | Float64) -> Some 8
  | _ -> None

let in_range ty term =
  match bounds ty with
  | Some (low, high) ->
      let in_bounds =
        Logic.(Operation ("<=", [ Integer low; term ]) &&& Operation ("<=", [ term; Integer high ]))
      in
      if Types.is_builtin Character ty then
        Logic.(
          in_bounds
          &&& not_
                (Operation ("<=", [ int 0xD800; term ]) &&& Operation ("<=", [ term; int 0xDFFF ])))
      else in_bounds
  | None -> Logic.Boolean true

(* Runs [make] the first time a fact is met in a definition's proof, for a
   fact that is stated once. *)
let once context stated make =
  if not (Hashtbl.mem context.stated stated) then begin
    Hashtbl.replace context.stated stated ();
    make ()
  end

(* A term with its quantifiers' bound names numbered in the order they
   appear, so two terms that differ only in those names are the same. *)
let canonical_binders term =
  let count = ref 0 in
  let rec walk renamed = function
    | Logic.Symbol name -> (
        match List.assoc_opt name renamed with
        | Some other -> Logic.Symbol other
        | None -> Logic.Symbol name)
    | ( Logic.Integer _ | Logic.Boolean _ | Logic.Bits _ | Logic.Apply _ | Logic.Operation _
      | Logic.Is _ ) as term ->
        Logic.map_arguments (walk renamed) term
    | Logic.Forall (bound, trigger, body) ->
        let bound, renamed = rename renamed bound in
        Logic.Forall (bound, List.map (walk renamed) trigger, walk renamed body)
    | Logic.Exists (bound, body) ->
        let bound, renamed = rename renamed bound in
        Logic.Exists (bound, walk renamed body)
  and rename renamed bound =
    List.fold_right
      (fun (name, sort) (bound, renamed) ->
        incr count;
        let other = Symbol.Variable { label = "binder"; numbers = [ !count ] } in
        ((other, sort) :: bound, (name, other) :: renamed))
      bound ([], renamed)
  in
  walk [] term

(* A value of a type that arrives from outside the known facts: a parameter,
   a call's result, a loop's havocked local. *)
let arrive context frame prefix ty =
  let value = fresh context frame prefix (sort_of context ty) in
  assume context frame (in_range ty value);
  value

(* A local bound to a value of a type. *)
let bind frame local ty term =
  {
    frame with
    locals = Locals.add local term frame.locals;
    types = Locals.add local ty frame.types;
  }

(* A type in a frame, substituted and normalized: a trait's [Self.Key]
   read for a [List] is a [USize]. *)
let substituted context frame ty =
  Interface.Impls.normalize context.database
    ~bounds:(fun _ -> [])
    (Types.substitute frame.substitution ty)

let local_type context frame local =
  Option.map (substituted context frame) (Locals.find_opt local frame.types)

let mentions_potential term =
  let rec walk = function
    | Logic.Apply ((Symbol.Potential _ | Symbol.Slack _), _) -> true
    | Logic.Forall (_, _, body) | Logic.Exists (_, body) -> walk body
    | term -> List.exists walk (Logic.arguments term)
  in
  walk term

(* Paths *)

let restrict frame condition = { frame with condition = Logic.( &&& ) frame.condition condition }

(* Joins paths: the condition is that one of them was taken, and each
   local whose values differ gets a fresh symbol each path defines. *)
let join context ?value_type frames =
  match frames with
  | [] -> None
  | [ (frame, value) ] -> Some (frame, value)
  | (first, _) :: _ ->
      let condition = Logic.disjunction (List.map (fun (frame, _) -> frame.condition) frames) in
      (* The joined condition is named, so that each later fact on the path
         names it rather than repeating every branch's condition, which
         would grow with each join. A callee's clause or body, read where
         nothing is checked, is an expression, whose few facts after a join
         repeat it less than a name and its definition cost. *)
      let is_expression = not first.checking in
      let condition =
        match condition with
        | Logic.Boolean _ | Logic.Symbol _ -> condition
        | _ when is_expression || Logic.mentions first.bound condition -> condition
        | _ ->
            let path = fresh context first "path" Logic.Bool in
            fact context first (Logic.equal path condition);
            path
      in
      let merged = { first with condition } in
      let define prefix sort pick =
        let values = List.map (fun ((frame : frame), item) -> (frame, pick frame item)) frames in
        match values with
        | (_, Some term) :: rest when List.for_all (fun (_, other) -> other = Some term) rest ->
            Some term
        | _ when List.exists (fun (_, term) -> term = None) values -> None
        | _
          when List.for_all
                 (fun (_, term) -> match term with Some (Logic.Boolean _) -> true | _ -> false)
                 values ->
            (* A [Bool] each path gives as a constant, such as a short-circuit
               operator's value, holds where a path that gives [true] was
               taken: the paths are exclusive. *)
            Some
              (Logic.disjunction
                 (List.filter_map
                    (fun ((frame : frame), term) ->
                      if term = Some (Logic.Boolean true) then Some frame.condition else None)
                    values))
        | _
          when is_expression
               || List.exists
                    (fun ((frame : frame), term) ->
                      Logic.mentions first.bound frame.condition
                      ||
                      match term with
                      | Some term -> Logic.mentions first.bound term
                      | None -> false)
                    values -> (
            (* Inside a quantifier, a fact about a fresh symbol could not
               mention the bound variable, and an expression's value needs
               no name, so the value is an [ite]. *)
            match List.rev values with
            | (_, Some last) :: earlier ->
                Some
                  (List.fold_left
                     (fun otherwise ((frame : frame), term) ->
                       match term with
                       | Some term -> Logic.ite frame.condition term otherwise
                       | None -> otherwise)
                     last earlier)
            | _ -> None)
        | _ ->
            let symbol = fresh context first prefix sort in
            List.iter
              (fun ((frame : frame), term) ->
                match term with
                | Some term ->
                    fact context first (Logic.( ==> ) frame.condition (Logic.equal symbol term))
                | None -> ())
              values;
            Some symbol
      in
      let locals =
        Locals.mapi
          (fun id term ->
            let sort =
              match local_type context first id with
              | Some ty -> sort_of context ty
              | None -> ( match term with Logic.Boolean _ -> Logic.Bool | _ -> Logic.Int)
            in
            match define "joined" sort (fun frame _ -> Locals.find_opt id frame.locals) with
            | Some joined -> joined
            | None -> term)
          first.locals
      in
      (* [self] and the part a lending method has lent change along paths
         too, like locals. *)
      let self =
        match first.self_type with
        | Some ty -> (
            match define "self" (sort_of context ty) (fun frame _ -> frame.self) with
            | Some joined -> Some joined
            | None -> first.self)
        | None -> first.self
      in
      let in_joined (frame : frame) amount =
        let renamed =
          Locals.fold
            (fun id joined renamed ->
              match Locals.find_opt id frame.locals with
              | Some own when own <> joined -> (own, joined) :: renamed
              | _ -> renamed)
            locals []
        in
        let renamed =
          match (frame.self, self) with
          | Some own, Some joined when own <> joined -> (own, joined) :: renamed
          | _ -> renamed
        in
        List.fold_left (fun amount (from, into) -> Logic.replace ~from ~into amount) amount renamed
      in
      (* At a join, a counter is a fresh symbol defined as an [ite] of the
         paths' costs, which a loop's per-iteration bound can see through. *)
      let spent =
        List.map
          (fun (key, term) ->
            let values =
              List.map
                (fun ((frame : frame), _) ->
                  ( frame.condition,
                    in_joined frame
                      (match List.assoc_opt key frame.spent with
                      | Some spent_term -> spent_term
                      | None -> term) ))
                frames
            in
            match values with
            | (_, first_value) :: rest
              when List.for_all (fun (_, variant) -> variant = first_value) rest ->
                (key, first_value)
            | _ ->
                let choice =
                  match List.rev values with
                  | (_, last) :: earlier ->
                      List.fold_left
                        (fun otherwise (condition, value) -> Logic.ite condition value otherwise)
                        last earlier
                  | [] -> term
                in
                if Logic.mentions first.bound choice || mentions_potential choice then (key, choice)
                else
                  let symbol = fresh context first "spent" Logic.Int in
                  fact context first (Logic.equal symbol choice);
                  (key, symbol))
          first.spent
      in
      let value =
        match value_type with
        | Some ty -> define "value" (sort_of context ty) (fun _ value -> value)
        | None -> None
      in
      let yielded_so_far =
        match context.yielded_part with
        | Some part -> (
            match
              define "parts"
                (sort_of context
                   (Types.Named { path = Well_known.path Sequence; arguments = [ Types.Type part ] }))
                (fun frame _ -> frame.yielded_so_far)
            with
            | Some joined -> Some joined
            | None -> first.yielded_so_far)
        | None -> first.yielded_so_far
      in
      Some ({ merged with locals; spent; self; yielded_so_far }, value)

let join_frames context frames =
  Option.map fst (join context (List.map (fun frame -> (frame, None)) frames))
