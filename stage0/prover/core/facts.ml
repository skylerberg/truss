let make_variable ?(numbers = []) label = Logic.Symbol.Variable { label; numbers }

type unsupported = {
  location : Obligation.location;
  construct : string;
  foreign_definition : string option;
}

exception Unsupported of unsupported

let raise_unsupported location format =
  Printf.ksprintf
    (fun construct -> raise (Unsupported { location; construct; foreign_definition = None }))
    format

let run_in_source (context : State.context) (source : State.source) read =
  try read ()
  with
  | Unsupported ({ foreign_definition = None; _ } as unsupported)
  when source.key <> Some context.home
  ->
    raise (Unsupported { unsupported with foreign_definition = Some source.name })

let raise_bug format = Compiler_bug.raise_bug ~stage:"Prover" format
let list_method_type_arguments ~self_type arguments = Types.Type self_type :: arguments

let read_parameter_name (parameter : Mir.parameter) =
  match Mir.find_local_name parameter.local with
  | Some name -> name
  | None -> raise_bug "a parameter that no definition names"

let rec show_callee (path : Path.t) =
  match path with
  | Top { name; _ } -> name
  | Method { owner = Impl { for_type; _ } | Derived { type_ = for_type; _ }; name; _ }
  | Method { owner = for_type; name; _ }
  | Member_constant { owner = for_type; name } ->
      show_callee for_type ^ "." ^ name
  | Impl _ | Derived _ | Test _ | Law_proof _ | Unresolved _ -> Path.show path

let is_in_recursion_group (context : State.context) node =
  let is_inherited_from declaration member =
    match context.lookups.mir.find_form_origin member with
    | Some (Inherited key, _) -> Path.equal key.path declaration
    | Some ((Written _ | Derived _), _) | None -> false
  in
  List.exists (Path.equal node) (context.lookups.list_recursion_group context.node)
  ||
  match context.node with
  | Method { owner; _ }
    when Option.is_some (Interface.Definition.find_trait_interface context.lookups.interface owner)
    ->
      List.exists (is_inherited_from context.node) (context.lookups.list_recursion_group node)
  | _ -> false

let list_clauses (requires : Mir.requirement list) =
  List.map (fun (requirement : Mir.requirement) -> requirement.clause) requires

let declare (context : State.context) (declaration : Logic.declaration) =
  match declaration with
  | Constant (name, _) | Function (name, _, _) ->
      if not (Tables.Symbol_table.mem context.declared name) then begin
        Tables.Symbol_table.replace context.declared name ();
        context.declarations <- declaration :: context.declarations
      end
  | Definition { symbol; _ } ->
      if not (Tables.Symbol_table.mem context.definitions symbol) then begin
        Tables.Symbol_table.replace context.definitions symbol ();
        context.declarations <- declaration :: context.declarations
      end
  | Datatype _ -> invalid_arg "Translate.declare: a datatype is declared by its sort"

let add_fact (context : State.context) fact = context.facts <- fact :: context.facts

let declare_value_symbol context (frame : State.frame) name sort =
  match List.rev frame.binders with
  | [] ->
      declare context (Logic.Constant (name, sort));
      Logic.Symbol name
  | outermost_first ->
      declare context
        (Logic.Function (name, List.map (fun (_, sort, _) -> sort) outermost_first, sort));
      Logic.Apply (name, List.map (fun (bound, _, _) -> Logic.Symbol bound) outermost_first)

let make_fresh_name (context : State.context) label =
  context.fresh <- context.fresh + 1;
  make_variable label ~numbers:[ context.fresh ]

let declare_fresh context frame label sort =
  let name = make_fresh_name context label in
  Tables.Symbol_table.replace context.fresh_order name context.fresh;
  declare_value_symbol context frame name sort

let mentions_fresh_after (context : State.context) mark term =
  let is_fresh_after name =
    match Tables.Symbol_table.find_opt context.fresh_order name with
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

let close_over_binders (frame : State.frame) term =
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

let add_scoped_fact (context : State.context) (frame : State.frame) term =
  let named = List.filter (fun name -> Logic.mentions [ name ] term) frame.bound in
  if List.for_all (fun name -> List.mem_assoc name context.scopes) named then
    match List.find_opt (fun (name, _) -> List.mem name named) context.scopes with
    | Some (_, facts) -> facts := term :: !facts
    | None -> ()

let list_scope_facts (context : State.context) names =
  List.concat_map
    (fun (name, facts) -> if List.mem name names then List.rev !facts else [])
    context.scopes

let add_quantifier_facts ~binders (context : State.context) term =
  let is_stated bound fact =
    List.for_all
      (fun name -> List.mem name bound || not (Logic.mentions [ name ] fact))
      context.quantifier_symbols
  in
  let rec walk positive bound term =
    let collect_facts symbols =
      let bound = List.map fst symbols @ bound in
      ( bound,
        List.filter (is_stated bound)
          (Option.value ~default:[] (Tables.Term_table.find_opt context.quantifier_facts term)) )
    in
    match term with
    | Logic.Forall (symbols, trigger, body) when positive ->
        let bound, facts = collect_facts symbols in
        let body = walk positive bound body in
        Logic.Forall
          ( symbols,
            trigger,
            match facts with [] -> body | facts -> Logic.( ==> ) (Logic.conjunction facts) body )
    | Logic.Exists (symbols, body) when not positive ->
        let bound, facts = collect_facts symbols in
        let body = walk positive bound body in
        Logic.Exists
          ( symbols,
            match facts with [] -> body | facts -> Logic.( &&& ) (Logic.conjunction facts) body )
    | Logic.Operation (((And | Or) as operator), parts) ->
        Logic.Operation (operator, List.map (walk positive bound) parts)
    | Logic.Operation (Implies, [ premise; conclusion ]) ->
        Logic.Operation
          (Implies, [ walk (not positive) bound premise; walk positive bound conclusion ])
    | Logic.Operation (Not, [ inner ]) -> Logic.Operation (Not, [ walk (not positive) bound inner ])
    | term -> term
  in
  walk true binders term

let add_frame_fact context (frame : State.frame) term =
  if not (Logic.mentions frame.bound term) then add_fact context term
  else add_scoped_fact context frame term

let assume context (frame : State.frame) term =
  match term with
  | Logic.Boolean true -> ()
  | _ ->
      let guarded = Logic.( ==> ) frame.condition term in
      if not (Logic.mentions frame.bound term || Logic.mentions frame.bound frame.condition) then
        add_fact context guarded
      else add_scoped_fact context frame guarded

let locate (context : State.context) (source : State.source) origin =
  if source.key = Some context.home then Obligation.Node origin else Whole_definition

let insert_line_before_body (context : State.context) (line : Obligation.message) =
  let names = context.lookups.interface.names in
  let text = names.read_text context.home in
  let brace =
    match names.read_definition context.home with
    | { kind = Function { body; _ }; _ } ->
        Some (Source.Definition_span.locate (names.read_spans context.home) body.id).start
    | _ -> None
  in
  let edit at before =
    Some { Obligation.at; replacement = (Obligation.Text (before ^ "  ") :: line) @ [ Text "\n" ] }
  in
  match brace with
  | Some at when at > 0 && text.[at - 1] = '\n' ->
      edit (Source.Definition_span.make_zero_width at) ""
  | Some at when at > 0 && text.[at - 1] = ' ' ->
      edit (Source.Definition_span.make (at - 1) at) "\n"
  | _ -> None

let make_panic_fix (context : State.context) =
  let names = context.lookups.interface.names in
  let edit =
    match names.read_definition context.home with
    | { kind = Function { signature; _ }; _ } -> (
        let locate id = Source.Definition_span.locate (names.read_spans context.home) id in
        match
          ( List.find_opt
              (fun (clause : Syntax.clause) -> match clause.kind with Uses _ -> true | _ -> false)
              signature.clauses,
            signature.clauses )
        with
        | Some uses, _ ->
            Some
              {
                Obligation.at = Source.Definition_span.make_zero_width (locate uses.id).stop;
                replacement = [ Text ", Panic" ];
              }
        | None, first :: _ ->
            Some
              {
                Obligation.at = Source.Definition_span.make_zero_width (locate first.id).start;
                replacement = [ Text "uses Panic\n  " ];
              }
        | None, [] -> insert_line_before_body context [ Text "uses Panic" ])
    | _ -> None
  in
  match edit with
  | Some edit when not context.inherits_precondition ->
      [ { Obligation.title = [ Text "Add `uses Panic`" ]; edits = [ edit ] } ]
  | Some _ | None -> []

let make_requires_fix (context : State.context) required =
  match insert_line_before_body context (Obligation.Text "requires " :: required) with
  | Some edit when not context.inherits_precondition ->
      [
        {
          Obligation.title = (Obligation.Text "Add `requires " :: required) @ [ Text "`" ];
          edits = [ edit ];
        };
      ]
  | Some _ | None -> []

let find_parameter_name (context : State.context) symbol =
  if List.mem symbol context.entry then
    match List.assoc_opt symbol context.values with Some name -> Some name | None -> Some "self"
  else None

let collect_printed printed =
  if List.mem None printed then None else Some (List.filter_map Fun.id printed)

let show_truss_value context term =
  let parenthesize level inner text = if inner < level then "(" ^ text ^ ")" else text in
  let rec show_arithmetic level = function
    | Logic.Operation (Add, (_ :: _ :: _ as parts)) -> show_infix level 1 " + " parts
    | Logic.Operation (Multiply, (_ :: _ :: _ as parts)) -> show_infix level 2 " * " parts
    | Logic.Operation (Subtract, [ left; right ]) ->
        Option.map
          (fun printed -> parenthesize level 1 (String.concat " - " printed))
          (collect_printed [ show_arithmetic 1 left; show_arithmetic 2 right ])
    | Logic.Operation (Negate, [ Logic.Operation (Negate, [ inner ]) ]) ->
        show_arithmetic level inner
    | Logic.Operation (Negate, [ inner ]) ->
        Option.map (fun printed -> parenthesize level 3 ("-" ^ printed)) (show_arithmetic 4 inner)
    | Logic.Integer value when Z.sign value < 0 && level > 0 -> Some ("(" ^ Z.to_string value ^ ")")
    | Logic.Apply (Logic.Symbol.Field { field; variant = None; _ }, [ receiver ]) ->
        Option.map (fun receiver -> receiver ^ "." ^ field) (show_arithmetic 4 receiver)
    | Logic.Symbol symbol -> find_parameter_name context symbol
    | Logic.Integer value -> Some (Z.to_string value)
    | Logic.Boolean value -> Some (if value then "true" else "false")
    | _ -> None
  and show_infix level inner separator parts =
    Option.map
      (fun printed -> parenthesize level inner (String.concat separator printed))
      (collect_printed (List.map (show_arithmetic inner) parts))
  in
  show_arithmetic 0 term

let show_truss_goal context term =
  let show_value = show_truss_value context in
  let rec print = function
    | Logic.Operation (Less, [ left; right ]) -> show_comparison left "<" right
    | Logic.Operation (Less_equal, [ left; right ]) -> show_comparison left "<=" right
    | Logic.Operation (Greater, [ left; right ]) -> show_comparison left ">" right
    | Logic.Operation (Greater_equal, [ left; right ]) -> show_comparison left ">=" right
    | Logic.Operation (Equal, [ left; right ]) -> show_comparison left "==" right
    | Logic.Operation (And, parts) -> join_parts " && " parts
    | Logic.Operation (Or, parts) -> join_parts " || " parts
    | Logic.Operation (Not, [ inner ]) -> Option.map (Printf.sprintf "!(%s)") (print inner)
    | Logic.Operation (Implies, [ premise; conclusion ]) -> (
        match (print premise, print conclusion) with
        | Some premise, Some conclusion -> Some (Printf.sprintf "(%s) ==> (%s)" premise conclusion)
        | _ -> None)
    | term -> show_value term
  and show_comparison left spelling right =
    match (show_value left, show_value right) with
    | Some left, Some right -> Some (Printf.sprintf "%s %s %s" left spelling right)
    | _ -> None
  and join_parts separator parts =
    Option.map
      (fun printed -> "(" ^ String.concat separator printed ^ ")")
      (collect_printed (List.map print parts))
  in
  let printed =
    match term with
    | Logic.Operation (And, parts) ->
        Option.map (String.concat " && ") (collect_printed (List.map print parts))
    | Logic.Operation (Or, parts) ->
        Option.map (String.concat " || ") (collect_printed (List.map print parts))
    | term -> print term
  in
  if List.exists (fun symbol -> List.mem symbol context.entry) (Logic.list_free_constants term) then
    printed
  else None

let add_requires (context : State.context) (frame : State.frame) (required : Obligation.message) =
  let required =
    match context.condition with
    | [] -> required
    | condition -> required @ [ Obligation.Text (" when " ^ Types.show_condition condition) ]
  in
  match frame.condition with
  | Logic.Boolean true -> make_requires_fix context required
  | condition -> (
      match show_truss_goal context condition with
      | Some premise ->
          make_requires_fix context
            ((Obligation.Text ("(" ^ premise ^ ") ==> (") :: required) @ [ Obligation.Text ")" ])
      | None -> make_requires_fix context required)

let rec make_closed_obligation ?template_clause context (frame : State.frame) code location message
    goal =
  if not frame.makes_obligations then None
  else if not (Logic.mentions frame.bound goal || Logic.mentions frame.bound frame.condition) then
    Some (make_obligation ?template_clause context frame code location message goal)
  else
    let names = List.map (fun (name, _, _) -> name) frame.binders in
    let goal =
      match list_scope_facts context names with
      | [] -> goal
      | facts -> Logic.( ==> ) (Logic.conjunction facts) goal
    in
    match close_over_binders frame (Logic.( ==> ) frame.condition goal) with
    | Some closed ->
        Some
          (make_obligation ?template_clause context
             { frame with condition = Logic.Boolean true }
             code location message closed)
    | None -> None

and make_obligation ?template_clause (context : State.context) (frame : State.frame) code location
    message goal : Obligation.t =
  let query =
    Logic.prune
      {
        declarations = List.rev context.declarations;
        facts = List.rev context.facts;
        goal = Logic.( ==> ) frame.condition goal;
      }
  in
  {
    code;
    location;
    message;
    cited = None;
    fixes = [];
    query;
    values = context.values;
    decisions = List.rev context.decisions;
    locals =
      (let is_parameter = function
         | Logic.Symbol symbol -> List.mem_assoc symbol context.values
         | _ -> false
       in
       Locals.fold
         (fun local term shown ->
           match Tables.Local_table.find_opt context.local_names local with
           | Some name when not (is_parameter term || List.mem_assoc term shown) ->
               (term, name) :: shown
           | _ -> shown)
         frame.locals
         (match frame.result with
         | Some term when not (is_parameter term) -> [ (term, "result") ]
         | _ -> []));
    template_clause;
  }

let is_panic_obligation : Diagnostic.Code.prover -> bool = function
  | Overflow | Division | Shift | Panic -> true
  | _ -> false

let oblige ?template_clause ?cited ?(fixes = []) ?holds_when (context : State.context)
    (frame : State.frame) code location message goal =
  let holds_when = Option.value holds_when ~default:context.obligation_condition in
  if
    (is_panic_obligation code && context.panics)
    || (Option.is_some context.panic_condition && not (is_panic_obligation code))
    || not
         (holds_when = context.condition
         || (code = Diagnostic.Code.Termination && context.keeps_termination)
         || (is_panic_obligation code && context.keeps_failures))
  then assume context frame goal
  else
    match
      make_closed_obligation ?template_clause context frame code location message
        (add_quantifier_facts
           ~binders:(List.map (fun (name, _, _) -> name) frame.binders)
           context goal)
    with
    | Some obligation ->
        let is_home_body = frame.source.key = Some context.home && frame.makes_obligations in
        let fixes =
          match fixes with
          | [] when is_home_body -> (
              match show_truss_goal context goal with
              | Some required -> add_requires context frame [ Text required ]
              | None -> [])
          | fixes -> fixes
        in
        let fixes =
          if is_panic_obligation code && context.can_declare_panic && is_home_body then
            fixes @ make_panic_fix context
          else fixes
        in
        context.obligations <- { obligation with cited; fixes } :: context.obligations;
        assume context frame goal
    | None -> ()

let reject_recursion_through_supplied_code (context : State.context) (frame : State.frame) location
    (statement : Mir.statement) =
  let reject text = oblige context frame Termination location [ Text text ] (Logic.Boolean false) in
  let reject_supply (supplier : Mir.Call_edges.supplier) code =
    let recursive = List.filter (is_in_recursion_group context) code in
    (match supplier with
    | Named_function path when List.exists (Path.equal path) recursive ->
        reject
          (Printf.sprintf
             "Naming `%s` as a value reaches back here, and such a use passes no arguments the \
              prover can compare, so the recursion cannot be shown to end: write it as a direct \
              call on a part."
             (Path.show path))
    | Named_function _ | Call | Conversion_to_any | Provide -> ());
    List.iter
      (fun owner ->
        let owner = Path.show owner in
        reject
          (match supplier with
          | Call ->
              Printf.sprintf
                "This call uses `%s` where a bound needs it, and its methods reach back here. Such \
                 a use passes no arguments the prover can compare, so the recursion cannot be \
                 shown to end: write it as a direct call on a part."
                owner
          | Named_function path ->
              Printf.sprintf
                "Naming `%s` as a value uses `%s` where a bound needs it, and its methods reach \
                 back here. Such a use passes no arguments the prover can compare, so the \
                 recursion cannot be shown to end."
                (Path.show path) owner
          | Conversion_to_any ->
              Printf.sprintf
                "This conversion to `any` gives `%s`, whose methods call back here, so the prover \
                 cannot show that the recursion ends."
                owner
          | Provide ->
              Printf.sprintf
                "This `provide` gives `%s`, whose methods call back here, so the prover cannot \
                 show that the recursion ends."
                owner))
      (List.sort_uniq Path.compare
         (List.filter_map
            (fun (node : Path.t) -> match node with Method { owner; _ } -> Some owner | _ -> None)
            recursive))
  in
  if context.terminates && frame.makes_obligations then
    List.iter
      (fun (edge : Mir.Call_edges.edge) ->
        match edge with Calls _ -> () | Supplies { supplier; code } -> reject_supply supplier code)
      (Mir.Call_edges.list_statement_edges context.lookups.interface frame.substitution statement)

let find_recursive_callee (context : State.context) (frame : State.frame) location callee =
  let resolution =
    Mir.Call_edges.resolve_callee context.lookups.interface frame.substitution callee
  in
  let reject target origin =
    oblige context frame Termination location
      [
        Text
          (Printf.sprintf
             "This call to `%s` reaches back here through code that its `impl` %s. No measure can \
              be stated for that code, so the recursion cannot be shown to end."
             (show_callee target) origin);
      ]
      (Logic.Boolean false);
    None
  in
  let recursive_callee =
    match resolution.target with
    | Some target when frame.makes_obligations && is_in_recursion_group context target -> (
        match context.lookups.mir.find_form_origin target with
        | Some (Derived _, _) when context.terminates -> reject target "derives"
        | Some (Inherited _, _) when context.terminates -> reject target "inherits from its trait"
        | Some ((Written _ | Derived _ | Inherited _), _) | None -> Some target)
    | Some _ | None -> None
  in
  (resolution, recursive_callee)

let reject_uncompared_recursion (context : State.context) frame location recursive_callee ~describe
    =
  if context.terminates then
    Option.iter
      (fun callee ->
        oblige context frame Termination location
          [ Text (describe (show_callee callee)) ]
          (Logic.Boolean false))
      recursive_callee

let quote (source : State.source) origin =
  match source.key with
  | Some key -> Obligation.Quote (key, origin)
  | None -> Text "this expression"

let quote_span text (span : Source.Definition_span.t) =
  if span.stop = span.start then "this expression" else Source.Definition_span.quote text span

let quote_origin (context : State.context) (frame : State.frame) origin =
  if frame.source.key <> Some context.home then
    raise_bug "a quote of %s, outside the definition being proven" frame.source.name;
  let names = context.lookups.interface.names in
  quote_span (names.read_text context.home)
    (Source.Definition_span.locate (names.read_spans context.home) origin)

let find_bounds (ty : Types.ty) =
  if Types.is_builtin Character ty then Some (Z.zero, Z.of_int 0x10FFFF)
  else Types.find_integer_range ty

let is_numeric (ty : Types.ty) = match ty with Types.Integer -> true | _ -> find_bounds ty <> None

let find_float_format (ty : Types.ty) =
  match Types.find_builtin ty with
  | Some Float32 -> Some (8, 24)
  | Some Float64 -> Some (11, 53)
  | _ -> None

let is_bool ty = Types.is_builtin Bool ty

let make_constructor_symbol (ty : Types.ty) variant =
  Logic.Symbol.Constructor { type_ = ty; variant }

let make_selector_symbol ty variant field = Logic.Symbol.Field { type_ = ty; variant; field }
let is_standard_equal = Well_known.is Equal

let find_visible_type (context : State.context) (ty : Types.ty) =
  match ty with
  | Named { path; arguments } when Types.find_builtin ty = None -> (
      match Interface.Definition.find_interface context.lookups.interface path with
      | Some (Interface.Environment.Type_interface interface)
        when (not interface.opaque)
             || Path.locate_package path = Path.locate_package context.current ->
          let substitution = Types.make_substitution interface.type_generics arguments in
          Some (interface, substitution)
      | _ -> None)
  | _ -> None

let find_constructors context ty =
  match find_visible_type context ty with
  | Some (interface, substitution) -> (
      let list_fields (list : Types.field list) =
        List.sort compare
          (List.map
             (fun (field : Types.field) ->
               (field.field_name, Types.substitute substitution field.field_type))
             list)
      in
      match interface.shape with
      | Record list -> Some [ (None, list_fields list) ]
      | Sum variants ->
          Some
            (List.sort compare
               (List.map
                  (fun (variant : Types.variant) ->
                    ( Some variant.variant_name,
                      match variant.fields with Some list -> list_fields list | None -> [] ))
                  variants))
      | Todo_type | Builtin_type _ -> None)
  | None -> None

let rec declare_sort (context : State.context) (ty : Types.ty) : Logic.sort =
  if is_numeric ty then Int
  else if is_bool ty then Bool
  else
    match (ty, find_float_format ty) with
    | _, Some (exponent, significand) -> Float (exponent, significand)
    | _ when Types.equal ty Types.unit ->
        if not (Tables.Type_table.mem context.datatypes ty) then begin
          Tables.Type_table.replace context.datatypes ty ();
          context.declarations <-
            Logic.Datatype (ty, [ (Logic.Symbol.Unit, []) ]) :: context.declarations
        end;
        Type_sort ty
    | Function function_type, _ -> Function_sort (List.length function_type.inputs)
    | _ -> begin
        (if not (Tables.Type_table.mem context.datatypes ty) then
           match find_constructors context ty with
           | Some shape ->
               Tables.Type_table.replace context.datatypes ty ();
               let declaration =
                 Logic.Datatype
                   ( ty,
                     List.map
                       (fun (variant, fields) ->
                         ( make_constructor_symbol ty variant,
                           List.map
                             (fun (field, field_type) ->
                               ( make_selector_symbol ty variant field,
                                 declare_sort context field_type ))
                             fields ))
                       shape )
               in
               context.declarations <- declaration :: context.declarations
           | None -> ());
        Type_sort ty
      end

let rec is_equality_identity context ?(seen = []) (ty : Types.ty) =
  is_numeric ty || is_bool ty || Types.is_builtin Character ty || Types.equal ty Types.unit
  || List.exists (Types.equal ty) seen
  ||
  match (find_visible_type context ty, find_constructors context ty) with
  | Some (interface, _), Some shape ->
      List.exists is_standard_equal interface.derives
      && List.for_all
           (fun (_, fields) ->
             List.for_all
               (fun (_, field_type) -> is_equality_identity context ~seen:(ty :: seen) field_type)
               fields)
           shape
  | _ -> false

let make_in_range ty term =
  match find_bounds ty with
  | Some (low, high) ->
      let in_bounds = Logic.(less_equal (Integer low) term &&& less_equal term (Integer high)) in
      if Types.is_builtin Character ty then
        Logic.(in_bounds &&& not_ (less_equal (int 0xD800) term &&& less_equal term (int 0xDFFF)))
      else in_bounds
  | None -> Logic.Boolean true

let run_once (context : State.context) stated make =
  if not (Tables.Stated_table.mem context.stated stated) then begin
    Tables.Stated_table.replace context.stated stated ();
    make ()
  end

let arrive context frame prefix ty =
  let value = declare_fresh context frame prefix (declare_sort context ty) in
  assume context frame (make_in_range ty value);
  value

let read_or_arrive context frame prefix ty read =
  try read frame with Unsupported _ -> arrive context frame prefix ty

let bind (frame : State.frame) local ty term =
  {
    frame with
    State.locals = Locals.add local term frame.locals;
    types = Locals.add local ty frame.types;
  }

let list_definition_bounds (lookups : Lookups.t) ~(current : Path.t) ~(condition : Types.condition)
    : Interface.Impls.bounds =
  let list_impl_generics path =
    match Interface.Definition.find_impl_interface lookups.interface path with
    | Some interface -> interface.impl_generics
    | None -> []
  in
  let generics =
    match current with
    | Method { owner; _ } -> (
        list_impl_generics owner
        @
        match Interface.Impls.read_signature lookups.interface current with
        | Some signature -> signature.generics
        | None -> [])
    | _ -> (
        match Interface.Impls.read_signature lookups.interface current with
        | Some signature -> signature.generics
        | None -> list_impl_generics current)
  in
  let list_self_bounds (parameter : Types.parameter) =
    match
      if Types.is_self_parameter parameter then
        Interface.Definition.find_trait_interface lookups.interface parameter.owner
      else None
    with
    | Some interface ->
        [
          {
            Types.trait = parameter.owner;
            trait_arguments = Types.list_generic_arguments interface.trait_generics;
            associated = [];
          };
        ]
    | None -> []
  in
  Interface.Impls.add_condition_bounds
    (fun parameter -> list_self_bounds parameter @ Types.list_bounds generics parameter)
    condition

let substitute_type (context : State.context) (frame : State.frame) ty =
  (Interface.Impls.normalize context.lookups.interface ~list_bounds:context.bounds)
    (Types.substitute frame.substitution ty)

let find_local_type context frame local =
  Option.map (substitute_type context frame) (Locals.find_opt local frame.types)

let is_potential = function
  | Logic.Apply ((Logic.Symbol.Potential _ | Logic.Symbol.Slack _), _) -> true
  | Logic.Apply (_, arguments) ->
      List.exists
        (function Logic.Symbol (Logic.Symbol.Potential_measure _) -> true | _ -> false)
        arguments
  | _ -> false

let mentions_potential term =
  let rec walk term =
    is_potential term
    ||
    match term with
    | Logic.Forall (_, _, body) | Logic.Exists (_, body) -> walk body
    | term -> List.exists walk (Logic.list_arguments term)
  in
  walk term

let rec list_potentials term =
  if is_potential term then [ term ]
  else List.concat_map list_potentials (Logic.list_arguments term)

let rec take_potential_as_zero term =
  if is_potential term then Logic.Integer Z.zero
  else Logic.map_arguments take_potential_as_zero term

let restrict (frame : State.frame) condition =
  { frame with State.condition = Logic.( &&& ) frame.condition condition }

let merge_known_on_paths (paths : (Logic.term * State.frame) list) =
  let merge_known pick ~is_same ~on_differing =
    let keys =
      List.fold_left
        (fun keys ((_, frame) : Logic.term * State.frame) ->
          Locals.fold (fun key _ keys -> Locals.add key () keys) (pick frame) keys)
        Locals.empty paths
    in
    Locals.mapi
      (fun key () ->
        let each =
          List.map (fun (condition, frame) -> (condition, Locals.find_opt key (pick frame))) paths
        in
        match each with
        | (_, Some one) :: rest
          when List.for_all
                 (fun (_, other) ->
                   match other with Some other -> is_same one other | None -> false)
                 rest ->
            one
        | _ -> on_differing each)
      keys
  in
  let guard condition = List.map (fun (on, known) -> (Logic.( &&& ) condition on, known)) in
  let guard_each each =
    List.concat_map
      (fun (condition, known) -> guard condition (Option.value ~default:[] known))
      each
  in
  let aliases = merge_known (fun frame -> frame.aliases) ~is_same:( = ) ~on_differing:guard_each in
  let lends = merge_known (fun frame -> frame.lends) ~is_same:( == ) ~on_differing:guard_each in
  (aliases, lends)

let name_path_condition context (frame : State.frame) condition =
  match condition with
  | Logic.Boolean _ | Logic.Symbol _ -> condition
  | _ when (not frame.makes_obligations) || Logic.mentions frame.bound condition -> condition
  | _ ->
      let path = declare_fresh context frame "path" Logic.Bool in
      add_frame_fact context frame (Logic.equal path condition);
      path

let merge context ?value_type ~condition
    (paths : (Logic.term * State.frame * Logic.term option) list) =
  let first = match paths with (_, first, _) :: _ -> first | [] -> raise_bug "no paths meet" in
  let is_expression = not first.makes_obligations in
  let aliases, lends = merge_known_on_paths (List.map (fun (on, frame, _) -> (on, frame)) paths) in
  let merged = { first with condition; aliases; lends } in
  let choose values =
    match List.rev values with
    | (_, _, last) :: earlier ->
        List.fold_left (fun otherwise (on, _, term) -> Logic.ite on term otherwise) last earlier
    | [] -> raise_bug "a value that no path gives"
  in
  let define prefix sort (values : (Logic.term * State.frame * Logic.term) list) =
    match values with
    | (_, _, term) :: rest
      when List.for_all (fun (_, _, other) -> other == term || other = term) rest ->
        term
    | _
      when List.for_all
             (fun (_, _, term) -> match term with Logic.Boolean _ -> true | _ -> false)
             values ->
        Logic.disjunction
          (List.filter_map
             (fun (on, _, term) -> if term = Logic.Boolean true then Some on else None)
             values)
    | _
      when is_expression
           || List.exists
                (fun (on, (frame : State.frame), term) ->
                  Logic.mentions first.bound on
                  || Logic.mentions first.bound frame.condition
                  || Logic.mentions first.bound term)
                values ->
        choose values
    | _ ->
        let symbol = declare_fresh context first prefix sort in
        List.iter
          (fun (_, (frame : State.frame), term) ->
            add_frame_fact context first (Logic.( ==> ) frame.condition (Logic.equal symbol term)))
          values;
        symbol
  in
  let find_held pick =
    let values =
      List.filter_map
        (fun (on, frame, _) -> Option.map (fun term -> (on, frame, term)) (pick frame))
        paths
    in
    if List.length values = List.length paths then Some values else None
  in
  let keys =
    List.fold_left
      (fun keys (_, (frame : State.frame), _) ->
        Locals.fold (fun key _ keys -> Locals.add key () keys) frame.locals keys)
      Locals.empty paths
  in
  let locals =
    Locals.mapi
      (fun id () ->
        match find_held (fun frame -> Locals.find_opt id frame.locals) with
        | Some values ->
            let sort =
              match find_local_type context first id with
              | Some ty -> declare_sort context ty
              | None -> (
                  match values with (_, _, Logic.Boolean _) :: _ -> Logic.Bool | _ -> Logic.Int)
            in
            define "joined" sort values
        | None -> (
            match
              List.find_map
                (fun (_, (frame : State.frame), _) -> Locals.find_opt id frame.locals)
                paths
            with
            | Some term -> term
            | None -> raise_bug "a local that no path binds"))
      keys
  in
  let types =
    List.fold_left
      (fun types (_, (frame : State.frame), _) ->
        Locals.union (fun _ ty _ -> Some ty) types frame.types)
      Locals.empty paths
  in
  let self =
    match (first.self_type, find_held (fun frame -> frame.self)) with
    | Some ty, Some values -> Some (define "self" (declare_sort context ty) values)
    | _ -> first.self
  in
  let rename_into_joined (frame : State.frame) amount =
    let renamed =
      Locals.fold
        (fun id joined renamed ->
          match Locals.find_opt id frame.locals with
          | Some incoming when incoming != joined && incoming <> joined ->
              (incoming, joined) :: renamed
          | _ -> renamed)
        locals []
    in
    let renamed =
      match (frame.self, self) with
      | Some incoming, Some joined when incoming <> joined -> (incoming, joined) :: renamed
      | _ -> renamed
    in
    List.fold_left (fun amount (from, into) -> Logic.replace ~from ~into amount) amount renamed
  in
  let spent =
    List.map
      (fun (key, term) ->
        let values =
          List.map
            (fun (on, (frame : State.frame), _) ->
              ( on,
                rename_into_joined frame
                  (match List.assoc_opt key frame.spent with
                  | Some spent_term -> spent_term
                  | None -> term) ))
            paths
        in
        match values with
        | (_, first_value) :: rest
          when List.for_all (fun (_, other) -> other == first_value || other = first_value) rest ->
            (key, first_value)
        | _ ->
            let choice =
              match List.rev values with
              | (_, last) :: earlier ->
                  List.fold_left
                    (fun otherwise (on, value) -> Logic.ite on value otherwise)
                    last earlier
              | [] -> term
            in
            if Logic.mentions first.bound choice || mentions_potential choice then (key, choice)
            else
              let symbol = declare_fresh context first "spent" Logic.Int in
              add_frame_fact context first (Logic.equal symbol choice);
              (key, symbol))
      first.spent
  in
  let value =
    let values =
      List.filter_map
        (fun (on, frame, value) -> Option.map (fun term -> (on, frame, term)) value)
        paths
    in
    if values = [] || List.length values <> List.length paths then None
    else
      match value_type with
      | Some ty -> Some (define "value" (declare_sort context ty) values)
      | None -> Some (choose values)
  in
  let yielded_so_far =
    match (context.yielded_part, find_held (fun frame -> frame.yielded_so_far)) with
    | Some part, Some values ->
        Some
          (define "parts"
             (declare_sort context
                (Types.Named
                   { path = Well_known.make_path Sequence; arguments = [ Types.Type part ] }))
             values)
    | _ -> first.yielded_so_far
  in
  ({ merged with locals; types; spent; self; yielded_so_far }, value)

let join context ?value_type frames =
  match frames with
  | [] -> None
  | [ (frame, value) ] -> Some (frame, value)
  | (first, _) :: _ ->
      let condition =
        name_path_condition context first
          (Logic.disjunction (List.map (fun ((frame : State.frame), _) -> frame.condition) frames))
      in
      Some
        (merge context ?value_type ~condition
           (List.map (fun ((frame : State.frame), value) -> (frame.condition, frame, value)) frames))

let join_frames context frames =
  Option.map fst (join context (List.map (fun frame -> (frame, None)) frames))
