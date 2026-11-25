let make_variable ?(numbers = []) label = Logic.Symbol.Variable { label; numbers }

type unsupported = {
  location : Obligation.location;
  construct : Catalog.Prover.construct;
  foreign_definition : string option;
}

exception Unsupported of unsupported

let is_home (context : State.context) (source : State.source) =
  source.key = context.home && Path.equal source.definition context.home.path

let is_in_home_package (context : State.context) (source : State.source) =
  Path.compare_package
    (Path.locate_package source.definition)
    (Path.locate_package context.home.path)
  = 0

let raise_unsupported location construct =
  raise (Unsupported { location; construct; foreign_definition = None })

let run_in_source (context : State.context) (source : State.source) read =
  try read ()
  with
  | Unsupported ({ foreign_definition = None; _ } as unsupported)
  when not (is_home context source)
  ->
    raise (Unsupported { unsupported with foreign_definition = Some source.name })

let raise_bug format = Compiler_bug.raise_bug ~stage:"Prover" format
let list_method_type_arguments ~self_type arguments = Types.Type self_type :: arguments

let read_parameter_name (parameter : Mir.parameter) =
  match Mir.find_local_name parameter.local with
  | Some name -> name
  | None -> raise_bug "a parameter that no definition names"

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
  let declare_symbol name arguments =
    if not (Tables.Symbol_table.mem context.declared name) then begin
      Tables.Symbol_table.replace context.declared name arguments;
      context.declarations <- declaration :: context.declarations
    end
  in
  match declaration with
  | Constant (name, _) -> declare_symbol name []
  | Function (name, arguments, _) -> declare_symbol name arguments
  | Definition { symbol; _ } ->
      if not (Tables.Symbol_table.mem context.definitions symbol) then begin
        Tables.Symbol_table.replace context.definitions symbol ();
        context.declarations <- declaration :: context.declarations
      end
  | Datatype _ -> invalid_arg "Translate.declare: a datatype is declared by its sort"

let find_argument_sorts (context : State.context) symbol =
  Tables.Symbol_table.find_opt context.declared symbol

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
    | Logic.Operation (Ite, [ condition; then_; else_ ]) ->
        Logic.Operation (Ite, [ condition; walk positive bound then_; walk positive bound else_ ])
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
  if is_home context source then Obligation.Node origin else Whole_definition

let add_hole (context : State.context) hole =
  if not (List.mem hole context.holes) then context.holes <- hole :: context.holes

let find_signature (context : State.context) =
  match context.lookups.interface.names.read_definition context.home with
  | { kind = Function { signature; body; _ }; _ } -> Some (signature, body)
  | _ -> None

let make_panic_fix (context : State.context) : Catalog.Prover.fix list =
  match find_signature context with
  | Some (signature, body) when not context.inherits_precondition ->
      [
        Add_panic
          (match
             ( List.find_opt
                 (fun (clause : Syntax.clause) ->
                   match clause.kind with Uses _ -> true | _ -> false)
                 signature.clauses,
               signature.clauses )
           with
          | Some uses, _ -> After_uses (Written uses.id)
          | None, first :: _ -> Before_clause (Written first.id)
          | None, [] -> Before_body (Written body.id));
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

let add_requires (context : State.context) (frame : State.frame) required : Catalog.Prover.fix list
    =
  match find_signature context with
  | Some (_, body) when not context.inherits_precondition ->
      [
        Add_requires
          {
            body = Written body.id;
            required;
            premise =
              (match frame.condition with
              | Logic.Boolean true -> None
              | condition -> show_truss_goal context condition);
            condition = context.condition;
          };
      ]
  | Some _ | None -> []

let rec make_closed_obligation context (frame : State.frame) location obligation goal =
  if not frame.makes_obligations then None
  else if not (Logic.mentions frame.bound goal || Logic.mentions frame.bound frame.condition) then
    Some (make_obligation context frame location obligation goal)
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
          (make_obligation context
             { frame with condition = Logic.Boolean true }
             location obligation closed)
    | None -> None

and make_obligation (context : State.context) (frame : State.frame) location obligation goal :
    Obligation.t =
  let query =
    Logic.prune
      {
        declarations = List.rev context.declarations;
        facts = List.rev context.facts;
        goal = Logic.( ==> ) frame.condition goal;
      }
  in
  {
    obligation;
    instance = [];
    location;
    cited = None;
    fixes = [];
    query;
    values = context.values;
    path_notes = List.rev context.path_notes;
    has_untriggered_written_fact =
      Logic.has_untriggered_fact query
        ~is_counted:(Tables.Term_table.mem context.written_quantifiers);
    is_rejection = goal = Logic.Boolean false;
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
  }

let remove_panic_condition (uses : Types.capability_set) =
  Types.replace_capabilities
    (function Types.Capability_unless_values _ -> Some Types.no_capabilities | _ -> None)
    uses

let is_panic_obligation : Diagnostic.Code.prover -> bool = function
  | Overflow | Division | Shift | Panic -> true
  | _ -> false

let find_counter_condition (context : State.context) counter =
  if List.mem counter context.conditional_counters then context.condition else []

let oblige ?cited ?(fixes = []) ?(can_be_required = true) ?holds_when (context : State.context)
    (frame : State.frame) location obligation goal =
  let code = Catalog.Prover_description.find_code obligation in
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
      make_closed_obligation context frame location obligation
        (add_quantifier_facts
           ~binders:(List.map (fun (name, _, _) -> name) frame.binders)
           context goal)
    with
    | Some obligation ->
        let is_home_body = is_home context frame.source && frame.makes_obligations in
        let fixes =
          match fixes with
          | [] when is_home_body && can_be_required -> (
              match show_truss_goal context goal with
              | Some _ when Logic.is_refuted goal -> []
              | Some required -> add_requires context frame [ Code required ]
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
  let reject supplied =
    oblige context frame location (Recursion_through_supply supplied) (Logic.Boolean false)
  in
  let reject_supply (supplier : Mir.Call_edges.supplier) code =
    let recursive = List.filter (is_in_recursion_group context) code in
    (match supplier with
    | Named_function path when List.exists (Path.equal path) recursive ->
        reject (Named_function path)
    | Named_function _ | Call | Provide -> ());
    List.iter
      (fun owner ->
        reject
          (match supplier with
          | Call -> Bound_through_call { call = { at = location; callee = None }; owner }
          | Named_function path -> Bound_through_name { path; owner }
          | Provide -> Provided owner))
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
  let reject target impl =
    oblige context frame location
      (Recursion_through_impl { call = { at = location; callee = Some target }; impl })
      (Logic.Boolean false);
    None
  in
  match
    (Mir.Call_edges.resolve_callee context.lookups.interface frame.substitution callee).target
  with
  | Some target when frame.makes_obligations && is_in_recursion_group context target -> (
      match context.lookups.mir.find_form_origin target with
      | Some (Derived _, _) when context.terminates -> reject target Derives
      | Some (Inherited _, _) when context.terminates -> reject target Inherits
      | Some ((Written _ | Derived _ | Inherited _), _) | None -> Some target)
  | Some _ | None -> None

let reject_uncompared_recursion (context : State.context) frame location recursive_callee =
  if context.terminates then
    Option.iter
      (fun callee ->
        oblige context frame location
          (Uncompared_recursion { call = { at = location; callee = Some callee } })
          (Logic.Boolean false))
      recursive_callee

let is_constant_expression (code : Mir.t) =
  let is_made_for_a_literal : Mir.operand Core.target -> bool = function
    | Function { path; _ } -> Path.equal path (Well_known.make_method_path List_from_storage)
    | Trait_method { trait; _ } ->
        Path.equal trait.trait (Well_known.make_path From_elements)
        || Path.equal trait.trait (Well_known.make_path From_entries)
    | Intrinsic _ -> true
    | Capability_method _ | Indirect _ -> false
  in
  let calls_function = ref false in
  Mir.iter_code
    (fun statement ->
      match Mir.find_callee statement with
      | Some callee when not (is_made_for_a_literal callee.target) -> calls_function := true
      | Some _ | None -> ())
    code;
  not !calls_function

let is_evaluated_constant (context : State.context) path code =
  (not (is_constant_expression code))
  && context.lookups.list_recursion_group path = []
  && Option.is_none
       (Types.find_specification_only_type
          (Interface.Definition.read_constant_type context.lookups.interface path))

let make_catalog_dependency (dependency : Mir.Call_edges.dependency) : Catalog.Prover.dependency =
  {
    kind = (match dependency.kind with Read -> Reads | Direct_call -> Calls | Supplied _ -> Uses);
    path = dependency.path;
    omitted =
      Option.map
        (fun (omitted : Mir.Call_edges.omitted) : Catalog.Prover.omitted ->
          match omitted with
          | Field field -> Omitted_field field
          | Argument parameter -> Omitted_argument parameter)
        dependency.omitted;
  }

let reject_constant_cycle (context : State.context) (frame : State.frame) (code : Mir.t) =
  if context.lookups.list_recursion_group context.node <> [] then
    List.iter
      (fun (dependency : Mir.Call_edges.dependency) ->
        if is_in_recursion_group context dependency.path then
          oblige context frame (Node dependency.origin)
            (Constant_cycle
               { cyclic = context.node; dependency = make_catalog_dependency dependency })
            (Logic.Boolean false))
      (Mir.Call_edges.list_dependencies
         { interface = context.lookups.interface; mir = context.lookups.mir }
         Types.no_substitution code)

type circular_proof = { location : Obligation.location; proof : Catalog.Prover.circular_proof }

let is_in_proof_cycle (context : State.context) path =
  List.exists (Path.equal path) (context.lookups.list_proof_group context.node)
  && not (is_in_recursion_group context path)

let has_proof_cycle (context : State.context) =
  List.exists
    (fun member -> not (is_in_recursion_group context member))
    (context.lookups.list_proof_group context.node)

let list_circular_dependencies context ~make_proof dependencies =
  List.filter_map
    (fun (dependency : Mir.Call_edges.dependency) ->
      if is_in_proof_cycle context dependency.path then
        Some
          {
            location = Obligation.Node dependency.origin;
            proof = make_proof (make_catalog_dependency dependency);
          }
      else None)
    dependencies

let list_circular_instance_uses (context : State.context) (frame : State.frame) lookups =
  let reported = ref [] in
  List.filter_map
    (fun (instance : Mir.Call_edges.instance_use) ->
      match List.find_opt (is_in_proof_cycle context) instance.dependencies with
      | Some dependency when not (List.exists (Path.equal dependency) !reported) ->
          reported := dependency :: !reported;
          Some
            {
              location =
                (match instance.used.origin with
                | Some origin -> locate context frame.source origin
                | None -> Whole_definition);
              proof =
                Circular_instance { type_ = instance.used.type_; dependency; cyclic = context.node };
            }
      | Some _ | None -> None)
    (Mir.Call_edges.list_instance_uses lookups context.node)

let list_circular_clauses (context : State.context) frame ~type_ =
  let lookups : Mir.Call_edges.lookups =
    { interface = context.lookups.interface; mir = context.lookups.mir }
  in
  let make_proof clause dependency : Catalog.Prover.circular_proof =
    Circular_clause { clause; type_; dependency }
  in
  if has_proof_cycle context then
    list_circular_dependencies context ~make_proof:(make_proof Invariant_clause)
      (Mir.Call_edges.list_invariant_dependencies lookups context.node)
    @ list_circular_dependencies context ~make_proof:(make_proof Potential_clause)
        (Mir.Call_edges.list_potential_dependencies lookups context.node)
    @ list_circular_instance_uses context frame lookups
  else []

let has_circular_clause lookups group member =
  List.exists
    (fun (dependency : Mir.Call_edges.dependency) -> List.exists (Path.equal dependency.path) group)
    (Mir.Call_edges.list_invariant_dependencies lookups member
    @ Mir.Call_edges.list_potential_dependencies lookups member)

let list_circular_contracts (context : State.context) frame =
  if not (has_proof_cycle context) then []
  else
    let lookups : Mir.Call_edges.lookups =
      { interface = context.lookups.interface; mir = context.lookups.mir }
    in
    let written = Mir.Call_edges.list_contract_dependencies lookups context.node in
    let is_written (inherited : Mir.Call_edges.dependency) =
      List.exists
        (fun (dependency : Mir.Call_edges.dependency) -> Path.equal dependency.path inherited.path)
        written
    in
    match
      list_circular_dependencies context
        ~make_proof:(fun dependency -> Circular_contract { cyclic = context.node; dependency })
        written
      @ List.map
          (fun (circular : circular_proof) -> { circular with location = Whole_definition })
          (list_circular_dependencies context
             ~make_proof:(fun dependency ->
               Circular_inherited_contract { cyclic = context.node; dependency })
             (List.filter
                (fun inherited -> not (is_written inherited))
                (Mir.Call_edges.list_inherited_contract_dependencies lookups context.node)))
      @ list_circular_instance_uses context frame lookups
    with
    | [] -> []
    | circular ->
        let group = context.lookups.list_proof_group context.node in
        if List.exists (has_circular_clause lookups group) group then [] else circular

let reject_circular_proof context frame (circular : circular_proof) =
  oblige context frame circular.location (Circular_proof circular.proof) (Logic.Boolean false)

let quote (source : State.source) origin : Catalog.Prover.quoted = { key = source.key; origin }

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
      match Tables.Type_table.find_opt context.visible_types ty with
      | Some visible -> visible
      | None ->
          let visible =
            match Interface.Definition.find_interface context.lookups.interface path with
            | Some (Interface.Environment.Type_interface interface)
              when (not interface.opaque)
                   || Path.locate_package path = Path.locate_package context.current ->
                Some (interface, Types.make_substitution interface.type_generics arguments)
            | _ -> None
          in
          Tables.Type_table.replace context.visible_types ty visible;
          visible)
  | _ -> None

let find_constructors context ty =
  match find_visible_type context ty with
  | Some (interface, substitution) -> (
      let list_fields (list : Types.field list) =
        List.sort compare
          (List.map
             (fun (field : Types.field) ->
               (field.field_name, Types.substitute_erased substitution field.field_type))
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
  let ty = Types.erase_views ty in
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
  Interface.Impls.add_condition_bounds lookups.interface
    (Interface.Properties.Bounds.close lookups.interface (fun parameter ->
         list_self_bounds parameter @ Types.list_bounds generics parameter))
    condition

let substitute_declared_type (context : State.context) (frame : State.frame) ty =
  (Interface.Impls.normalize context.lookups.interface ~list_bounds:context.bounds)
    (Types.substitute frame.substitution ty)

let substitute_type context frame ty = Types.erase_views (substitute_declared_type context frame ty)

let find_local_type context frame local =
  Option.map (substitute_type context frame) (Locals.find_opt local frame.types)

let find_impl (context : State.context) (trait : Types.trait_reference) (ty : Types.ty) =
  match
    Interface.Impls.resolve_evidence context.lookups.interface Types.no_substitution ~self_type:ty
      ~trait Bound
  with
  | Impl { impl; substitution } | Derived_for_view { viewed = impl; substitution } ->
      Some (impl, substitution)
  | Bound -> None

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

let find_shared_potential_summands
    (values : (Logic.term * (Logic.term * Logic.term) list * Logic.term) list) =
  let joined_terms = List.concat_map (fun (_, renamings, _) -> List.map snd renamings) values in
  let linear =
    List.map (fun (on, renamings, amount) -> (on, renamings, Costs.linearize amount)) values
  in
  let find_coefficient sums atom = Option.value (List.assoc_opt atom sums) ~default:Z.zero in
  let joined_atoms =
    List.fold_left
      (fun atoms (_, _, (sums, _)) ->
        List.fold_left
          (fun atoms (atom, _) ->
            if
              is_potential atom
              && List.exists (fun joined -> Costs.mentions_part ~part:joined atom) joined_terms
              && not (List.mem atom atoms)
            then atoms @ [ atom ]
            else atoms)
          atoms sums)
      [] linear
  in
  let align linear atom =
    match
      List.find_map
        (fun (_, _, (sums, _)) ->
          let coefficient = find_coefficient sums atom in
          if Z.equal coefficient Z.zero then None else Some coefficient)
        linear
    with
    | None -> linear
    | Some target ->
        List.map
          (fun (on, renamings, (sums, constant)) ->
            let difference = Z.sub target (find_coefficient sums atom) in
            if Z.equal difference Z.zero then (on, renamings, (sums, constant))
            else
              let on_path =
                List.fold_left
                  (fun atom (incoming, joined) -> Logic.replace ~from:joined ~into:incoming atom)
                  atom renamings
              in
              ( on,
                renamings,
                Costs.linearize
                  (Costs.plus
                     (Costs.combine (sums, constant))
                     (Costs.times (Logic.Integer difference) (Costs.minus atom on_path))) ))
          linear
  in
  let is_misaligned atom =
    match linear with
    | (_, _, (first_sums, _)) :: rest ->
        let coefficient = find_coefficient first_sums atom in
        List.exists
          (fun (_, _, (sums, _)) -> not (Z.equal (find_coefficient sums atom) coefficient))
          rest
    | [] -> false
  in
  match List.filter is_misaligned joined_atoms with
  | [] -> None
  | misaligned ->
      let aligned = List.fold_left align linear misaligned in
      let shared =
        match aligned with
        | (_, _, (first_sums, _)) :: rest ->
            List.filter
              (fun (atom, coefficient) ->
                is_potential atom
                && List.for_all
                     (fun (_, _, (sums, _)) ->
                       match List.assoc_opt atom sums with
                       | Some other -> Z.equal other coefficient
                       | None -> false)
                     rest)
              first_sums
        | [] -> []
      in
      Some
        ( Costs.combine (shared, Z.zero),
          List.map
            (fun (on, _, (sums, constant)) ->
              ( on,
                Costs.combine
                  (List.filter (fun (atom, _) -> not (List.mem_assoc atom shared)) sums, constant)
              ))
            aligned )

let split_shared_summands (values : (Logic.term * Logic.term) list) =
  let linear = List.map (fun (on, value) -> (on, Costs.linearize value)) values in
  let shared =
    match linear with
    | (_, (first_sums, _)) :: rest ->
        List.filter
          (fun (atom, coefficient) ->
            List.for_all
              (fun (_, (sums, _)) ->
                match List.assoc_opt atom sums with
                | Some other -> Z.equal other coefficient
                | None -> false)
              rest)
          first_sums
    | [] -> []
  in
  ( Costs.combine (shared, Z.zero),
    List.map
      (fun (on, (sums, constant)) ->
        ( on,
          Costs.combine
            (List.filter (fun (atom, _) -> not (List.mem_assoc atom shared)) sums, constant) ))
      linear )

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
  let list_renamings (frame : State.frame) =
    let renamings =
      Locals.fold
        (fun id joined renamings ->
          match Locals.find_opt id frame.locals with
          | Some incoming when incoming != joined && incoming <> joined ->
              (incoming, joined) :: renamings
          | _ -> renamings)
        locals []
    in
    match (frame.self, self) with
    | Some incoming, Some joined when incoming <> joined -> (incoming, joined) :: renamings
    | _ -> renamings
  in
  let spent =
    List.map
      (fun (key, term) ->
        let values =
          List.map
            (fun (on, (frame : State.frame), _) ->
              let renamings = list_renamings frame in
              ( on,
                renamings,
                List.fold_left
                  (fun amount (from, into) -> Logic.replace ~from ~into amount)
                  (match List.assoc_opt key frame.spent with
                  | Some spent_term -> spent_term
                  | None -> term)
                  renamings ))
            paths
        in
        let choose_amount values =
          match List.rev values with
          | (_, last) :: earlier ->
              List.fold_left
                (fun otherwise (on, value) -> Logic.ite on value otherwise)
                last earlier
          | [] -> term
        in
        let name_amount choice =
          if Logic.mentions first.bound choice || mentions_potential choice then choice
          else
            let symbol = declare_fresh context first "spent" Logic.Int in
            add_frame_fact context first (Logic.equal symbol choice);
            symbol
        in
        match values with
        | (_, _, first_value) :: rest
          when List.for_all (fun (_, _, other) -> other == first_value || other = first_value) rest
          ->
            (key, first_value)
        | _ when not key.counts_potential -> (
            match split_shared_summands (List.map (fun (on, _, value) -> (on, value)) values) with
            | shared, (_, first_rest) :: others
              when List.for_all (fun (_, other) -> other = first_rest) others ->
                (key, Costs.plus shared first_rest)
            | shared, rests -> (key, Costs.plus shared (choose_amount rests)))
        | _ -> (
            match find_shared_potential_summands values with
            | None ->
                ( key,
                  name_amount (choose_amount (List.map (fun (on, _, value) -> (on, value)) values))
                )
            | Some (shared, (_, first_rest) :: others)
              when List.for_all (fun (_, other) -> other = first_rest) others ->
                (key, Costs.plus shared first_rest)
            | Some (shared, rests) -> (key, Costs.plus shared (name_amount (choose_amount rests)))))
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
    match (context.lending, find_held (fun frame -> frame.yielded_so_far)) with
    | Some { part_type; _ }, Some values ->
        Some
          (define "parts"
             (declare_sort context
                (Types.Named
                   { path = Well_known.make_path Sequence; arguments = [ Types.Type part_type ] }))
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
