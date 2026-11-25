module String_map = Map.Make (String)

type specification_function = Log | Power | Call_cost of Language.Metric.t | Calls

type module_path = {
  module_ : Path.module_;
  imported : Path.module_ option;
  last_name : Syntax.name;
}

type target =
  | Binding
  | Local of Syntax.id
  | Law_parameter of int
  | Type_parameter of Types.parameter
  | Capability_parameter of Types.parameter
  | Value_parameter of Types.parameter
  | Definition of Names.named * Path.t
  | Variant of Path.t * string
  | Module of module_path
  | Field of string
  | Result_value
  | Old
  | Identical
  | Visited
  | Final
  | Specification_function of specification_function
  | Unknown of Diagnostic.reported

type bracket = Index | Type_arguments | Method_bracket

type value =
  | Value_local of Syntax.id
  | Value_generic of Types.parameter
  | Value_field of string
  | Value_law_parameter of int

type word = Meaning of target | Meaning_unless_defined of target | Loop_element

type scope = {
  values : (value * Catalog.Resolve.binding) String_map.t;
  words : word String_map.t;
  cost_bound_functions : specification_function String_map.t;
  types : target String_map.t;
  capability_parameters : target String_map.t;
  is_lending_method : bool;
}

let cost_bound_functions =
  String_map.of_list
    ([ ("log", Log); ("power", Power); ("calls", Calls) ]
    @ List.map (fun metric -> (Language.Metric.show metric, Call_cost metric)) Language.Metric.all)

let bind_words scope words =
  {
    scope with
    words =
      List.fold_left (fun bound (text, word) -> String_map.add text word bound) scope.words words;
  }

let specification_words =
  String_map.of_list
    [
      ("old", Meaning Old);
      ("identical", Meaning Identical);
      ("log", Meaning_unless_defined (Specification_function Log));
      ("power", Meaning_unless_defined (Specification_function Power));
    ]

let enter_specification scope =
  { scope with words = specification_words; cost_bound_functions = String_map.empty }

type section = Interface | Contract | Body

type section_names = {
  names : target option array;
  brackets : bracket option array;
  mutable holes : (Syntax.id * (string * value) list) list;
  mutable diagnostics : Catalog.diagnostic list;
  mutable used_imports : string list;
}

type state = {
  lookups : Names.lookups;
  key : Names.key;
  spans : Source.Definition_span.t array;
  syntax_errors : Source.Definition_span.t list;
  imports : (string * Path.module_) list Lazy.t;
  visible_packages : Path.package list Lazy.t;
  interface : section_names;
  contract : section_names;
  body : section_names;
  mutable section : section;
}

let make_section_names size =
  {
    names = Array.make size None;
    brackets = Array.make size None;
    holes = [];
    diagnostics = [];
    used_imports = [];
  }

let create lookups key ~spans ~syntax_errors =
  let size = Array.length spans in
  {
    lookups;
    key;
    spans;
    syntax_errors;
    imports = lazy (lookups.list_imports key);
    visible_packages = lazy (Names.list_visible_packages lookups key.module_.package);
    interface = make_section_names size;
    contract = make_section_names size;
    body = make_section_names size;
    section = Interface;
  }

let lookup_section_names state = function
  | Interface -> state.interface
  | Contract -> state.contract
  | Body -> state.body

let lookup_current_names state = lookup_section_names state state.section

let run_in_section state section walk =
  let enclosing = state.section in
  state.section <- section;
  walk ();
  state.section <- enclosing

let add_diagnostic state diagnostic =
  let reported = Catalog.Resolve diagnostic in
  let names = lookup_current_names state in
  names.diagnostics <- reported :: names.diagnostics;
  Catalog.make_reported reported

let report state diagnostic = ignore (add_diagnostic state diagnostic)

let set_target state (name : Syntax.name) target =
  (lookup_current_names state).names.(name.id) <- Some target

let report_unknown state (name : Syntax.name) ~expected candidates =
  set_target state name
    (Unknown
       (add_diagnostic state
          (Unknown { name = Written name.id; written = name.text; expected; candidates })))

let find_module_item state text = state.lookups.find state.key.module_ text

let note_import_use state text =
  let names = lookup_current_names state in
  if List.mem_assoc text (Lazy.force state.imports) && not (List.mem text names.used_imports) then
    names.used_imports <- text :: names.used_imports

let find_in_module state module_ (name : Syntax.name) ~types =
  let is_kind = if types then Names.Scope.is_type_kind else Names.Scope.is_value_kind in
  match Names.Scope.lookup_in state.lookups ~from:state.key.module_ module_ name.text ~is_kind with
  | Visible (item, path) ->
      set_target state name (Definition (item.kind, path));
      Some (path, item)
  | Hidden (path, visibility) ->
      set_target state name
        (Unknown (add_diagnostic state (Not_visible { name = Written name.id; path; visibility })));
      None
  | Absent ->
      let candidates =
        List.filter_map
          (fun (item : Names.entry) ->
            if
              (if types then Names.Scope.is_type_kind item.kind
               else Names.Scope.is_value_kind item.kind)
              && Names.Scope.is_visible ~from:state.key.module_ module_ item.visibility
            then Some item.name
            else None)
          (state.lookups.list_entries module_)
      in
      report_unknown state name ~expected:(In_module module_) candidates;
      None

let report_unresolved_path_start state scope (first : Syntax.name) ~may_start_with_value =
  let name = Core.Written first.id in
  let module_ = state.key.module_ in
  function
  | Names.Scope.Found_module _ ->
      Compiler_bug.raise_bug ~stage:"Resolve" "`%s` starts a path to a module and is reported"
        first.text
  | Restricted_module -> add_diagnostic state (Intrinsic_import { name })
  | Ambiguous_module (imported, package) ->
      add_diagnostic state (Import_or_package { name; written = first.text; imported; package })
  | No_module text -> add_diagnostic state (No_module { name; written = text; path_start = None })
  | No_package text ->
      if state.lookups.module_exists { package = module_.package; modules = [ first.text ] } then
        add_diagnostic state (No_module { name; written = text; path_start = Some module_ })
      else if may_start_with_value then
        let candidates =
          List.map fst (String_map.bindings scope.values)
          @ List.filter_map
              (fun (item : Names.entry) ->
                if Names.Scope.is_value_kind item.kind then Some item.name else None)
              (state.lookups.list_entries module_)
          @ List.map fst (Lazy.force state.imports)
          @ Names.list_package_roots (Lazy.force state.visible_packages)
        in
        add_diagnostic state (Unknown_value_or_module { name; written = first.text; candidates })
      else add_diagnostic state (No_module { name; written = text; path_start = None })

let resolve_path state scope (first : Syntax.name) (rest : Syntax.name list) ~module_lengths
    ~may_start_with_value =
  note_import_use state first.text;
  let lookup length =
    Names.Scope.lookup_module state.lookups
      ~visible_packages:(Lazy.force state.visible_packages)
      ~from:state.key.module_ ~imports:(Lazy.force state.imports) first.text
      (List.map (fun (name : Syntax.name) -> name.text) (List.take length rest))
  in
  let rec search ~longest_failure = function
    | [] ->
        Compiler_bug.raise_bug ~stage:"Resolve" "the path at `%s` has no length to try" first.text
    | length :: shorter -> (
        match lookup length with
        | Found_module { module_; imported } -> Ok (module_, imported, length)
        | (No_module _ | No_package _) as failure ->
            let longest_failure = Option.value longest_failure ~default:failure in
            if shorter = [] then Error (longest_failure, length)
            else search ~longest_failure:(Some longest_failure) shorter
        | failure -> Error (failure, length))
  in
  match search ~longest_failure:None module_lengths with
  | Ok (module_, imported, length) ->
      let item = List.nth rest length in
      let last_name = if length = 0 then first else List.nth rest (length - 1) in
      set_target state first (Module { module_; imported; last_name });
      ignore (find_in_module state module_ item ~types:(item.case = Upper))
  | Error (failure, length) ->
      let report = report_unresolved_path_start state scope first ~may_start_with_value failure in
      set_target state first (Unknown report);
      set_target state (List.nth rest length) (Unknown report)

let list_type_candidates state scope =
  List.map fst (String_map.bindings scope.types)
  @ List.filter_map
      (fun (item : Names.entry) ->
        if Names.Scope.is_type_kind item.kind then Some item.name else None)
      (state.lookups.list_entries state.key.module_)
  @ List.map fst Prelude.types

let list_types_with_variant state text =
  let declared_types =
    List.filter_map
      (fun (declaration : Names.declaration) ->
        match declaration.kind with
        | Type -> (
            match (state.lookups.read_definition declaration.key).kind with
            | Type_definition { name; body = Variants variants; _ }
              when List.exists (fun (variant : Syntax.variant) -> variant.name.text = text) variants
              ->
                Some (state.lookups.read_place declaration.key, name.text)
            | _ -> None)
        | _ -> None)
      (state.lookups.list_declarations state.key.module_)
  in
  List.map snd (List.sort (fun (first, _) (second, _) -> compare first second) declared_types)

let report_bare_variant state (name : Syntax.name) owners =
  match owners with
  | owner :: other_owners ->
      set_target state name
        (Unknown
           (add_diagnostic state
              (Bare_variant { name = Written name.id; written = name.text; owner; other_owners })))
  | [] -> Compiler_bug.raise_bug ~stage:"Resolve" "`%s` is a variant of no type" name.text

let resolve_written_path state scope (first : Syntax.name) (rest : Syntax.name list)
    (last : Syntax.name) =
  resolve_path state scope first (rest @ [ last ])
    ~module_lengths:[ List.length rest ]
    ~may_start_with_value:false

let resolve_type_name state scope ?(variants = false) (path : Syntax.path) =
  match path.modules with
  | first :: rest -> resolve_written_path state scope first rest path.last
  | [] -> (
      let text = path.last.text in
      match String_map.find_opt text scope.types with
      | Some parameter -> set_target state path.last parameter
      | None -> (
          match Names.Scope.find_bare_type state.lookups ~from:state.key.module_ text with
          | Some (item, found) -> set_target state path.last (Definition (item.kind, found))
          | None -> (
              match if variants then Prelude.find_variant text else None with
              | Some (type_, variant) -> set_target state path.last (Variant (type_, variant))
              | None when variants && list_types_with_variant state text <> [] ->
                  report_bare_variant state path.last (list_types_with_variant state text)
              | None ->
                  report_unknown state path.last ~expected:Type_here
                    (list_type_candidates state scope
                    @ if variants then List.map Well_known.show_variant Prelude.variants else []))))

let find_target state (name : Syntax.name) = (lookup_current_names state).names.(name.id)

let rec resolve_type_expression state scope (type_ : Syntax.type_expression) =
  match type_.kind with
  | Path_type path -> resolve_path_type state scope path
  | Self_type _ -> ()
  | Associated (base, member) ->
      resolve_associated_base state scope base member Catalog.Resolve.Associated_type
  | Function_type { inputs; output; clauses } ->
      List.iter
        (fun (input : Syntax.function_input) -> resolve_type_expression state scope input.type_)
        inputs;
      Option.iter (resolve_type_expression state scope) output;
      let named =
        List.fold_left
          (fun scope (input : Syntax.function_input) ->
            Option.fold ~none:scope ~some:(declare_parameter state scope) input.name)
          scope inputs
      in
      List.iter (resolve_clause state named) clauses
  | Type_error -> ()

and resolve_associated_base state scope (base : Syntax.name) (member : Syntax.name) associated =
  match String_map.find_opt base.text scope.types with
  | Some parameter -> set_target state base parameter
  | None ->
      set_target state base
        (Unknown
           (add_diagnostic state
              (Not_a_generic_parameter
                 { base = Written base.id; written = base.text; member = member.text; associated })))

and resolve_capability_reference state scope (reference : Syntax.capability_reference) =
  match reference.kind with
  | Capability_path { path = { modules = []; last }; arguments = []; _ }
    when String_map.mem last.text scope.capability_parameters
         && not (String_map.mem last.text scope.types) ->
      set_target state last
        (Unknown
           (add_diagnostic state
              (Capability_parameter_without_generic { name = Written last.id; written = last.text })))
  | Capability_path path -> resolve_path_type state scope path
  | Self_capabilities _ -> ()
  | Associated_capabilities (base, member) ->
      resolve_associated_base state scope base member Catalog.Resolve.Associated_capability_set
  | Generic_capability name ->
      set_target state name
        (match String_map.find_opt name.text scope.capability_parameters with
        | Some target -> target
        | None ->
            Unknown
              (add_diagnostic state
                 (Unknown_generic_capability
                    { reference = Written reference.id; written = name.text })))

and resolve_path_type state scope (path : Syntax.path_type) =
  resolve_type_name state scope path.path;
  List.iter (resolve_type_argument state scope) path.arguments

and resolve_type_argument state scope = function
  | Type_argument type_ -> resolve_type_expression state scope type_
  | Count _ -> ()
  | Count_name name -> count_name state scope name
  | Constraint (_, type_) -> resolve_type_expression state scope type_

and count_name state scope (name : Syntax.name) =
  match String_map.find_opt name.text scope.values with
  | Some (Value_generic parameter, _) -> set_target state name (Value_parameter parameter)
  | shadowing -> (
      match find_module_item state name.text with
      | Some item when item.kind = Constant && shadowing = None ->
          set_target state name
            (Definition (Constant, Top { module_ = state.key.module_; name = name.text }))
      | _ ->
          set_target state name
            (Unknown
               (add_diagnostic state
                  (Not_a_constant { name = Written name.id; written = name.text }))))

and resolve_clause_condition state scope (condition : Syntax.condition) =
  List.iter
    (fun (bound : Syntax.bound_condition) ->
      resolve_type_expression state scope bound.subject;
      List.iter (resolve_path_type state scope) bound.bounds)
    condition

and resolve_capability_use state scope (use : Syntax.capability_use) =
  resolve_capability_reference state scope use.capability;
  Option.iter (resolve_clause_condition state scope) use.unless;
  List.iter (resolve_expression state (enter_specification scope)) use.unless_values

and resolve_clause state scope (clause : Syntax.clause) =
  Option.iter (resolve_clause_condition state scope) clause.condition;
  match clause.kind with
  | Uses uses -> List.iter (resolve_capability_use state scope) uses
  | Requires value -> resolve_expression state (enter_specification scope) value
  | Ensures value ->
      resolve_expression state
        (bind_words (enter_specification scope)
           (("result", Meaning Result_value)
           :: (if scope.is_lending_method then [ ("final", Meaning Final) ] else [])))
        value
  | Decreases measures -> List.iter (resolve_expression state (enter_specification scope)) measures
  | Modifies parts -> List.iter (resolve_expression state scope) parts
  | Cost cost -> resolve_cost state scope ~clause_words:[] cost
  | Clause_error -> ()

and resolve_cost state scope ~clause_words (cost : Syntax.cost) =
  (match cost.resource with
  | Calls (Call_parameter name) -> resolve_local_value state (bind_words scope clause_words) name
  | Calls (Call_capability path) -> resolve_path_type state scope path
  | Calls (Call_method (path, _)) -> resolve_path_type state scope path
  | Metric _ -> ());
  let bound =
    {
      (bind_words (enter_specification scope) (clause_words @ [ ("result", Meaning Result_value) ])) with
      cost_bound_functions;
    }
  in
  match cost.bound with
  | Big_o value | At_most value | Exactly value -> resolve_expression state bound value

and resolve_local_value state scope (name : Syntax.name) =
  let text = name.text in
  match String_map.find_opt text scope.values with
  | Some (Value_local id, _) -> set_target state name (Local id)
  | Some (Value_generic parameter, _) -> set_target state name (Value_parameter parameter)
  | Some (Value_field field, _) -> set_target state name (Field field)
  | Some (Value_law_parameter index, _) -> set_target state name (Law_parameter index)
  | None -> (
      match String_map.find_opt text scope.words with
      | Some (Meaning target) -> set_target state name target
      | Some Loop_element ->
          set_target state name
            (Unknown
               (add_diagnostic state (Loop_element { name = Written name.id; written = text })))
      | (Some (Meaning_unless_defined _) | None) as word -> (
          match (find_module_item state text, word) with
          | Some item, _ when Names.Scope.is_value_kind item.kind ->
              set_target state name
                (Definition (item.kind, Top { module_ = state.key.module_; name = text }))
          | _, Some (Meaning_unless_defined target) -> set_target state name target
          | _ ->
              if text = "null" || text = "nil" then begin
                set_target state name
                  (Unknown (add_diagnostic state (Null { name = Written name.id; written = text })))
              end
              else
                report_unknown state name ~expected:Value_here
                  (List.map fst (String_map.bindings scope.values)
                  @ List.filter_map
                      (fun (item : Names.entry) ->
                        if Names.Scope.is_value_kind item.kind then Some item.name else None)
                      (state.lookups.list_entries state.key.module_))))

and resolve_name_expression state scope (name : Syntax.name) =
  match name.case with
  | Upper -> resolve_type_name state scope ~variants:true { modules = []; last = name }
  | Lower -> resolve_local_value state scope name

and classify_path_head state scope text =
  let is_local =
    String_map.mem text scope.values
    ||
    match String_map.find_opt text scope.words with
    | Some (Meaning _ | Loop_element) -> true
    | Some (Meaning_unless_defined _) | None -> false
  in
  if is_local then `Value
  else if List.mem_assoc text (Lazy.force state.imports) then `Module
  else
    match find_module_item state text with
    | Some item when Names.Scope.is_value_kind item.kind ->
        if List.mem text (Names.list_package_roots (Lazy.force state.visible_packages)) then
          `Ambiguous
        else `Value
    | Some _ | None -> `Module

and resolve_member_chain state scope (value : Syntax.expression) =
  let rec flatten (written : Syntax.expression) members =
    match written.kind with
    | Member (base, member) -> flatten base (member :: members)
    | _ -> (written, members)
  in
  match flatten value [] with
  | ({ kind = Name ({ case = Lower; _ } as first); _ } as head), (member :: _ as members) -> (
      match classify_path_head state scope first.text with
      | `Module -> resolve_expression_path state scope first members
      | `Ambiguous ->
          let report =
            add_diagnostic state
              (Definition_or_package
                 {
                   name = Written first.id;
                   written = first.text;
                   module_ = state.key.module_;
                   member = member.text;
                 })
          in
          set_target state first (Unknown report);
          set_target state member (Unknown report)
      | `Value -> resolve_expression state scope head)
  | head, _ -> resolve_expression state scope head

and resolve_expression_path state scope (first : Syntax.name) (members : Syntax.name list) =
  let rec count_lower : Syntax.name list -> int = function
    | { case = Lower; _ } :: rest -> 1 + count_lower rest
    | _ -> 0
  in
  let longest = min (count_lower members) (List.length members - 1) in
  resolve_path state scope first members
    ~module_lengths:(List.init (longest + 1) (fun shorter -> longest - shorter))
    ~may_start_with_value:true

and find_name_target state (value : Syntax.expression) =
  match value.kind with
  | Name name | Member (_, name) -> find_target state name
  | Parenthesized inner -> find_name_target state inner
  | _ -> None

and resolve_bracket state scope (value : Syntax.expression) base items =
  resolve_expression state scope base;
  let decision =
    match (base.kind, find_name_target state base) with
    | Member _, None -> Method_bracket
    | _, target -> (
        match target with
        | Some (Definition ((Type | Trait | Capability), _)) | Some (Type_parameter _) ->
            Type_arguments
        | Some (Definition ((Function | Theorem), Top { module_; name })) ->
            let generic =
              match state.lookups.find module_ name with Some item -> item.generic | None -> false
            in
            if not generic then
              report state (Not_generic { value = Written value.id; function_ = name });
            Type_arguments
        | _ -> Index)
  in
  (lookup_current_names state).brackets.(value.id) <- Some decision;
  List.iter
    (function
      | Syntax.Item item -> resolve_expression state scope item
      | Item_constraint (_, type_) -> resolve_type_expression state scope type_)
    items

and check_place state (written : Syntax.expression) (inner : Syntax.expression) =
  let classify_target value = function
    | Some (Local _ | Field _) -> `Place false
    | Some (Definition (Constant, _)) -> `Place false
    | Some (Unknown _) -> `Unknown
    | _ -> `Not_a_place value
  in
  let rec classify_head (value : Syntax.expression) =
    match value.kind with
    | Member (base, name) -> (
        match find_target state name with
        | Some _ as target -> classify_target value target
        | None -> classify_head base)
    | Parenthesized inner -> classify_head inner
    | Bracket (base, _) -> (
        match (lookup_current_names state).brackets.(value.id) with
        | Some (Index | Method_bracket) -> classify_head base
        | _ -> `Not_a_place value)
    | Call ({ kind = Member (base, _); _ }, _)
    | Call ({ kind = Bracket ({ kind = Member (base, _); _ }, _); _ }, _)
    | With (base, _) -> (
        match classify_head base with `Place _ -> `Place true | other -> other)
    | Try base -> (
        match classify_head base with `Place false -> `Not_a_place value | other -> other)
    | Self_value -> `Place false
    | Name name -> classify_target value (find_target state name)
    | _ -> `Not_a_place value
  in
  match classify_head inner with
  | `Place _ | `Unknown -> ()
  | `Not_a_place _ ->
      report state (Not_a_place { written = Written written.id; inner = Written inner.id })

and resolve_expression state scope (value : Syntax.expression) =
  match value.kind with
  | Todo ->
      let names = lookup_current_names state in
      names.holes <-
        ( value.id,
          List.map (fun (name, (value, _)) -> (name, value)) (String_map.bindings scope.values) )
        :: names.holes
  | Integer _ | Float _ | True | False | Unreachable | Break | Continue | Self_value
  | Self_type_value | Expression_error ->
      ()
  | String literal -> resolve_string_literal state scope literal
  | Name name -> resolve_name_expression state scope name
  | Member _ -> resolve_member_chain state scope value
  | Bracket (base, items) -> resolve_bracket state scope value base items
  | Call (callee, arguments) ->
      (match callee.kind with
      | Name last -> (
          match String_map.find_opt last.text scope.cost_bound_functions with
          | Some function_ -> set_target state last (Specification_function function_)
          | None -> resolve_expression state scope callee)
      | _ -> resolve_expression state scope callee);
      List.iter
        (fun (argument : Syntax.argument) -> resolve_expression state scope argument.value)
        arguments
  | Try inner | Prefix (_, inner) | Echo inner | Parenthesized inner ->
      resolve_expression state scope inner
  | Mode (_, inner) ->
      resolve_expression state scope inner;
      check_place state value inner
  | With (base, updates) ->
      resolve_expression state scope base;
      List.iter
        (fun (update : Syntax.update) ->
          match update.kind with
          | Update { value; _ } -> resolve_expression state scope value
          | Update_error -> ())
        updates
  | Binary { operator = Connective And; _ } | Is _ -> ignore (resolve_condition state scope value)
  | Binary { left; right; _ } ->
      resolve_expression state scope left;
      resolve_expression state scope right
  | Range { start; stop; _ } ->
      Option.iter (resolve_expression state scope) start;
      Option.iter (resolve_expression state scope) stop
  | Quantified { binder; body; _ } ->
      let inner =
        match binder with
        | Binder_in (pattern_, collection) ->
            resolve_expression state scope collection;
            bind_pattern state scope pattern_
        | Binder_type (name, type_) ->
            resolve_type_expression state scope type_;
            declare_value state scope name
      in
      resolve_expression state inner body
  | Return inner -> Option.iter (resolve_expression state scope) inner
  | List items -> List.iter (resolve_expression state scope) items
  | Map entries ->
      List.iter
        (fun (key, item) ->
          resolve_expression state scope key;
          resolve_expression state scope item)
        entries
  | Lambda { parameters; body } ->
      let inner =
        List.fold_left (fun scope pattern_ -> bind_pattern state scope pattern_) scope parameters
      in
      resolve_block state inner body
  | If { condition = test; then_; else_ } ->
      let inner = resolve_condition state scope test in
      resolve_block state inner then_;
      Option.iter
        (function
          | Syntax.Else block_ -> resolve_block state scope block_
          | Else_if branch -> resolve_expression state scope branch)
        else_
  | Match { scrutinees; arms } ->
      List.iter (resolve_expression state scope) scrutinees;
      List.iter (resolve_arm state scope) arms
  | Provide { implementations; body } ->
      List.iter (resolve_expression state scope) implementations;
      resolve_block state scope body
  | Block body -> resolve_block state scope body

and resolve_condition state scope (value : Syntax.expression) =
  match value.kind with
  | Binary { operator = Connective And; left; right; _ } ->
      let after_left = resolve_condition state scope left in
      resolve_condition state after_left right
  | Is { value = tested; pattern = pattern_; _ } ->
      resolve_expression state scope tested;
      bind_pattern state scope pattern_
  | Parenthesized inner -> resolve_condition state scope inner
  | _ ->
      resolve_expression state scope value;
      scope

and resolve_string_literal state scope (literal : Syntax.string_literal) =
  Option.iter (fun tag -> resolve_type_name state scope tag) literal.tag;
  List.iter (fun (value, _) -> resolve_expression state scope value) literal.rest

and resolve_arm state scope (arm_ : Syntax.arm) =
  let inner =
    List.fold_left (fun scope pattern_ -> bind_pattern state scope pattern_) scope arm_.patterns
  in
  let guarded =
    match arm_.guard with Some guard -> resolve_condition state inner guard | None -> inner
  in
  ignore (resolve_statement state guarded arm_.body)

and declare_value state scope (name : Syntax.name) =
  let check_shadowing existing =
    report state (Shadowed { name = Written name.id; written = name.text; existing })
  in
  (match String_map.find_opt name.text scope.values with
  | Some (_, existing) -> check_shadowing existing
  | None -> ());
  set_target state name Binding;
  {
    scope with
    values = String_map.add name.text (Value_local name.id, Catalog.Resolve.Local) scope.values;
  }

and declare_parameter state scope (name : Syntax.name) =
  let scope = declare_value state scope name in
  {
    scope with
    values = String_map.add name.text (Value_local name.id, Catalog.Resolve.Parameter) scope.values;
  }

and bind_pattern state scope (pattern_ : Syntax.pattern) =
  let bound = ref [] in
  resolve_pattern state scope bound pattern_;
  List.fold_left
    (fun scope (name : Syntax.name) -> declare_value state scope name)
    scope (List.rev !bound)

and resolve_pattern state scope bound (pattern_ : Syntax.pattern) =
  match pattern_.kind with
  | Wildcard | Pattern_error -> ()
  | Binding name -> bound := name :: !bound
  | Qualified_constant constant_ -> resolve_qualified_constant state scope constant_
  | Literal literal -> resolve_literal_pattern state scope literal
  | Pattern_range { start; stop; _ } ->
      resolve_range_end state scope start;
      resolve_range_end state scope stop
  | Variant { fields; _ } ->
      Option.iter (List.iter (resolve_pattern_field state scope bound)) fields
  | Record fields -> List.iter (resolve_pattern_field state scope bound) fields
  | Tuple patterns -> List.iter (resolve_pattern state scope bound) patterns
  | Alternatives alternatives -> (
      let each =
        List.map
          (fun alternative ->
            let names = ref [] in
            resolve_pattern state scope names alternative;
            (alternative, List.rev !names))
          alternatives
      in
      match each with
      | [] -> ()
      | (_, first) :: rest ->
          bound := List.rev_append first !bound;
          let list_texts names =
            List.sort compare (List.map (fun (name : Syntax.name) -> name.text) names)
          in
          List.iter
            (fun ((alternative : Syntax.pattern), names) ->
              if list_texts names <> list_texts first then
                report state
                  (Alternative_bindings
                     {
                       alternative = Written alternative.id;
                       first = list_texts first;
                       this = list_texts names;
                     })
              else
                List.iter
                  (fun (name : Syntax.name) ->
                    match
                      List.find_opt (fun (other : Syntax.name) -> other.text = name.text) first
                    with
                    | Some other -> set_target state name (Local other.id)
                    | None -> ())
                  names)
            rest)

and resolve_pattern_field state scope bound (field : Syntax.pattern_field) =
  match field.kind with
  | Named_field (_, inner) | Field inner -> resolve_pattern state scope bound inner
  | Rest -> ()

and resolve_literal_pattern state scope = function
  | Literal_string literal -> resolve_string_literal state scope literal
  | Literal_integer _ | Literal_true | Literal_false -> ()

and resolve_qualified_constant state scope = function
  | Module_constant { modules = []; last } ->
      report_unknown state last ~expected:Constant_in_module_here []
  | Module_constant { modules = first :: rest; last } ->
      resolve_written_path state scope first rest last
  | Type_constant (path, _) -> resolve_type_name state scope path

and resolve_range_end state scope (end_ : Syntax.range_end) =
  match end_.kind with
  | End_literal literal -> resolve_literal_pattern state scope literal
  | End_constant constant_ -> resolve_qualified_constant state scope constant_

and resolve_block state scope (block_ : Syntax.block) =
  ignore
    (List.fold_left
       (fun scope statement_ -> resolve_statement state scope statement_)
       scope block_.statements)

and resolve_statement state scope (statement_ : Syntax.statement) =
  match statement_.kind with
  | Let { pattern = pattern_; annotation; value; else_; _ } ->
      Option.iter (resolve_type_expression state scope) annotation;
      resolve_expression state scope value;
      Option.iter (resolve_block state scope) else_;
      bind_pattern state scope pattern_
  | Expression value ->
      resolve_expression state scope value;
      scope
  | Assignment { target; value; _ } ->
      resolve_expression state scope target;
      resolve_expression state scope value;
      scope
  | For { pattern = pattern_; annotation; iterable; clauses; body; _ } ->
      Option.iter (resolve_type_expression state scope) annotation;
      resolve_expression state scope iterable;
      let inner = bind_pattern state scope pattern_ in
      let clause_scope, elements =
        match iterable.kind with
        | Range { start = Some _; stop = Some _; _ } -> (inner, [])
        | _ ->
            ( scope,
              String_map.fold
                (fun name binding elements ->
                  if String_map.find_opt name scope.values = Some binding then elements
                  else (name, Loop_element) :: elements)
                inner.values [] )
      in
      List.iter
        (resolve_loop_clause state clause_scope
           ~clause_words:(elements @ [ ("visited", Meaning Visited) ]))
        clauses;
      resolve_block state inner body;
      scope
  | While { condition = test; clauses; body } ->
      let inner = resolve_condition state scope test in
      List.iter (resolve_loop_clause state scope ~clause_words:[]) clauses;
      resolve_block state inner body;
      scope
  | Parallel body | Concurrent body ->
      let word = match statement_.kind with Concurrent _ -> "concurrent" | _ -> "parallel" in
      List.fold_left
        (fun (after : scope) (branch : Syntax.statement) ->
          let branch_scope = resolve_statement state scope branch in
          let bound =
            String_map.filter
              (fun key _ -> not (String_map.mem key scope.values))
              branch_scope.values
          in
          String_map.iter
            (fun key _ ->
              if String_map.mem key after.values then
                report state
                  (Shadowed_in_branch { branch = Written branch.id; block = word; written = key }))
            bound;
          { after with values = String_map.union (fun _ left _ -> Some left) after.values bound })
        scope body.statements
  | Proof body ->
      resolve_block state (enter_specification scope) body;
      scope
  | Assert { value; _ } ->
      resolve_expression state scope value;
      scope
  | Statement_error -> scope

and resolve_loop_clause state scope ~clause_words (written : Syntax.loop_clause) =
  let specification = bind_words (enter_specification scope) clause_words in
  Option.iter (resolve_clause_condition state scope) written.condition;
  match written.kind with
  | Invariant value -> resolve_expression state specification value
  | Loop_decreases measures -> List.iter (resolve_expression state specification) measures
  | Loop_cost cost -> resolve_cost state scope ~clause_words cost

let find_shadowed_type state scope text : Catalog.Resolve.binding option =
  if String_map.mem text scope.types then Some Generic_parameter_here
  else
    match find_module_item state text with
    | Some item when Names.Scope.is_type_kind item.kind ->
        Some (Module_definition (Names.convert_named item.kind))
    | _ -> if List.mem text Prelude.names then Some Prelude_name else None

let report_shadowing state (name : Syntax.name) existing =
  add_diagnostic state (Shadowed { name = Written name.id; written = name.text; existing })

let declare_type state scope (name : Syntax.name) target =
  Option.iter
    (fun existing -> ignore (report_shadowing state name existing))
    (find_shadowed_type state scope name.text);
  set_target state name Binding;
  { scope with types = String_map.add name.text target scope.types }

let rec list_generic_capabilities (type_ : Syntax.type_expression) : Syntax.name list =
  match type_.kind with
  | Path_type path ->
      List.concat_map
        (function
          | Syntax.Type_argument argument | Constraint (_, argument) ->
              list_generic_capabilities argument
          | Count _ | Count_name _ -> [])
        path.arguments
  | Function_type { inputs; output; clauses } ->
      List.concat_map
        (fun (input : Syntax.function_input) -> list_generic_capabilities input.type_)
        inputs
      @ Option.fold ~none:[] ~some:list_generic_capabilities output
      @ list_used_generic_capabilities clauses
  | Self_type _ | Associated _ | Type_error -> []

and list_used_generic_capabilities (clauses : Syntax.clause list) =
  List.concat_map
    (fun (clause : Syntax.clause) ->
      match clause.kind with
      | Uses uses ->
          List.filter_map
            (fun (use : Syntax.capability_use) ->
              match use.capability.kind with Generic_capability name -> Some name | _ -> None)
            uses
      | Requires _ | Ensures _ | Decreases _ | Modifies _ | Cost _ | Clause_error -> [])
    clauses

let declare_capability_parameters state scope ~(owner : Path.t)
    ~(types : Syntax.type_expression list) (clauses : Syntax.clause list) =
  let constrained = List.concat_map list_generic_capabilities types in
  let used = list_used_generic_capabilities clauses in
  List.iter
    (fun (name : Syntax.name) ->
      if not (List.exists (fun (typed : Syntax.name) -> typed.text = name.text) constrained) then
        report state
          (Unconstrained_capability_parameter { name = Written name.id; written = name.text }))
    used;
  let parameters =
    List.fold_left
      (fun parameters (name : Syntax.name) ->
        if String_map.mem name.text parameters then parameters
        else
          String_map.add name.text
            (match find_shadowed_type state scope name.text with
            | Some existing -> Unknown (report_shadowing state name existing)
            | None -> Capability_parameter { owner; name = name.text })
            parameters)
      String_map.empty (constrained @ used)
  in
  { scope with capability_parameters = parameters }

let list_parameter_types (parameters : Syntax.parameter list) =
  List.filter_map
    (fun (parameter : Syntax.parameter) ->
      match parameter.kind with
      | Named_parameter { type_; _ } -> Some type_
      | Self_parameter _ | Parameter_error -> None)
    parameters

let resolve_generics state scope ~(owner : Path.t) (generics : Syntax.generic_parameter list) =
  let make_parameter (name : Syntax.name) : Types.parameter = { owner; name = name.text } in
  let scope =
    List.fold_left
      (fun scope (generic : Syntax.generic_parameter) ->
        match generic.kind with
        | Type_parameter (name, _) ->
            declare_type state scope name (Type_parameter (make_parameter name))
        | Value_parameter (name, _) ->
            let scope = declare_value state scope name in
            {
              scope with
              values =
                String_map.add name.text
                  (Value_generic (make_parameter name), Catalog.Resolve.Generic_parameter)
                  scope.values;
            }
        | Generic_error -> scope)
      scope generics
  in
  List.iter
    (fun (generic : Syntax.generic_parameter) ->
      match generic.kind with
      | Type_parameter (_, bounds) -> List.iter (resolve_path_type state scope) bounds
      | Value_parameter (_, type_) -> resolve_type_expression state scope type_
      | Generic_error -> ())
    generics;
  scope

let resolve_parameters state scope (parameters_ : Syntax.parameter list) =
  List.fold_left
    (fun scope (parameter : Syntax.parameter) ->
      match parameter.kind with
      | Named_parameter { name; type_; default; _ } ->
          resolve_type_expression state scope type_;
          Option.iter
            (fun default ->
              run_in_section state Contract (fun () -> resolve_expression state scope default))
            default;
          declare_parameter state scope name
      | Self_parameter _ | Parameter_error -> scope)
    scope parameters_

let resolve_result state scope = function
  | Some (Syntax.Returns type_ | Lends (_, type_)) -> resolve_type_expression state scope type_
  | None -> ()

let empty_scope =
  {
    values = String_map.empty;
    words = String_map.empty;
    cost_bound_functions = String_map.empty;
    types = String_map.empty;
    capability_parameters = String_map.empty;
    is_lending_method = false;
  }

let resolve_head state scope ~owner = function
  | Syntax.Plain_name _ -> scope
  | Member_name (head_, _) ->
      resolve_type_name state scope head_.path;
      resolve_generics state scope ~owner head_.generics

let resolve_clauses state scope (clauses_ : Syntax.clause list) =
  List.iter
    (fun (clause_ : Syntax.clause) ->
      match clause_.kind with
      | Requires _ | Ensures _ | Decreases _ ->
          run_in_section state Contract (fun () -> resolve_clause state scope clause_)
      | Uses _ | Modifies _ | Cost _ | Clause_error -> resolve_clause state scope clause_)
    clauses_

let resolve_signature state scope ~owner ~(broken : bool) (signature_ : Syntax.signature) =
  if broken then None
  else begin
    let scope = resolve_generics state scope ~owner signature_.generics in
    let scope =
      declare_capability_parameters state scope ~owner
        ~types:
          (list_parameter_types signature_.parameters
          @
          match signature_.result with
          | Some (Returns type_ | Lends (_, type_)) -> [ type_ ]
          | None -> [])
        signature_.clauses
    in
    let scope = resolve_parameters state scope signature_.parameters in
    resolve_result state scope signature_.result;
    let scope =
      match signature_.result with
      | Some (Lends _) -> { scope with is_lending_method = true }
      | _ -> scope
    in
    resolve_clauses state scope signature_.clauses;
    Some scope
  end

let resolve_fields state scope (fields_ : Syntax.field list) =
  List.iter
    (fun (field : Syntax.field) ->
      match field.kind with
      | Field_declaration { type_; default; _ } ->
          resolve_type_expression state scope type_;
          Option.iter
            (fun default ->
              run_in_section state Contract (fun () -> resolve_expression state scope default))
            default
      | Field_error -> ())
    fields_

let list_field_names (fields_ : Syntax.field list) =
  List.filter_map
    (fun (field : Syntax.field) ->
      match field.kind with Field_declaration { name; _ } -> Some name.text | Field_error -> None)
    fields_

let find_law_parameters lookups (trait : Path.t) law =
  match Names.find_definition lookups trait with
  | Some (_, { kind = Trait { members; _ }; _ }) ->
      List.find_map
        (fun (member : Syntax.trait_member Syntax.node) ->
          match member.kind with
          | Law written_law when written_law.name.text = law ->
              Some
                (List.filter_map
                   (fun (parameter : Syntax.parameter) ->
                     match parameter.kind with
                     | Named_parameter { name; _ } -> Some name.text
                     | Self_parameter _ | Parameter_error -> None)
                   written_law.parameters)
          | _ -> None)
        members
  | _ -> None

let resolve_inherited scope ~(owner : Path.t) (generics : Syntax.generic_parameter list) =
  List.fold_left
    (fun scope (generic : Syntax.generic_parameter) ->
      let make_parameter (name : Syntax.name) : Types.parameter = { owner; name = name.text } in
      let add_type (name : Syntax.name) (target : target) =
        { scope with types = String_map.add name.text target scope.types }
      in
      match generic.kind with
      | Type_parameter (name, _) -> add_type name (Type_parameter (make_parameter name))
      | Value_parameter (name, _) ->
          {
            scope with
            values =
              String_map.add name.text
                (Value_generic (make_parameter name), Catalog.Resolve.Generic_parameter)
                scope.values;
          }
      | Generic_error -> scope)
    scope generics

let resolve_definition state ~(path : Path.t) ?(container : (Path.t * Syntax.definition) option)
    (definition_ : Syntax.definition) =
  let is_broken part =
    Option.is_some
      (Parts.find_syntax_error ~spans:state.spans ~syntax_errors:state.syntax_errors definition_
         part)
  in
  let header_broken = is_broken Header and body_broken = is_broken Body in
  let scope =
    match container with
    | Some (owner, { kind = Trait { generics = generics_; _ }; _ }) ->
        resolve_inherited empty_scope ~owner generics_
    | Some (owner, { kind = Impl { type_; _ }; _ }) ->
        resolve_inherited empty_scope ~owner type_.generics
    | _ -> empty_scope
  in
  match definition_.kind with
  | Function { signature = signature_; body } ->
      if not header_broken then begin
        let scope = resolve_head state scope ~owner:path signature_.name in
        match resolve_signature state scope ~owner:path ~broken:false signature_ with
        | Some scope ->
            if not body_broken then
              run_in_section state Body (fun () -> resolve_block state scope body)
        | None -> ()
      end
  | Method_declaration signature_ ->
      if not header_broken then
        ignore (resolve_signature state scope ~owner:path ~broken:false signature_)
  | Type_definition { generics = generics_; body; clauses; _ } ->
      if not header_broken then begin
        let scope = resolve_generics state scope ~owner:path generics_ in
        let record_fields =
          match body with Fields fields_ -> list_field_names fields_ | _ -> []
        in
        (match body with
        | Fields fields_ -> resolve_fields state scope fields_
        | Variants variants ->
            List.iter
              (fun (variant : Syntax.variant) ->
                Option.iter (resolve_fields state scope) variant.fields)
              variants
        | Type_todo -> ());
        let clause_scope =
          {
            (enter_specification scope) with
            values =
              List.fold_left
                (fun values field ->
                  String_map.add field (Value_field field, Catalog.Resolve.Field) values)
                scope.values record_fields;
          }
        in
        List.iter
          (fun (clause : Syntax.type_clause) ->
            match clause.kind with
            | Type_invariant value | Potential value ->
                run_in_section state Contract (fun () ->
                    resolve_expression state clause_scope value)
            | Derives traits -> List.iter (resolve_path_type state scope) traits)
          clauses
      end
  | Trait { generics = generics_; requires; members; _ } ->
      if not header_broken then begin
        let scope = resolve_generics state scope ~owner:path generics_ in
        List.iter (resolve_path_type state scope) requires;
        List.iteri
          (fun index (line : Syntax.trait_member Syntax.node) ->
            if not (is_broken (Member_header index)) then
              match line.kind with
              | Associated_type (_, bounds) -> List.iter (resolve_path_type state scope) bounds
              | Law { parameters = parameters_; requires; body; _ } ->
                  let inner = resolve_parameters state (enter_specification scope) parameters_ in
                  run_in_section state Contract (fun () ->
                      List.iter (resolve_expression state inner) requires;
                      if not (is_broken (Member_body index)) then resolve_block state inner body)
              | Associated_capability _ | Trait_member_error -> ())
          members
      end
  | Impl { trait_; type_; uses; members } ->
      if not header_broken then begin
        resolve_type_name state scope type_.path;
        let scope = resolve_generics state scope ~owner:path type_.generics in
        resolve_path_type state scope trait_;
        List.iter (resolve_capability_reference state scope) uses;
        List.iteri
          (fun index (line : Syntax.impl_member Syntax.node) ->
            if not (is_broken (Member_header index)) then
              match line.kind with
              | Associated_definition (_, type_) -> resolve_type_expression state scope type_
              | Capability_definition (_, capabilities) ->
                  List.iter (resolve_capability_use state scope) capabilities
              | Impl_member_error -> ())
          members
      end
  | Capability _ -> ()
  | Constant { name; type_; value } ->
      if not header_broken then begin
        let scope = resolve_head state scope ~owner:path name in
        resolve_type_expression state scope type_;
        if not body_broken then
          run_in_section state Body (fun () -> resolve_expression state scope value)
      end
  | Test { uses; body; _ } ->
      if not header_broken then begin
        List.iter (resolve_capability_reference state scope) uses;
        if not body_broken then run_in_section state Body (fun () -> resolve_block state scope body)
      end
  | Theorem { generics = generics_; parameters = parameters_; clauses = clauses_; body; _ } ->
      if not header_broken then begin
        let scope = resolve_generics state (enter_specification scope) ~owner:path generics_ in
        let scope =
          declare_capability_parameters state scope ~owner:path
            ~types:(list_parameter_types parameters_)
            clauses_
        in
        let scope = resolve_parameters state scope parameters_ in
        resolve_clauses state scope clauses_;
        if not body_broken then run_in_section state Body (fun () -> resolve_block state scope body)
      end
  | Law_proof { trait_; law; type_; body } ->
      if not header_broken then begin
        resolve_type_name state scope type_.path;
        let scope = resolve_generics state scope ~owner:path type_.generics in
        resolve_path_type state scope trait_;
        let law_parameters =
          match (lookup_current_names state).names.(trait_.path.last.id) with
          | Some (Definition (Trait, trait)) ->
              Option.value ~default:[] (find_law_parameters state.lookups trait law.text)
          | _ -> []
        in
        let values =
          List.fold_left
            (fun values (index, name) ->
              String_map.add name (Value_law_parameter index, Catalog.Resolve.Law_parameter) values)
            scope.values
            (List.mapi (fun index name -> (index, name)) law_parameters)
        in
        if not body_broken then
          run_in_section state Body (fun () ->
              resolve_block state { (enter_specification scope) with values } body)
      end
  | Definition_error _ -> ()
