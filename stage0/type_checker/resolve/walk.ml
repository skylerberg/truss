module String_map = Map.Make (String)

type specification_function = Log | Power | Call_cost of Metric.t | Calls

type target =
  | Binding
  | Local of Syntax.id
  | Law_parameter of int
  | Type_parameter of Types.parameter
  | Capability_parameter of Types.parameter
  | Value_parameter of Types.parameter
  | Definition of Names.named * Path.t
  | Variant of Path.t * string
  | Module of Path.module_
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

type specification = {
  active : bool;
  names_result : bool;
  cost_bound : bool;
  names_visited : bool;
  names_final : bool;
  elements : string list;
}

type scope = {
  values : (value * string) String_map.t;
  types : target String_map.t;
  capability_parameters : target String_map.t;
  specification : specification;
  is_lending_method : bool;
}

let no_specification =
  {
    active = false;
    names_result = false;
    cost_bound = false;
    names_visited = false;
    names_final = false;
    elements = [];
  }

let in_specification = { no_specification with active = true }

type section = Interface | Contract | Body

type section_names = {
  names : target option array;
  brackets : bracket option array;
  mutable holes : (Syntax.id * (string * value) list) list;
  mutable diagnostics : Diagnostic.in_definition list;
  mutable used_imports : string list;
}

type state = {
  lookups : Names.lookups;
  key : Names.key;
  spans : Source.Definition_span.t array;
  interface : section_names;
  contract : section_names;
  body : section_names;
  walked : section;
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

let create lookups key ~spans ~walked =
  let size = Array.length spans in
  {
    lookups;
    key;
    spans;
    interface = make_section_names size;
    contract = make_section_names size;
    body = make_section_names size;
    walked;
    section = Interface;
  }

let lookup_section_names state = function
  | Interface -> state.interface
  | Contract -> state.contract
  | Body -> state.body

let lookup_current_names state = lookup_section_names state state.section
let read_span state id = state.spans.(id)

let run_in_section state section walk =
  if section = state.walked then begin
    let enclosing = state.section in
    state.section <- section;
    walk ();
    state.section <- enclosing
  end

let add_diagnostic state ?fixes code (span : Source.Definition_span.t) message =
  let diagnostic = Diagnostic.make ?fixes ~code:(Resolve code) span message in
  let names = lookup_current_names state in
  names.diagnostics <- diagnostic :: names.diagnostics;
  Diagnostic.make_reported diagnostic

let report state ?fixes code span message = ignore (add_diagnostic state ?fixes code span message)

let set_target state (name : Syntax.name) target =
  (lookup_current_names state).names.(name.id) <- Some target

let report_unknown state (name : Syntax.name) ~expected candidates =
  let fixes =
    match Diagnostic.find_closest name.text candidates with
    | Some candidate ->
        [
          Diagnostic.fix
            (Printf.sprintf "Write `%s`." candidate)
            [ Diagnostic.replace (read_span state name.id) candidate ];
        ]
    | None -> []
  in
  set_target state name
    (Unknown
       (add_diagnostic state ~fixes Unknown_name (read_span state name.id)
          (Printf.sprintf "Nothing named `%s` is %s." name.text expected)))

let find_module_item state text = state.lookups.find state.key.module_ text

let resolve_module_names state (first : Syntax.name) (rest : Syntax.name list) =
  let make_failure report =
    set_target state first (Unknown report);
    Error report
  in
  if
    List.mem_assoc first.text (state.lookups.list_imports state.key)
    && not (List.mem first.text (lookup_current_names state).used_imports)
  then
    (lookup_current_names state).used_imports <-
      first.text :: (lookup_current_names state).used_imports;
  begin match
    Names.lookup_module state.lookups ~from:state.key.module_
      ~imports:(state.lookups.list_imports state.key)
      first.text
      (List.map (fun (name : Syntax.name) -> name.text) rest)
  with
  | Found_module module_ ->
      set_target state first (Module module_);
      Ok module_
  | Restricted_module ->
      make_failure
        (add_diagnostic state Intrinsic_import (read_span state first.id)
           Names.restricted_module_message)
  | Ambiguous_module (imported, package) ->
      make_failure
        (add_diagnostic state Ambiguous_module (read_span state first.id)
           (Printf.sprintf
              "`%s` could be the imported module `%s` or the module `%s`. Write the imported one's \
               full path, or remove its `use`."
              first.text (Path.show_module imported) (Path.show_module package)))
  | No_module text ->
      make_failure
        (add_diagnostic state Unknown_module (read_span state first.id)
           (Printf.sprintf "No module `%s` is imported or exists." text))
  end

let find_in_module state module_ (name : Syntax.name) ~types =
  let is_kind = if types then Names.is_type_kind else Names.is_value_kind in
  match Names.lookup_in state.lookups ~from:state.key.module_ module_ name.text ~is_kind with
  | Visible (item, path) ->
      set_target state name (Definition (item.kind, path));
      Some (path, item)
  | Hidden (path, visibility) ->
      set_target state name
        (Unknown
           (add_diagnostic state Not_visible (read_span state name.id)
              (Names.describe_hidden path visibility)));
      None
  | Absent ->
      let candidates =
        List.filter_map
          (fun (item : Names.entry) ->
            if
              (if types then Names.is_type_kind item.kind else Names.is_value_kind item.kind)
              && Names.is_visible ~from:state.key.module_ module_ item.visibility
            then Some item.name
            else None)
          (state.lookups.list_entries module_)
      in
      report_unknown state name ~expected:("in `" ^ Path.show_module module_ ^ "`") candidates;
      None

let list_type_candidates state scope =
  List.map fst (String_map.bindings scope.types)
  @ List.filter_map
      (fun (item : Names.entry) -> if Names.is_type_kind item.kind then Some item.name else None)
      (state.lookups.list_entries state.key.module_)
  @ List.map fst Prelude.types

let resolve_type_name state scope ?(variants = false) (path : Syntax.path) =
  match path.modules with
  | first :: rest -> (
      match resolve_module_names state first rest with
      | Ok module_ -> ignore (find_in_module state module_ path.last ~types:true)
      | Error report -> set_target state path.last (Unknown report))
  | [] -> (
      let text = path.last.text in
      match String_map.find_opt text scope.types with
      | Some parameter -> set_target state path.last parameter
      | None -> (
          match Names.find_bare_type state.lookups ~from:state.key.module_ text with
          | Some (item, found) -> set_target state path.last (Definition (item.kind, found))
          | None -> (
              match if variants then Prelude.find_variant text else None with
              | Some (type_, variant) -> set_target state path.last (Variant (type_, variant))
              | None ->
                  report_unknown state path.last ~expected:"a type here"
                    (list_type_candidates state scope
                    @ if variants then List.map fst Prelude.variants else []))))

let find_target state (name : Syntax.name) = (lookup_current_names state).names.(name.id)

let rec resolve_type_expression state scope (type_ : Syntax.type_expression) =
  match type_.kind with
  | Path_type path -> resolve_path_type state scope path
  | Any_type path -> resolve_path_type state scope path
  | Self_type _ -> ()
  | Associated (base, member) -> resolve_associated_base state scope base member "type"
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

and resolve_associated_base state scope (base : Syntax.name) (member : Syntax.name) kind =
  match String_map.find_opt base.text scope.types with
  | Some parameter -> set_target state base parameter
  | None ->
      set_target state base
        (Unknown
           (add_diagnostic state Not_a_generic_parameter (read_span state base.id)
              (Printf.sprintf
                 "`%s.%s` names an associated %s, so `%s` must be a generic parameter here."
                 base.text member.text kind base.text)))

and resolve_capability_reference state scope (reference : Syntax.capability_reference) =
  match reference.kind with
  | Capability_path { path = { modules = []; last }; arguments = []; _ }
    when String_map.mem last.text scope.capability_parameters
         && not (String_map.mem last.text scope.types) ->
      let span = read_span state last.id in
      set_target state last
        (Unknown
           (add_diagnostic state
              ~fixes:
                [
                  Diagnostic.fix
                    (Printf.sprintf "Write `generic %s`." last.text)
                    [ Diagnostic.replace span ("generic " ^ last.text) ];
                ]
              Unknown_name span
              (Printf.sprintf
                 "`%s` is a capability parameter of this signature, which is written `generic %s` \
                  at each use."
                 last.text last.text)))
  | Capability_path path -> resolve_path_type state scope path
  | Self_capabilities _ -> ()
  | Associated_capabilities (base, member) ->
      resolve_associated_base state scope base member "capability set"
  | Generic_capability name ->
      set_target state name
        (match String_map.find_opt name.text scope.capability_parameters with
        | Some target -> target
        | None ->
            Unknown
              (add_diagnostic state Unknown_name (read_span state reference.id)
                 (Printf.sprintf
                    "`generic %s` names no capability parameter here. A capability parameter \
                     belongs to a function, a method, or a theorem, whose signature names it."
                    name.text)))

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
               (add_diagnostic state Not_a_constant (read_span state name.id)
                  (Printf.sprintf
                     "`%s` in a type argument must be a value generic parameter or a constant."
                     name.text))))

and resolve_clause state scope (clause : Syntax.clause) =
  let specification = { scope with specification = in_specification } in
  match clause.kind with
  | Uses capabilities -> List.iter (resolve_capability_reference state scope) capabilities
  | Requires value -> resolve_expression state specification value
  | Ensures value ->
      resolve_expression state
        {
          specification with
          specification =
            { in_specification with names_result = true; names_final = scope.is_lending_method };
        }
        value
  | Decreases measures -> List.iter (resolve_expression state specification) measures
  | Cost cost -> (
      (match cost.resource with
      | Calls (Call_parameter name) -> resolve_local_value state scope name
      | Calls (Call_capability path) -> resolve_path_type state scope path
      | Calls (Call_method (path, _)) -> resolve_path_type state scope path
      | Metric _ -> ());
      let bound =
        {
          scope with
          specification =
            { scope.specification with active = true; names_result = true; cost_bound = true };
        }
      in
      match cost.bound with
      | Big_o value | At_most value | Exactly value -> resolve_expression state bound value)
  | Clause_error -> ()

and resolve_local_value state scope (name : Syntax.name) =
  let text = name.text in
  match String_map.find_opt text scope.values with
  | Some (Value_local id, _) -> set_target state name (Local id)
  | Some (Value_generic parameter, _) -> set_target state name (Value_parameter parameter)
  | Some (Value_field field, _) -> set_target state name (Field field)
  | Some (Value_law_parameter index, _) -> set_target state name (Law_parameter index)
  | None ->
      if scope.specification.active && text = "old" then set_target state name Old
      else if scope.specification.names_visited && text = "visited" then
        set_target state name Visited
      else if scope.specification.names_final && text = "final" then set_target state name Final
      else if scope.specification.active && text = "identical" then set_target state name Identical
      else if scope.specification.names_result && text = "result" then
        set_target state name Result_value
      else if List.mem text scope.specification.elements then
        set_target state name
          (Unknown
             (add_diagnostic state Unknown_name (read_span state name.id)
                (Printf.sprintf
                   "`%s` is the loop's element, which is bound only in the loop's body: the loop's \
                    clauses hold before the first element and after the last. Name the elements so \
                    far with `visited`."
                   text)))
      else
        begin match find_module_item state text with
        | Some item when Names.is_value_kind item.kind ->
            set_target state name
              (Definition (item.kind, Top { module_ = state.key.module_; name = text }))
        | _ ->
            if text = "null" || text = "nil" then begin
              set_target state name
                (Unknown
                   (add_diagnostic state Null (read_span state name.id)
                      ~fixes:
                        [
                          Diagnostic.fix "Write `None`."
                            [ Diagnostic.replace (read_span state name.id) "None" ];
                        ]
                      (Printf.sprintf
                         "Truss has no `%s`. A value that may be missing is an `Option`, and \
                          `None` is its empty case."
                         text)))
            end
            else
              report_unknown state name ~expected:"a value here"
                (List.map fst (String_map.bindings scope.values)
                @ List.filter_map
                    (fun (item : Names.entry) ->
                      if Names.is_value_kind item.kind then Some item.name else None)
                    (state.lookups.list_entries state.key.module_))
        end

and resolve_name_expression state scope (path : Syntax.path) =
  match path.modules with
  | first :: rest -> (
      match resolve_module_names state first rest with
      | Ok module_ ->
          let upper = path.last.text.[0] >= 'A' && path.last.text.[0] <= 'Z' in
          ignore (find_in_module state module_ path.last ~types:upper)
      | Error report -> set_target state path.last (Unknown report))
  | [] ->
      if path.last.text.[0] >= 'A' && path.last.text.[0] <= 'Z' then
        resolve_type_name state scope ~variants:true path
      else resolve_local_value state scope path.last

and find_name_target state (value : Syntax.expression) =
  match value.kind with
  | Name path -> find_target state path.last
  | Parenthesized inner -> find_name_target state inner
  | _ -> None

and find_specification_function state scope name =
  let is_free_name () =
    (not (String_map.mem name scope.values))
    &&
    match find_module_item state name with
    | Some item -> not (Names.is_value_kind item.kind)
    | None -> true
  in
  let specification_function =
    match name with
    | "log" -> Some Log
    | "power" -> Some Power
    | "calls" -> Some Calls
    | _ -> Option.map (fun metric -> Call_cost metric) (Metric.find name)
  in
  match specification_function with
  | Some _ when scope.specification.cost_bound -> specification_function
  | Some (Log | Power) when scope.specification.active && is_free_name () -> specification_function
  | Some (Log | Power | Call_cost _ | Calls) | None -> None

and resolve_bracket state scope (value : Syntax.expression) base items =
  resolve_expression state scope base;
  let decision =
    match base.kind with
    | Member _ -> Method_bracket
    | _ -> (
        match find_name_target state base with
        | Some (Definition ((Type | Trait | Capability), _)) | Some (Type_parameter _) ->
            Type_arguments
        | Some (Definition ((Function | Theorem), Top { module_; name })) ->
            let generic =
              match state.lookups.find module_ name with Some item -> item.generic | None -> false
            in
            if not generic then
              report state Not_generic (read_span state value.id)
                (Printf.sprintf
                   "`%s` is a function without generic parameters, so `[...]` cannot give it type \
                    arguments, and a function cannot be indexed."
                   name);
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
  let rec classify_head (value : Syntax.expression) =
    match value.kind with
    | Member (base, _) -> classify_head base
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
    | Name path -> (
        match find_target state path.last with
        | Some (Local _ | Field _) -> `Place false
        | Some (Definition (Constant, _)) -> `Place false
        | Some (Unknown _) -> `Unknown
        | _ -> `Not_a_place value)
    | _ -> `Not_a_place value
  in
  match classify_head inner with
  | `Place _ | `Unknown -> ()
  | `Not_a_place _ ->
      let keyword_end = (read_span state inner.id).start in
      report state Not_a_place (read_span state written.id)
        ~fixes:
          [
            Diagnostic.fix "Remove the keyword."
              [
                Diagnostic.delete
                  (Source.Definition_span.make (read_span state written.id).start keyword_end);
              ];
          ]
        "Only a place, such as a variable, a field, or an element, can take `mut` or `own`. A \
         temporary value is always passed as owned."

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
  | Name path -> resolve_name_expression state scope path
  | Member (base, _) -> resolve_expression state scope base
  | Bracket (base, items) -> resolve_bracket state scope value base items
  | Call (callee, arguments) ->
      (match callee.kind with
      | Name { modules = []; last } -> (
          match find_specification_function state scope last.text with
          | Some function_ -> set_target state last (Specification_function function_)
          | None -> resolve_expression state scope callee)
      | _ -> resolve_expression state scope callee);
      List.iter
        (fun (argument : Syntax.argument) -> resolve_expression state scope argument.value)
        arguments
  | Try inner | Prefix (_, inner) | Any inner | Echo inner | Parenthesized inner ->
      resolve_expression state scope inner
  | Mode (_, inner) ->
      resolve_expression state scope inner;
      check_place state value inner
  | With (base, updates) ->
      resolve_expression state scope base;
      List.iter
        (fun (update : Syntax.update) ->
          match update.kind with
          | Update { field; value = None; path = [] } -> resolve_local_value state scope field
          | Update { value = Some value; _ } -> resolve_expression state scope value
          | Update { value = None; _ } | Update_error -> ())
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
    report state Shadowed_name (read_span state name.id)
      (Printf.sprintf "`%s` is already %s, and a name cannot shadow another. Choose another name."
         name.text existing)
  in
  (match String_map.find_opt name.text scope.values with
  | Some (_, existing) -> check_shadowing existing
  | None -> ());
  set_target state name Binding;
  {
    scope with
    values = String_map.add name.text (Value_local name.id, "a local here") scope.values;
  }

and declare_parameter state scope (name : Syntax.name) =
  let scope = declare_value state scope name in
  { scope with values = String_map.add name.text (Value_local name.id, "a parameter") scope.values }

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
                report state Alternative_bindings (read_span state alternative.id)
                  (Printf.sprintf
                     "Every alternative of a pattern must bind the same names. The first binds %s, \
                      and this one binds %s."
                     (match list_texts first with
                     | [] -> "none"
                     | names -> "`" ^ String.concat "`, `" names ^ "`")
                     (match list_texts names with
                     | [] -> "none"
                     | names -> "`" ^ String.concat "`, `" names ^ "`"))
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
      report_unknown state last ~expected:"a constant in a module here" []
  | Module_constant { modules = first :: rest; last } -> (
      match resolve_module_names state first rest with
      | Ok module_ -> ignore (find_in_module state module_ last ~types:false)
      | Error report -> set_target state last (Unknown report))
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
      let elements, clause_scope =
        match iterable.kind with
        | Range { start = Some _; stop = Some _; _ } -> ([], inner)
        | _ ->
            ( String_map.fold
                (fun name binding names ->
                  if String_map.find_opt name scope.values = Some binding then names
                  else name :: names)
                inner.values [],
              scope )
      in
      List.iter (resolve_loop_clause ~for_loop:true ~elements state clause_scope) clauses;
      resolve_block state inner body;
      scope
  | While { condition = test; clauses; body } ->
      let inner = resolve_condition state scope test in
      List.iter (resolve_loop_clause state scope) clauses;
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
                report state Shadowed_name (read_span state branch.id)
                  (Printf.sprintf
                     "Another branch of this `%s` block already binds `%s`, and a name cannot \
                      shadow another. Choose another name."
                     word key))
            bound;
          { after with values = String_map.union (fun _ left _ -> Some left) after.values bound })
        scope body.statements
  | Proof body ->
      resolve_block state { scope with specification = in_specification } body;
      scope
  | Assert { value; _ } ->
      resolve_expression state scope value;
      scope
  | Statement_error -> scope

and resolve_loop_clause ?(for_loop = false) ?(elements = []) state scope
    (written : Syntax.loop_clause) =
  let scope =
    if for_loop then
      { scope with specification = { scope.specification with names_visited = true; elements } }
    else scope
  in
  let specification =
    { scope with specification = { in_specification with names_visited = for_loop; elements } }
  in
  match written.kind with
  | Invariant value -> resolve_expression state specification value
  | Loop_decreases measures -> List.iter (resolve_expression state specification) measures
  | Loop_cost cost -> resolve_clause state scope { kind = Cost cost; id = written.id }

let find_shadowed_type state scope text =
  if String_map.mem text scope.types then Some "a generic parameter here"
  else
    match find_module_item state text with
    | Some item when Names.is_type_kind item.kind ->
        Some (Names.show_kind (Names.convert_named item.kind) ^ " of this module")
    | _ -> if List.mem text Prelude.names then Some "a name in the prelude" else None

let report_shadowing state (name : Syntax.name) existing =
  add_diagnostic state Shadowed_name (read_span state name.id)
    (Printf.sprintf "`%s` is already %s, and a name cannot shadow another. Choose another name."
       name.text existing)

let declare_type state scope (name : Syntax.name) target =
  Option.iter
    (fun existing -> ignore (report_shadowing state name existing))
    (find_shadowed_type state scope name.text);
  set_target state name Binding;
  { scope with types = String_map.add name.text target scope.types }

let rec list_generic_capabilities (type_ : Syntax.type_expression) : Syntax.name list =
  match type_.kind with
  | Path_type path | Any_type path ->
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
      | Uses references ->
          List.filter_map
            (fun (reference : Syntax.capability_reference) ->
              match reference.kind with Generic_capability name -> Some name | _ -> None)
            references
      | Requires _ | Ensures _ | Decreases _ | Cost _ | Clause_error -> [])
    clauses

let declare_capability_parameters state scope ~(owner : Path.t)
    ~(types : Syntax.type_expression list) (clauses : Syntax.clause list) =
  let constrained = List.concat_map list_generic_capabilities types in
  let used = list_used_generic_capabilities clauses in
  List.iter
    (fun (name : Syntax.name) ->
      if not (List.exists (fun (typed : Syntax.name) -> typed.text = name.text) constrained) then
        report state Unconstrained_capability_parameter (read_span state name.id)
          (Printf.sprintf
             "`generic %s` appears only in the function's own `uses`, so no argument gives it \
              capabilities, and it stands for none. Name it in the type of a parameter, as in \
              `visit: (fn() uses generic %s)`."
             name.text name.text))
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
                  (Value_generic (make_parameter name), "a generic parameter")
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
    types = String_map.empty;
    capability_parameters = String_map.empty;
    specification = no_specification;
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
      | Uses _ | Cost _ | Clause_error -> resolve_clause state scope clause_)
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
                (Value_generic (make_parameter name), "a generic parameter")
                scope.values;
          }
      | Generic_error -> scope)
    scope generics

let resolve_definition state ~(path : Path.t) ?(container : (Path.t * Syntax.definition) option)
    (definition_ : Syntax.definition) =
  let is_broken part = Names.is_broken state.lookups state.key part in
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
            scope with
            specification = in_specification;
            values =
              List.fold_left
                (fun values field -> String_map.add field (Value_field field, "a field") values)
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
                  let inner =
                    resolve_parameters state
                      { scope with specification = in_specification }
                      parameters_
                  in
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
                  List.iter (resolve_capability_reference state scope) capabilities
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
        let scope =
          resolve_generics state
            { scope with specification = in_specification }
            ~owner:path generics_
        in
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
              Option.value ~default:[] (Names.find_law_parameters state.lookups trait law.text)
          | _ -> []
        in
        let values =
          List.fold_left
            (fun values (index, name) ->
              String_map.add name (Value_law_parameter index, "a parameter of the law") values)
            scope.values
            (List.mapi (fun index name -> (index, name)) law_parameters)
        in
        if not body_broken then
          run_in_section state Body (fun () ->
              resolve_block state { scope with values; specification = in_specification } body)
      end
  | Definition_error _ -> ()
