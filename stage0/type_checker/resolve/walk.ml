open Syntax
module String_map = Map.Make (String)

type specification_function = Log | Power | Time | Calls

type target =
  | Binding
  | Local of id
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
  | Value_local of id
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
  mutable holes : (id * (string * value) list) list;
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

let section_names size =
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
    interface = section_names size;
    contract = section_names size;
    body = section_names size;
    walked;
    section = Interface;
  }

let names_of state = function
  | Interface -> state.interface
  | Contract -> state.contract
  | Body -> state.body

let current state = names_of state state.section
let read_span state id = state.spans.(id)

let in_section state section walk =
  if section = state.walked then begin
    let enclosing = state.section in
    state.section <- section;
    walk ();
    state.section <- enclosing
  end

let reported state ?fixes code (span : Source.Definition_span.t) message =
  let diagnostic = Diagnostic.make ?fixes ~code:(Resolve code) span message in
  let names = current state in
  names.diagnostics <- diagnostic :: names.diagnostics;
  Diagnostic.reported diagnostic

let report state ?fixes code span message = ignore (reported state ?fixes code span message)
let set state (name : name) target = (current state).names.(name.id) <- Some target

let unknown state (name : name) ~expected candidates =
  let fixes =
    match Diagnostic.closest name.text candidates with
    | Some candidate ->
        [
          Diagnostic.fix
            (Printf.sprintf "Write `%s`." candidate)
            [ Diagnostic.replace (read_span state name.id) candidate ];
        ]
    | None -> []
  in
  set state name
    (Unknown
       (reported state ~fixes Unknown_name (read_span state name.id)
          (Printf.sprintf "Nothing named `%s` is %s." name.text expected)))

let module_item state text = state.lookups.find state.key.module_ text

let module_of_names state (first : name) (rest : name list) =
  let failed report =
    set state first (Unknown report);
    Error report
  in
  if
    List.mem_assoc first.text (state.lookups.imports state.key)
    && not (List.mem first.text (current state).used_imports)
  then (current state).used_imports <- first.text :: (current state).used_imports;
  begin match
    Names.lookup_module state.lookups ~from:state.key.module_
      ~imports:(state.lookups.imports state.key)
      (List.map (fun (name : Syntax.name) -> name.text) (first :: rest))
  with
  | Found_module (module_, `Package)
    when module_ = Intrinsic.module_ && state.key.module_.package <> Path.standard_package ->
      failed
        (reported state Intrinsic_import (read_span state first.id)
           "Only the `standard` package can use `standard::intrinsic`.")
  | Found_module (module_, _) ->
      set state first (Module module_);
      Ok module_
  | Ambiguous_module (imported, package) ->
      failed
        (reported state Ambiguous_module (read_span state first.id)
           (Printf.sprintf
              "`%s` could be the imported module `%s` or the module `%s`. Write the imported one's \
               full path, or remove its `use`."
              first.text (Path.show_module imported) (Path.show_module package)))
  | No_module text ->
      failed
        (reported state Unknown_module (read_span state first.id)
           (Printf.sprintf "No module `%s` is imported or exists." text))
  end

let in_module state module_ (name : name) ~types =
  let is_kind = if types then Names.is_type_kind else Names.is_value_kind in
  match Names.find_in state.lookups ~from:state.key.module_ module_ name.text ~is_kind with
  | Found_name (item, path) ->
      set state name (Definition (item.kind, path));
      Some (path, item)
  | Hidden_name item ->
      set state name
        (Unknown
           (reported state Not_visible (read_span state name.id)
              (Printf.sprintf "`%s::%s` is %s." (Path.show_module module_) name.text
                 (match item.visibility with
                 | Private -> "private to its module, so it cannot be used here"
                 | _ -> "internal to its package, so it cannot be used here"))));
      None
  | No_name ->
      let candidates =
        List.filter_map
          (fun (item : Names.entry) ->
            if
              (if types then Names.is_type_kind item.kind else Names.is_value_kind item.kind)
              && Names.visible ~from:state.key.module_ module_ item.visibility
            then Some item.name
            else None)
          (state.lookups.entries module_)
      in
      unknown state name ~expected:("in `" ^ Path.show_module module_ ^ "`") candidates;
      None

let type_candidates state scope =
  List.map fst (String_map.bindings scope.types)
  @ List.filter_map
      (fun (item : Names.entry) -> if Names.is_type_kind item.kind then Some item.name else None)
      (state.lookups.entries state.key.module_)
  @ List.map fst Prelude.types

let type_name state scope ?(variants = false) (path : path) =
  match path.modules with
  | first :: rest -> (
      match module_of_names state first rest with
      | Ok module_ -> ignore (in_module state module_ path.last ~types:true)
      | Error report -> set state path.last (Unknown report))
  | [] -> (
      let text = path.last.text in
      match String_map.find_opt text scope.types with
      | Some parameter -> set state path.last parameter
      | None -> (
          match Names.find_bare_type state.lookups ~from:state.key.module_ text with
          | Some (item, found) -> set state path.last (Definition (item.kind, found))
          | None -> (
              match if variants then Prelude.find_variant text else None with
              | Some (type_, variant) -> set state path.last (Variant (type_, variant))
              | None ->
                  unknown state path.last ~expected:"a type here"
                    (type_candidates state scope
                    @ if variants then List.map fst Prelude.variants else []))))

let target_of state (name : name) = (current state).names.(name.id)

let rec type_expression state scope (type_ : type_expression) =
  match type_.kind with
  | Path_type path -> path_type state scope path
  | Any_type path -> path_type state scope path
  | Self_type _ -> ()
  | Associated (base, member) -> associated_base state scope base member "type"
  | Function_type { inputs; output; clauses } ->
      List.iter (fun (input : function_input) -> type_expression state scope input.type_) inputs;
      Option.iter (type_expression state scope) output;
      let named =
        List.fold_left
          (fun scope (input : function_input) ->
            Option.fold ~none:scope ~some:(declare_parameter state scope) input.name)
          scope inputs
      in
      List.iter (clause state named) clauses
  | Type_error -> ()

and associated_base state scope (base : name) (member : name) kind =
  match String_map.find_opt base.text scope.types with
  | Some parameter -> set state base parameter
  | None ->
      set state base
        (Unknown
           (reported state Not_a_generic_parameter (read_span state base.id)
              (Printf.sprintf
                 "`%s.%s` names an associated %s, so `%s` must be a generic parameter here."
                 base.text member.text kind base.text)))

and capability_reference state scope (reference : capability_reference) =
  match reference.kind with
  | Capability_path path -> path_type state scope path
  | Self_capabilities _ -> ()
  | Associated_capabilities (base, member) ->
      associated_base state scope base member "capability set"

and path_type state scope (path : path_type) =
  type_name state scope path.path;
  List.iter (type_argument state scope) path.arguments

and type_argument state scope = function
  | Type_argument type_ -> type_expression state scope type_
  | Count _ -> ()
  | Count_name name -> count_name state scope name
  | Constraint (_, type_) -> type_expression state scope type_

and count_name state scope (name : name) =
  match String_map.find_opt name.text scope.values with
  | Some (Value_generic parameter, _) -> set state name (Value_parameter parameter)
  | shadowing -> (
      match module_item state name.text with
      | Some item when item.kind = Constant && shadowing = None ->
          set state name
            (Definition (Constant, Top { module_ = state.key.module_; name = name.text }))
      | _ ->
          set state name
            (Unknown
               (reported state Not_a_constant (read_span state name.id)
                  (Printf.sprintf
                     "`%s` in a type argument must be a value generic parameter or a constant."
                     name.text))))

and clause state scope (clause : clause) =
  let specification = { scope with specification = in_specification } in
  match clause.kind with
  | Uses capabilities -> List.iter (capability_reference state scope) capabilities
  | Requires value -> expression state specification value
  | Ensures value ->
      expression state
        {
          specification with
          specification =
            { in_specification with names_result = true; names_final = scope.is_lending_method };
        }
        value
  | Decreases measures -> List.iter (expression state specification) measures
  | Cost cost -> (
      (match cost.resource with
      | Calls (Call_parameter name) -> local_value state scope name
      | Calls (Call_capability path) -> path_type state scope path
      | Calls (Call_method (path, _)) -> path_type state scope path
      | Time | Allocations | Allocated_bytes -> ());
      let bound =
        {
          scope with
          specification =
            { scope.specification with active = true; names_result = true; cost_bound = true };
        }
      in
      match cost.bound with
      | Big_o value | At_most value | Exactly value -> expression state bound value
      | Finite -> ())
  | Clause_error -> ()

and local_value state scope (name : name) =
  let text = name.text in
  match String_map.find_opt text scope.values with
  | Some (Value_local id, _) -> set state name (Local id)
  | Some (Value_generic parameter, _) -> set state name (Value_parameter parameter)
  | Some (Value_field field, _) -> set state name (Field field)
  | Some (Value_law_parameter index, _) -> set state name (Law_parameter index)
  | None ->
      if scope.specification.active && text = "old" then set state name Old
      else if scope.specification.names_visited && text = "visited" then set state name Visited
      else if scope.specification.names_final && text = "final" then set state name Final
      else if scope.specification.active && text = "identical" then set state name Identical
      else if scope.specification.names_result && text = "result" then set state name Result_value
      else if List.mem text scope.specification.elements then
        set state name
          (Unknown
             (reported state Unknown_name (read_span state name.id)
                (Printf.sprintf
                   "`%s` is the loop's element, which is bound only in the loop's body: the loop's \
                    clauses hold before the first element and after the last. Name the elements so \
                    far with `visited`."
                   text)))
      else
        begin match module_item state text with
        | Some item when Names.is_value_kind item.kind ->
            set state name
              (Definition (item.kind, Top { module_ = state.key.module_; name = text }))
        | _ ->
            if text = "null" || text = "nil" then begin
              set state name
                (Unknown
                   (reported state Null (read_span state name.id)
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
              unknown state name ~expected:"a value here"
                (List.map fst (String_map.bindings scope.values)
                @ List.filter_map
                    (fun (item : Names.entry) ->
                      if Names.is_value_kind item.kind then Some item.name else None)
                    (state.lookups.entries state.key.module_))
        end

and name_expression state scope (path : path) =
  match path.modules with
  | first :: rest -> (
      match module_of_names state first rest with
      | Ok module_ ->
          let upper = path.last.text.[0] >= 'A' && path.last.text.[0] <= 'Z' in
          ignore (in_module state module_ path.last ~types:upper)
      | Error report -> set state path.last (Unknown report))
  | [] ->
      if path.last.text.[0] >= 'A' && path.last.text.[0] <= 'Z' then
        type_name state scope ~variants:true path
      else local_value state scope path.last

and name_target state (value : expression) =
  match value.kind with
  | Name path -> target_of state path.last
  | Parenthesized inner -> name_target state inner
  | _ -> None

and bracket state scope (value : expression) base items =
  expression state scope base;
  let decision =
    match base.kind with
    | Member _ -> Method_bracket
    | _ -> (
        match name_target state base with
        | Some (Definition ((Type | Trait | Capability), _))
        | Some (Type_parameter _ | Capability_parameter _) ->
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
  (current state).brackets.(value.id) <- Some decision;
  List.iter
    (function
      | Item item -> expression state scope item
      | Item_constraint (_, type_) -> type_expression state scope type_)
    items

and check_place state (written : expression) (inner : expression) =
  let rec head (value : expression) =
    match value.kind with
    | Member (base, _) -> head base
    | Parenthesized inner -> head inner
    | Bracket (base, _) -> (
        match (current state).brackets.(value.id) with
        | Some (Index | Method_bracket) -> head base
        | _ -> `Not_a_place value)
    | Call ({ kind = Member (base, _); _ }, _)
    | Call ({ kind = Bracket ({ kind = Member (base, _); _ }, _); _ }, _) -> (
        match head base with `Place _ -> `Place true | other -> other)
    | Try base -> ( match head base with `Place false -> `Not_a_place value | other -> other)
    | Self_value -> `Place false
    | Name path -> (
        match target_of state path.last with
        | Some (Local _ | Field _) -> `Place false
        | Some (Definition (Constant, _)) -> `Place false
        | Some (Unknown _) -> `Unknown
        | _ -> `Not_a_place value)
    | _ -> `Not_a_place value
  in
  match head inner with
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

and expression state scope (value : expression) =
  match value.kind with
  | Todo ->
      let names = current state in
      names.holes <-
        ( value.id,
          List.map (fun (name, (value, _)) -> (name, value)) (String_map.bindings scope.values) )
        :: names.holes
  | Integer _ | Float _ | True | False | Unreachable | Break | Continue | Self_value
  | Self_type_value | Expression_error ->
      ()
  | String literal -> string_literal state scope literal
  | Name path -> name_expression state scope path
  | Member (base, _) -> expression state scope base
  | Bracket (base, items) -> bracket state scope value base items
  | Call ({ kind = Name { modules = []; last }; _ }, arguments)
    when (scope.specification.cost_bound && List.mem last.text [ "log"; "power"; "time"; "calls" ])
         || scope.specification.active
            && List.mem last.text [ "log"; "power" ]
            && (not (String_map.mem last.text scope.values))
            &&
            match module_item state last.text with
            | Some item -> not (Names.is_value_kind item.kind)
            | None -> true ->
      set state last
        (Specification_function
           (match last.text with "log" -> Log | "power" -> Power | "time" -> Time | _ -> Calls));
      List.iter (fun (argument : argument) -> expression state scope argument.value) arguments
  | Call (callee, arguments) ->
      expression state scope callee;
      List.iter (fun (argument : argument) -> expression state scope argument.value) arguments
  | Try inner | Prefix (_, inner) | Any inner | Echo inner | Parenthesized inner ->
      expression state scope inner
  | Mode (_, inner) ->
      expression state scope inner;
      check_place state value inner
  | With (base, updates) ->
      expression state scope base;
      List.iter
        (fun (update : update) ->
          match update.kind with
          | Update { field; value = None; path = [] } -> local_value state scope field
          | Update { value = Some value; _ } -> expression state scope value
          | Update { value = None; _ } | Update_error -> ())
        updates
  | Binary { operator = And; _ } | Is _ -> ignore (condition state scope value)
  | Binary { left; right; _ } ->
      expression state scope left;
      expression state scope right
  | Range { start; stop; _ } ->
      Option.iter (expression state scope) start;
      Option.iter (expression state scope) stop
  | Quantified { binder; body; _ } ->
      let inner =
        match binder with
        | Binder_in (pattern_, collection) ->
            expression state scope collection;
            bind_pattern state scope pattern_
        | Binder_type (name, type_) ->
            type_expression state scope type_;
            declare_value state scope name
      in
      expression state inner body
  | Return inner -> Option.iter (expression state scope) inner
  | List items -> List.iter (expression state scope) items
  | Map entries ->
      List.iter
        (fun (key, item) ->
          expression state scope key;
          expression state scope item)
        entries
  | Lambda { parameters; body } ->
      let inner =
        List.fold_left (fun scope pattern_ -> bind_pattern state scope pattern_) scope parameters
      in
      block state inner body
  | If { condition = test; then_; else_ } ->
      let inner = condition state scope test in
      block state inner then_;
      Option.iter
        (function
          | Else block_ -> block state scope block_
          | Else_if branch -> expression state scope branch)
        else_
  | Match { scrutinees; arms } ->
      List.iter (expression state scope) scrutinees;
      List.iter (arm state scope) arms
  | Provide { implementations; body } ->
      List.iter (expression state scope) implementations;
      block state scope body
  | Block body -> block state scope body

and condition state scope (value : expression) =
  match value.kind with
  | Binary { operator = And; left; right; _ } ->
      let after_left = condition state scope left in
      condition state after_left right
  | Is { value = tested; pattern = pattern_; _ } ->
      expression state scope tested;
      bind_pattern state scope pattern_
  | Parenthesized inner -> condition state scope inner
  | _ ->
      expression state scope value;
      scope

and string_literal state scope (literal : string_literal) =
  Option.iter (fun tag -> type_name state scope tag) literal.tag;
  List.iter (fun (value, _) -> expression state scope value) literal.rest

and arm state scope (arm_ : arm) =
  let inner =
    List.fold_left (fun scope pattern_ -> bind_pattern state scope pattern_) scope arm_.patterns
  in
  let guarded = match arm_.guard with Some guard -> condition state inner guard | None -> inner in
  ignore (statement state guarded arm_.body)

and declare_value state scope (name : name) =
  let shadows existing =
    report state Shadowed_name (read_span state name.id)
      (Printf.sprintf "`%s` is already %s, and a name cannot shadow another. Choose another name."
         name.text existing)
  in
  (match String_map.find_opt name.text scope.values with
  | Some (_, existing) -> shadows existing
  | None -> ());
  set state name Binding;
  {
    scope with
    values = String_map.add name.text (Value_local name.id, "a local here") scope.values;
  }

and declare_parameter state scope (name : name) =
  let scope = declare_value state scope name in
  { scope with values = String_map.add name.text (Value_local name.id, "a parameter") scope.values }

and bind_pattern state scope (pattern_ : pattern) =
  let bound = ref [] in
  pattern state scope bound pattern_;
  List.fold_left (fun scope (name : name) -> declare_value state scope name) scope (List.rev !bound)

and pattern state scope bound (pattern_ : pattern) =
  match pattern_.kind with
  | Wildcard | Pattern_error -> ()
  | Binding name -> bound := name :: !bound
  | Qualified_constant constant_ -> qualified_constant state scope constant_
  | Literal literal -> literal_pattern state scope literal
  | Pattern_range { start; stop; _ } ->
      range_end state scope start;
      range_end state scope stop
  | Variant { fields; _ } -> Option.iter (List.iter (pattern_field state scope bound)) fields
  | Record fields -> List.iter (pattern_field state scope bound) fields
  | Alternatives alternatives -> (
      let each =
        List.map
          (fun alternative ->
            let names = ref [] in
            pattern state scope names alternative;
            (alternative, List.rev !names))
          alternatives
      in
      match each with
      | [] -> ()
      | (_, first) :: rest ->
          bound := List.rev_append first !bound;
          let texts names = List.sort compare (List.map (fun (name : name) -> name.text) names) in
          List.iter
            (fun ((alternative : pattern), names) ->
              if texts names <> texts first then
                report state Alternative_bindings (read_span state alternative.id)
                  (Printf.sprintf
                     "Every alternative of a pattern must bind the same names. The first binds %s, \
                      and this one binds %s."
                     (match texts first with
                     | [] -> "none"
                     | names -> "`" ^ String.concat "`, `" names ^ "`")
                     (match texts names with
                     | [] -> "none"
                     | names -> "`" ^ String.concat "`, `" names ^ "`"))
              else
                List.iter
                  (fun (name : name) ->
                    match List.find_opt (fun (other : name) -> other.text = name.text) first with
                    | Some other -> set state name (Local other.id)
                    | None -> ())
                  names)
            rest)

and pattern_field state scope bound (field : pattern_field) =
  match field.kind with
  | Named_field (_, inner) | Field inner -> pattern state scope bound inner
  | Rest -> ()

and literal_pattern state scope = function
  | Literal_string literal -> string_literal state scope literal
  | Literal_integer _ | Literal_true | Literal_false -> ()

and qualified_constant state scope = function
  | Module_constant { modules = []; last } ->
      unknown state last ~expected:"a constant in a module here" []
  | Module_constant { modules = first :: rest; last } -> (
      match module_of_names state first rest with
      | Ok module_ -> ignore (in_module state module_ last ~types:false)
      | Error report -> set state last (Unknown report))
  | Type_constant (path, _) -> type_name state scope path

and range_end state scope (end_ : range_end) =
  match end_.kind with
  | End_literal literal -> literal_pattern state scope literal
  | End_constant constant_ -> qualified_constant state scope constant_

and block state scope (block_ : block) =
  ignore
    (List.fold_left
       (fun scope statement_ -> statement state scope statement_)
       scope block_.statements)

and statement state scope (statement_ : statement) =
  match statement_.kind with
  | Let { pattern = pattern_; annotation; value; else_; _ } ->
      Option.iter (type_expression state scope) annotation;
      expression state scope value;
      Option.iter (block state scope) else_;
      bind_pattern state scope pattern_
  | Expression value ->
      expression state scope value;
      scope
  | Assignment { target; value; _ } ->
      expression state scope target;
      expression state scope value;
      scope
  | For { pattern = pattern_; annotation; iterable; clauses; body; _ } ->
      Option.iter (type_expression state scope) annotation;
      expression state scope iterable;
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
      List.iter (loop_clause ~for_loop:true ~elements state clause_scope) clauses;
      block state inner body;
      scope
  | While { condition = test; clauses; body } ->
      let inner = condition state scope test in
      List.iter (loop_clause state scope) clauses;
      block state inner body;
      scope
  | Parallel body | Concurrent body ->
      let word = match statement_.kind with Concurrent _ -> "concurrent" | _ -> "parallel" in
      List.fold_left
        (fun (after : scope) (branch : statement) ->
          let branch_scope = statement state scope branch in
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
      block state { scope with specification = in_specification } body;
      scope
  | Assert { value; _ } ->
      expression state scope value;
      scope
  | Statement_error -> scope

and loop_clause ?(for_loop = false) ?(elements = []) state scope (written : loop_clause) =
  let scope =
    if for_loop then
      { scope with specification = { scope.specification with names_visited = true; elements } }
    else scope
  in
  let specification =
    { scope with specification = { in_specification with names_visited = for_loop; elements } }
  in
  match written.kind with
  | Invariant value -> expression state specification value
  | Loop_decreases measures -> List.iter (expression state specification) measures
  | Loop_cost cost -> clause state scope { kind = Cost cost; id = written.id }

let declare_type state scope (name : name) target =
  let shadows existing =
    report state Shadowed_name (read_span state name.id)
      (Printf.sprintf "`%s` is already %s, and a name cannot shadow another. Choose another name."
         name.text existing)
  in
  (if String_map.mem name.text scope.types then shadows "a generic parameter here"
   else
     match module_item state name.text with
     | Some item when Names.is_type_kind item.kind ->
         shadows (Names.kind_name (Names.kind_of_named item.kind) ^ " of this module")
     | _ -> if List.mem name.text Prelude.names then shadows "a name in the prelude");
  set state name Binding;
  { scope with types = String_map.add name.text target scope.types }

let generics state scope ~(owner : Path.t) (generics : generic_parameter list) =
  let parameter (name : name) : Types.parameter = { owner; name = name.text } in
  let scope =
    List.fold_left
      (fun scope (generic : generic_parameter) ->
        match generic.kind with
        | Type_parameter (name, _) ->
            declare_type state scope name (Type_parameter (parameter name))
        | Capability_parameter name ->
            declare_type state scope name (Capability_parameter (parameter name))
        | Value_parameter (name, _) ->
            let scope = declare_value state scope name in
            {
              scope with
              values =
                String_map.add name.text
                  (Value_generic (parameter name), "a generic parameter")
                  scope.values;
            }
        | Generic_error -> scope)
      scope generics
  in
  List.iter
    (fun (generic : generic_parameter) ->
      match generic.kind with
      | Type_parameter (_, bounds) -> List.iter (path_type state scope) bounds
      | Value_parameter (_, type_) -> type_expression state scope type_
      | Capability_parameter _ | Generic_error -> ())
    generics;
  scope

let parameters state scope (parameters_ : parameter list) =
  List.fold_left
    (fun scope (parameter : parameter) ->
      match parameter.kind with
      | Named_parameter { name; type_; default; _ } ->
          type_expression state scope type_;
          Option.iter
            (fun default -> in_section state Contract (fun () -> expression state scope default))
            default;
          declare_parameter state scope name
      | Self_parameter _ | Parameter_error -> scope)
    scope parameters_

let result state scope = function
  | Some (Returns type_ | Lends (_, type_)) -> type_expression state scope type_
  | None -> ()

let empty_scope =
  {
    values = String_map.empty;
    types = String_map.empty;
    specification = no_specification;
    is_lending_method = false;
  }

let head state scope ~owner = function
  | Plain_name _ -> scope
  | Member_name (head_, _) ->
      type_name state scope head_.path;
      generics state scope ~owner head_.generics

let clauses state scope (clauses_ : clause list) =
  List.iter
    (fun (clause_ : clause) ->
      match clause_.kind with
      | Requires _ | Ensures _ | Decreases _ ->
          in_section state Contract (fun () -> clause state scope clause_)
      | Uses _ | Cost _ | Clause_error -> clause state scope clause_)
    clauses_

let signature state scope ~owner ~(broken : bool) (signature_ : signature) =
  if broken then None
  else begin
    let scope = generics state scope ~owner signature_.generics in
    let scope = parameters state scope signature_.parameters in
    result state scope signature_.result;
    let scope =
      match signature_.result with
      | Some (Lends _) -> { scope with is_lending_method = true }
      | _ -> scope
    in
    clauses state scope signature_.clauses;
    Some scope
  end

let fields state scope (fields_ : field list) =
  List.iter
    (fun (field : field) ->
      match field.kind with
      | Field_declaration { type_; default; _ } ->
          type_expression state scope type_;
          Option.iter
            (fun default -> in_section state Contract (fun () -> expression state scope default))
            default
      | Field_error -> ())
    fields_

let field_names (fields_ : field list) =
  List.filter_map
    (fun (field : field) ->
      match field.kind with Field_declaration { name; _ } -> Some name.text | Field_error -> None)
    fields_

let inherited scope ~(owner : Path.t) (generics : generic_parameter list) =
  List.fold_left
    (fun scope (generic : generic_parameter) ->
      let parameter (name : name) : Types.parameter = { owner; name = name.text } in
      let type_ (name : name) (target : target) =
        { scope with types = String_map.add name.text target scope.types }
      in
      match generic.kind with
      | Type_parameter (name, _) -> type_ name (Type_parameter (parameter name))
      | Capability_parameter name -> type_ name (Capability_parameter (parameter name))
      | Value_parameter (name, _) ->
          {
            scope with
            values =
              String_map.add name.text
                (Value_generic (parameter name), "a generic parameter")
                scope.values;
          }
      | Generic_error -> scope)
    scope generics

let definition state ~(path : Path.t) ?(container : (Path.t * definition) option)
    (definition_ : definition) =
  let broken part = Names.is_broken state.lookups state.key part in
  let header_broken = broken Header and body_broken = broken Body in
  let scope =
    match container with
    | Some (owner, { kind = Trait { generics = generics_; _ }; _ }) ->
        inherited empty_scope ~owner generics_
    | Some (owner, { kind = Impl { type_; _ }; _ }) -> inherited empty_scope ~owner type_.generics
    | _ -> empty_scope
  in
  match definition_.kind with
  | Function { signature = signature_; body } ->
      if not header_broken then begin
        let scope = head state scope ~owner:path signature_.name in
        match signature state scope ~owner:path ~broken:false signature_ with
        | Some scope ->
            if not body_broken then in_section state Body (fun () -> block state scope body)
        | None -> ()
      end
  | Method_declaration signature_ ->
      if not header_broken then ignore (signature state scope ~owner:path ~broken:false signature_)
  | Type_definition { generics = generics_; body; clauses; _ } ->
      if not header_broken then begin
        let scope = generics state scope ~owner:path generics_ in
        let record_fields = match body with Fields fields_ -> field_names fields_ | _ -> [] in
        (match body with
        | Fields fields_ -> fields state scope fields_
        | Variants variants ->
            List.iter
              (fun (variant : variant) -> Option.iter (fields state scope) variant.fields)
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
          (fun (clause : type_clause) ->
            match clause.kind with
            | Type_invariant value | Potential value ->
                in_section state Contract (fun () -> expression state clause_scope value)
            | Derives traits -> List.iter (path_type state scope) traits)
          clauses
      end
  | Trait { generics = generics_; requires; members; _ } ->
      if not header_broken then begin
        let scope = generics state scope ~owner:path generics_ in
        List.iter (path_type state scope) requires;
        List.iteri
          (fun index (line : trait_member node) ->
            if not (broken (Member_header index)) then
              match line.kind with
              | Associated_type (_, bounds) -> List.iter (path_type state scope) bounds
              | Law { parameters = parameters_; requires; body; _ } ->
                  let inner =
                    parameters state { scope with specification = in_specification } parameters_
                  in
                  in_section state Contract (fun () ->
                      List.iter (expression state inner) requires;
                      if not (broken (Member_body index)) then block state inner body)
              | Associated_capability _ | Trait_member_error -> ())
          members
      end
  | Impl { trait_; type_; uses; members } ->
      if not header_broken then begin
        type_name state scope type_.path;
        let scope = generics state scope ~owner:path type_.generics in
        path_type state scope trait_;
        List.iter (capability_reference state scope) uses;
        List.iteri
          (fun index (line : impl_member node) ->
            if not (broken (Member_header index)) then
              match line.kind with
              | Associated_definition (_, type_) -> type_expression state scope type_
              | Capability_definition (_, capabilities) ->
                  List.iter (capability_reference state scope) capabilities
              | Impl_member_error -> ())
          members
      end
  | Capability _ -> ()
  | Constant { name; type_; value } ->
      if not header_broken then begin
        let scope = head state scope ~owner:path name in
        type_expression state scope type_;
        if not body_broken then in_section state Body (fun () -> expression state scope value)
      end
  | Test { uses; body; _ } ->
      if not header_broken then begin
        List.iter (capability_reference state scope) uses;
        if not body_broken then in_section state Body (fun () -> block state scope body)
      end
  | Theorem { generics = generics_; parameters = parameters_; clauses = clauses_; body; _ } ->
      if not header_broken then begin
        let scope =
          generics state { scope with specification = in_specification } ~owner:path generics_
        in
        let scope = parameters state scope parameters_ in
        clauses state scope clauses_;
        if not body_broken then in_section state Body (fun () -> block state scope body)
      end
  | Law_proof { trait_; law; type_; body } ->
      if not header_broken then begin
        type_name state scope type_.path;
        let scope = generics state scope ~owner:path type_.generics in
        path_type state scope trait_;
        let law_parameters =
          match (current state).names.(trait_.path.last.id) with
          | Some (Definition (Trait, trait)) ->
              Option.value ~default:[] (Names.law_parameters state.lookups trait law.text)
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
          in_section state Body (fun () ->
              block state { scope with values; specification = in_specification } body)
      end
  | Definition_error _ -> ()
