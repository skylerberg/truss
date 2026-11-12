(* Resolving the names of one definition. The walk maintains a scope with
   the referent of each name at each point. It records, in tables keyed by
   node id, the referent of each name and the interpretation of each
   [name[...]]. It never changes the tree. Broken parts are not walked,
   because their trees differ from the source. *)

open Syntax
module String_map = Map.Make (String)

type specification_function = Log | Power | Time | Calls

type target =
  | Binding  (** This name binds a local, a parameter, or a generic parameter. *)
  | Local of id  (** A local or parameter, by the id of the name that binds it. *)
  | Law_parameter of int
      (** In a law's proof, a parameter of the law, by its position among the law's parameters. *)
  | Type_parameter of Types.parameter
      (** A generic type parameter, by the definition that declares it and its name. *)
  | Capability_parameter of Types.parameter  (** A generic parameter declared [capability Name]. *)
  | Value_parameter of Types.parameter  (** A [USize] generic parameter. *)
  | Definition of Names.named * Path.t  (** A definition, with its kind. *)
  | Variant of Path.t * string  (** A prelude variant written bare, such as [Some]. *)
  | Module of Path.module_
  | Field of string  (** A record's field, by name, in the record's invariant or potential. *)
  | Result_value  (** [result], in [ensures] and [cost]. *)
  | Old  (** [old], in specifications and proofs. *)
  | Identical  (** [identical], in specifications and proofs: identity, for every type. *)
  | Yielded
      (** [yielded]: the sequence of the parts that a lending or yielding method has yielded so far.
      *)
  | Finished  (** [finished], whether a yielding method ran to its end. *)
  | Specification_function of specification_function
      (** [log], [power], [time], or [calls] in a [cost] bound, or [log] or [power] in another
          specification. *)
  | Unknown of Diagnostic.reported  (** A name that refers to nothing, with its report. *)

type bracket = Index | Type_arguments | Method_bracket

(* The kind of a local value name in scope. *)
type value =
  | Value_local of id
  | Value_generic of Types.parameter
  | Value_field of string
  | Value_law_parameter of int

type specification = {
  active : bool;  (** In a specification or a proof, where [old] has its meaning. *)
  names_result : bool;  (** In [ensures] or [cost], where [result] does. *)
  cost_bound : bool;  (** In a [cost] bound, where [time] and [calls] have their meaning. *)
  names_yielded : bool;
      (** In the [ensures] of a lending or yielding method, or in the clauses of a [for] loop, where
          [yielded] is the sequence of the parts yielded so far. *)
  names_finished : bool;
      (** In a lending or yielding method's [ensures], where [finished] has its meaning. *)
  elements : string list;
      (** In the clauses of a [for] loop over a collection or a cursor, the names its pattern binds,
          which hold no value there. *)
}

type scope = {
  values : (value * string) String_map.t;
      (** With the kind of its binding, as diagnostics name it. *)
  types : target String_map.t;  (** Generic type and capability parameters, as names mean them. *)
  specification : specification;
  lends_or_yields : bool;
      (** In a method that lends or yields, whose [ensures] can name the yielded parts. *)
}

let no_specification =
  {
    active = false;
    names_result = false;
    cost_bound = false;
    names_yielded = false;
    names_finished = false;
    elements = [];
  }

let in_specification = { no_specification with active = true }

type state = {
  database : Query.context;
  module_ : Path.module_;
  names : target option array;
  brackets : bracket option array;
  mutable diagnostics : Syntax.diagnostic list;
  mutable holes : (id * (string * value) list) list;
      (** Each [todo], by its id, with the values in scope there, by name, latest first *)
}

let reported state ?fixes code (span : span) message =
  let diagnostic = Diagnostic.make ?fixes ~code:(Resolve code) span message in
  state.diagnostics <- diagnostic :: state.diagnostics;
  Diagnostic.reported diagnostic

let report state ?fixes code span message = ignore (reported state ?fixes code span message)
let set state (name : name) target = state.names.(name.id) <- Some target

let unknown state (name : name) ~expected candidates =
  let fixes =
    match Diagnostic.closest name.text candidates with
    | Some candidate ->
        [
          Diagnostic.fix
            (Printf.sprintf "Write `%s`." candidate)
            [ Diagnostic.replace name.span candidate ];
        ]
    | None -> []
  in
  set state name
    (Unknown
       (reported state ~fixes Unknown_name name.span
          (Printf.sprintf "Nothing named `%s` is %s." name.text expected)))

let file_item state text = Query.demand state.database Names.find (state.module_, text)

let module_of_names state (first : name) (rest : name list) =
  let failed report =
    set state first (Unknown report);
    Error report
  in
  begin match
    Names.lookup_module state.database ~from:state.module_
      (List.map (fun (name : Syntax.name) -> name.text) (first :: rest))
  with
  (* For a name through an import, the [use] line has the error, and the
     names after it resolve as usual. *)
  | Found_module (module_, `Package)
    when module_ = Intrinsic.module_ && state.module_.package <> Path.standard_package ->
      failed
        (reported state Intrinsic_import first.span
           "Only the `standard` package can use `standard::intrinsic`.")
  | Found_module (module_, _) ->
      set state first (Module module_);
      Ok module_
  | Ambiguous_module (imported, package) ->
      failed
        (reported state Ambiguous_module first.span
           (Printf.sprintf
              "`%s` could be the imported module `%s` or the module `%s`. Write the imported one's \
               full path, or remove its `use`."
              first.text (Path.show_module imported) (Path.show_module package)))
  | No_module text ->
      failed
        (reported state Unknown_module first.span
           (Printf.sprintf "No module `%s` is imported or exists." text))
  end

(* A name written after a module, [json::parse], which must be visible from
   here. *)
let in_module state module_ (name : name) ~types =
  match Query.demand state.database Names.find (module_, name.text) with
  | Some item when if types then Names.is_type_kind item.kind else Names.is_value_kind item.kind ->
      if Names.visible ~from:state.module_ module_ item.visibility then begin
        let path : Path.t = Top { module_; name = name.text } in
        set state name (Definition (item.kind, path));
        Some (path, item)
      end
      else begin
        set state name
          (Unknown
             (reported state Not_visible name.span
                (Printf.sprintf "`%s::%s` is %s." (Path.show_module module_) name.text
                   (match item.visibility with
                   | Private -> "private to its file, so it cannot be used here"
                   | _ -> "internal to its package, so it cannot be used here"))));
        None
      end
  | _ ->
      let candidates =
        List.filter_map
          (fun (item : Names.entry) ->
            if
              (if types then Names.is_type_kind item.kind else Names.is_value_kind item.kind)
              && Names.visible ~from:state.module_ module_ item.visibility
            then Some item.name
            else None)
          (Query.demand state.database Names.entries module_)
      in
      unknown state name ~expected:("in `" ^ Path.show_module module_ ^ "`") candidates;
      None

let prelude_type state text =
  match Prelude.find_type text with
  | Some module_ -> (
      match Query.demand state.database Names.find (module_, text) with
      | Some item when Names.is_type_kind item.kind -> Some (Path.Top { module_; name = text }, item)
      | _ -> None)
  | None -> None

let type_candidates state scope =
  List.map fst (String_map.bindings scope.types)
  @ List.filter_map
      (fun (item : Names.entry) -> if Names.is_type_kind item.kind then Some item.name else None)
      (Query.demand state.database Names.entries state.module_)
  @ List.map fst Prelude.types

(* An UpperCamelCase name in the types namespace. With [variants], a prelude
   variant also counts, as in expressions. *)
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
          match file_item state text with
          | Some item when Names.is_type_kind item.kind ->
              set state path.last
                (Definition (item.kind, Top { module_ = state.module_; name = text }))
          | _ -> (
              match prelude_type state text with
              | Some (path_, item) -> set state path.last (Definition (item.kind, path_))
              | None -> (
                  match if variants then Prelude.find_variant text else None with
                  | Some (type_, variant) -> set state path.last (Variant (type_, variant))
                  | None ->
                      unknown state path.last ~expected:"a type here"
                        (type_candidates state scope
                        @ if variants then List.map fst Prelude.variants else [])))))

let target_of state (name : name) = state.names.(name.id)

let rec type_expression state scope (type_ : type_expression) =
  match type_.kind with
  | Path_type path -> path_type state scope path
  | Any_type path -> path_type state scope path
  | Self_type _ -> ()
  | Associated (base, member) -> associated_base state scope base member "type"
  | Function_type { inputs; input_names; output; clauses } ->
      List.iter (fun (_, input) -> type_expression state scope input) inputs;
      Option.iter (type_expression state scope) output;
      (* The names of the inputs are in scope in the type's own [requires],
         after the parameters before it in a signature. *)
      let named = List.fold_left (declare_parameter state) scope input_names in
      List.iter (clause state named) clauses
  | Type_error -> ()

(* The generic parameter before the [.] of [Items.Element] or [Source.Uses]. *)
and associated_base state scope (base : name) (member : name) kind =
  match String_map.find_opt base.text scope.types with
  | Some parameter -> set state base parameter
  | None ->
      set state base
        (Unknown
           (reported state Not_a_generic_parameter base.span
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

(* A lowercase type argument: a value generic parameter, or a constant. *)
and count_name state scope (name : name) =
  match String_map.find_opt name.text scope.values with
  | Some (Value_generic parameter, _) -> set state name (Value_parameter parameter)
  | _ -> (
      match file_item state name.text with
      | Some item when item.kind = Constant ->
          set state name (Definition (Constant, Top { module_ = state.module_; name = name.text }))
      | _ ->
          set state name
            (Unknown
               (reported state Not_a_constant name.span
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
            {
              in_specification with
              names_result = true;
              names_yielded = scope.lends_or_yields;
              names_finished = scope.lends_or_yields;
            };
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

(* A lowercase name used as a value. *)
and local_value state scope (name : name) =
  let text = name.text in
  match String_map.find_opt text scope.values with
  | Some (Value_local id, _) -> set state name (Local id)
  | Some (Value_generic parameter, _) -> set state name (Value_parameter parameter)
  | Some (Value_field field, _) -> set state name (Field field)
  | Some (Value_law_parameter index, _) -> set state name (Law_parameter index)
  | None ->
      if scope.specification.active && text = "old" then set state name Old
      else if scope.specification.names_yielded && text = "yielded" then set state name Yielded
      else if scope.specification.names_finished && text = "finished" then set state name Finished
      else if scope.specification.active && text = "identical" then set state name Identical
      else if scope.specification.names_result && text = "result" then set state name Result_value
      else if List.mem text scope.specification.elements then
        set state name
          (Unknown
             (reported state Unknown_name name.span
                (Printf.sprintf
                   "`%s` is the loop's element, which is bound only in the loop's body: the loop's \
                    clauses hold before the first element and after the last. Name the elements so \
                    far with `yielded`."
                   text)))
      else
        begin match file_item state text with
        | Some item when Names.is_value_kind item.kind ->
            set state name (Definition (item.kind, Top { module_ = state.module_; name = text }))
        | _ ->
            if text = "null" || text = "nil" then begin
              set state name
                (Unknown
                   (reported state Null name.span
                      ~fixes:
                        [ Diagnostic.fix "Write `None`." [ Diagnostic.replace name.span "None" ] ]
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
                    (Query.demand state.database Names.entries state.module_))
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

(* The referent of a name expression, if the expression is a name. *)
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
              match Query.demand state.database Names.find (module_, name) with
              | Some item -> item.generic
              | None -> false
            in
            if not generic then
              report state Not_generic value.span
                (Printf.sprintf
                   "`%s` is a function without generic parameters, so `[...]` cannot give it type \
                    arguments, and a function cannot be indexed."
                   name);
            Type_arguments
        | _ -> Index)
  in
  state.brackets.(value.id) <- Some decision;
  List.iter
    (function
      | Item item -> expression state scope item
      | Item_constraint (_, type_) -> type_expression state scope type_)
    items

(* Whether a marked expression starts with a place: a local, a parameter,
   [self], or a constant, then fields and indexes, up to the first method
   call. After that call, the expression works on its result, so a [?] can
   follow it, as in [mut file.read_line()?]. *)
and check_place state (marked : expression) (inner : expression) =
  (* [`Place called]: [called] is whether the place is the receiver of a
     method call. *)
  let rec head (value : expression) =
    match value.kind with
    | Member (base, _) -> head base
    | Parenthesized inner -> head inner
    (* An index, or type arguments after a method's name, which reads the
       same place. *)
    | Bracket (base, _) -> (
        match state.brackets.(value.id) with
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
      let keyword_end = inner.span.start in
      report state Not_a_place marked.span
        ~fixes:
          [
            Diagnostic.fix "Remove the mark."
              [ Diagnostic.delete (Span.make marked.span.start keyword_end) ];
          ]
        "Only a place, such as a variable, a field, or an element, can be marked `mut` or `own`. A \
         temporary value is always handed over as owned."

and expression state scope (value : expression) =
  match value.kind with
  | Todo ->
      state.holes <-
        ( value.id,
          List.map (fun (name, (value, _)) -> (name, value)) (String_map.bindings scope.values) )
        :: state.holes
  | Integer _ | Float _ | True | False | Unreachable | Break | Continue | Self_value
  | Self_type_value | Expression_error ->
      ()
  | String literal -> string_literal state scope literal
  | Name path -> name_expression state scope path
  | Member (base, _) -> expression state scope base
  | Bracket (base, items) -> bracket state scope value base items
  (* In a [cost] bound, the four names are the specification functions.
     [log] and [power] are also that in any other specification, on
     [Integer], unless a local or a definition of the file has the name. *)
  | Call ({ kind = Name { modules = []; last }; _ }, arguments)
    when (scope.specification.cost_bound && List.mem last.text [ "log"; "power"; "time"; "calls" ])
         || scope.specification.active
            && List.mem last.text [ "log"; "power" ]
            && (not (String_map.mem last.text scope.values))
            &&
            match file_item state last.text with
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

(* A condition. A name that an [is] at the top level of its [&&] chain binds
   is in scope in the rest of the chain, and in the returned scope, which is
   for the block that the condition guards. *)
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

(* Declares a value name, reporting it if it hides another. *)
and declare_value state scope (name : name) =
  let hides existing =
    report state Hides_name name.span
      (Printf.sprintf "`%s` is already %s, and a name cannot hide another. Choose another name."
         name.text existing)
  in
  (match String_map.find_opt name.text scope.values with
  | Some (_, existing) -> hides existing
  | None -> (
      match file_item state name.text with
      | Some item when Names.is_value_kind item.kind ->
          hides (Names.kind_name (Names.kind_of_named item.kind) ^ " in this file")
      | _ -> ()));
  set state name Binding;
  {
    scope with
    values = String_map.add name.text (Value_local name.id, "a local here") scope.values;
  }

and declare_parameter state scope (name : name) =
  let scope = declare_value state scope name in
  { scope with values = String_map.add name.text (Value_local name.id, "a parameter") scope.values }

(* The names a pattern binds, in the order written, with alternatives
   checked to bind the same names. *)
and bind_pattern state scope (pattern_ : pattern) =
  let bound = ref [] in
  pattern state scope bound pattern_;
  List.fold_left (fun scope (name : name) -> declare_value state scope name) scope (List.rev !bound)

and pattern state scope bound (pattern_ : pattern) =
  match pattern_.kind with
  | Wildcard | Pattern_error -> ()
  | Binding_or_constant name -> (
      match String_map.find_opt name.text scope.values with
      | Some (Value_generic parameter, _) -> set state name (Value_parameter parameter)
      | _ -> (
          match file_item state name.text with
          | Some item when item.kind = Constant ->
              set state name
                (Definition (Constant, Top { module_ = state.module_; name = name.text }))
          | _ -> bound := name :: !bound))
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
                report state Alternative_bindings alternative.span
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
      (* The parser builds a qualified constant only with a module before it. *)
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
  | End_name name -> (
      match (String_map.find_opt name.text scope.values, file_item state name.text) with
      | Some (Value_generic parameter, _), _ -> set state name (Value_parameter parameter)
      | _, Some item when item.kind = Constant ->
          set state name (Definition (Constant, Top { module_ = state.module_; name = name.text }))
      | _ ->
          set state name
            (Unknown
               (reported state Not_a_constant name.span
                  (Printf.sprintf
                     "The end of a range pattern must be a literal or a constant, and `%s` is not \
                      a constant."
                     name.text))))

and block state scope (block_ : block) =
  ignore
    (List.fold_left
       (fun scope statement_ -> statement state scope statement_)
       scope block_.statements)

(* A statement, returning the scope for the statements after it. *)
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
  | For { pattern = pattern_; iterable; clauses; body; _ } ->
      expression state scope iterable;
      let inner = bind_pattern state scope pattern_ in
      (* A range's index names the next index in the loop's clauses. Any
         other loop's element is bound only in its body. *)
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
      (* Each branch has only the scope before the block. The names that the
         branches bind are in scope after the block. *)
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
                report state Hides_name branch.span
                  (Printf.sprintf
                     "Another branch of this `%s` block already binds `%s`, and a name cannot hide \
                      another. Choose another name."
                     word key))
            bound;
          { after with values = String_map.union (fun _ left _ -> Some left) after.values bound })
        scope body.statements
  | Proof body ->
      block state { scope with specification = in_specification } body;
      scope
  | Assert value | Yield value ->
      expression state scope value;
      scope
  | Statement_error -> scope

and loop_clause ?(for_loop = false) ?(elements = []) state scope (written : loop_clause) =
  let scope =
    if for_loop then
      { scope with specification = { scope.specification with names_yielded = true; elements } }
    else scope
  in
  (* [yielded] refers to the parts of the nearest loop or method: the parts
     of a [for] loop, or else, in a lending or yielding method, the parts of
     the method. *)
  let specification =
    {
      scope with
      specification =
        { in_specification with names_yielded = for_loop || scope.lends_or_yields; elements };
    }
  in
  match written.kind with
  | Invariant value -> expression state specification value
  | Loop_decreases measures -> List.iter (expression state specification) measures
  | Loop_cost cost -> clause state scope { kind = Cost cost; span = written.span; id = written.id }

let declare_type state scope (name : name) target =
  let hides existing =
    report state Hides_name name.span
      (Printf.sprintf "`%s` is already %s, and a name cannot hide another. Choose another name."
         name.text existing)
  in
  (if String_map.mem name.text scope.types then hides "a generic parameter here"
   else
     match file_item state name.text with
     | Some item when Names.is_type_kind item.kind ->
         hides (Names.kind_name (Names.kind_of_named item.kind) ^ " in this file")
     | _ -> if List.mem name.text Prelude.names then hides "a name in the prelude");
  set state name Binding;
  { scope with types = String_map.add name.text target scope.types }

(* A definition's generic parameters, each named by the definition that
   declares it, [owner], and its own name: an [impl]'s by the [impl], and a
   method's own by the method. *)
let generics state scope ~(owner : Path.t) (generics : generic_parameter list) =
  let parameter (name : name) : Types.parameter = { owner; name = name.text } in
  (* All of a list's parameters are in scope in each one's bounds. *)
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
          Option.iter (expression state scope) default;
          declare_parameter state scope name
      | Self_parameter _ | Parameter_error -> scope)
    scope parameters_

let result state scope = function
  | Some (Returns type_ | Yields (_, type_) | Lends (_, type_)) -> type_expression state scope type_
  | None -> ()

let empty_scope =
  {
    values = String_map.empty;
    types = String_map.empty;
    specification = no_specification;
    lends_or_yields = false;
  }

(* The scope of a definition's head: the generic parameters of the type
   head, for a method or a member constant. *)
let head state scope ~owner = function
  | Plain_name _ -> scope
  | Member_name (head_, _) ->
      type_name state scope head_.path;
      generics state scope ~owner head_.generics

let signature state scope ~owner ~(broken : bool) (signature_ : signature) =
  if broken then None
  else begin
    let scope = generics state scope ~owner signature_.generics in
    let scope = parameters state scope signature_.parameters in
    result state scope signature_.result;
    let scope =
      match signature_.result with
      | Some (Yields _ | Lends _) -> { scope with lends_or_yields = true }
      | _ -> scope
    in
    List.iter (clause state scope) signature_.clauses;
    Some scope
  end

let fields state scope (fields_ : field list) =
  List.iter
    (fun (field : field) ->
      match field.kind with
      | Field_declaration { type_; default; _ } ->
          type_expression state scope type_;
          Option.iter (expression state scope) default
      | Field_error -> ())
    fields_

let field_names (fields_ : field list) =
  List.filter_map
    (fun (field : field) ->
      match field.kind with Field_declaration { name; _ } -> Some name.text | Field_error -> None)
    fields_

(* The generic parameters of the trait or the [impl] a method is written
   inside, which the method's own tree does not hold: they are in scope as
   that one's, and it is where they are bound and their bounds resolved. *)
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

(* [container] is the trait, the [impl], or the capability a method is
   written inside, with its path. *)
let definition state ~(path : Path.t) ?(container : (Path.t * definition) option)
    (definition_ : definition) =
  let broken part = Parts.broken definition_ part in
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
        | Some scope -> if not body_broken then block state scope body
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
            | Type_invariant value | Potential value -> expression state clause_scope value
            | Derives traits -> List.iter (path_type state scope) traits)
          clauses
      end
  | Trait { generics = generics_; requires; members; _ } ->
      if not header_broken then begin
        let scope = generics state scope ~owner:path generics_ in
        List.iter (path_type state scope) requires;
        List.iteri
          (fun index (line : trait_member line) ->
            if not (broken (Member_header index)) then
              match line.kind with
              | Associated_type (_, bounds) -> List.iter (path_type state scope) bounds
              | Law { parameters = parameters_; requires; body; _ } ->
                  let inner =
                    parameters state { scope with specification = in_specification } parameters_
                  in
                  List.iter (expression state inner) requires;
                  if not (broken (Member_body index)) then block state inner body
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
          (fun index (line : impl_member line) ->
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
        if not body_broken then expression state scope value
      end
  | Test { uses; body; _ } ->
      if not header_broken then begin
        List.iter (capability_reference state scope) uses;
        if not body_broken then block state scope body
      end
  | Theorem { generics = generics_; parameters = parameters_; clauses; body; _ } ->
      if not header_broken then begin
        let scope =
          generics state { scope with specification = in_specification } ~owner:path generics_
        in
        let scope = parameters state scope parameters_ in
        List.iter (clause state scope) clauses;
        if not body_broken then block state scope body
      end
  | Law_proof { trait_; law; type_; body } ->
      if not header_broken then begin
        type_name state scope type_.path;
        let scope = generics state scope ~owner:path type_.generics in
        path_type state scope trait_;
        (* The body is checked as the law's body is: with the law's
           parameters in scope. *)
        let law_parameters =
          match state.names.(trait_.path.last.id) with
          | Some (Definition (Trait, trait)) ->
              Option.value ~default:[]
                (Query.demand state.database Names.law_parameters (trait, law.text))
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
          block state { scope with values; specification = in_specification } body
      end
  | Definition_error _ -> ()
