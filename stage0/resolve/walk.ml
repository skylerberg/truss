(* Resolving the names of one definition.

   The walk keeps a scope of what each name means at each point, and records
   in tables keyed by node id what each name refers to and how each
   [name[...]] reads. It never changes the tree. Parts the parser did not
   build as written are not walked, since their trees are not what the
   source says. *)

open Syntax
module String_map = Map.Make (String)

type cost_function = Log | Power | Time | Calls

type target =
  | Binding  (** This name binds a local, a parameter, or a generic parameter. *)
  | Local of id  (** A local or parameter, by the id of the name that binds it. *)
  | Type_parameter of id  (** A generic type parameter, by the id of the name that binds it. *)
  | Capability_parameter of id  (** A generic parameter declared [capability Name]. *)
  | Value_parameter of id  (** A [USize] generic parameter. *)
  | Definition of Names.named * Path.t  (** A definition, and what kind of definition it is. *)
  | Variant of Path.t * string  (** A prelude variant written bare, such as [Some]. *)
  | Module of Path.module_
  | Field of string  (** A record's field, by name, in the record's invariant or potential. *)
  | Result_value  (** [result], in [ensures] and [cost]. *)
  | Old  (** [old], in specifications and proofs. *)
  | Identical  (** [identical], in specifications and proofs: identity, for every type. *)
  | Yielded  (** [yielded], what a lending or yielding method handed out so far. *)
  | Finished  (** [finished], whether a yielding method ran to its end. *)
  | Cost_function of cost_function  (** [log], [power], [time], or [calls], in a [cost] bound. *)
  | Unknown of Diagnostic.reported  (** A name that refers to nothing, with its report. *)

type bracket = Index | Type_arguments | Method_bracket

(* What a local value name in scope is. *)
type value = Value_local of id | Value_generic of id | Value_field of string

type specification = {
  active : bool;  (** In a specification or a proof, where [old] has its meaning. *)
  result : bool;  (** In [ensures] or [cost], where [result] does. *)
  cost_bound : bool;  (** In a [cost] bound, where the cost functions do. *)
  yielded : bool;
      (** In a lending or yielding method's [ensures], or a [for] loop's clauses, where [yielded]
          names what was handed out so far. *)
  finished : bool;
      (** In a lending or yielding method's [ensures], where [finished] has its meaning. *)
}

type scope = {
  values : (value * string) String_map.t;  (** With what binds it, as messages name it. *)
  types : target String_map.t;  (** Generic type and capability parameters, as names mean them. *)
  specification : specification;
  hands_out : bool;  (** In a method that lends or yields, whose [ensures] name what it hands out. *)
}

let no_specification =
  { active = false; result = false; cost_bound = false; yielded = false; finished = false }

let in_specification = { no_specification with active = true }

type state = {
  database : Query.context;
  module_ : Path.module_;
  names : target option array;
  brackets : bracket option array;
  mutable diagnostics : Diagnostic.t list;
  mutable holes : (id * (string * value) list) list;
      (** Each [todo], by its id, with the values in scope there, by name, latest first *)
}

let reported state ?fixes code (span : span) message =
  let diagnostic =
    Diagnostic.make ?fixes ~code:(Resolve code) (Source.span span.start span.stop) message
  in
  state.diagnostics <- diagnostic :: state.diagnostics;
  Diagnostic.reported diagnostic

let report state ?fixes code span message = ignore (reported state ?fixes code span message)
let set state (name : name) target = state.names.(name.id) <- Some target

(* Closest names *)

(* The optimal string alignment distance: insertions, deletions,
   substitutions, and swaps of two neighboring letters, the usual typos,
   each count one. *)
let distance left right =
  let rows = String.length left + 1 and columns = String.length right + 1 in
  let table = Array.make_matrix rows columns 0 in
  for i = 0 to rows - 1 do
    table.(i).(0) <- i
  done;
  for j = 0 to columns - 1 do
    table.(0).(j) <- j
  done;
  for i = 1 to rows - 1 do
    for j = 1 to columns - 1 do
      let cost = if left.[i - 1] = right.[j - 1] then 0 else 1 in
      let best =
        min (min (table.(i - 1).(j) + 1) (table.(i).(j - 1) + 1)) (table.(i - 1).(j - 1) + cost)
      in
      table.(i).(j) <-
        (if i > 1 && j > 1 && left.[i - 1] = right.[j - 2] && left.[i - 2] = right.[j - 1] then
           min best (table.(i - 2).(j - 2) + 1)
         else best)
    done
  done;
  table.(rows - 1).(columns - 1)

(* The visible name closest to [text], if one is near enough to be a typo:
   at most a third of the name's letters away, and at least one. *)
let closest text candidates =
  let limit = max 1 (String.length text / 3) in
  let best =
    List.fold_left
      (fun best candidate ->
        let distance = distance text candidate in
        if candidate = text || distance > limit then best
        else
          match best with
          | Some (_, best_distance) when best_distance <= distance -> best
          | _ -> Some (candidate, distance))
      None
      (List.sort_uniq compare candidates)
  in
  Option.map fst best

let unknown state (name : name) ~what candidates =
  let fixes =
    match closest name.text candidates with
    | Some candidate ->
        [
          Diagnostic.fix
            (Printf.sprintf "Write `%s`." candidate)
            [ Diagnostic.replace (Source.span name.span.start name.span.stop) candidate ];
        ]
    | None -> []
  in
  set state name
    (Unknown
       (reported state ~fixes Unknown_name name.span
          (Printf.sprintf "Nothing named `%s` is %s." name.text what)))

(* The file's own definitions *)

let file_item state text = Query.demand state.database Names.find (state.module_, text)

(* Modules *)

let module_of_names state (first : name) (rest : name list) =
  let failed report =
    set state first (Unknown report);
    Error report
  in
  begin match
    Names.lookup_module state.database ~from:state.module_
      (List.map (fun (name : Syntax.name) -> name.text) (first :: rest))
  with
  (* Through an import, the [use] line has the error, and the names
         after it mean what they say. *)
  | Found_module (module_, `Package)
    when module_ = Intrinsic.module_ && state.module_.package <> Prelude.standard ->
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
      unknown state name ~what:("in `" ^ Path.show_module module_ ^ "`") candidates;
      None

(* Types *)

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
                      unknown state path.last ~what:"a type here"
                        (type_candidates state scope
                        @ if variants then List.map fst Prelude.variants else [])))))

let target_of state (name : name) = state.names.(name.id)

let rec type_expression state scope (type_ : type_expression) =
  match type_.kind with
  | Path_type path -> path_type state scope path
  | Any_type path -> path_type state scope path
  | Self_type _ -> ()
  | Associated (base, _) -> (
      match String_map.find_opt base.text scope.types with
      | Some parameter -> set state base parameter
      | None ->
          set state base
            (Unknown
               (reported state Not_a_generic_parameter base.span
                  (Printf.sprintf
                     "`%s.%s` names an associated type, so `%s` must be a generic parameter here."
                     base.text
                     (match type_.kind with Associated (_, name) -> name.text | _ -> "")
                     base.text))))
  | Function_type { inputs; input_names; output; clauses } ->
      List.iter (fun (_, input) -> type_expression state scope input) inputs;
      Option.iter (type_expression state scope) output;
      (* The names of the inputs are in scope in the type's own [requires],
         after the parameters before it in a signature. *)
      let named = List.fold_left (declare_parameter state) scope input_names in
      List.iter (clause state named) clauses
  | Type_error -> ()

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
  | Some (Value_generic id, _) -> set state name (Value_parameter id)
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

(* Clauses *)

and clause state scope (clause : clause) =
  let specification = { scope with specification = in_specification } in
  match clause.kind with
  | Uses capabilities -> List.iter (path_type state scope) capabilities
  | Requires value -> expression state specification value
  | Ensures value ->
      expression state
        {
          specification with
          specification =
            {
              in_specification with
              result = true;
              yielded = scope.hands_out;
              finished = scope.hands_out;
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
            { scope.specification with active = true; result = true; cost_bound = true };
        }
      in
      match cost.bound with
      | Big_o value | At_most value | Exactly value -> expression state bound value
      | Finite -> ())
  | Clause_error -> ()

(* Values *)

(* A lowercase name used as a value. *)
and local_value state scope (name : name) =
  let text = name.text in
  match String_map.find_opt text scope.values with
  | Some (Value_local id, _) -> set state name (Local id)
  | Some (Value_generic id, _) -> set state name (Value_parameter id)
  | Some (Value_field field, _) -> set state name (Field field)
  | None ->
      if scope.specification.active && text = "old" then set state name Old
      else if scope.specification.yielded && text = "yielded" then set state name Yielded
      else if scope.specification.finished && text = "finished" then set state name Finished
      else if scope.specification.active && text = "identical" then set state name Identical
      else if scope.specification.result && text = "result" then set state name Result_value
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
                        [
                          Diagnostic.fix "Write `None`."
                            [
                              Diagnostic.replace (Source.span name.span.start name.span.stop) "None";
                            ];
                        ]
                      (Printf.sprintf
                         "Truss has no `%s`. A value that may be missing is an `Option`, and \
                          `None` is its empty case."
                         text)))
            end
            else
              unknown state name ~what:"a value here"
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

(* What a name expression resolved to, if it is a name. *)
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
  (* [`Place called] says whether a method call took the place. *)
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
              [ Diagnostic.delete (Source.span marked.span.start keyword_end) ];
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
  | Call ({ kind = Name { modules = []; last }; _ }, arguments)
    when scope.specification.cost_bound && List.mem last.text [ "log"; "power"; "time"; "calls" ] ->
      set state last
        (Cost_function
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

(* A condition: what an [is] at the top of its [&&] chain binds is in scope
   in the rest of the chain, and in the scope this returns, for the block
   the condition guards. *)
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

(* Bindings *)

(* Declares a value name, reporting it if it hides another. *)
and declare_value state scope (name : name) =
  let hides what =
    report state Hides_name name.span
      (Printf.sprintf "`%s` is already %s, and a name cannot hide another. Choose another name."
         name.text what)
  in
  (match String_map.find_opt name.text scope.values with
  | Some (_, what) -> hides what
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
      | Some (Value_generic id, _) -> set state name (Value_parameter id)
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
      unknown state last ~what:"a constant in a module here" []
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
      | Some (Value_generic id, _), _ -> set state name (Value_parameter id)
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

(* Statements *)

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
      List.iter (loop_clause ~for_loop:true state inner) clauses;
      block state inner body;
      scope
  | While { condition = test; clauses; body } ->
      let inner = condition state scope test in
      List.iter (loop_clause state scope) clauses;
      block state inner body;
      scope
  | Parallel body ->
      (* Each branch sees only what is in scope before the block; what the
         branches bind is in scope after it. *)
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
                     "Another branch of this `parallel` block already binds `%s`, and a name \
                      cannot hide another. Choose another name."
                     key))
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

and loop_clause ?(for_loop = false) state scope (written : loop_clause) =
  let scope =
    if for_loop then { scope with specification = { scope.specification with yielded = true } }
    else scope
  in
  (* [yielded] names what the nearest loop or method hands out: a [for]
     loop's own parts, or else, in a lending or yielding method, the
     method's. *)
  let specification =
    { scope with specification = { in_specification with yielded = for_loop || scope.hands_out } }
  in
  match written.kind with
  | Invariant value -> expression state specification value
  | Loop_decreases measures -> List.iter (expression state specification) measures
  | Loop_cost cost -> clause state scope { kind = Cost cost; span = written.span; id = written.id }

(* Generic parameters *)

let declare_type state scope (name : name) ~parameter =
  let hides what =
    report state Hides_name name.span
      (Printf.sprintf "`%s` is already %s, and a name cannot hide another. Choose another name."
         name.text what)
  in
  (if String_map.mem name.text scope.types then hides "a generic parameter here"
   else
     match file_item state name.text with
     | Some item when Names.is_type_kind item.kind ->
         hides (Names.kind_name (Names.kind_of_named item.kind) ^ " in this file")
     | _ -> if List.mem name.text Prelude.names then hides "a name in the prelude");
  set state name Binding;
  { scope with types = String_map.add name.text (parameter name.id) scope.types }

let generics state scope (generics : generic_parameter list) =
  (* All of a list's parameters are in scope in each one's bounds. *)
  let scope =
    List.fold_left
      (fun scope (generic : generic_parameter) ->
        match generic.kind with
        | Type_parameter (name, _) ->
            declare_type state scope name ~parameter:(fun id : target -> Type_parameter id)
        | Capability_parameter name ->
            declare_type state scope name ~parameter:(fun id : target -> Capability_parameter id)
        | Value_parameter (name, _) ->
            let scope = declare_value state scope name in
            {
              scope with
              values =
                String_map.add name.text (Value_generic name.id, "a generic parameter") scope.values;
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
    hands_out = false;
  }

(* The scope a definition's head gives: the type head's generic parameters,
   for a method or a member constant. *)
let head state scope = function
  | Plain_name _ -> scope
  | Member_name (head_, _) ->
      type_name state scope head_.path;
      generics state scope head_.generics

let signature state scope ~(broken : bool) (signature_ : signature) =
  if broken then None
  else begin
    let scope = generics state scope signature_.generics in
    let scope = parameters state scope signature_.parameters in
    result state scope signature_.result;
    let scope =
      match signature_.result with
      | Some (Yields _ | Lends _) -> { scope with hands_out = true }
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

(* The definition *)

let definition state (definition_ : definition) =
  let broken part = Parts.broken definition_ part in
  let header_broken = broken Header and body_broken = broken Body in
  let scope = empty_scope in
  match definition_.kind with
  | Function { signature = signature_; body } ->
      if not header_broken then begin
        let scope = head state scope signature_.name in
        match signature state scope ~broken:false signature_ with
        | Some scope -> if not body_broken then block state scope body
        | None -> ()
      end
  | Type_definition { generics = generics_; body; clauses; _ } ->
      if not header_broken then begin
        let scope = generics state scope generics_ in
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
        let scope = generics state scope generics_ in
        List.iter (path_type state scope) requires;
        List.iteri
          (fun index (line : trait_member line) ->
            if not (broken (Member_header index)) then
              match line.kind with
              | Trait_method { signature = signature_; body } -> (
                  match signature state scope ~broken:false signature_ with
                  | Some inner ->
                      if not (broken (Member_body index)) then Option.iter (block state inner) body
                  | None -> ())
              | Associated_type (_, bounds) -> List.iter (path_type state scope) bounds
              | Law { parameters = parameters_; requires; body; _ } ->
                  let inner =
                    parameters state { scope with specification = in_specification } parameters_
                  in
                  List.iter (expression state inner) requires;
                  if not (broken (Member_body index)) then block state inner body
              | Trait_member_error -> ())
          members
      end
  | Impl { trait_; type_; uses; members } ->
      if not header_broken then begin
        type_name state scope type_.path;
        let scope = generics state scope type_.generics in
        path_type state scope trait_;
        List.iter (path_type state scope) uses;
        List.iteri
          (fun index (line : impl_member line) ->
            if not (broken (Member_header index)) then
              match line.kind with
              | Impl_method { signature = signature_; body } -> (
                  match signature state scope ~broken:false signature_ with
                  | Some inner -> if not (broken (Member_body index)) then block state inner body
                  | None -> ())
              | Associated_definition (_, type_) -> type_expression state scope type_
              | Impl_member_error -> ())
          members
      end
  | Capability { members; _ } ->
      List.iteri
        (fun index (line : capability_member line) ->
          if not (broken (Member_header index)) then
            match line.kind with
            | Capability_method signature_ ->
                ignore (signature state scope ~broken:false signature_)
            | Capability_member_error -> ())
        members
  | Constant { name; type_; value } ->
      if not header_broken then begin
        let scope = head state scope name in
        type_expression state scope type_;
        if not body_broken then expression state scope value
      end
  | Test { uses; body; _ } ->
      if not header_broken then begin
        List.iter (path_type state scope) uses;
        if not body_broken then block state scope body
      end
  | Theorem { generics = generics_; parameters = parameters_; clauses; body; _ } ->
      if not header_broken then begin
        let scope = generics state { scope with specification = in_specification } generics_ in
        let scope = parameters state scope parameters_ in
        List.iter (clause state scope) clauses;
        if not body_broken then block state scope body
      end
  | Law_proof { trait_; type_; body; _ } ->
      if not header_broken then begin
        path_type state scope trait_;
        type_expression state scope type_;
        if not body_broken then block state { scope with specification = in_specification } body
      end
  | Definition_error _ -> ()
