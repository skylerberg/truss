module Parameter_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Types.parameter
end))

type t = {
  lookups : Lookups.t;
  resolved : Resolve.resolved;
  bounds : Types.trait_reference list Parameter_table.t;
  known_bounds : Properties.Bounds.t;
  condition : Types.condition;
  broken_parameters : Catalog.reported Parameter_table.t;
  self_type : Types.ty option;
  self_trait : Types.trait_reference option;
  self_associated : (string * Types.ty) list;
  self_capabilities : (string * Types.capability_set) list;
  is_in_capability : bool;
  is_in_impl : bool;
  diagnostics : Catalog.diagnostic list ref;
  named : (Syntax.id * Types.ty) list ref;
}

let create_with lookups resolved (scope : _ Environment.scope) ~known_bounds =
  let bounds = Parameter_table.create 8 in
  List.iter
    (fun (parameter, traits) -> Parameter_table.replace bounds parameter traits)
    scope.bounds;
  let broken_parameters = Parameter_table.create 1 in
  List.iter
    (fun (parameter, report) -> Parameter_table.replace broken_parameters parameter report)
    scope.broken_parameters;
  {
    lookups;
    resolved;
    bounds;
    known_bounds;
    condition = [];
    broken_parameters;
    self_type = scope.self_type;
    self_trait = scope.self_trait;
    self_associated = scope.self_associated;
    self_capabilities = scope.self_capabilities;
    is_in_capability = false;
    is_in_impl = false;
    diagnostics = ref [];
    named = ref [];
  }

let create_declared lookups resolved (scope : Environment.declared_bounds Environment.scope) =
  create_with lookups resolved scope ~known_bounds:Properties.Bounds.none

let create lookups resolved (scope : Environment.known_bounds Environment.scope) =
  create_with lookups resolved scope ~known_bounds:(Properties.Bounds.of_known scope.bounds)

let list_bounds context parameter =
  let declared = Option.value ~default:[] (Parameter_table.find_opt context.bounds parameter) in
  match
    List.filter_map
      (fun (bound : Types.bound_condition) ->
        match bound.subject with
        | Types.Parameter subject when subject = parameter -> Some bound.bound
        | _ -> None)
      context.condition
  with
  | [] -> declared
  | conditional -> declared @ conditional

let list_known_bounds context =
  Properties.Bounds.append context.known_bounds
    (Properties.Bounds.close context.lookups (fun parameter ->
         List.filter_map
           (fun (bound : Types.bound_condition) ->
             match bound.subject with
             | Types.Parameter subject when subject = parameter -> Some bound.bound
             | _ -> None)
           context.condition))

let find_self_type context = context.self_type

let add_condition context condition =
  { context with condition = Types.make_condition (context.condition @ condition) }

let list_diagnostics context = !(context.diagnostics)
let list_named_types context = !(context.named)

let make_scope context : Environment.declared_bounds Environment.scope =
  {
    self_type = context.self_type;
    self_trait = context.self_trait;
    self_associated = context.self_associated;
    self_capabilities = context.self_capabilities;
    bounds =
      List.sort compare
        (Parameter_table.fold
           (fun parameter bounds bounds_by_parameter -> (parameter, bounds) :: bounds_by_parameter)
           context.bounds []);
    broken_parameters =
      List.sort compare
        (Parameter_table.fold
           (fun parameter report broken -> (parameter, report) :: broken)
           context.broken_parameters []);
  }

let empty_scope : Environment.declared_bounds Environment.scope =
  {
    self_type = None;
    self_trait = None;
    self_associated = [];
    self_capabilities = [];
    bounds = [];
    broken_parameters = [];
  }

let list_trait_closure (lookups : Lookups.t) path =
  let closure = ref [] in
  let rec visit path =
    if not (List.exists (Path.equal path) !closure) then begin
      closure := path :: !closure;
      match lookups.find_trait_header path with
      | Some header -> List.iter visit header.required
      | None -> ()
    end
  in
  visit path;
  List.rev !closure

let record_diagnostic diagnostics (diagnostic : Catalog.Typing.t) =
  let reported = Catalog.Typing diagnostic in
  diagnostics := reported :: !diagnostics;
  Catalog.make_reported reported

let report_error_type context diagnostic =
  Types.Error (record_diagnostic context.diagnostics diagnostic)

let report_error_capability context diagnostic =
  [ Types.Capability_error (record_diagnostic context.diagnostics diagnostic) ]

let raise_bug format = Compiler_bug.raise_bug ~stage:"Interface" format
let find_target context (name : Syntax.name) = context.resolved.names.(name.id)

let resolve_parameter context (name : Syntax.name) =
  match find_target context name with
  | Some (Type_parameter parameter) -> (
      match Parameter_table.find_opt context.broken_parameters parameter with
      | Some report -> Error report
      | None -> Ok parameter)
  | Some (Unknown report) -> Error report
  | _ -> raise_bug "`%s` is not resolved as a generic parameter" name.text

let show_path (path : Syntax.path) =
  String.concat "."
    (List.map (fun (name : Syntax.name) -> name.text) (path.modules @ [ path.last ]))

let find_literal_bound (bound : Syntax.bound) : Types.cost_bound option =
  match bound with
  | Big_o { kind = Integer _; _ } -> Some Order_of
  | At_most { kind = Integer limit; _ } -> Some (No_more_than limit)
  | Exactly { kind = Integer amount; _ } -> Some (Exactly_cost amount)
  | Big_o _ | At_most _ | Exactly _ -> None

let rec elaborate_type context (written : Syntax.type_expression) : Types.ty =
  match written.kind with
  | Path_type path -> elaborate_path_type context path
  | Self_type None -> (
      match elaborate_self context (Written written.id) with
      | Ok self -> self
      | Error report -> Types.Error report)
  | Self_type (Some key) -> elaborate_self_associated context (Written written.id) key
  | Associated (base, key) -> (
      match resolve_parameter context base with
      | Ok parameter -> elaborate_associated context (Types.Parameter parameter) parameter key
      | Error report -> Types.Error report)
  | Function_type function_type -> (
      match elaborate_function_type context function_type with
      | Ok function_type -> Types.Function function_type
      | Error report -> Types.Error report)
  | Type_error -> Types.Error Catalog.reported_elsewhere

and elaborate_self context (at : Core.origin) =
  match context.self_type with
  | Some self -> Ok self
  | None -> Error (record_diagnostic context.diagnostics (Misplaced_self_type { at }))

and elaborate_self_associated context (at : Core.origin) (key : Syntax.name) =
  match List.assoc_opt key.text context.self_associated with
  | Some fixed -> fixed
  | None -> (
      match (elaborate_self context at, context.self_trait) with
      | Error report, _ -> Types.Error report
      | Ok _, None ->
          report_error_type context
            (Self_outside_trait
               { at = Written key.id; name = key.text; associated = Associated_type })
      | Ok self, Some trait -> (
          match List.assoc_opt key.text trait.associated with
          | Some fixed -> fixed
          | None -> (
              match find_declaring_trait context trait.trait key.text with
              | Some _ -> Types.Projection { base = self; trait; name = key.text }
              | None ->
                  report_error_type context
                    (Undeclared_associated
                       { at = Written key.id; trait; name = key.text; associated = Associated_type })
              )))

and find_declaring_trait ?(capability = false) context trait name =
  List.find_opt
    (fun path ->
      match context.lookups.find_trait_header path with
      | Some header -> List.mem name (if capability then header.capabilities else header.associated)
      | None -> false)
    (list_trait_closure context.lookups trait)

and elaborate_associated context base parameter (key : Syntax.name) =
  let bounds = list_bounds context parameter in
  let associated_type =
    List.find_map
      (fun (bound : Types.trait_reference) ->
        match List.assoc_opt key.text bound.associated with
        | Some fixed -> Some fixed
        | None -> (
            match find_declaring_trait context bound.trait key.text with
            | Some _ -> Some (Types.Projection { base; trait = bound; name = key.text })
            | None -> None))
      bounds
  in
  match associated_type with
  | Some associated_type -> associated_type
  | None ->
      report_error_type context
        (Unbounded_associated
           {
             at = Written key.id;
             parameter = parameter.name;
             name = key.text;
             associated = Associated_type;
           })

and elaborate_arguments context (path : Syntax.path_type) =
  List.filter_map
    (function
      | Syntax.Type_argument written -> Some (Types.Type (elaborate_type context written))
      | Count (value, _) -> Some (Types.Value (Types.Known value))
      | Count_name name -> Some (elaborate_count_name context name)
      | Constraint _ -> None)
    path.arguments

and elaborate_count_name context (name : Syntax.name) : Types.argument =
  match find_target context name with
  | Some (Value_parameter parameter) -> Types.Value (Types.Value_parameter parameter)
  | Some (Definition (Constant, path)) -> (
      match Constants.evaluate_count context.lookups path with
      | Ok value -> Types.Value (Types.Known value)
      | Error error ->
          Types.Type
            (report_error_type context
               (Count_error { at = Written name.id; written = name.text; error })))
  | Some (Unknown report) -> Types.Type (Types.Error report)
  | _ -> raise_bug "`%s` is not resolved as a type argument" name.text

and check_arity context (path : Syntax.path_type) shown expected :
    (unit, Catalog.reported) Stdlib.result =
  match expected with
  | None -> Ok ()
  | Some expected -> (
      let written =
        List.filter (function Syntax.Constraint _ -> false | _ -> true) path.arguments
      in
      let argument_count = List.length written in
      if argument_count <> List.length expected then
        Error
          (record_diagnostic context.diagnostics
             (Arity
                {
                  at = Written path.id;
                  written = shown;
                  expected = List.length expected;
                  given = argument_count;
                }))
      else
        let errors =
          List.concat
            (List.map2
               (fun argument (name, kind) ->
                 let is_value =
                   match argument with Syntax.Count _ | Count_name _ -> true | _ -> false
                 in
                 let report_argument_kind mismatch =
                   [
                     record_diagnostic context.diagnostics
                       (Argument_kind
                          { at = Written path.id; written = shown; parameter = name; mismatch });
                   ]
                 in
                 match (kind, is_value) with
                 | Resolve.Names.Value_kind, false -> report_argument_kind Value_for_type
                 | Resolve.Names.Type_kind, true -> report_argument_kind Type_for_value
                 | _ -> [])
               written expected)
        in
        match errors with [] -> Ok () | error :: _ -> Error error)

and elaborate_path_type context (path : Syntax.path_type) : Types.ty =
  let shown = show_path path.path in
  match find_target context path.path.last with
  | Some (Type_parameter _) when path.arguments <> [] ->
      report_error_type context (Arguments_to_parameter { at = Written path.id; written = shown })
  | Some (Type_parameter parameter) -> (
      match Parameter_table.find_opt context.broken_parameters parameter with
      | Some report -> Types.Error report
      | None -> Types.Parameter parameter)
  | Some (Definition (Type, definition_path)) -> (
      match Well_known.find_builtin_type definition_path with
      | Some Never -> Types.Never
      | Some Integer -> Types.Integer
      | Some _ | None -> (
          let arguments = elaborate_arguments context path in
          match
            check_arity context path shown
              (Resolve.Names.find_generics context.lookups.names definition_path)
          with
          | Error report -> Types.Error report
          | Ok () ->
              let type_ = Types.Named { path = definition_path; arguments } in
              context.named := (path.id, type_) :: !(context.named);
              type_))
  | Some (Definition (Trait, _)) ->
      report_error_type context (Trait_as_type { at = Written path.id; written = shown })
  | Some (Definition (Capability, _)) ->
      report_error_type context (Capability_as_type { at = Written path.id; written = shown })
  | Some (Unknown report) -> Types.Error report
  | _ -> raise_bug "`%s` is not resolved as a type" shown

and elaborate_trait_reference ?(capability = false) context (path : Syntax.path_type) :
    (Types.trait_reference, Catalog.reported) Stdlib.result =
  let shown = show_path path.path in
  let build_trait_reference trait : (Types.trait_reference, Catalog.reported) Stdlib.result =
    let associated =
      List.sort compare
        (List.filter_map
           (function
             | Syntax.Constraint (name, written) -> Some (name.text, elaborate_type context written)
             | Type_argument _ | Count _ | Count_name _ -> None)
           path.arguments)
    in
    let trait_arguments = elaborate_arguments context path in
    match
      check_arity context path shown (Resolve.Names.find_generics context.lookups.names trait)
    with
    | Error report -> Error report
    | Ok () -> Ok { trait; trait_arguments; associated }
  in
  match find_target context path.path.last with
  | Some (Definition (Trait, trait)) -> build_trait_reference trait
  | Some (Definition (Capability, trait)) when capability -> build_trait_reference trait
  | Some (Definition _) ->
      Error
        (record_diagnostic context.diagnostics
           (Not_a_trait { at = Written path.id; written = shown; is_parameter = false }))
  | Some (Type_parameter _) ->
      Error
        (record_diagnostic context.diagnostics
           (Not_a_trait { at = Written path.id; written = shown; is_parameter = true }))
  | Some (Unknown report) -> Error report
  | _ -> raise_bug "`%s` is not resolved as a trait" shown

and elaborate_condition context (written : Syntax.condition) : Types.condition =
  Types.make_condition
    (List.concat_map
       (fun (bound : Syntax.bound_condition) ->
         let subject = elaborate_type context bound.subject in
         let is_decided =
           match subject with
           | Types.Parameter _ | Types.Error _ -> false
           | _ ->
               Option.fold ~none:true
                 ~some:(fun self -> not (Types.equal self subject))
                 context.self_type
         in
         if is_decided then begin
           ignore
             (record_diagnostic context.diagnostics
                (match subject with
                | Types.Projection { base; trait; name } ->
                    Decided_projection_condition
                      { at = Written bound.subject.id; subject; base; trait; name }
                | _ -> Decided_condition { at = Written bound.subject.id; subject }));
           []
         end
         else
           List.filter_map
             (fun path ->
               Result.to_option
                 (Result.map
                    (fun (reference : Types.trait_reference) ->
                      { Types.subject; bound = reference })
                    (elaborate_trait_reference context path)))
             bound.bounds)
       written)

and elaborate_trait_bounds context paths =
  let references = List.map (elaborate_trait_reference context) paths in
  ( List.filter_map Result.to_option references,
    List.find_map (function Error report -> Some report | Ok _ -> None) references )

and elaborate_capability_path context (path : Syntax.path_type) : Types.capability list =
  let shown = show_path path.path in
  match find_target context path.path.last with
  | Some (Type_parameter _) ->
      report_error_capability context
        (Not_a_capability { at = Written path.id; written = shown; is_type_parameter = true })
  | Some (Definition (Capability, path_)) -> [ Types.make_capability path_ ]
  | Some (Definition _) ->
      report_error_capability context
        (Not_a_capability { at = Written path.id; written = shown; is_type_parameter = false })
  | Some (Unknown report) -> [ Types.Capability_error report ]
  | _ -> raise_bug "`%s` is not resolved as a capability" shown

and find_capability_projection context base traits (key : Syntax.name) =
  List.find_map
    (fun (bound : Types.trait_reference) ->
      Option.map
        (fun _ ->
          Types.Capability_projection
            { base; trait = { bound with associated = [] }; name = key.text })
        (find_declaring_trait ~capability:true context bound.trait key.text))
    traits

and elaborate_capability context (written : Syntax.capability_reference) : Types.capability list =
  match written.kind with
  | Capability_path path -> elaborate_capability_path context path
  | Generic_capability name -> (
      match find_target context name with
      | Some (Capability_parameter parameter) -> [ Types.Capability_parameter parameter ]
      | Some (Unknown report) -> [ Types.Capability_error report ]
      | _ -> raise_bug "`generic %s` is not resolved as a capability parameter" name.text)
  | Self_capabilities key -> (
      match List.assoc_opt key.text context.self_capabilities with
      | Some set -> Types.list_capabilities set
      | None -> (
          match (elaborate_self context (Written written.id), context.self_trait) with
          | Error report, _ -> [ Types.Capability_error report ]
          | Ok _, None ->
              report_error_capability context
                (Self_outside_trait
                   { at = Written key.id; name = key.text; associated = Associated_capability_set })
          | Ok self, Some trait -> (
              match find_capability_projection context self [ trait ] key with
              | Some projection -> [ projection ]
              | None ->
                  report_error_capability context
                    (Undeclared_associated
                       {
                         at = Written key.id;
                         trait;
                         name = key.text;
                         associated = Associated_capability_set;
                       }))))
  | Associated_capabilities (base, key) -> (
      match resolve_parameter context base with
      | Error report -> [ Types.Capability_error report ]
      | Ok parameter -> (
          let bounds = list_bounds context parameter in
          match find_capability_projection context (Types.Parameter parameter) bounds key with
          | Some projection -> [ projection ]
          | None ->
              report_error_capability context
                (Unbounded_associated
                   {
                     at = Written key.id;
                     parameter = parameter.name;
                     name = key.text;
                     associated = Associated_capability_set;
                   })))

and elaborate_capabilities context written =
  Types.make_capability_set (List.concat_map (elaborate_capability context) written)

and elaborate_mode = function
  | None -> Language.Mode.Read
  | Some Syntax.Mut -> Language.Mode.Mut
  | Some Own -> Language.Mode.Own

and elaborate_parameter_type context mode (written : Syntax.type_expression) =
  let type_ = elaborate_type context written in
  let report_owning_type ~written_path ~view ~copy ~takes =
    Types.Error
      (record_diagnostic context.diagnostics
         (Read_only_owning_parameter
            {
              at = Written written.id;
              name = Written written_path.Syntax.last.id;
              written = show_path written_path;
              view;
              copy;
              takes;
            }))
  in
  match (mode, type_, written.kind) with
  | Language.Mode.Read, Types.Named { path; _ }, Path_type { path = written_path; _ }
    when not context.is_in_impl ->
      if Well_known.is List path then
        report_owning_type ~written_path ~view:"Slice" ~copy:"list"
          ~takes:"a `List`, an `Array`, and a range of either"
      else if Well_known.is String path then
        report_owning_type ~written_path ~view:"StringSlice" ~copy:"string"
          ~takes:"a `String`, a string literal, and a part of a string"
      else type_
  | _ -> type_

and elaborate_function_type context (written : Syntax.function_type) :
    (Types.function_type, Catalog.reported) Stdlib.result =
  let inputs =
    List.map
      (fun (input : Syntax.function_input) ->
        let mode = elaborate_mode input.mode in
        (mode, elaborate_parameter_type context mode input.type_))
      written.inputs
  in
  let output =
    match written.output with Some output -> elaborate_type context output | None -> Types.unit
  in
  let uses = elaborate_uses context written.clauses in
  report_time_of_run_forever context ~uses written.clauses;
  match elaborate_costs context written.clauses with
  | Ok costs -> Ok { inputs; output; uses; costs = List.sort_uniq compare costs }
  | Error report -> Error report

and report_time_of_run_forever context ~uses (clauses : Syntax.clause list) =
  if Types.has_capability (Built_in Run_forever) uses then
    List.iter
      (fun (clause : Syntax.clause) ->
        match clause.kind with
        | Cost { resource = Metric Time; _ } ->
            ignore
              (record_diagnostic context.diagnostics
                 (Time_of_run_forever { at = Written clause.id }))
        | _ -> ())
      clauses

and elaborate_uses context clauses =
  Types.make_capability_set
    (List.concat_map
       (fun (clause : Syntax.clause) ->
         match clause.kind with Uses uses -> elaborate_capability_uses context uses | _ -> [])
       clauses)

and elaborate_capability_uses context uses =
  List.concat_map
    (fun (use : Syntax.capability_use) ->
      let capabilities = elaborate_capability context use.capability in
      match (use.unless, use.unless_values) with
      | None, [] -> capabilities
      | Some unless, [] ->
          let unless = elaborate_condition context unless in
          List.filter_map (fun capability -> Types.make_unless capability unless) capabilities
      | unless, (first :: _ : Syntax.expression list) ->
          let report condition =
            ignore
              (record_diagnostic context.diagnostics
                 (Misplaced_value_condition { at = Written first.id; condition }));
            capabilities
          in
          if context.is_in_capability then report In_capability_method
          else if Option.is_some unless then report Joined_with_bound
          else if capabilities <> [ Built_in Panic ] then report (Not_panic capabilities)
          else [ Types.Capability_unless_values (Built_in Panic) ])
    uses

and elaborate_costs context clauses : (Types.cost list, Catalog.reported) Stdlib.result =
  let report_error diagnostic = Error (record_diagnostic context.diagnostics diagnostic) in
  let elaborate_counted (path : Syntax.path_type) (method_ : Syntax.name option) :
      (Types.resource, Catalog.reported) Stdlib.result =
    let shown = show_path path.path in
    match find_target context path.path.last with
    | Some (Definition (Capability, capability)) -> (
        match method_ with
        | Some method_
          when Option.is_none
                 (context.lookups.names.find_key
                    (Path.make_capability_method capability method_.text)) ->
            report_error
              (Unknown_capability_method
                 { at = Written method_.id; written = shown; method_ = method_.text })
        | _ ->
            Ok
              (Calls
                 {
                   capability;
                   method_ = Option.map (fun (method_ : Syntax.name) -> method_.text) method_;
                 }))
    | Some (Unknown report) -> Error report
    | _ -> report_error (Calls_not_a_capability { at = Written path.id; written = shown })
  in
  let costs =
    List.filter_map
      (fun (clause : Syntax.clause) ->
        match clause.kind with
        | Cost cost ->
            let resource : (Types.resource, Catalog.reported) Stdlib.result =
              match cost.resource with
              | Metric metric -> Ok (Metric metric)
              | Calls (Call_capability path) -> elaborate_counted path None
              | Calls (Call_method (path, method_)) -> elaborate_counted path (Some method_)
              | Calls (Call_parameter name) ->
                  report_error (Calls_through_parameter { at = Written name.id; name = name.text })
            in
            let bound =
              match find_literal_bound cost.bound with
              | Some bound -> bound
              | None -> raise_bug "a function type's cost bound is not an integer literal"
            in
            Some
              (Result.map
                 (fun resource -> { Types.amortized = cost.amortized; resource; bound })
                 resource)
        | _ -> None)
      clauses
  in
  match List.find_map (function Error report -> Some report | Ok _ -> None) costs with
  | Some report -> Error report
  | None -> Ok (List.filter_map Result.to_option costs)

let elaborate_generics context owner (written : Syntax.generic_parameter list) : Types.generic list
    =
  let make_parameter (name : Syntax.name) : Types.parameter = { owner; name = name.text } in
  let declared =
    List.filter_map
      (fun (generic : Syntax.generic_parameter) ->
        match generic.kind with
        | Type_parameter (name, bounds) -> Some (make_parameter name, `Type bounds)
        | Value_parameter (name, type_) -> Some (make_parameter name, `Value type_)
        | Generic_error -> None)
      written
  in
  List.map
    (fun (parameter, kind) ->
      match kind with
      | `Type bounds ->
          let bounds, broken = elaborate_trait_bounds context bounds in
          Parameter_table.replace context.bounds parameter bounds;
          Option.iter (Parameter_table.replace context.broken_parameters parameter) broken;
          { Types.generic = parameter; kind = Type_generic bounds }
      | `Value (written : Syntax.type_expression) ->
          let type_ = elaborate_type context written in
          if not (Types.is_builtin UInt64 type_ || Types.is_error type_) then begin
            ignore
              (record_diagnostic context.diagnostics
                 (Wrong_value_parameter_type
                    { at = Written written.id; parameter = parameter.name; type_ }))
          end;
          { Types.generic = parameter; kind = Value_generic })
    declared

let list_constant_costs (clauses : Syntax.clause list) : Types.cost list =
  List.filter_map
    (fun (clause : Syntax.clause) ->
      match clause.kind with
      | Cost { amortized; resource = Metric metric; bound } when Option.is_none clause.condition ->
          Option.map
            (fun bound -> { Types.amortized; resource = Metric metric; bound })
            (find_literal_bound bound)
      | _ -> None)
    clauses

type operand_callee =
  | Function_parameter of Syntax.name
  | Bound_method of { type_ : Syntax.expression; method_ : Syntax.name }
  | Not_a_callee

type cost_operand = {
  written : Syntax.expression;
  cost_function : Syntax.name;
  metric : Language.Metric.t;
  callee : operand_callee;
}

let list_cost_operands context (bound : Syntax.expression) =
  let operands = ref [] in
  let rec visit (value : Syntax.expression) =
    (match value.kind with
    | Call ({ kind = Name cost_function; _ }, arguments) -> (
        match find_target context cost_function with
        | Some (Specification_function (Call_cost metric)) ->
            let callee =
              match arguments with
              | [ { value = { kind = Name last; _ }; _ } ] -> Function_parameter last
              | [ { value = { kind = Member (type_, method_); _ }; _ } ] ->
                  Bound_method { type_; method_ }
              | _ -> Not_a_callee
            in
            operands := { written = value; cost_function; metric; callee } :: !operands
        | _ -> ())
    | _ -> ());
    Syntax_walk.visit_children visit value
  in
  visit bound;
  List.rev !operands

let find_trait_parts (lookups : Lookups.t) trait =
  match Option.bind (lookups.names.find_key trait) lookups.find_header with
  | Some { container = Trait_parts { trait_generics; requires; associated_types; _ }; _ } ->
      Some (trait_generics, requires, associated_types)
  | Some { container = Capability_parts | Impl_parts _; _ } | None -> None

let list_bound_closure lookups ~self (bound : Types.trait_reference) =
  Properties.list_bound_closure_over ~find_requirements:(find_trait_parts lookups) ~self bound

let list_required_traits lookups trait =
  match find_trait_parts lookups trait with
  | Some (_, requires, _) ->
      List.map (fun (required : Types.trait_reference) -> required.trait) requires
  | None -> []

let list_requirements_first lookups (requires : Path.t list) =
  let visited = ref [] in
  let rec visit trait =
    if not (List.exists (Path.equal trait) !visited) then begin
      visited := trait :: !visited;
      List.concat_map visit (list_required_traits lookups trait) @ [ trait ]
    end
    else []
  in
  List.concat_map visit requires

let restates_required_method (lookups : Lookups.t) trait name receiver =
  List.exists
    (fun required ->
      List.exists
        (fun (member : Resolve.Names.key) ->
          match member.path with
          | Method { receiver = declared; _ } -> declared = receiver
          | _ -> false)
        (lookups.names.list_members required name))
    (list_requirements_first lookups (list_required_traits lookups trait))

let close_scope lookups (scope : Environment.declared_bounds Environment.scope) :
    Environment.known_bounds Environment.scope =
  {
    self_type = scope.self_type;
    self_trait = scope.self_trait;
    self_associated = scope.self_associated;
    self_capabilities = scope.self_capabilities;
    bounds =
      List.map
        (fun (parameter, bounds) ->
          ( parameter,
            List.concat_map (list_bound_closure lookups ~self:(Types.Parameter parameter)) bounds ))
        scope.bounds;
    broken_parameters = scope.broken_parameters;
  }

let list_direct_bounds context (type_ : Types.ty) =
  match type_ with
  | Types.Parameter parameter -> list_bounds context parameter
  | Types.Projection { base; trait; name } ->
      List.concat_map
        (fun (declaring : Types.trait_reference) ->
          match find_trait_parts context.lookups declaring.trait with
          | Some (trait_generics, _, associated_types) ->
              let substitution =
                Types.bind_argument
                  (Types.make_self_parameter declaring.trait)
                  (Types.Type base)
                  (Types.make_substitution trait_generics declaring.trait_arguments)
              in
              List.concat_map
                (fun (associated : Types.associated_type) ->
                  if associated.associated_name = name then
                    List.map (Types.substitute_trait substitution) associated.associated_bounds
                  else [])
                associated_types
          | None -> [])
        (list_bound_closure context.lookups ~self:base trait)
  | _ -> []

let rec find_bounded_type context (written : Syntax.expression) =
  match written.kind with
  | Self_type_value -> (
      match context.self_type with
      | Some (Types.Parameter _ as self) -> Some self
      | Some _ | None -> None)
  | Name last -> (
      match find_target context last with
      | Some (Type_parameter parameter) -> Some (Types.Parameter parameter)
      | Some _ | None -> None)
  | Member (base, associated) ->
      Option.bind (find_bounded_type context base) (fun base ->
          let bounds = list_direct_bounds context base in
          match
            List.find_map
              (fun (bound : Types.trait_reference) ->
                List.assoc_opt associated.text bound.associated)
              bounds
          with
          | Some ((Types.Parameter _ | Types.Projection _) as fixed) -> Some fixed
          | Some _ -> None
          | None ->
              List.find_map
                (fun (bound : Types.trait_reference) ->
                  Option.map
                    (fun _ -> Types.Projection { base; trait = bound; name = associated.text })
                    (find_declaring_trait context bound.trait associated.text))
                bounds)
  | Parenthesized inner -> find_bounded_type context inner
  | _ -> None

type bound_method = {
  self_type : Types.ty;
  trait : Types.trait_reference;
  name : string;
  receiver : Path.receiver;
}

let list_bound_methods context (self_type : Types.ty) name =
  List.fold_left
    (fun methods (trait : Types.trait_reference) ->
      List.fold_left
        (fun methods (member : Resolve.Names.key) ->
          match member.path with
          | Method { receiver; _ }
            when (not
                    (List.exists
                       (fun (known : bound_method) ->
                         Path.equal known.trait.trait trait.trait && known.receiver = receiver)
                       methods))
                 && not (restates_required_method context.lookups trait.trait name receiver) ->
              methods @ [ { self_type; trait = { trait with associated = [] }; name; receiver } ]
          | _ -> methods)
        methods
        (context.lookups.names.list_members trait.trait name))
    []
    (List.concat_map
       (list_bound_closure context.lookups ~self:self_type)
       (list_direct_bounds context self_type))

let find_operand_method (overloads : bound_method list) =
  match overloads with
  | [ only ] -> Some only
  | several -> (
      match
        List.filter (fun (method_ : bound_method) -> method_.receiver = Instance Read) several
      with
      | [ read_only ] -> Some read_only
      | _ -> None)

let report_time_of_parameters_that_run_forever context ~(parameters : Types.parameter_info list)
    (clauses : Syntax.clause list) =
  let report_operand (operand : cost_operand) =
    match (operand.metric, operand.callee) with
    | Time, Function_parameter name -> (
        match
          List.find_opt
            (fun (parameter : Types.parameter_info) -> parameter.name = name.text)
            parameters
        with
        | Some { type_ = Function { uses; _ }; _ } when not (Types.terminates uses) ->
            ignore
              (record_diagnostic context.diagnostics
                 (Time_of_unbounded_parameter { at = Written operand.written.id; name = name.text }))
        | Some _ | None -> ())
    | Time, (Bound_method _ | Not_a_callee) | (Allocations | Allocated_bytes), _ -> ()
  in
  List.iter
    (fun (clause : Syntax.clause) ->
      match clause.kind with
      | Cost { resource = Metric Time; bound = Big_o value | At_most value | Exactly value; _ } ->
          List.iter report_operand (list_cost_operands context value)
      | _ -> ())
    clauses

let rec split_field_path (value : Syntax.expression) =
  match value.kind with
  | Name name -> Some (name.text, [])
  | Self_value -> Some ("self", [])
  | Member (base, field) ->
      Option.map (fun (root, fields) -> (root, fields @ [ field ])) (split_field_path base)
  | _ -> None

let elaborate_modifies context (signature : Types.signature) (clauses : Syntax.clause list) =
  let report diagnostic = ignore (record_diagnostic context.diagnostics diagnostic) in
  let rec has_index (value : Syntax.expression) =
    match value.kind with
    | Bracket _ -> true
    | Member (base, _) | Call (base, _) | Parenthesized base -> has_index base
    | _ -> false
  in
  let rec is_resolved (value : Syntax.expression) =
    match value.kind with
    | Name name -> Option.is_some (find_target context name)
    | Member (base, _) -> is_resolved base
    | _ -> true
  in
  let elaborate_entry (value : Syntax.expression) =
    let at : Core.origin = Written value.id in
    match split_field_path value with
    | None ->
        report
          (if has_index value then Indexed_modified_part { at } else Not_a_modified_part { at });
        None
    | Some (parameter, names) -> (
        let fields = List.map (fun (name : Syntax.name) -> name.text) names in
        match Types.find_parameter_position signature parameter with
        | None ->
            if is_resolved value then report (Modified_non_parameter { at; name = parameter });
            None
        | Some position when (Types.read_parameter_at signature position).mode <> Mut ->
            report (Read_only_part { at; parameter; fields });
            None
        | Some _ when fields = [] ->
            report (Modified_whole_parameter { at; parameter });
            None
        | Some position -> Some (value, parameter, { Types.position; field_path = fields }))
  in
  let is_contained ~index (part : Types.modified) ~other_index (other : Types.modified) =
    other_index <> index && other.position = part.position
    && Types.is_field_path_prefix other.field_path part.field_path
    && (other.field_path <> part.field_path || other_index < index)
  in
  List.concat_map
    (fun (clause : Syntax.clause) ->
      match clause.kind with
      | Modifies entries -> (
          let entry_parts = List.map elaborate_entry entries in
          match List.filter_map Fun.id entry_parts with
          | parts when List.length parts < List.length entry_parts -> []
          | parts ->
              let numbered_parts = List.mapi (fun index part -> (index, part)) parts in
              List.filter_map
                (fun (index, ((value : Syntax.expression), parameter, (part : Types.modified))) ->
                  match
                    List.find_map
                      (fun (other_index, (_, _, other)) ->
                        if is_contained ~index part ~other_index other then Some other else None)
                      numbered_parts
                  with
                  | Some (container : Types.modified) ->
                      report
                        (Repeated_part
                           {
                             at = Written value.id;
                             parameter;
                             fields = part.field_path;
                             container = container.field_path;
                             siblings =
                               Catalog.read_entry_siblings
                                 (List.map
                                    (fun (entry : Syntax.expression) ->
                                      { Catalog.covering = [ Core.Written entry.id ] })
                                    entries)
                                 index;
                           });
                      None
                  | None -> Some part)
                numbered_parts)
      | Uses _ | Requires _ | Ensures _ | Decreases _ | Cost _ | Clause_error -> [])
    clauses

let elaborate_signature context ~owner ~head ~self_type (written : Syntax.signature) :
    Types.signature =
  let own = elaborate_generics context owner written.generics in
  let generics_ = head @ own in
  let receiver =
    match written.parameters with
    | { kind = Self_parameter mode; _ } :: _ ->
        Option.map (fun self -> (elaborate_mode mode, self)) self_type
    | _ -> None
  in
  let parameters =
    List.filter_map
      (fun (parameter : Syntax.parameter) ->
        match parameter.kind with
        | Named_parameter { name; mode; type_; default } ->
            let mode = elaborate_mode mode in
            Some
              {
                Types.name = name.text;
                mode;
                type_ = elaborate_parameter_type context mode type_;
                has_default = Option.is_some default;
              }
        | Self_parameter _ | Parameter_error -> None)
      written.parameters
  in
  let output =
    match written.result with
    | None -> Types.Returns Types.unit
    | Some (Returns result) -> Types.Returns (elaborate_type context result)
    | Some (Lends (mode, result)) -> Types.Lends (elaborate_mode mode, elaborate_type context result)
  in
  let uses = elaborate_uses context written.clauses in
  report_time_of_run_forever context ~uses written.clauses;
  report_time_of_parameters_that_run_forever context ~parameters written.clauses;
  let signature : Types.signature =
    {
      generics = generics_;
      capability_parameters =
        Array.fold_left
          (fun listed -> function
            | Some (Resolve.Capability_parameter (parameter : Types.parameter))
              when Path.equal parameter.owner owner && not (List.mem parameter listed) ->
                listed @ [ parameter ]
            | _ -> listed)
          [] context.resolved.names;
      receiver;
      parameters;
      output;
      uses;
      costs = list_constant_costs written.clauses;
      modifies = [];
      specification_only =
        Well_known.is Model owner
        || Types.mentions_specification_only_type parameters output
        || Option.is_some
             (Option.bind receiver (fun (_, self) -> Types.find_specification_only_type self));
      is_update_step = false;
      capture_free_parameters = Types.list_capture_free_parameters parameters;
    }
  in
  { signature with modifies = elaborate_modifies context signature written.clauses }

let elaborate_type_head context owner (head : Syntax.type_head) =
  let generics = elaborate_generics context owner head.generics in
  match find_target context head.path.last with
  | Some (Definition (Type, type_path)) ->
      let type_ =
        match Resolve.Names.find_generics context.lookups.names type_path with
        | Some expected when List.length expected <> List.length generics ->
            report_error_type context
              (Head_arity
                 {
                   at = Written head.id;
                   written = show_path head.path;
                   expected = List.length expected;
                   given = List.length generics;
                 })
        | _ -> (
            match Well_known.find_builtin_type type_path with
            | Some Never -> Types.Never
            | Some Integer -> Types.Integer
            | _ ->
                Types.Named { path = type_path; arguments = Types.list_generic_arguments generics })
      in
      (generics, type_)
  | Some (Definition (((Trait | Capability) as kind), _)) ->
      ( generics,
        report_error_type context
          (Head_not_a_type
             {
               at = Written head.id;
               written = show_path head.path;
               kind = Resolve.Names.convert_named kind;
             }) )
  | Some (Unknown report) -> (generics, Types.Error report)
  | _ -> raise_bug "the type head `%s` is not resolved" (show_path head.path)

let elaborate_fields context (written : Syntax.field list) =
  List.filter_map
    (fun (field : Syntax.field) ->
      match field.kind with
      | Field_declaration { name; type_; default } ->
          let field_type = elaborate_type context type_ in
          let field_type =
            match Types.find_specification_only_type field_type with
            | None -> field_type
            | Some specification_type ->
                report_error_type context
                  (Specification_only_field { at = Written type_.id; type_ = specification_type })
          in
          Some
            { Types.field_name = name.text; field_type; field_has_default = Option.is_some default }
      | Field_error -> None)
    written

let elaborate_container (context : t) (path : Path.t) (definition : Syntax.definition) :
    (Environment.container, Catalog.reported) Stdlib.result * t =
  match definition.kind with
  | Trait { generics; requires; members; _ } ->
      let trait_generics = elaborate_generics context path generics in
      let self_parameter = Types.make_self_parameter path in
      let self_trait : Types.trait_reference =
        {
          trait = path;
          trait_arguments = Types.list_generic_arguments trait_generics;
          associated = [];
        }
      in
      Parameter_table.replace context.bounds self_parameter [ self_trait ];
      let context =
        {
          context with
          self_type = Some (Types.Parameter self_parameter);
          self_trait = Some self_trait;
        }
      in
      let requires, broken_requirement = elaborate_trait_bounds context requires in
      let associated_types, broken_associated =
        List.split
          (List.filter_map
             (fun (line : Syntax.trait_member Syntax.node) ->
               match line.kind with
               | Associated_type (name, bounds) ->
                   let associated_bounds, broken = elaborate_trait_bounds context bounds in
                   Some
                     ( { Types.associated_name = name.text; associated_bounds },
                       Option.map (fun report -> (name.text, Types.Error report)) broken )
               | Associated_capability _ | Law _ | Trait_member_error -> None)
             members)
      in
      let context =
        {
          context with
          self_type =
            (match broken_requirement with
            | Some report -> Some (Types.Error report)
            | None -> context.self_type);
          self_associated = context.self_associated @ List.filter_map Fun.id broken_associated;
        }
      in
      let associated_capabilities =
        List.filter_map
          (fun (line : Syntax.trait_member Syntax.node) ->
            match line.kind with Associated_capability name -> Some name.text | _ -> None)
          members
      in
      let laws =
        List.filter_map
          (fun (line : Syntax.trait_member Syntax.node) ->
            match line.kind with
            | Law law ->
                Some
                  ( law.name.text,
                    List.filter_map
                      (fun (parameter : Syntax.parameter) ->
                        match parameter.kind with
                        | Named_parameter { name; type_; _ } ->
                            Some (name.text, elaborate_type context type_)
                        | Self_parameter _ | Parameter_error -> None)
                      law.parameters )
            | Associated_type _ | Associated_capability _ | Trait_member_error -> None)
          members
      in
      ( Ok
          (Trait_parts { trait_generics; requires; associated_types; associated_capabilities; laws }),
        context )
  | Impl { trait_; type_ = head; uses; members } -> (
      let impl_generics, for_type = elaborate_type_head context path head in
      match elaborate_trait_reference ~capability:true context trait_ with
      | Error report -> (Error report, context)
      | Ok implements ->
          let associated =
            List.sort compare
              (List.filter_map
                 (fun (line : Syntax.impl_member Syntax.node) ->
                   match line.kind with
                   | Associated_definition (name, written) ->
                       Some
                         ( name.text,
                           elaborate_type { context with self_type = Some for_type } written )
                   | Capability_definition _ | Impl_member_error -> None)
                 members)
          in
          let implements = { implements with associated } in
          let context =
            {
              context with
              self_type = Some for_type;
              self_trait = Some implements;
              self_associated = associated;
            }
          in
          let capability_sets =
            List.fold_left
              (fun sets (line : Syntax.impl_member Syntax.node) ->
                match line.kind with
                | Capability_definition (name, written) ->
                    let set =
                      Types.make_capability_set
                        (elaborate_capability_uses
                           { context with self_capabilities = sets }
                           written)
                    in
                    let is_defined_by_this_impl = function
                      | Types.Capability_projection { base; trait; name } ->
                          Types.equal base for_type
                          && Option.equal Path.equal
                               (find_declaring_trait ~capability:true context trait.trait name)
                               (Some implements.trait)
                      | _ -> false
                    in
                    if List.mem_assoc name.text sets then sets
                    else if Types.exists_capability is_defined_by_this_impl set then
                      ( name.text,
                        Types.make_capability_set
                          (report_error_capability context
                             (Self_defined_capability_set { at = Written name.id; name = name.text }))
                      )
                      :: sets
                    else (name.text, set) :: sets
                | Associated_definition _ | Impl_member_error -> sets)
              [] members
          in
          let declared =
            match context.lookups.find_trait_header implements.trait with
            | Some header -> header.capabilities
            | None -> []
          in
          let context =
            {
              context with
              self_capabilities =
                List.map
                  (fun name ->
                    ( name,
                      Option.value ~default:Types.no_capabilities
                        (List.assoc_opt name capability_sets) ))
                  declared;
            }
          in
          ( Ok
              (Impl_parts
                 {
                   impl_generics;
                   implements;
                   for_type;
                   impl_uses = elaborate_capabilities context uses;
                   capability_sets =
                     List.sort compare
                       (List.filter (fun (name, _) -> List.mem name declared) capability_sets);
                 }),
            context ))
  | _ -> (Ok Capability_parts, context)

let has_broken_elaborated_member (lookups : Lookups.t) (key : Resolve.Names.key)
    (definition : Syntax.definition) =
  let has_broken_member is_elaborated members =
    List.exists Fun.id
      (List.mapi
         (fun index (member : _ Syntax.node) ->
           is_elaborated member.kind
           && Resolve.Names.is_broken lookups.names key (Member_header index))
         members)
  in
  match definition.kind with
  | Trait { members; _ } ->
      has_broken_member
        (function
          | Syntax.Associated_type _ | Law _ -> true
          | Associated_capability _ | Trait_member_error -> false)
        members
  | Impl { members; _ } ->
      has_broken_member
        (function
          | Syntax.Associated_definition _ | Capability_definition _ -> true
          | Impl_member_error -> false)
        members
  | Capability _ | Function _ | Method_declaration _ | Type_definition _ | Constant _ | Test _
  | Theorem _ | Law_proof _ | Definition_error _ ->
      false

let elaborate_header (lookups : Lookups.t) (key : Resolve.Names.key) =
  let resolved = lookups.read_resolved Interface key in
  let definition = lookups.names.read_definition key in
  if
    Resolve.Names.is_broken lookups.names key Header
    || has_broken_elaborated_member lookups key definition
  then Error []
  else
    match
      elaborate_container (create_declared lookups resolved empty_scope) key.path definition
    with
    | _, context when !(context.diagnostics) <> [] -> Error (List.rev !(context.diagnostics))
    | Error _, _ -> Error []
    | Ok container, context ->
        Ok
          {
            Environment.container;
            container_scope = make_scope context;
            container_named = List.rev !(context.named);
          }

let make_elaborated_interface context interface : Environment.elaborated_interface =
  {
    interface;
    diagnostics = List.rev !(context.diagnostics);
    named = List.rev !(context.named);
    scope = close_scope context.lookups (make_scope context);
  }

let list_methods (lookups : Lookups.t) key =
  List.filter_map
    (fun (member : Resolve.Names.key) ->
      match (member.path, lookups.names.read_definition member) with
      | Method { name; receiver; _ }, { kind = Function _; _ } ->
          Some { Types.method_name = name; method_receiver = receiver; provided = true }
      | Method { name; receiver; _ }, { kind = Method_declaration _; _ } ->
          Some { Types.method_name = name; method_receiver = receiver; provided = false }
      | _ -> None)
    (lookups.names.list_contained key)

let split_restated_methods (lookups : Lookups.t) (requires : Types.trait_reference list) members =
  let inherited =
    List.concat_map
      (fun trait ->
        match lookups.names.find_key trait with
        | Some key ->
            List.map
              (fun (method_ : Types.trait_method) ->
                ((method_.method_name, method_.method_receiver), trait))
              (list_methods lookups key)
        | None -> [])
      (list_requirements_first lookups
         (List.map (fun (required : Types.trait_reference) -> required.trait) requires))
  in
  List.partition_map
    (fun (method_ : Types.trait_method) ->
      match List.assoc_opt (method_.method_name, method_.method_receiver) inherited with
      | Some declared_by ->
          Either.Right
            {
              Types.restated_name = method_.method_name;
              restated_receiver = method_.method_receiver;
              declared_by;
            }
      | None -> Either.Left method_)
    members

let list_supertraits (lookups : Lookups.t) (key : Resolve.Names.key) trait_generics =
  match
    Properties.list_bound_closure_over
      ~find_requirements:(fun trait ->
        match Option.bind (lookups.names.find_key trait) lookups.find_header with
        | Some { container = Trait_parts { trait_generics; requires; associated_types; _ }; _ } ->
            Some (trait_generics, requires, associated_types)
        | Some { container = Capability_parts | Impl_parts _; _ } | None -> None)
      ~self:(Types.Parameter (Types.make_self_parameter key.path))
      {
        trait = key.path;
        trait_arguments = Types.list_generic_arguments trait_generics;
        associated = [];
      }
  with
  | _ :: supertraits -> supertraits
  | [] -> []

let make_container_interface lookups (key : Resolve.Names.key) (header : Environment.header) :
    Environment.elaborated_interface =
  let methods = list_methods lookups key in
  let interface =
    match header.container with
    | Trait_parts { trait_generics; requires; associated_types; associated_capabilities; laws } ->
        let methods, restated = split_restated_methods lookups requires methods in
        Environment.Trait_interface
          {
            trait_generics;
            requires;
            supertraits = list_supertraits lookups key trait_generics;
            associated_types;
            associated_capabilities;
            laws;
            methods;
            restated;
            is_capability = false;
          }
    | Capability_parts ->
        Trait_interface
          {
            trait_generics = [];
            requires = [];
            supertraits = [];
            associated_types = [];
            associated_capabilities = [];
            laws = [];
            methods;
            restated = [];
            is_capability = true;
          }
    | Impl_parts { impl_generics; implements; for_type; impl_uses; capability_sets } ->
        Impl_interface
          {
            impl_generics;
            implements;
            for_type;
            impl_uses;
            capability_sets;
            impl_methods =
              List.map
                (fun (method_ : Types.trait_method) ->
                  (method_.method_name, method_.method_receiver))
                methods;
          }
  in
  {
    interface;
    diagnostics = [];
    named = header.container_named;
    scope = close_scope lookups header.container_scope;
  }

let elaborate_member (lookups : Lookups.t) ~path resolved (definition : Syntax.definition)
    (header : Environment.header) =
  let context = create_declared lookups resolved header.container_scope in
  match definition.kind with
  | Function { signature; _ } | Method_declaration signature ->
      let is_in_capability, is_in_impl =
        match header.container with
        | Capability_parts -> (true, false)
        | Trait_parts _ -> (false, false)
        | Impl_parts _ -> (false, true)
      in
      make_elaborated_interface context
        (Function_interface
           (elaborate_signature
              { context with self_capabilities = []; is_in_capability; is_in_impl }
              ~owner:path ~head:[] ~self_type:header.container_scope.self_type signature))
  | _ -> make_elaborated_interface context (Error_interface Catalog.reported_elsewhere)

let elaborate_definition (lookups : Lookups.t) (key : Resolve.Names.key) =
  let resolved = lookups.read_resolved Interface key in
  let definition = lookups.names.read_definition key in
  let path = key.path in
  Compiler_bug.run_while_doing ~stage:"Interface" (Resolve.Names.show_key key) (fun () ->
      let context = create_declared lookups resolved empty_scope in
      let make_error_interface () =
        make_elaborated_interface context (Error_interface Catalog.reported_elsewhere)
      in
      match
        ( Resolve.Names.find_syntax_error lookups.names key Header,
          Option.map lookups.find_header (lookups.names.find_container key) )
      with
      | Some report, _ -> make_elaborated_interface context (Error_interface report)
      | None, Some None -> make_error_interface ()
      | None, Some (Some header) -> elaborate_member lookups ~path resolved definition header
      | None, None -> (
          match definition.kind with
          | Trait _ | Capability _ | Impl _ -> (
              match lookups.find_header key with
              | Some header -> make_container_interface lookups key header
              | None -> raise_bug "`%s` has no header" (Resolve.Names.show_key key))
          | Method_declaration _ | Definition_error _ -> make_error_interface ()
          | Function { signature; _ } ->
              let head, self_type =
                match signature.name with
                | Plain_name _ -> ([], None)
                | Member_name (head, _) ->
                    let generics, self = elaborate_type_head context path head in
                    (generics, Some self)
              in
              let context = { context with self_type } in
              let elaborated = elaborate_signature context ~owner:path ~head ~self_type signature in
              let takes_mut_self =
                match elaborated.receiver with
                | Some (Mut, _) -> true
                | Some ((Read | Own), _) | None -> false
              in
              make_elaborated_interface context
                (Function_interface
                   {
                     elaborated with
                     is_update_step =
                       takes_mut_self && (lookups.names.read_declaration key).visibility = Private;
                   })
          | Type_definition { is_tuple; generics; body; clauses; _ } ->
              let type_generics = elaborate_generics context path generics in
              let self =
                Types.Named { path; arguments = Types.list_generic_arguments type_generics }
              in
              let context = { context with self_type = Some self } in
              let shape =
                match body with
                | Fields written -> Types.Record (elaborate_fields context written)
                | Variants variants ->
                    Types.Sum
                      (List.map
                         (fun (variant : Syntax.variant) ->
                           {
                             Types.variant_name = variant.name.text;
                             fields = Option.map (elaborate_fields context) variant.fields;
                             indirect = variant.indirect;
                           })
                         variants)
                | Type_todo -> Types.Todo_type
              in
              let derives =
                List.map
                  (fun (_, _, trait) -> trait)
                  (Definition.list_derives_entries context.resolved clauses)
              in
              make_elaborated_interface context
                (Type_interface
                   {
                     type_generics;
                     shape;
                     opaque = (lookups.names.read_declaration key).visibility = Public_opaque;
                     is_tuple;
                     derives;
                   })
          | Constant { name; type_; _ } ->
              let context =
                match name with
                | Plain_name _ -> context
                | Member_name (head, _) ->
                    let _, self_type = elaborate_type_head context path head in
                    { context with self_type = Some self_type }
              in
              make_elaborated_interface context
                (Constant_interface { constant_type = elaborate_type context type_ })
          | Test { uses; _ } ->
              make_elaborated_interface context
                (Test_interface
                   {
                     generics = [];
                     capability_parameters = [];
                     receiver = None;
                     parameters = [];
                     output = Returns Types.unit;
                     uses = elaborate_capabilities context uses;
                     costs = [];
                     modifies = [];
                     specification_only = false;
                     is_update_step = false;
                     capture_free_parameters = [];
                   })
          | Theorem { name; generics; parameters; clauses; _ } ->
              let signature : Syntax.signature =
                { name = Plain_name name; generics; parameters; result = None; clauses }
              in
              let elaborated =
                elaborate_signature context ~owner:path ~head:[] ~self_type:None signature
              in
              make_elaborated_interface context
                (Theorem_interface { elaborated with specification_only = true })
          | Law_proof { trait_; law; type_; _ } -> (
              let generics, for_type = elaborate_type_head context path type_ in
              match elaborate_trait_reference context trait_ with
              | Ok trait ->
                  make_elaborated_interface context
                    (Law_proof_interface { generics; trait; law = law.text; for_type })
              | Error report -> make_elaborated_interface context (Error_interface report))))
