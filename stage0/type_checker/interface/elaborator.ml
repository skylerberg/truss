module Parameter_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Types.parameter
end))

type t = {
  lookups : Lookups.t;
  resolved : Resolve.resolved;
  bounds : Types.trait_reference list Parameter_table.t;
  broken_parameters : Diagnostic.reported Parameter_table.t;
  self_type : Types.ty option;
  self_trait : Types.trait_reference option;
  self_associated : (string * Types.ty) list;
  self_capabilities : (string * Types.capability_set) list;
  diagnostics : Diagnostic.in_definition list ref;
  named : (Syntax.id * Types.ty) list ref;
  spans : Source.Definition_span.t array;
}

let create lookups resolved ~spans (scope : Environment.scope) =
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
    broken_parameters;
    self_type = scope.self_type;
    self_trait = scope.self_trait;
    self_associated = scope.self_associated;
    self_capabilities = scope.self_capabilities;
    diagnostics = ref [];
    named = ref [];
    spans;
  }

let read_span context id = context.spans.(id)

let list_bounds context parameter =
  Option.value ~default:[] (Parameter_table.find_opt context.bounds parameter)

let find_self_type context = context.self_type
let list_diagnostics context = !(context.diagnostics)
let list_named_types context = !(context.named)

let make_scope context : Environment.scope =
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

let empty_scope : Environment.scope =
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

let record_diagnostic diagnostics ?fixes code (span : Source.Definition_span.t) message =
  let diagnostic = Diagnostic.make ?fixes ~code:(Types code) span message in
  diagnostics := diagnostic :: !diagnostics;
  Diagnostic.make_reported diagnostic

let report_error_type context code span message =
  Types.Error (record_diagnostic context.diagnostics code span message)

let report_error_capability context code span message =
  [ Types.Capability_error (record_diagnostic context.diagnostics code span message) ]

let raise_bug format = Compiler_bug.raise_bug ~stage:"Interface" format
let find_target context (name : Syntax.name) = context.resolved.names.(name.id)

let resolve_parameter context (name : Syntax.name) =
  match find_target context name with
  | Some (Type_parameter parameter) -> (
      match Parameter_table.find_opt context.broken_parameters parameter with
      | Some report -> Error report
      | None -> Ok parameter)
  | Some (Capability_parameter _) ->
      Error
        (record_diagnostic context.diagnostics Unknown_associated_type context.spans.(name.id)
           (Printf.sprintf
              "`%s` is a capability parameter, which has no associated types or capability sets."
              name.text))
  | Some (Unknown report) -> Error report
  | _ -> raise_bug "`%s` is not resolved as a generic parameter" name.text

let show_path (path : Syntax.path) =
  String.concat "::"
    (List.map (fun (name : Syntax.name) -> name.text) (path.modules @ [ path.last ]))

let is_uint64 (lookups : Lookups.t) path =
  match Resolve.Names.find_definition lookups.names path with
  | Some (key, { kind = Constant { type_ = { kind = Path_type written; _ }; _ }; _ }) ->
      (lookups.read_resolved Interface key).names.(written.path.last.id)
      = Some (Definition (Type, Intrinsic.make_builtin_path UInt64))
  | _ -> false

let rec elaborate_type context (written : Syntax.type_expression) : Types.ty =
  match written.kind with
  | Path_type path -> elaborate_path_type context path
  | Self_type None -> (
      match elaborate_self context context.spans.(written.id) with
      | Ok self -> self
      | Error report -> Types.Error report)
  | Self_type (Some key) -> elaborate_self_associated context context.spans.(written.id) key
  | Associated (base, key) -> (
      match resolve_parameter context base with
      | Ok parameter -> elaborate_associated context (Types.Parameter parameter) parameter key
      | Error report -> Types.Error report)
  | Any_type path -> (
      match elaborate_trait_reference context path with
      | Ok (trait : Types.trait_reference) -> (
          let open_names =
            List.concat_map
              (fun trait_path ->
                match context.lookups.find_trait_header trait_path with
                | Some header ->
                    List.filter
                      (fun name -> not (List.mem_assoc name trait.associated))
                      header.associated
                | None -> [])
              (list_trait_closure context.lookups trait.trait)
          in
          match open_names with
          | first :: _ ->
              report_error_type context Associated_type_not_fixed context.spans.(path.id)
                (Printf.sprintf
                   "`any %s` must fix every associated type of its trait, such as `%s[%s = ...]`."
                   (show_path path.path) (show_path path.path) first)
          | [] -> Types.Any trait)
      | Error report -> Types.Error report)
  | Function_type function_type -> (
      match elaborate_function_type context function_type with
      | Ok function_type -> Types.Function function_type
      | Error report -> Types.Error report)
  | Type_error -> Types.Error (Diagnostic.make_recovered context.spans.(written.id))

and elaborate_self context (span : Source.Definition_span.t) =
  match context.self_type with
  | Some self -> Ok self
  | None ->
      Error
        (record_diagnostic context.diagnostics Misplaced_self_type span
           "`Self` names a type only in a type's definition, a trait, an `impl`, or a method.")

and elaborate_self_associated context (span : Source.Definition_span.t) (key : Syntax.name) =
  match List.assoc_opt key.text context.self_associated with
  | Some fixed -> fixed
  | None -> (
      match (elaborate_self context span, context.self_trait) with
      | Error report, _ -> Types.Error report
      | Ok _, None ->
          report_error_type context Unknown_associated_type context.spans.(key.id)
            (Printf.sprintf
               "`Self.%s` names an associated type of a trait, and `Self` is not in a trait or in \
                an `impl` of one here."
               key.text)
      | Ok self, Some trait -> (
          match List.assoc_opt key.text trait.associated with
          | Some fixed -> fixed
          | None -> (
              match find_declaring_trait context trait.trait key.text with
              | Some _ -> Types.Projection { base = self; trait; name = key.text }
              | None ->
                  report_error_type context Unknown_associated_type context.spans.(key.id)
                    (Printf.sprintf "`%s` declares no associated type `%s`."
                       (Types.show_trait trait) key.text))))

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
      report_error_type context Unknown_associated_type context.spans.(key.id)
        (Printf.sprintf "No bound of `%s` declares an associated type `%s`." parameter.name key.text)

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
      if not (is_uint64 context.lookups path) then
        Types.Type
          (report_error_type context Arity context.spans.(name.id)
             (Printf.sprintf "`%s` in a type argument must be a constant of type `UInt64`."
                name.text))
      else
        match context.lookups.find_constant_value path with
        | Some value -> Types.Value (Types.Known value)
        | None ->
            Types.Type
              (report_error_type context Arity context.spans.(name.id)
                 (Printf.sprintf
                    "The value of `%s` cannot be computed: a constant used in a type cannot refer \
                     to itself, and is made of literals, arithmetic, and other such constants."
                    name.text)))
  | Some (Unknown report) -> Types.Type (Types.Error report)
  | _ -> raise_bug "`%s` is not resolved as a type argument" name.text

and check_arity context (path : Syntax.path_type) shown expected :
    (unit, Diagnostic.reported) Stdlib.result =
  match expected with
  | None -> Ok ()
  | Some expected -> (
      let written =
        List.filter (function Syntax.Constraint _ -> false | _ -> true) path.arguments
      in
      let argument_count = List.length written in
      if argument_count <> List.length expected then
        Error
          (record_diagnostic context.diagnostics Arity context.spans.(path.id)
             (Printf.sprintf "`%s` takes %s, and %s given." shown
                (Diagnostic.show_count (List.length expected) "argument" "arguments")
                (Diagnostic.show_count argument_count "is" "are")))
      else
        let errors =
          List.concat
            (List.map2
               (fun argument (name, kind) ->
                 let is_value =
                   match argument with Syntax.Count _ | Count_name _ -> true | _ -> false
                 in
                 let report_argument_kind message =
                   [
                     record_diagnostic context.diagnostics Argument_kind context.spans.(path.id)
                       message;
                   ]
                 in
                 match (kind, is_value) with
                 | Resolve.Names.Value_kind, false ->
                     report_argument_kind
                       (Printf.sprintf "`%s`'s parameter `%s` is a `UInt64` value, not a type."
                          shown name)
                 | (Resolve.Names.Type_kind | Resolve.Names.Capability_kind), true ->
                     report_argument_kind
                       (Printf.sprintf "`%s`'s parameter `%s` is a type, not a value." shown name)
                 | _ -> [])
               written expected)
        in
        match errors with [] -> Ok () | error :: _ -> Error error)

and elaborate_path_type context (path : Syntax.path_type) : Types.ty =
  let shown = show_path path.path in
  match find_target context path.path.last with
  | Some (Type_parameter _) when path.arguments <> [] ->
      report_error_type context Arity context.spans.(path.id)
        (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." shown)
  | Some (Type_parameter parameter) -> (
      match Parameter_table.find_opt context.broken_parameters parameter with
      | Some report -> Types.Error report
      | None -> Types.Parameter parameter)
  | Some (Capability_parameter _) ->
      report_error_type context Not_a_type context.spans.(path.id)
        (Printf.sprintf "`%s` is a capability parameter, not a type." shown)
  | Some (Definition (Type, definition_path)) -> (
      match Intrinsic.find_builtin definition_path with
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
      report_error_type context Not_a_type context.spans.(path.id)
        (Printf.sprintf "`%s` is a trait, not a type. A value of any type with it is `any %s`."
           shown shown)
  | Some (Definition (Capability, _)) ->
      report_error_type context Not_a_type context.spans.(path.id)
        (Printf.sprintf "`%s` is a capability, not a type." shown)
  | Some (Unknown report) -> Types.Error report
  | _ -> raise_bug "`%s` is not resolved as a type" shown

and elaborate_trait_reference ?(capability = false) context (path : Syntax.path_type) :
    (Types.trait_reference, Diagnostic.reported) Stdlib.result =
  let shown = show_path path.path in
  let build_trait_reference trait : (Types.trait_reference, Diagnostic.reported) Stdlib.result =
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
        (record_diagnostic context.diagnostics Not_a_trait context.spans.(path.id)
           (Printf.sprintf "`%s` is not a trait." shown))
  | Some (Type_parameter _ | Capability_parameter _) ->
      Error
        (record_diagnostic context.diagnostics Not_a_trait context.spans.(path.id)
           (Printf.sprintf "`%s` is a generic parameter, not a trait." shown))
  | Some (Unknown report) -> Error report
  | _ -> raise_bug "`%s` is not resolved as a trait" shown

and elaborate_trait_bounds context paths =
  let references = List.map (elaborate_trait_reference context) paths in
  ( List.filter_map Result.to_option references,
    List.find_map (function Error report -> Some report | Ok _ -> None) references )

and elaborate_capability_path context (path : Syntax.path_type) : Types.capability list =
  let shown = show_path path.path in
  match find_target context path.path.last with
  | Some (Capability_parameter parameter) -> [ Types.Capability_parameter parameter ]
  | Some (Type_parameter _) ->
      report_error_capability context Not_a_capability context.spans.(path.id)
        (Printf.sprintf
           "`%s` is a type parameter. A capability parameter is declared `capability %s`." shown
           shown)
  | Some (Definition (Capability, path_)) -> [ Types.Capability path_ ]
  | Some (Definition _) ->
      report_error_capability context Not_a_capability context.spans.(path.id)
        (Printf.sprintf "`%s` is not a capability." shown)
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
  | Self_capabilities key -> (
      match List.assoc_opt key.text context.self_capabilities with
      | Some set -> (set :> Types.capability list)
      | None -> (
          match (elaborate_self context context.spans.(written.id), context.self_trait) with
          | Error report, _ -> [ Types.Capability_error report ]
          | Ok _, None ->
              report_error_capability context Unknown_associated_capability context.spans.(key.id)
                (Printf.sprintf
                   "`Self.%s` names an associated capability set of a trait, and `Self` is not in \
                    a trait or in an `impl` of one here."
                   key.text)
          | Ok self, Some trait -> (
              match find_capability_projection context self [ trait ] key with
              | Some projection -> [ projection ]
              | None ->
                  report_error_capability context Unknown_associated_capability
                    context.spans.(key.id)
                    (Printf.sprintf "`%s` declares no associated capability set `%s`."
                       (Types.show_trait trait) key.text))))
  | Associated_capabilities (base, key) -> (
      match resolve_parameter context base with
      | Error report -> [ Types.Capability_error report ]
      | Ok parameter -> (
          let bounds = list_bounds context parameter in
          match find_capability_projection context (Types.Parameter parameter) bounds key with
          | Some projection -> [ projection ]
          | None ->
              report_error_capability context Unknown_associated_capability context.spans.(key.id)
                (Printf.sprintf "No bound of `%s` declares an associated capability set `%s`."
                   parameter.name key.text)))

and elaborate_capabilities context written =
  Types.make_capability_set (List.concat_map (elaborate_capability context) written)

and elaborate_mode = function
  | None -> Types.Read
  | Some Syntax.Mut -> Types.Mut
  | Some Own -> Types.Own

and elaborate_function_type context (written : Syntax.function_type) :
    (Types.function_type, Diagnostic.reported) Stdlib.result =
  let inputs =
    List.map
      (fun (input : Syntax.function_input) ->
        (elaborate_mode input.mode, elaborate_type context input.type_))
      written.inputs
  in
  let output =
    match written.output with Some output -> elaborate_type context output | None -> Types.unit
  in
  let uses = elaborate_uses context written.clauses in
  match elaborate_costs context written.clauses with
  | Ok costs -> Ok { inputs; output; uses; costs }
  | Error report -> Error report

and elaborate_uses context clauses =
  elaborate_capabilities context
    (List.concat_map
       (fun (clause : Syntax.clause) -> match clause.kind with Uses written -> written | _ -> [])
       clauses)

and elaborate_costs context clauses : (Types.cost list, Diagnostic.reported) Stdlib.result =
  let report_error code span message =
    Error (record_diagnostic context.diagnostics code span message)
  in
  let elaborate_counted (path : Syntax.path_type) (method_ : Syntax.name option) :
      (Types.resource, Diagnostic.reported) Stdlib.result =
    let shown = show_path path.path in
    match find_target context path.path.last with
    | Some (Definition (Capability, capability)) -> (
        match method_ with
        | Some method_ when context.lookups.names.list_members capability method_.text = [] ->
            report_error Unknown_member context.spans.(method_.id)
              (Printf.sprintf "`%s` has no method `%s`." shown method_.text)
        | _ ->
            Ok
              (Calls
                 {
                   capability;
                   method_ = Option.map (fun (method_ : Syntax.name) -> method_.text) method_;
                 }))
    | Some (Unknown report) -> Error report
    | _ ->
        report_error Not_a_capability context.spans.(path.id)
          (Printf.sprintf "`calls` counts the calls of a capability, and `%s` is not one." shown)
  in
  let costs =
    List.filter_map
      (fun (clause : Syntax.clause) ->
        match clause.kind with
        | Cost cost ->
            let resource : (Types.resource, Diagnostic.reported) Stdlib.result =
              match cost.resource with
              | Time -> Ok Time
              | Allocations -> Ok Allocations
              | Allocated_bytes -> Ok Allocated_bytes
              | Calls (Call_capability path) -> elaborate_counted path None
              | Calls (Call_method (path, method_)) -> elaborate_counted path (Some method_)
              | Calls (Call_parameter name) ->
                  report_error Not_a_capability context.spans.(name.id)
                    (Printf.sprintf
                       "A function type's `calls` counts the calls of a capability, as in \
                        `calls(FileRead)`: a type cannot name `%s`. Calls through a parameter are \
                        counted in a function's own clauses."
                       name.text)
            in
            let evaluate_constant (value : Syntax.expression) =
              match value.kind with Integer value -> Some value | _ -> None
            in
            let bound : Types.cost_bound =
              match cost.bound with
              | Finite -> Finite_cost
              | Big_o _ -> Order_of
              | At_most value -> No_more_than (evaluate_constant value)
              | Exactly value -> Exactly_cost (evaluate_constant value)
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
        | Capability_parameter name -> Some (make_parameter name, `Capability)
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
      | `Value _ -> { Types.generic = parameter; kind = Value_generic }
      | `Capability -> { Types.generic = parameter; kind = Capability_generic })
    declared

let mentions_specification_only_type type_ =
  Option.is_some (Types.find_specification_only_type type_)

let terminates (clauses : Syntax.clause list) =
  List.exists
    (fun (clause : Syntax.clause) ->
      match clause.kind with Cost { resource = Time; _ } -> true | _ -> false)
    clauses

let elaborate_signature context ~owner ~head ~self_type (written : Syntax.signature) :
    Types.signature =
  let own = elaborate_generics context owner written.generics in
  let generics_ = head @ own in
  let receiver =
    match written.parameters with
    | { kind = Self_parameter mode; _ } :: _ ->
        let receiver : Path.receiver =
          match mode with None -> Read | Some Mut -> Mut | Some Own -> Own
        in
        Option.map (fun self -> (receiver, self)) self_type
    | _ -> None
  in
  let parameters =
    List.filter_map
      (fun (parameter : Syntax.parameter) ->
        match parameter.kind with
        | Named_parameter { name; mode; type_; default } ->
            Some
              {
                Types.name = name.text;
                mode = elaborate_mode mode;
                type_ = elaborate_type context type_;
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
  let terminates = terminates written.clauses in
  let result_type = Types.extract_result_type output in
  {
    generics = generics_;
    receiver;
    parameters;
    output;
    uses = elaborate_uses context written.clauses;
    terminates;
    specification_only =
      Well_known.is Model owner
      || mentions_specification_only_type result_type
      || List.exists
           (fun (parameter : Types.parameter_info) ->
             mentions_specification_only_type parameter.type_)
           parameters;
    capture_free_parameters =
      List.filter_map
        (fun (parameter : Types.parameter_info) ->
          match (parameter.mode, parameter.type_) with
          | Own, Function _ -> Some parameter.name
          | _ -> None)
        parameters;
  }

let elaborate_type_head context owner (head : Syntax.type_head) =
  let generics = elaborate_generics context owner head.generics in
  match find_target context head.path.last with
  | Some (Definition (Type, type_path)) ->
      let type_ =
        match Resolve.Names.find_generics context.lookups.names type_path with
        | Some expected when List.length expected <> List.length generics ->
            report_error_type context Arity context.spans.(head.id)
              (Printf.sprintf "`%s` takes %s, and this head names %d." (show_path head.path)
                 (Diagnostic.show_count (List.length expected) "generic parameter"
                    "generic parameters")
                 (List.length generics))
        | _ -> (
            match Intrinsic.find_builtin type_path with
            | Some Never -> Types.Never
            | Some Integer -> Types.Integer
            | _ ->
                Types.Named { path = type_path; arguments = Types.list_generic_arguments generics })
      in
      (generics, type_)
  | Some (Definition (((Trait | Capability) as kind), _)) ->
      ( generics,
        report_error_type context Not_a_type context.spans.(head.id)
          (Printf.sprintf "`%s` is %s, not a type, so it has no methods, constants, or `impl`s."
             (show_path head.path)
             (Resolve.Names.show_kind (Resolve.Names.convert_named kind))) )
  | Some (Unknown report) -> (generics, Types.Error report)
  | _ -> raise_bug "the type head `%s` is not resolved" (show_path head.path)

let elaborate_fields context (written : Syntax.field list) =
  List.stable_sort
    (fun (left : Types.field) (right : Types.field) ->
      String.compare left.field_name right.field_name)
    (List.filter_map
       (fun (field : Syntax.field) ->
         match field.kind with
         | Field_declaration { name; type_; default } ->
             let field_type = elaborate_type context type_ in
             let field_type =
               match Types.find_specification_only_type field_type with
               | None -> field_type
               | Some specification_type ->
                   report_error_type context Specification_only context.spans.(type_.id)
                     (Printf.sprintf
                        "`%s` exists only in specifications and has no representation in code that \
                         runs, so it is not the type of a field."
                        (Types.show specification_type))
             in
             Some
               {
                 Types.field_name = name.text;
                 field_type;
                 field_has_default = Option.is_some default;
               }
         | Field_error -> None)
       written)

let elaborate_container (context : t) (path : Path.t) (definition : Syntax.definition) :
    (Environment.container, Diagnostic.reported) Stdlib.result * t =
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
                      elaborate_capabilities { context with self_capabilities = sets } written
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
                    else if List.exists is_defined_by_this_impl (set :> Types.capability list) then
                      ( name.text,
                        Types.make_capability_set
                          (report_error_capability context Unknown_associated_capability
                             context.spans.(name.id)
                             (Printf.sprintf
                                "`%s` is defined from itself, or from a set that this `impl` \
                                 defines after it."
                                name.text)) )
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

let elaborate_header (lookups : Lookups.t) (key : Resolve.Names.key) =
  let resolved = lookups.read_resolved Interface key in
  if Resolve.Names.is_broken lookups.names key Header then Error []
  else
    match
      elaborate_container
        (create lookups resolved ~spans:(lookups.names.read_spans key) empty_scope)
        key.path
        (lookups.names.read_definition key)
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
    scope = make_scope context;
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

let make_container_interface lookups key (header : Environment.header) :
    Environment.elaborated_interface =
  let methods = list_methods lookups key in
  let interface =
    match header.container with
    | Trait_parts { trait_generics; requires; associated_types; associated_capabilities; laws } ->
        Environment.Trait_interface
          {
            trait_generics;
            requires;
            associated_types;
            associated_capabilities;
            laws;
            methods;
            is_capability = false;
          }
    | Capability_parts ->
        Trait_interface
          {
            trait_generics = [];
            requires = [];
            associated_types = [];
            associated_capabilities = [];
            laws = [];
            methods;
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
  { interface; diagnostics = []; named = header.container_named; scope = header.container_scope }

let elaborate_member (lookups : Lookups.t) ~path ~spans resolved (definition : Syntax.definition)
    (header : Environment.header) =
  let context = create lookups resolved ~spans header.container_scope in
  match definition.kind with
  | Function { signature; _ } | Method_declaration signature ->
      make_elaborated_interface context
        (Function_interface
           (elaborate_signature
              { context with self_capabilities = [] }
              ~owner:path ~head:[] ~self_type:header.container_scope.self_type signature))
  | _ ->
      make_elaborated_interface context
        (Error_interface (Diagnostic.make_recovered spans.(definition.id)))

let elaborate_definition (lookups : Lookups.t) (key : Resolve.Names.key) =
  let resolved = lookups.read_resolved Interface key in
  let definition = lookups.names.read_definition key in
  let spans = lookups.names.read_spans key in
  let path = key.path in
  Compiler_bug.run_while_doing ~stage:"Interface" (Resolve.Names.show_key key) (fun () ->
      let context = create lookups resolved ~spans empty_scope in
      let recover () =
        make_elaborated_interface context
          (Error_interface (Diagnostic.make_recovered spans.(definition.id)))
      in
      match
        ( Resolve.Names.find_recovery_report lookups.names key Header,
          Option.map lookups.find_header (lookups.names.find_container key) )
      with
      | Some report, _ -> make_elaborated_interface context (Error_interface report)
      | None, Some None -> recover ()
      | None, Some (Some header) -> elaborate_member lookups ~path ~spans resolved definition header
      | None, None -> (
          match definition.kind with
          | Trait _ | Capability _ | Impl _ -> (
              match lookups.find_header key with
              | Some header -> make_container_interface lookups key header
              | None -> raise_bug "`%s` has no header" (Resolve.Names.show_key key))
          | Method_declaration _ | Definition_error _ -> recover ()
          | Function { signature; _ } ->
              let head, self_type =
                match signature.name with
                | Plain_name _ -> ([], None)
                | Member_name (head, _) ->
                    let generics, self = elaborate_type_head context path head in
                    (generics, Some self)
              in
              let context = { context with self_type } in
              make_elaborated_interface context
                (Function_interface
                   (elaborate_signature context ~owner:path ~head ~self_type signature))
          | Type_definition { generics; body; clauses; _ } ->
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
                List.concat_map
                  (fun (clause : Syntax.type_clause) ->
                    match clause.kind with
                    | Derives traits ->
                        List.filter_map
                          (fun (trait : Syntax.path_type) ->
                            match find_target context trait.path.last with
                            | Some (Definition (_, trait)) -> Some trait
                            | _ -> None)
                          traits
                    | Type_invariant _ | Potential _ -> [])
                  clauses
              in
              make_elaborated_interface context
                (Type_interface
                   { type_generics; shape; opaque = definition.visibility = Public_opaque; derives })
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
                (Test_interface (elaborate_capabilities context uses))
          | Theorem { name; generics; parameters; clauses; _ } ->
              let signature : Syntax.signature =
                { name = Plain_name name; generics; parameters; result = None; clauses }
              in
              make_elaborated_interface context
                (Theorem_interface
                   {
                     (elaborate_signature context ~owner:path ~head:[] ~self_type:None signature) with
                     specification_only = true;
                   })
          | Law_proof { trait_; law; type_; _ } -> (
              let generics, for_type = elaborate_type_head context path type_ in
              match elaborate_trait_reference context trait_ with
              | Ok trait ->
                  make_elaborated_interface context
                    (Law_proof_interface { generics; trait; law = law.text; for_type })
              | Error report -> make_elaborated_interface context (Error_interface report))))
