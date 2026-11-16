open Environment
open Syntax
module Names = Resolve.Names

type t = {
  lookups : Lookups.t;
  resolved : Resolve.resolved;
  bounds : (Types.parameter, Types.trait_reference list) Hashtbl.t;
  self_type : Types.ty option;
  self_trait : Types.trait_reference option;
  self_associated : (string * Types.ty) list;
  self_capabilities : (string * Types.capability_set) list;
  diagnostics : Diagnostic.in_definition list ref;
  named : (id * Types.ty) list ref;
  spans : Source.Definition_span.t array;
}

let create lookups resolved ~spans (scope : Environment.scope) =
  let bounds = Hashtbl.create 8 in
  List.iter (fun (parameter, traits) -> Hashtbl.replace bounds parameter traits) scope.bounds;
  {
    lookups;
    resolved;
    bounds;
    self_type = scope.self_type;
    self_trait = scope.self_trait;
    self_associated = scope.self_associated;
    self_capabilities = scope.self_capabilities;
    diagnostics = ref [];
    named = ref [];
    spans;
  }

let make_scope context : Environment.scope =
  {
    self_type = context.self_type;
    self_trait = context.self_trait;
    self_associated = context.self_associated;
    self_capabilities = context.self_capabilities;
    bounds =
      List.sort compare
        (Hashtbl.fold
           (fun parameter bounds bounds_by_parameter -> (parameter, bounds) :: bounds_by_parameter)
           context.bounds []);
  }

let empty_scope =
  { self_type = None; self_trait = None; self_associated = []; self_capabilities = []; bounds = [] }

let list_trait_closure (lookups : Lookups.t) path =
  let closure = ref [] in
  let rec visit path =
    if not (List.exists (Path.equal path) !closure) then begin
      closure := path :: !closure;
      match lookups.trait_header path with
      | Some header -> List.iter visit header.required
      | None -> ()
    end
  in
  visit path;
  List.rev !closure

let record_diagnostic diagnostics ?fixes code (span : Source.Definition_span.t) message =
  let diagnostic = Diagnostic.make ?fixes ~code:(Types code) span message in
  diagnostics := diagnostic :: !diagnostics;
  Diagnostic.reported diagnostic

let report context code span message =
  ignore (record_diagnostic context.diagnostics code span message)

let report_error_type context code span message =
  Types.Error (record_diagnostic context.diagnostics code span message)

let bug format = Compiler_bug.bug ~stage:"Interface" format
let find_target context (name : name) = context.resolved.names.(name.id)

let find_parameter context (name : name) =
  match find_target context name with
  | Some (Type_parameter parameter) -> Ok parameter
  | Some (Capability_parameter _) ->
      Error
        (record_diagnostic context.diagnostics Unknown_associated_type context.spans.(name.id)
           (Printf.sprintf
              "`%s` is a capability parameter, which has no associated types or capability sets."
              name.text))
  | Some (Unknown report) -> Error report
  | _ -> bug "`%s` is not resolved as a generic parameter" name.text

let show_path (path : path) =
  String.concat "::" (List.map (fun (name : name) -> name.text) (path.modules @ [ path.last ]))

let is_uint64 (lookups : Lookups.t) path =
  match Names.definition_of_path lookups.names path with
  | Some (key, { kind = Constant { type_ = { kind = Path_type written; _ }; _ }; _ }) ->
      (lookups.resolved Interface key).names.(written.path.last.id)
      = Some (Definition (Type, Intrinsic.builtin_path UInt64))
  | _ -> false

let rec elaborate_type context (written : type_expression) : Types.ty =
  match written.kind with
  | Path_type path -> elaborate_path_type context path
  | Self_type None -> (
      match elaborate_self context context.spans.(written.id) with
      | Ok self -> self
      | Error report -> Types.Error report)
  | Self_type (Some key) -> elaborate_self_associated context context.spans.(written.id) key
  | Associated (base, key) -> (
      match find_parameter context base with
      | Ok parameter -> elaborate_associated context (Types.Parameter parameter) parameter key
      | Error report -> Types.Error report)
  | Any_type path -> (
      match elaborate_trait_reference context path with
      | Ok (trait : Types.trait_reference) ->
          let open_names =
            List.concat_map
              (fun trait_path ->
                match context.lookups.trait_header trait_path with
                | Some header ->
                    List.filter
                      (fun name -> not (List.mem_assoc name trait.associated))
                      header.associated
                | None -> [])
              (list_trait_closure context.lookups trait.trait)
          in
          if open_names <> [] then
            report context Associated_type_not_fixed context.spans.(path.id)
              (Printf.sprintf
                 "`any %s` must fix every associated type of its trait, such as `%s[%s = ...]`."
                 (show_path path.path) (show_path path.path) (List.hd open_names));
          Types.Any trait
      | Error report -> Types.Error report)
  | Function_type function_type -> Types.Function (elaborate_function_type context function_type)
  | Type_error -> Types.Error (Resolve.Parts.recovery_report context.spans.(written.id))

and elaborate_self context (span : Source.Definition_span.t) =
  match context.self_type with
  | Some self -> Ok self
  | None ->
      Error
        (record_diagnostic context.diagnostics Misplaced_self_type span
           "`Self` names a type only in a type's definition, a trait, an `impl`, or a method.")

and elaborate_self_associated context (span : Source.Definition_span.t) (key : name) =
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
              | Some declaring_trait ->
                  let trait =
                    if Path.equal declaring_trait trait.trait then trait
                    else { Types.trait = declaring_trait; trait_arguments = []; associated = [] }
                  in
                  Types.Projection { base = self; trait; name = key.text }
              | None ->
                  report_error_type context Unknown_associated_type context.spans.(key.id)
                    (Printf.sprintf "`%s` declares no associated type `%s`."
                       (Types.show_trait trait) key.text))))

and find_declaring_trait ?(capability = false) context trait name =
  List.find_opt
    (fun path ->
      match context.lookups.trait_header path with
      | Some header -> List.mem name (if capability then header.capabilities else header.associated)
      | None -> false)
    (list_trait_closure context.lookups trait)

and elaborate_associated context base parameter (key : name) =
  let bounds = Option.value ~default:[] (Hashtbl.find_opt context.bounds parameter) in
  let associated_type =
    List.find_map
      (fun (bound : Types.trait_reference) ->
        match List.assoc_opt key.text bound.associated with
        | Some fixed -> Some fixed
        | None -> (
            match find_declaring_trait context bound.trait key.text with
            | Some declaring_trait ->
                let trait =
                  if Path.equal declaring_trait bound.trait then bound
                  else { Types.trait = declaring_trait; trait_arguments = []; associated = [] }
                in
                Some (Types.Projection { base; trait; name = key.text })
            | None -> None))
      bounds
  in
  match associated_type with
  | Some associated_type -> associated_type
  | None ->
      report_error_type context Unknown_associated_type context.spans.(key.id)
        (Printf.sprintf "No bound of `%s` declares an associated type `%s`." parameter.name key.text)

and elaborate_arguments context (path : path_type) =
  List.filter_map
    (function
      | Type_argument written -> Some (Types.Type (elaborate_type context written))
      | Count (value, _) -> Some (Types.Value (Types.Known value))
      | Count_name name -> Some (elaborate_count_name context name)
      | Constraint _ -> None)
    path.arguments

and elaborate_count_name context (name : name) : Types.argument =
  match find_target context name with
  | Some (Value_parameter parameter) -> Types.Value (Types.Value_parameter parameter)
  | Some (Definition (Constant, path)) -> (
      if not (is_uint64 context.lookups path) then
        Types.Type
          (report_error_type context Arity context.spans.(name.id)
             (Printf.sprintf "`%s` in a type argument must be a constant of type `UInt64`."
                name.text))
      else
        match context.lookups.constant_value path with
        | Some value -> Types.Value (Types.Known value)
        | None ->
            Types.Type
              (report_error_type context Arity context.spans.(name.id)
                 (Printf.sprintf
                    "The value of `%s` cannot be computed: a constant used in a type cannot refer \
                     to itself, and is made of literals, arithmetic, and other such constants."
                    name.text)))
  | Some (Unknown report) -> Types.Type (Types.Error report)
  | _ -> bug "`%s` is not resolved as a type argument" name.text

and check_arity context (path : path_type) shown expected =
  match expected with
  | None -> ()
  | Some expected ->
      let argument_count =
        List.length (List.filter (function Constraint _ -> false | _ -> true) path.arguments)
      in
      if argument_count <> List.length expected then
        report context Arity context.spans.(path.id)
          (Printf.sprintf "`%s` takes %d %s, and %d %s given." shown (List.length expected)
             (if List.length expected = 1 then "argument" else "arguments")
             argument_count
             (if argument_count = 1 then "is" else "are"))
      else
        let written = List.filter (function Constraint _ -> false | _ -> true) path.arguments in
        List.iter2
          (fun argument (name, kind) ->
            let is_value = match argument with Count _ | Count_name _ -> true | _ -> false in
            match (kind, is_value) with
            | Resolve.Names.Value_kind, false ->
                report context Argument_kind context.spans.(path.id)
                  (Printf.sprintf "`%s`'s parameter `%s` is a `UInt64` value, not a type." shown
                     name)
            | (Resolve.Names.Type_kind | Resolve.Names.Capability_kind), true ->
                report context Argument_kind context.spans.(path.id)
                  (Printf.sprintf "`%s`'s parameter `%s` is a type, not a value." shown name)
            | _ -> ())
          written expected

and elaborate_path_type context (path : path_type) : Types.ty =
  let shown = show_path path.path in
  match find_target context path.path.last with
  | Some (Type_parameter parameter) ->
      if path.arguments <> [] then begin
        report context Arity context.spans.(path.id)
          (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." shown)
      end;
      Types.Parameter parameter
  | Some (Capability_parameter _) ->
      report_error_type context Not_a_type context.spans.(path.id)
        (Printf.sprintf "`%s` is a capability parameter, not a type." shown)
  | Some (Definition (Type, definition_path)) -> (
      match Intrinsic.builtin_of_path definition_path with
      | Some Never -> Types.Never
      | Some Integer -> Types.Integer
      | Some _ | None ->
          check_arity context path shown (Names.generics_of context.lookups.names definition_path);
          let type_ =
            Types.Named { path = definition_path; arguments = elaborate_arguments context path }
          in
          context.named := (path.id, type_) :: !(context.named);
          type_)
  | Some (Definition (Trait, _)) ->
      report_error_type context Not_a_type context.spans.(path.id)
        (Printf.sprintf "`%s` is a trait, not a type. A value of any type with it is `any %s`."
           shown shown)
  | Some (Definition (Capability, _)) ->
      report_error_type context Not_a_type context.spans.(path.id)
        (Printf.sprintf "`%s` is a capability, not a type." shown)
  | Some (Unknown report) -> Types.Error report
  | _ -> bug "`%s` is not resolved as a type" shown

and elaborate_trait_reference ?(capability = false) context (path : path_type) :
    (Types.trait_reference, Diagnostic.reported) Stdlib.result =
  let shown = show_path path.path in
  let trait_reference_of trait : (Types.trait_reference, Diagnostic.reported) Stdlib.result =
    check_arity context path shown (Names.generics_of context.lookups.names trait);
    let associated =
      List.sort compare
        (List.filter_map
           (function
             | Constraint (name, written) -> Some (name.text, elaborate_type context written)
             | Type_argument _ | Count _ | Count_name _ -> None)
           path.arguments)
    in
    Ok { trait; trait_arguments = elaborate_arguments context path; associated }
  in
  match find_target context path.path.last with
  | Some (Definition (Trait, trait)) -> trait_reference_of trait
  | Some (Definition (Capability, trait)) when capability -> trait_reference_of trait
  | Some (Definition _) ->
      Error
        (record_diagnostic context.diagnostics Not_a_trait context.spans.(path.id)
           (Printf.sprintf "`%s` is not a trait." shown))
  | Some (Type_parameter _ | Capability_parameter _) ->
      Error
        (record_diagnostic context.diagnostics Not_a_trait context.spans.(path.id)
           (Printf.sprintf "`%s` is a generic parameter, not a trait." shown))
  | Some (Unknown report) -> Error report
  | _ -> bug "`%s` is not resolved as a trait" shown

and elaborate_trait_bounds context paths =
  List.filter_map (fun path -> Result.to_option (elaborate_trait_reference context path)) paths

and elaborate_capability_path context (path : path_type) : Types.capability list =
  let shown = show_path path.path in
  match find_target context path.path.last with
  | Some (Capability_parameter parameter) -> [ Types.Capability_parameter parameter ]
  | Some (Type_parameter _) ->
      report context Not_a_capability context.spans.(path.id)
        (Printf.sprintf
           "`%s` is a type parameter. A capability parameter is declared `capability %s`." shown
           shown);
      []
  | Some (Definition (Capability, path_)) -> [ Types.Capability path_ ]
  | Some (Definition _) ->
      report context Not_a_capability context.spans.(path.id)
        (Printf.sprintf "`%s` is not a capability." shown);
      []
  | Some (Unknown _) -> []
  | _ -> bug "`%s` is not resolved as a capability" shown

and find_capability_projection context base traits (key : name) =
  List.find_map
    (fun (bound : Types.trait_reference) ->
      Option.map
        (fun declaring_trait ->
          let trait =
            if Path.equal declaring_trait bound.trait then { bound with associated = [] }
            else { Types.trait = declaring_trait; trait_arguments = []; associated = [] }
          in
          Types.Capability_projection { base; trait; name = key.text })
        (find_declaring_trait ~capability:true context bound.trait key.text))
    traits

and elaborate_capability context (written : capability_reference) : Types.capability list =
  match written.kind with
  | Capability_path path -> elaborate_capability_path context path
  | Self_capabilities key -> (
      match List.assoc_opt key.text context.self_capabilities with
      | Some set -> (set :> Types.capability list)
      | None -> (
          match (elaborate_self context context.spans.(written.id), context.self_trait) with
          | Error _, _ -> []
          | Ok _, None ->
              report context Unknown_associated_capability context.spans.(key.id)
                (Printf.sprintf
                   "`Self.%s` names an associated capability set of a trait, and `Self` is not in \
                    a trait or in an `impl` of one here."
                   key.text);
              []
          | Ok self, Some trait -> (
              match find_capability_projection context self [ trait ] key with
              | Some projection -> [ projection ]
              | None ->
                  report context Unknown_associated_capability context.spans.(key.id)
                    (Printf.sprintf "`%s` declares no associated capability set `%s`."
                       (Types.show_trait trait) key.text);
                  [])))
  | Associated_capabilities (base, key) -> (
      match find_parameter context base with
      | Error _ -> []
      | Ok parameter -> (
          let bounds = Option.value ~default:[] (Hashtbl.find_opt context.bounds parameter) in
          match find_capability_projection context (Types.Parameter parameter) bounds key with
          | Some projection -> [ projection ]
          | None ->
              report context Unknown_associated_capability context.spans.(key.id)
                (Printf.sprintf "No bound of `%s` declares an associated capability set `%s`."
                   parameter.name key.text);
              []))

and elaborate_capabilities context written =
  Types.make_capability_set (List.concat_map (elaborate_capability context) written)

and elaborate_mode = function None -> Types.Read | Some Mut -> Types.Mut | Some Own -> Types.Own

and elaborate_function_type context (written : function_type) : Types.function_type =
  {
    inputs =
      List.map
        (fun (input : function_input) ->
          (elaborate_mode input.mode, elaborate_type context input.type_))
        written.inputs;
    output =
      (match written.output with
      | Some output -> elaborate_type context output
      | None -> Types.unit);
    uses = elaborate_uses context written.clauses;
    costs = elaborate_costs context written.clauses;
  }

and elaborate_uses context clauses =
  elaborate_capabilities context
    (List.concat_map
       (fun (clause : clause) -> match clause.kind with Uses written -> written | _ -> [])
       clauses)

and elaborate_costs context clauses =
  let counted (path : path_type) (method_ : name option) : Types.resource option =
    let shown = show_path path.path in
    match find_target context path.path.last with
    | Some (Definition (Capability, capability)) -> (
        match method_ with
        | Some method_ when context.lookups.names.members capability method_.text = [] ->
            report context Unknown_member context.spans.(method_.id)
              (Printf.sprintf "`%s` has no method `%s`." shown method_.text);
            None
        | _ ->
            Some
              (Calls
                 { capability; method_ = Option.map (fun (method_ : name) -> method_.text) method_ })
        )
    | Some (Unknown _) -> None
    | _ ->
        report context Not_a_capability context.spans.(path.id)
          (Printf.sprintf "`calls` counts the calls of a capability, and `%s` is not one." shown);
        None
  in
  List.filter_map
    (fun (clause : clause) ->
      match clause.kind with
      | Cost cost ->
          let resource : Types.resource option =
            match cost.resource with
            | Time -> Some Time
            | Allocations -> Some Allocations
            | Allocated_bytes -> Some Allocated_bytes
            | Calls (Call_capability path) -> counted path None
            | Calls (Call_method (path, method_)) -> counted path (Some method_)
            | Calls (Call_parameter name) ->
                report context Not_a_capability context.spans.(name.id)
                  (Printf.sprintf
                     "A function type's `calls` counts the calls of a capability, as in \
                      `calls(FileRead)`: a type cannot name `%s`. Calls through a parameter are \
                      counted in a function's own clauses."
                     name.text);
                None
          in
          let constant (value : expression) =
            match value.kind with Integer value -> Some value | _ -> None
          in
          let bound : Types.cost_bound =
            match cost.bound with
            | Finite -> Finite_cost
            | Big_o _ -> Order_of
            | At_most value -> No_more_than (constant value)
            | Exactly value -> Exactly_cost (constant value)
          in
          Option.map
            (fun resource -> { Types.amortized = cost.amortized; resource; bound })
            resource
      | _ -> None)
    clauses

let elaborate_generics context owner (written : generic_parameter list) : Types.generic list =
  let parameter (name : name) : Types.parameter = { owner; name = name.text } in
  let declared =
    List.filter_map
      (fun (generic : generic_parameter) ->
        match generic.kind with
        | Type_parameter (name, bounds) -> Some (parameter name, `Type bounds)
        | Value_parameter (name, type_) -> Some (parameter name, `Value type_)
        | Capability_parameter name -> Some (parameter name, `Capability)
        | Generic_error -> None)
      written
  in
  List.map
    (fun (parameter, kind) ->
      match kind with
      | `Type bounds ->
          let bounds = elaborate_trait_bounds context bounds in
          Hashtbl.replace context.bounds parameter bounds;
          { Types.generic = parameter; kind = Type_generic bounds }
      | `Value _ -> { Types.generic = parameter; kind = Value_generic }
      | `Capability -> { Types.generic = parameter; kind = Capability_generic })
    declared

let mentions_specification_only_type type_ =
  Option.is_some (Types.find_specification_only_type type_)

let terminates (clauses : clause list) =
  List.exists
    (fun (clause : clause) ->
      match clause.kind with Cost { resource = Time; _ } -> true | _ -> false)
    clauses

let elaborate_signature context ~owner ~head ~self_type (written : signature) : Types.signature =
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
      (fun (parameter : parameter) ->
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

let elaborate_type_head context owner (head : type_head) =
  let generics = elaborate_generics context owner head.generics in
  match find_target context head.path.last with
  | Some (Definition (Type, type_path)) ->
      (match Names.generics_of context.lookups.names type_path with
      | Some expected when List.length expected <> List.length generics ->
          report context Arity context.spans.(head.id)
            (Printf.sprintf "`%s` takes %d generic %s, and this head names %d."
               (show_path head.path) (List.length expected)
               (if List.length expected = 1 then "parameter" else "parameters")
               (List.length generics))
      | _ -> ());
      let arguments = Types.list_generic_arguments generics in
      let type_ =
        match Intrinsic.builtin_of_path type_path with
        | Some Never -> Types.Never
        | Some Integer -> Types.Integer
        | _ -> Types.Named { path = type_path; arguments }
      in
      (generics, type_)
  | Some (Definition (((Trait | Capability) as kind), _)) ->
      ( generics,
        report_error_type context Not_a_type context.spans.(head.id)
          (Printf.sprintf "`%s` is %s, not a type, so it has no methods, constants, or `impl`s."
             (show_path head.path)
             (Names.kind_name (Names.kind_of_named kind))) )
  | Some (Unknown report) -> (generics, Types.Error report)
  | _ -> bug "the type head `%s` is not resolved" (show_path head.path)

let make_self_parameter trait : Types.parameter = { owner = trait; name = "Self" }

let elaborate_fields context (written : field list) =
  List.stable_sort
    (fun (left : Types.field) (right : Types.field) ->
      String.compare left.field_name right.field_name)
    (List.filter_map
       (fun (field : field) ->
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

let elaborate_container (context : t) (path : Path.t) (definition : definition) :
    (Environment.container, Diagnostic.reported) Stdlib.result * t =
  match definition.kind with
  | Trait { generics; requires; members; _ } ->
      let trait_generics = elaborate_generics context path generics in
      let self_parameter = make_self_parameter path in
      let self_trait : Types.trait_reference =
        {
          trait = path;
          trait_arguments = Types.list_generic_arguments trait_generics;
          associated = [];
        }
      in
      Hashtbl.replace context.bounds self_parameter [ self_trait ];
      let context =
        {
          context with
          self_type = Some (Types.Parameter self_parameter);
          self_trait = Some self_trait;
        }
      in
      let requires = elaborate_trait_bounds context requires in
      let associated_types =
        List.filter_map
          (fun (line : trait_member node) ->
            match line.kind with
            | Associated_type (name, bounds) ->
                Some
                  {
                    Types.associated_name = name.text;
                    associated_bounds = elaborate_trait_bounds context bounds;
                  }
            | Associated_capability _ | Law _ | Trait_member_error -> None)
          members
      in
      let associated_capabilities =
        List.filter_map
          (fun (line : trait_member node) ->
            match line.kind with Associated_capability name -> Some name.text | _ -> None)
          members
      in
      let laws =
        List.filter_map
          (fun (line : trait_member node) ->
            match line.kind with
            | Law law ->
                Some
                  ( law.name.text,
                    List.filter_map
                      (fun (parameter : parameter) ->
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
                 (fun (line : impl_member node) ->
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
              (fun sets (line : impl_member node) ->
                match line.kind with
                | Capability_definition (name, written) ->
                    let set =
                      elaborate_capabilities { context with self_capabilities = sets } written
                    in
                    let is_defined_by_this_impl = function
                      | Types.Capability_projection { base; trait; _ } ->
                          Types.equal base for_type && Path.equal trait.trait implements.trait
                      | _ -> false
                    in
                    if List.exists is_defined_by_this_impl (set :> Types.capability list) then begin
                      report context Unknown_associated_capability context.spans.(name.id)
                        (Printf.sprintf
                           "`%s` is defined from itself, or from a set that this `impl` defines \
                            after it."
                           name.text);
                      sets
                    end
                    else if List.mem_assoc name.text sets then sets
                    else (name.text, set) :: sets
                | Associated_definition _ | Impl_member_error -> sets)
              [] members
          in
          let declared =
            match context.lookups.trait_header implements.trait with
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

let elaborate_header (lookups : Lookups.t) (key : Names.key) =
  let resolved = lookups.resolved Interface key in
  if Names.is_broken lookups.names key Header then Error []
  else
    match
      elaborate_container
        (create lookups resolved ~spans:(lookups.names.spans key) empty_scope)
        key.path (lookups.names.definition key)
    with
    | _, context when !(context.diagnostics) <> [] -> Error (List.rev !(context.diagnostics))
    | Error _, _ -> Error []
    | Ok container, context ->
        Ok
          {
            container;
            container_scope = make_scope context;
            container_named = List.rev !(context.named);
          }

let make_elaborated_interface context interface : elaborated_interface =
  {
    interface;
    diagnostics = List.rev !(context.diagnostics);
    named = List.rev !(context.named);
    scope = make_scope context;
  }

let list_methods (lookups : Lookups.t) key =
  List.filter_map
    (fun (member : Names.key) ->
      match (member.path, lookups.names.definition member) with
      | Method { name; receiver; _ }, { kind = Function _; _ } ->
          Some { Types.method_name = name; method_receiver = receiver; provided = true }
      | Method { name; receiver; _ }, { kind = Method_declaration _; _ } ->
          Some { Types.method_name = name; method_receiver = receiver; provided = false }
      | _ -> None)
    (lookups.names.contained key)

let make_container_interface lookups key (header : header) : elaborated_interface =
  let methods = list_methods lookups key in
  let interface =
    match header.container with
    | Trait_parts { trait_generics; requires; associated_types; associated_capabilities; laws } ->
        Trait_interface
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

let elaborate_member (lookups : Lookups.t) ~path ~spans resolved (definition : definition)
    (header : header) =
  let context = create lookups resolved ~spans header.container_scope in
  match definition.kind with
  | Function { signature; _ } | Method_declaration signature ->
      let impl_generics, impl_uses =
        match header.container with
        | Impl_parts { impl_generics; impl_uses; _ } -> (impl_generics, impl_uses)
        | Trait_parts _ | Capability_parts -> ([], Types.no_capabilities)
      in
      let elaborated =
        Types.add_impl_generics_and_uses ~impl_generics ~impl_uses
          (elaborate_signature context ~owner:path ~head:[]
             ~self_type:header.container_scope.self_type signature)
      in
      let inherits_termination =
        match (path, header.container_scope.self_trait) with
        | Method { name; receiver; _ }, Some (implements : Types.trait_reference) -> (
            match
              Option.map lookups.names.definition
                (lookups.names.key (Method { owner = implements.trait; name; receiver }))
            with
            | Some { kind = Function { signature = declared; _ } | Method_declaration declared; _ }
              ->
                terminates declared.clauses
            | _ -> false)
        | _ -> false
      in
      make_elaborated_interface context
        (Function_interface
           { elaborated with terminates = elaborated.terminates || inherits_termination })
  | _ ->
      make_elaborated_interface context
        (Error_interface (Resolve.Parts.recovery_report spans.(definition.id)))

let elaborate_definition (lookups : Lookups.t) (key : Names.key) =
  let resolved = lookups.resolved Interface key in
  let definition = lookups.names.definition key in
  let spans = lookups.names.spans key in
  let path = key.path in
  Compiler_bug.while_doing ~stage:"Interface" (Names.show_key key) (fun () ->
      let context = create lookups resolved ~spans empty_scope in
      let recovered () =
        make_elaborated_interface context
          (Error_interface (Resolve.Parts.recovery_report spans.(definition.id)))
      in
      match
        ( Names.recovery_report lookups.names key Header,
          Option.map lookups.header (lookups.names.container key) )
      with
      | Some report, _ -> make_elaborated_interface context (Error_interface report)
      | None, Some None -> recovered ()
      | None, Some (Some header) -> elaborate_member lookups ~path ~spans resolved definition header
      | None, None -> (
          match definition.kind with
          | Trait _ | Capability _ | Impl _ -> (
              match lookups.header key with
              | Some header -> make_container_interface lookups key header
              | None -> bug "`%s` has no header" (Names.show_key key))
          | Method_declaration _ | Definition_error _ -> recovered ()
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
                         (fun (variant : variant) ->
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
                  (fun (clause : type_clause) ->
                    match clause.kind with
                    | Derives traits ->
                        List.filter_map
                          (fun (trait : path_type) ->
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
          | Theorem { generics; parameters; clauses; _ } ->
              let signature : signature =
                {
                  name = Plain_name { text = ""; id = definition.id };
                  generics;
                  parameters;
                  result = None;
                  clauses;
                }
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
