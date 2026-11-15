open Syntax
module Names = Resolve.Names

type context = {
  lookups : Lookups.t;
  resolved : Resolve.resolved;
  bounds : (Types.parameter, Types.trait_reference list) Hashtbl.t;
  self_type : Types.ty option;
  self_trait : Types.trait_reference option;
  self_associated : (string * Types.ty) list;
  self_capabilities : (string * Types.capability_set) list;
  diagnostics : Syntax.diagnostic list ref;
  named : (id * Types.ty) list ref;
}

let create lookups resolved (scope : Environment.scope) =
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
  }

let scope context : Environment.scope =
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

let rec trait_closure context ?(seen = []) path =
  if List.exists (Path.equal path) seen then []
  else
    match context.lookups.trait_header path with
    | None -> [ path ]
    | Some header ->
        path
        :: List.concat_map
             (fun required -> trait_closure context ~seen:(path :: seen) required)
             header.required
        |> List.fold_left
             (fun acc path -> if List.exists (Path.equal path) acc then acc else acc @ [ path ])
             []

let reported context code (span : span) message =
  let diagnostic = Diagnostic.make ~code:(Types code) span message in
  context.diagnostics := diagnostic :: !(context.diagnostics);
  Diagnostic.reported diagnostic

let report context code span message = ignore (reported context code span message)
let error context code span message = Types.Error (reported context code span message)
let bug format = Compiler_bug.bug ~stage:"Interface" format
let target context (name : name) = context.resolved.names.(name.id)

let parameter_of context (name : name) =
  match target context name with
  | Some (Type_parameter parameter) -> Ok parameter
  | Some (Capability_parameter _) ->
      Error
        (reported context Unknown_associated_type name.span
           (Printf.sprintf
              "`%s` is a capability parameter, which has no associated types or capability sets."
              name.text))
  | Some (Unknown report) -> Error report
  | _ -> bug "`%s` is not resolved as a generic parameter" name.text

let show_path (path : path) = Resolve.Names.spell_path path

let rec type_ context (written : type_expression) : Types.ty =
  match written.kind with
  | Path_type path -> path_type context path
  | Self_type None -> (
      match self context written.span with Ok self -> self | Error report -> Types.Error report)
  | Self_type (Some key) -> self_associated context written.span key
  | Associated (base, key) -> (
      match parameter_of context base with
      | Ok parameter -> associated context (Types.Parameter parameter) parameter key
      | Error report -> Types.Error report)
  | Any_type path -> (
      match trait_reference context path with
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
              (trait_closure context trait.trait)
          in
          if open_names <> [] then
            report context Associated_type_not_fixed path.span
              (Printf.sprintf
                 "`any %s` must fix every associated type of its trait, such as `%s[%s = ...]`."
                 (show_path path.path) (show_path path.path) (List.hd open_names));
          Types.Any trait
      | Error report -> Types.Error report)
  | Function_type function_type -> Types.Function (function_type_ context function_type)
  | Type_error -> Types.Error (Resolve.Parts.recovery_report written.span)

and self context (span : span) =
  match context.self_type with
  | Some self -> Ok self
  | None ->
      Error
        (reported context Misplaced_self_type span
           "`Self` names a type only in a type's definition, a trait, an `impl`, or a method.")

and self_associated context (span : span) (key : name) =
  match List.assoc_opt key.text context.self_associated with
  | Some fixed -> fixed
  | None -> (
      match (self context span, context.self_trait) with
      | Error report, _ -> Types.Error report
      | Ok _, None ->
          error context Unknown_associated_type key.span
            (Printf.sprintf
               "`Self.%s` names an associated type of a trait, and `Self` is not in a trait or in \
                an `impl` of one here."
               key.text)
      | Ok self, Some trait -> (
          match List.assoc_opt key.text trait.associated with
          | Some fixed -> fixed
          | None -> (
              match declaring context trait.trait key.text with
              | Some declaring_trait ->
                  let trait =
                    if Path.equal declaring_trait trait.trait then trait
                    else { Types.trait = declaring_trait; trait_arguments = []; associated = [] }
                  in
                  Types.Projection { base = self; trait; name = key.text }
              | None ->
                  error context Unknown_associated_type key.span
                    (Printf.sprintf "`%s` declares no associated type `%s`."
                       (Types.show_trait trait) key.text))))

and declaring ?(capability = false) context trait name =
  List.find_opt
    (fun path ->
      match context.lookups.trait_header path with
      | Some header -> List.mem name (if capability then header.capabilities else header.associated)
      | None -> false)
    (trait_closure context trait)

and associated context base parameter (key : name) =
  let bounds = Option.value ~default:[] (Hashtbl.find_opt context.bounds parameter) in
  let associated_type =
    List.find_map
      (fun (bound : Types.trait_reference) ->
        match List.assoc_opt key.text bound.associated with
        | Some fixed -> Some fixed
        | None -> (
            match declaring context bound.trait key.text with
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
      error context Unknown_associated_type key.span
        (Printf.sprintf "No bound of `%s` declares an associated type `%s`." parameter.name key.text)

and arguments context (path : path_type) =
  List.filter_map
    (function
      | Type_argument written -> Some (Types.Type (type_ context written))
      | Count (value, _) -> Some (Types.Value (Types.Known value))
      | Count_name name -> Some (count_name context name)
      | Constraint _ -> None)
    path.arguments

and count_name context (name : name) : Types.argument =
  match target context name with
  | Some (Value_parameter parameter) -> Types.Value (Types.Value_parameter parameter)
  | Some (Definition (Constant, path)) -> (
      if not (Constants.is_uint64 context.lookups path) then
        Types.Type
          (error context Arity name.span
             (Printf.sprintf "`%s` in a type argument must be a constant of type `UInt64`."
                name.text))
      else
        match context.lookups.constant_value path with
        | Some value -> Types.Value (Types.Known value)
        | None ->
            Types.Type
              (error context Arity name.span
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
        report context Arity path.span
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
                report context Argument_kind path.span
                  (Printf.sprintf "`%s`'s parameter `%s` is a `UInt64` value, not a type." shown
                     name)
            | (Resolve.Names.Type_kind | Resolve.Names.Capability_kind), true ->
                report context Argument_kind path.span
                  (Printf.sprintf "`%s`'s parameter `%s` is a type, not a value." shown name)
            | _ -> ())
          written expected

and path_type context (path : path_type) : Types.ty =
  let shown = show_path path.path in
  match target context path.path.last with
  | Some (Type_parameter parameter) ->
      if path.arguments <> [] then begin
        report context Arity path.span
          (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." shown)
      end;
      Types.Parameter parameter
  | Some (Capability_parameter _) ->
      error context Not_a_type path.span
        (Printf.sprintf "`%s` is a capability parameter, not a type." shown)
  | Some (Definition (Type, definition_path)) -> (
      match Intrinsic.builtin_of_path definition_path with
      | Some Never -> Types.Never
      | Some Integer -> Types.Integer
      | Some _ | None ->
          check_arity context path shown (Names.generics_of context.lookups.names definition_path);
          let type_ = Types.Named { path = definition_path; arguments = arguments context path } in
          context.named := (path.id, type_) :: !(context.named);
          type_)
  | Some (Definition (Trait, _)) ->
      error context Not_a_type path.span
        (Printf.sprintf "`%s` is a trait, not a type. A value of any type with it is `any %s`."
           shown shown)
  | Some (Definition (Capability, _)) ->
      error context Not_a_type path.span (Printf.sprintf "`%s` is a capability, not a type." shown)
  | Some (Unknown report) -> Types.Error report
  | _ -> bug "`%s` is not resolved as a type" shown

and trait_reference ?(capability = false) context (path : path_type) :
    (Types.trait_reference, Diagnostic.reported) Stdlib.result =
  let shown = show_path path.path in
  let trait_reference_of trait : (Types.trait_reference, Diagnostic.reported) Stdlib.result =
    check_arity context path shown (Names.generics_of context.lookups.names trait);
    let associated =
      List.sort compare
        (List.filter_map
           (function
             | Constraint (name, written) -> Some (name.text, type_ context written)
             | Type_argument _ | Count _ | Count_name _ -> None)
           path.arguments)
    in
    Ok { trait; trait_arguments = arguments context path; associated }
  in
  match target context path.path.last with
  | Some (Definition (Trait, trait)) -> trait_reference_of trait
  | Some (Definition (Capability, trait)) when capability -> trait_reference_of trait
  | Some (Definition _) ->
      Error (reported context Not_a_trait path.span (Printf.sprintf "`%s` is not a trait." shown))
  | Some (Type_parameter _ | Capability_parameter _) ->
      Error
        (reported context Not_a_trait path.span
           (Printf.sprintf "`%s` is a generic parameter, not a trait." shown))
  | Some (Unknown report) -> Error report
  | _ -> bug "`%s` is not resolved as a trait" shown

and trait_bounds context paths =
  List.filter_map (fun path -> Result.to_option (trait_reference context path)) paths

and capability_path context (path : path_type) : Types.capability list =
  let shown = show_path path.path in
  match target context path.path.last with
  | Some (Capability_parameter parameter) -> [ Types.Capability_parameter parameter ]
  | Some (Type_parameter _) ->
      report context Not_a_capability path.span
        (Printf.sprintf
           "`%s` is a type parameter. A capability parameter is declared `capability %s`." shown
           shown);
      []
  | Some (Definition (Capability, path_)) -> [ Types.Capability path_ ]
  | Some (Definition _) ->
      report context Not_a_capability path.span (Printf.sprintf "`%s` is not a capability." shown);
      []
  | Some (Unknown _) -> []
  | _ -> bug "`%s` is not resolved as a capability" shown

and capability_projection context base traits (key : name) =
  List.find_map
    (fun (bound : Types.trait_reference) ->
      Option.map
        (fun declaring_trait ->
          let trait =
            if Path.equal declaring_trait bound.trait then { bound with associated = [] }
            else { Types.trait = declaring_trait; trait_arguments = []; associated = [] }
          in
          Types.Capability_projection { base; trait; name = key.text })
        (declaring ~capability:true context bound.trait key.text))
    traits

and capability context (written : capability_reference) : Types.capability list =
  match written.kind with
  | Capability_path path -> capability_path context path
  | Self_capabilities key -> (
      match List.assoc_opt key.text context.self_capabilities with
      | Some set -> (set :> Types.capability list)
      | None -> (
          match (self context written.span, context.self_trait) with
          | Error _, _ -> []
          | Ok _, None ->
              report context Unknown_associated_capability key.span
                (Printf.sprintf
                   "`Self.%s` names an associated capability set of a trait, and `Self` is not in \
                    a trait or in an `impl` of one here."
                   key.text);
              []
          | Ok self, Some trait -> (
              match capability_projection context self [ trait ] key with
              | Some projection -> [ projection ]
              | None ->
                  report context Unknown_associated_capability key.span
                    (Printf.sprintf "`%s` declares no associated capability set `%s`."
                       (Types.show_trait trait) key.text);
                  [])))
  | Associated_capabilities (base, key) -> (
      match parameter_of context base with
      | Error _ -> []
      | Ok parameter -> (
          let bounds = Option.value ~default:[] (Hashtbl.find_opt context.bounds parameter) in
          match capability_projection context (Types.Parameter parameter) bounds key with
          | Some projection -> [ projection ]
          | None ->
              report context Unknown_associated_capability key.span
                (Printf.sprintf "No bound of `%s` declares an associated capability set `%s`."
                   parameter.name key.text);
              []))

and capabilities context written =
  Types.capability_set (List.concat_map (capability context) written)

and mode = function None -> Types.Read | Some Mut -> Types.Mut | Some Own -> Types.Own

and function_type_ context (written : function_type) : Types.function_type =
  {
    inputs =
      List.map
        (fun (input : function_input) -> (mode input.mode, type_ context input.type_))
        written.inputs;
    output =
      Types.Returns
        (match written.output with Some output -> type_ context output | None -> Types.unit);
    uses = uses context written.clauses;
    costs = costs context written.clauses;
  }

and uses context clauses =
  capabilities context
    (List.concat_map
       (fun (clause : clause) -> match clause.kind with Uses written -> written | _ -> [])
       clauses)

and costs context clauses =
  let counted (path : path_type) (method_ : name option) : Types.resource option =
    let shown = show_path path.path in
    match target context path.path.last with
    | Some (Definition (Capability, capability)) -> (
        match method_ with
        | Some method_ when context.lookups.names.members capability method_.text = [] ->
            report context Unknown_member method_.span
              (Printf.sprintf "`%s` has no method `%s`." shown method_.text);
            None
        | _ ->
            Some
              (Calls
                 { capability; method_ = Option.map (fun (method_ : name) -> method_.text) method_ })
        )
    | Some (Unknown _) -> None
    | _ ->
        report context Not_a_capability path.span
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
                report context Not_a_capability name.span
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

let generics context owner (written : generic_parameter list) : Types.generic list =
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
          let bounds = trait_bounds context bounds in
          Hashtbl.replace context.bounds parameter bounds;
          { Types.generic = parameter; kind = Type_generic bounds }
      | `Value _ -> { Types.generic = parameter; kind = Value_generic }
      | `Capability -> { Types.generic = parameter; kind = Capability_generic })
    declared

let specification_type (path : Path.t) =
  match path with Top { module_; _ } -> module_ = Well_known.specification | _ -> false

let mentions_integer =
  Types.exists (function
    | Types.Integer -> true
    | Types.Named { path; _ } -> specification_type path
    | _ -> false)

let terminates (clauses : clause list) =
  List.exists
    (fun (clause : clause) ->
      match clause.kind with Cost { resource = Time; _ } -> true | _ -> false)
    clauses

let signature context ~owner ~head ~self_type (written : signature) : Types.signature =
  let own = generics context owner written.generics in
  let generics_ = head @ own in
  let receiver =
    match written.parameters with
    | { kind = Self_parameter written_mode; _ } :: _ ->
        let receiver : Path.receiver =
          match written_mode with None -> Read | Some Mut -> Mut | Some Own -> Own
        in
        Option.map (fun self -> (receiver, self)) self_type
    | _ -> None
  in
  let parameters =
    List.filter_map
      (fun (parameter : parameter) ->
        match parameter.kind with
        | Named_parameter { name; mode = written_mode; type_ = written_type; default } ->
            Some
              {
                Types.name = name.text;
                mode = mode written_mode;
                type_ = type_ context written_type;
                has_default = Option.is_some default;
              }
        | Self_parameter _ | Parameter_error -> None)
      written.parameters
  in
  let output =
    match written.result with
    | None -> Types.Returns Types.unit
    | Some (Returns result) -> Types.Returns (type_ context result)
    | Some (Lends (written_mode, result)) -> Types.Lends (mode written_mode, type_ context result)
  in
  let terminates = terminates written.clauses in
  let result_type = Types.result_type output in
  {
    generics = generics_;
    receiver;
    parameters;
    output;
    uses = uses context written.clauses;
    terminates;
    specification_only =
      Well_known.is Model owner || mentions_integer result_type
      || List.exists
           (fun (parameter : Types.parameter_info) -> mentions_integer parameter.type_)
           parameters;
    capture_free_parameters =
      List.filter_map
        (fun (parameter : Types.parameter_info) ->
          match (parameter.mode, parameter.type_) with
          | Own, Function _ -> Some parameter.name
          | _ -> None)
        parameters;
  }
