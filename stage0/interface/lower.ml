open Syntax
module T = Types

type context = {
  database : Query.context;
  resolved : Resolve.resolved;
  bounds : (T.parameter, T.trait_reference list) Hashtbl.t;
  self_type : T.ty option;  (** What [Self] means here. *)
  self_trait : T.trait_reference option;  (** In a trait, the trait [Self] implements. *)
  self_associated : (string * T.ty) list;  (** In an [impl], its associated types. *)
  self_capabilities : (string * T.capability list) list;
      (** In an [impl], each associated capability set that its trait declares. *)
  diagnostics : Syntax.diagnostic list ref;  (** Shared by every copy of the context. *)
  named : (span * T.ty) list ref;  (** Each named type lowered, for checking its bounds. *)
}

let create database resolved =
  {
    database;
    resolved;
    bounds = Hashtbl.create 8;
    self_type = None;
    self_trait = None;
    self_associated = [];
    self_capabilities = [];
    diagnostics = ref [];
    named = ref [];
  }

let reported context code (span : span) message =
  let diagnostic = Diagnostic.make ~code:(Types code) span message in
  context.diagnostics := diagnostic :: !(context.diagnostics);
  Diagnostic.reported diagnostic

let report context code span message = ignore (reported context code span message)
let error context code span message = T.Error (reported context code span message)
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

(* Types *)

let show_path (path : path) = Resolve.Names.spell_path path

let rec type_ context (written : type_expression) : T.ty =
  match written.kind with
  | Path_type path -> path_type context path
  | Self_type None -> (
      match self context written.span with Ok self -> self | Error report -> T.Error report)
  | Self_type (Some key) -> self_associated context written.span key
  | Associated (base, key) -> (
      match parameter_of context base with
      | Ok parameter -> associated context (T.Parameter parameter) parameter key
      | Error report -> T.Error report)
  | Any_type path -> (
      match trait_reference context path with
      | Ok (trait : T.trait_reference) ->
          (* A method that mentions an associated type could not be called
             through [any] otherwise. *)
          let open_names =
            List.concat_map
              (fun trait_path ->
                match Query.demand context.database Summary.trait_header trait_path with
                | Some header ->
                    List.filter
                      (fun name -> not (List.mem_assoc name trait.associated))
                      header.associated
                | None -> [])
              (Summary.trait_closure context.database trait.trait)
          in
          if open_names <> [] then
            report context Associated_type_not_fixed path.span
              (Printf.sprintf
                 "`any %s` must fix every associated type of its trait, such as `%s[%s = ...]`."
                 (show_path path.path) (show_path path.path) (List.hd open_names));
          T.Any trait
      | Error report -> T.Error report)
  | Function_type function_type -> T.Function (function_type_ context function_type)
  | Type_error -> T.Error (Resolve.Parts.error_node written.span)

(* What [Self] means, which only lowering knows: resolution cannot tell a
   method of a type from a function. *)
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
      | Error report, _ -> T.Error report
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
              (* The projection goes through the trait that declares the
                 name, which may be one this trait requires. *)
              match declaring context trait.trait key.text with
              | Some declaring_trait ->
                  let trait =
                    if Path.equal declaring_trait trait.trait then trait
                    else { T.trait = declaring_trait; trait_arguments = []; associated = [] }
                  in
                  T.Projection { base = self; trait; name = key.text }
              | None ->
                  error context Unknown_associated_type key.span
                    (Printf.sprintf "`%s` declares no associated type `%s`." (T.show_trait trait)
                       key.text))))

(* The trait that declares an associated type, or with [capability] an
   associated capability set: the trait itself, or one that it requires. *)
and declaring ?(capability = false) context trait name =
  List.find_opt
    (fun path ->
      match Query.demand context.database Summary.trait_header path with
      | Some header -> List.mem name (if capability then header.capabilities else header.associated)
      | None -> false)
    (Summary.trait_closure context.database trait)

(* [Items.Element]: the associated type of a generic parameter's bound. *)
and associated context base parameter (key : name) =
  let bounds = Option.value ~default:[] (Hashtbl.find_opt context.bounds parameter) in
  let found =
    List.find_map
      (fun (bound : T.trait_reference) ->
        match List.assoc_opt key.text bound.associated with
        | Some fixed -> Some fixed
        | None -> (
            match declaring context bound.trait key.text with
            | Some declaring_trait ->
                let trait =
                  if Path.equal declaring_trait bound.trait then bound
                  else { T.trait = declaring_trait; trait_arguments = []; associated = [] }
                in
                Some (T.Projection { base; trait; name = key.text })
            | None -> None))
      bounds
  in
  match found with
  | Some found -> found
  | None ->
      error context Unknown_associated_type key.span
        (Printf.sprintf "No bound of `%s` declares an associated type `%s`." parameter.name key.text)

and arguments context (path : path_type) =
  List.filter_map
    (function
      | Type_argument written -> Some (T.Type (type_ context written))
      | Count (value, _) -> Some (T.Value (T.Known value))
      | Count_name name -> Some (count_name context name)
      | Constraint _ -> None)
    path.arguments

and count_name context (name : name) : T.argument =
  match target context name with
  | Some (Value_parameter parameter) -> T.Value (T.Value_parameter parameter)
  | Some (Definition (Constant, path)) -> (
      if not (Constants.is_usize context.database path) then
        T.Type
          (error context Arity name.span
             (Printf.sprintf "`%s` in a type argument must be a constant of type `USize`." name.text))
      else
        match Query.demand context.database Constants.value_of path with
        | Some value -> T.Value (T.Known value)
        | None ->
            T.Type
              (error context Arity name.span
                 (Printf.sprintf
                    "The value of `%s` cannot be worked out: a constant used in a type cannot \
                     refer to itself, and is made of literals, arithmetic, and other such \
                     constants."
                    name.text)))
  | Some (Unknown report) -> T.Type (T.Error report)
  | _ -> bug "`%s` is not resolved as a type argument" name.text

and check_arity context (path : path_type) shown expected =
  match expected with
  | None -> ()
  | Some expected ->
      let given =
        List.length (List.filter (function Constraint _ -> false | _ -> true) path.arguments)
      in
      if given <> List.length expected then
        report context Arity path.span
          (Printf.sprintf "`%s` takes %d %s, and %d %s given." shown (List.length expected)
             (if List.length expected = 1 then "argument" else "arguments")
             given
             (if given = 1 then "is" else "are"))
      else
        (* Each argument must be of its parameter's kind: a type, or a
           [USize] value. *)
        let written = List.filter (function Constraint _ -> false | _ -> true) path.arguments in
        List.iter2
          (fun argument (name, kind) ->
            let is_value = match argument with Count _ | Count_name _ -> true | _ -> false in
            match (kind, is_value) with
            | Summary.Value_kind, false ->
                report context Arity path.span
                  (Printf.sprintf "`%s`'s parameter `%s` is a `USize` value, not a type." shown name)
            | (Summary.Type_kind | Summary.Capability_kind), true ->
                report context Arity path.span
                  (Printf.sprintf "`%s`'s parameter `%s` is a type, not a value." shown name)
            | _ -> ())
          written expected

and path_type context (path : path_type) : T.ty =
  let shown = show_path path.path in
  match target context path.path.last with
  | Some (Type_parameter parameter) ->
      if path.arguments <> [] then begin
        report context Arity path.span
          (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." shown)
      end;
      T.Parameter parameter
  | Some (Capability_parameter _) ->
      error context Not_a_type path.span
        (Printf.sprintf "`%s` is a capability parameter, not a type." shown)
  | Some (Definition (Type, definition_path)) -> (
      match Intrinsic.builtin_of_path definition_path with
      | Some Never -> T.Never
      | Some Integer -> T.Integer
      | Some _ | None ->
          check_arity context path shown
            (Query.demand context.database Summary.generics_of definition_path);
          let type_ = T.Named { path = definition_path; arguments = arguments context path } in
          context.named := (path.span, type_) :: !(context.named);
          type_)
  | Some (Definition (Trait, _)) ->
      error context Not_a_type path.span
        (Printf.sprintf "`%s` is a trait, not a type. A value of any type with it is `any %s`."
           shown shown)
  | Some (Definition (Capability, _)) ->
      error context Not_a_type path.span (Printf.sprintf "`%s` is a capability, not a type." shown)
  | Some (Unknown report) -> T.Error report
  | _ -> bug "`%s` is not resolved as a type" shown

and trait_reference ?(capability = false) context (path : path_type) :
    (T.trait_reference, Diagnostic.reported) Stdlib.result =
  let shown = show_path path.path in
  let found trait : (T.trait_reference, Diagnostic.reported) Stdlib.result =
    check_arity context path shown (Query.demand context.database Summary.generics_of trait);
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
  | Some (Definition (Trait, trait)) -> found trait
  | Some (Definition (Capability, trait)) when capability -> found trait
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

and capability_path context (path : path_type) : T.capability list =
  let shown = show_path path.path in
  match target context path.path.last with
  | Some (Capability_parameter parameter) -> [ T.Capability_parameter parameter ]
  | Some (Type_parameter _) ->
      report context Not_a_capability path.span
        (Printf.sprintf
           "`%s` is a type parameter. A capability parameter is declared `capability %s`." shown
           shown);
      []
  | Some (Definition (Capability, path_)) -> [ T.Capability path_ ]
  | Some (Definition _) ->
      report context Not_a_capability path.span (Printf.sprintf "`%s` is not a capability." shown);
      []
  | Some (Unknown _) -> []
  | _ -> bug "`%s` is not resolved as a capability" shown

(* The associated capability set of a type whose [impl] is not known here:
   the projection through the first of [traits] that declares the set, or
   that requires the trait that does. *)
and capability_projection context base traits (key : name) =
  List.find_map
    (fun (bound : T.trait_reference) ->
      Option.map
        (fun declaring_trait ->
          let trait =
            if Path.equal declaring_trait bound.trait then { bound with associated = [] }
            else { T.trait = declaring_trait; trait_arguments = []; associated = [] }
          in
          T.Capability_projection { base; trait; name = key.text })
        (declaring ~capability:true context bound.trait key.text))
    traits

and capability context (written : capability_reference) : T.capability list =
  match written.kind with
  | Capability_path path -> capability_path context path
  | Self_capabilities key -> (
      match List.assoc_opt key.text context.self_capabilities with
      | Some set -> set
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
                       (T.show_trait trait) key.text);
                  [])))
  | Associated_capabilities (base, key) -> (
      match parameter_of context base with
      | Error _ -> []
      | Ok parameter -> (
          let bounds = Option.value ~default:[] (Hashtbl.find_opt context.bounds parameter) in
          match capability_projection context (T.Parameter parameter) bounds key with
          | Some projection -> [ projection ]
          | None ->
              report context Unknown_associated_capability key.span
                (Printf.sprintf "No bound of `%s` declares an associated capability set `%s`."
                   parameter.name key.text);
              []))

and capabilities context written =
  List.sort_uniq compare (List.concat_map (capability context) written)

and mode = function None -> T.Read | Some Mut -> T.Mut | Some Own -> T.Own

and function_type_ context (written : function_type) : T.function_type =
  {
    inputs =
      List.map
        (fun (written_mode, input) -> (mode written_mode, type_ context input))
        written.inputs;
    output =
      T.Returns (match written.output with Some output -> type_ context output | None -> T.unit);
    uses = uses context written.clauses;
    costs = costs context written.clauses;
  }

and uses context clauses =
  capabilities context
    (List.concat_map
       (fun (clause : clause) -> match clause.kind with Uses written -> written | _ -> [])
       clauses)

(* A function type's cost clauses. What [calls] counts there is a
   capability's calls: a type cannot name a parameter, whose calls a
   function's own clauses count. *)
and costs context clauses =
  let counted (path : path_type) (method_ : name option) : T.resource option =
    let shown = show_path path.path in
    match target context path.path.last with
    | Some (Definition (Capability, capability)) -> (
        match method_ with
        | Some method_
          when Query.demand context.database Resolve.Names.members (capability, method_.text) = []
          ->
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
          let resource : T.resource option =
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
          let bound : T.cost_bound =
            match cost.bound with
            | Finite -> Finite_cost
            | Big_o _ -> Order_of
            | At_most value -> No_more_than (constant value)
            | Exactly value -> Exactly_cost (constant value)
          in
          Option.map (fun resource -> { T.amortized = cost.amortized; resource; bound }) resource
      | _ -> None)
    clauses

let generics context owner (written : generic_parameter list) : T.generic list =
  let parameter (name : name) : T.parameter = { owner; name = name.text } in
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
          { T.generic = parameter; kind = Type_generic bounds }
      | `Value _ -> { T.generic = parameter; kind = Value_generic }
      | `Capability -> { T.generic = parameter; kind = Capability_generic })
    declared

(* The types that exist only in specifications: [Integer], and the
   mathematical collections of [standard::specification]. *)
let specification_type (path : Path.t) =
  match path with Top { module_; _ } -> module_ = Well_known.specification | _ -> false

let rec mentions_integer = function
  | T.Integer -> true
  | T.Named { path; _ } when specification_type path -> true
  | T.Named { arguments; _ } | T.Cursor { arguments; _ } ->
      List.exists
        (function T.Type type_ -> mentions_integer type_ | T.Value _ | T.Capabilities _ -> false)
        arguments
  | T.Function { inputs; output; _ } -> (
      List.exists (fun (_, type_) -> mentions_integer type_) inputs
      ||
      match output with
      | Returns type_ | Yields (_, type_) | Lends (_, type_) -> mentions_integer type_)
  | T.Projection { base; _ } -> mentions_integer base
  | T.Parameter _ | T.Any _ | T.Never | T.Variable _ | T.Literal _ | T.Hole | T.Error _ -> false

(* A signature, given the generics of the head before it and the type of
   [self]. *)
let terminates (clauses : clause list) =
  List.exists
    (fun (clause : clause) ->
      match clause.kind with Cost { resource = Time; _ } -> true | _ -> false)
    clauses

let signature context ~owner ~head ~self_type (written : signature) : T.signature =
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
                T.name = name.text;
                mode = mode written_mode;
                type_ = type_ context written_type;
                has_default = Option.is_some default;
              }
        | Self_parameter _ | Parameter_error -> None)
      written.parameters
  in
  let output =
    match written.result with
    | None -> T.Returns T.unit
    | Some (Returns result) -> T.Returns (type_ context result)
    | Some (Yields (written_mode, result)) -> T.Yields (mode written_mode, type_ context result)
    | Some (Lends (written_mode, result)) -> T.Lends (mode written_mode, type_ context result)
  in
  let terminates = terminates written.clauses in
  let result_type =
    match output with Returns type_ | Yields (_, type_) | Lends (_, type_) -> type_
  in
  {
    generics = generics_;
    receiver;
    parameters;
    output;
    uses = uses context written.clauses;
    terminates;
    specification_only =
      (* [Model]'s method returns a mathematical value. *)
      Well_known.is Model owner || mentions_integer result_type
      || List.exists
           (fun (parameter : T.parameter_info) -> mentions_integer parameter.type_)
           parameters;
    stores_functions =
      List.filter_map
        (fun (parameter : T.parameter_info) ->
          match (parameter.mode, parameter.type_) with
          | Own, Function _ -> Some parameter.name
          | _ -> None)
        parameters;
    transparent = false;
  }
