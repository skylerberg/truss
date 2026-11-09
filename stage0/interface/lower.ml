(* Lowering written types to [Types.ty], from a definition's resolved
   form. See TYPECHECKER.md, "Types" and "Checking signatures and
   definitions". Lowering reports what a type position alone shows to be
   wrong: a name that is not a type, a wrong number of arguments, an
   associated type no bound declares. Bounds are checked apart, by
   [Check]. *)

open Syntax
module T = Types

type context = {
  database : Query.database;
  resolved : Resolve.resolved;
  parameters : (id, T.parameter) Hashtbl.t;  (** Generic parameters, by the id of the name that binds them. *)
  bounds : (T.parameter, T.trait_reference list) Hashtbl.t;
  self_type : T.ty option;  (** What [Self] means here. *)
  self_trait : T.trait_reference option;  (** In a trait, the trait [Self] implements. *)
  self_associated : (string * T.ty) list;  (** In an [impl], its associated types. *)
  mutable diagnostics : Diagnostic.t list;
}

let create database resolved =
  {
    database;
    resolved;
    parameters = Hashtbl.create 8;
    bounds = Hashtbl.create 8;
    self_type = None;
    self_trait = None;
    self_associated = [];
    diagnostics = [];
  }

let report context code (span : span) message =
  context.diagnostics <-
    Diagnostic.make ~code:(Types code) (Source.span span.start span.stop) message :: context.diagnostics

let target context (name : name) = context.resolved.names.(name.id)

let parameter_of context (name : name) =
  match target context name with
  | Some (Generic id) -> Hashtbl.find_opt context.parameters id
  | _ -> None

let declare context owner (name : name) =
  let parameter : T.parameter = { owner; name = name.text } in
  Hashtbl.replace context.parameters name.id parameter;
  parameter

(* Types *)

let show_path (path : path) = Resolve.Names.spell_path path

let rec type_ context (written : type_expression) : T.ty =
  match written.kind with
  | Path_type path -> path_type context path
  | Self_type None -> ( match context.self_type with Some self -> self | None -> T.Error)
  | Self_type (Some key) -> self_associated context key
  | Associated (base, key) -> (
      match parameter_of context base with
      | Some parameter -> associated context (T.Parameter parameter) parameter key
      | None -> T.Error)
  | Any_type path -> (
      match trait_reference context path with
      | Some trait -> T.Any trait
      | None -> T.Error)
  | Function_type function_type -> T.Function (function_type_ context function_type)
  | Type_error -> T.Error

and self_associated context (key : name) =
  match List.assoc_opt key.text context.self_associated with
  | Some fixed -> fixed
  | None -> (
      match (context.self_type, context.self_trait) with
      | Some self, Some trait -> (
          match List.assoc_opt key.text trait.associated with
          | Some fixed -> fixed
          | None ->
              if declares context trait.trait key.text then T.Projection { base = self; trait; name = key.text }
              else begin
                report context Unknown_associated_type key.span
                  (Printf.sprintf "`%s` declares no associated type `%s`." (T.show_trait trait) key.text);
                T.Error
              end)
      | _ -> T.Error)

(* Whether a trait, or a trait it requires, declares the associated type. *)
and declares context trait name = Option.is_some (declaring context trait name)

and declaring context trait name =
  List.find_opt
    (fun path ->
      match Query.demand context.database Summary.trait_header path with
      | Some header -> List.mem name header.associated
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
      report context Unknown_associated_type key.span
        (Printf.sprintf "No bound of `%s` declares an associated type `%s`." parameter.name key.text);
      T.Error

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
  | Some (Generic id) -> (
      match Hashtbl.find_opt context.parameters id with
      | Some parameter -> T.Value (T.Value_parameter parameter)
      | None -> T.Type T.Error)
  | Some (Definition path) -> (
      match Query.demand context.database Constants.value_of path with
      | Some value -> T.Value (T.Known value)
      | None -> T.Type T.Error)
  | _ -> T.Type T.Error

and check_arity context (path : path_type) shown expected =
  match expected with
  | None -> ()
  | Some expected ->
      let given = List.length (List.filter (function Constraint _ -> false | _ -> true) path.arguments) in
      if given <> List.length expected then
        report context Arity path.span
          (Printf.sprintf "`%s` takes %d %s, and %d %s given." shown (List.length expected)
             (if List.length expected = 1 then "argument" else "arguments")
             given
             (if given = 1 then "is" else "are"))

and path_type context (path : path_type) : T.ty =
  let shown = show_path path.path in
  match target context path.path.last with
  | Some (Generic id) -> (
      if path.arguments <> [] then begin
        report context Arity path.span
          (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." shown)
      end;
      match Hashtbl.find_opt context.parameters id with
      | Some parameter -> T.Parameter parameter
      | None -> T.Error)
  | Some (Definition definition_path) -> (
      match Intrinsic.builtin_of_path definition_path with
      | Some Never -> T.Never
      | Some Integer -> T.Integer
      | Some _ ->
          check_arity context path shown (Query.demand context.database Summary.generics_of definition_path);
          T.Named { path = definition_path; arguments = arguments context path }
      | None -> (
          match Summary.kind_of context.database definition_path with
          | Some Type ->
              check_arity context path shown (Query.demand context.database Summary.generics_of definition_path);
              T.Named { path = definition_path; arguments = arguments context path }
          | Some (Trait | Capability) ->
              report context Not_a_type path.span
                (Printf.sprintf "`%s` is a trait, not a type. A value of any type with it is `any %s`."
                   shown shown);
              T.Error
          | _ ->
              report context Not_a_type path.span (Printf.sprintf "`%s` is not a type." shown);
              T.Error))
  | _ -> T.Error

(* A bound, an [impl]'s trait, or the trait after [any]. *)
and trait_reference context (path : path_type) : T.trait_reference option =
  let shown = show_path path.path in
  match target context path.path.last with
  | Some (Definition trait) -> (
      match Summary.kind_of context.database trait with
      | Some Trait ->
          check_arity context path shown (Query.demand context.database Summary.generics_of trait);
          let associated =
            List.sort compare
              (List.filter_map
                 (function
                   | Constraint (name, written) -> Some (name.text, type_ context written)
                   | Type_argument _ | Count _ | Count_name _ -> None)
                 path.arguments)
          in
          Some { trait; trait_arguments = arguments context path; associated }
      | _ ->
          report context Not_a_trait path.span (Printf.sprintf "`%s` is not a trait." shown);
          None)
  | _ -> None

and capability context (path : path_type) : T.capability option =
  let shown = show_path path.path in
  match target context path.path.last with
  | Some (Generic id) -> (
      match Hashtbl.find_opt context.parameters id with
      | Some parameter -> Some (T.Capability_parameter parameter)
      | None -> None)
  | Some (Definition path_) when Summary.kind_of context.database path_ = Some Capability ->
      Some (T.Capability path_)
  | Some (Definition _) ->
      report context Not_a_capability path.span (Printf.sprintf "`%s` is not a capability." shown);
      None
  | _ -> None

and capabilities context paths =
  List.sort_uniq compare (List.filter_map (capability context) paths)

and mode = function None -> T.Read | Some Mut -> T.Mut | Some Own -> T.Own

and function_type_ context (written : function_type) : T.function_type =
  {
    inputs = List.map (fun (written_mode, input) -> (mode written_mode, type_ context input)) written.inputs;
    output = T.Returns (match written.output with Some output -> type_ context output | None -> T.unit);
    uses =
      capabilities context
        (List.concat_map
           (fun (clause : clause) -> match clause.kind with Uses paths -> paths | _ -> [])
           written.clauses);
    costs = costs written.clauses;
  }

and costs clauses =
  List.filter_map
    (fun (clause : clause) ->
      match clause.kind with
      | Cost cost ->
          let resource =
            match cost.resource with
            | Time -> "time"
            | Allocations -> "allocations"
            | Allocated_bytes -> "allocated_bytes"
            | Calls _ -> "calls"
          in
          let bound =
            match cost.bound with
            | Finite -> "finite"
            | Big_o _ -> "O(...)"
            | At_most _ -> "<= ..."
            | Exactly _ -> "== ..."
          in
          Some { T.amortized = cost.amortized; resource; bound }
      | _ -> None)
    clauses

(* Generic parameters: every parameter of the list is declared before any
   bound is lowered, so bounds may name each other. *)
let generics context owner (written : generic_parameter list) : T.generic list =
  let declared =
    List.filter_map
      (fun (generic : generic_parameter) ->
        match generic.kind with
        | Type_parameter (name, bounds) -> Some (declare context owner name, `Type bounds)
        | Value_parameter (name, type_) -> Some (declare context owner name, `Value type_)
        | Capability_parameter name -> Some (declare context owner name, `Capability)
        | Generic_error -> None)
      written
  in
  List.map
    (fun (parameter, kind) ->
      match kind with
      | `Type bounds ->
          let bounds = List.filter_map (trait_reference context) bounds in
          Hashtbl.replace context.bounds parameter bounds;
          { T.generic = parameter; kind = Type_generic bounds }
      | `Value _ -> { T.generic = parameter; kind = Value_generic }
      | `Capability -> { T.generic = parameter; kind = Capability_generic })
    declared

let rec mentions_integer = function
  | T.Integer -> true
  | T.Named { arguments; _ } | T.Cursor { arguments; _ } ->
      List.exists (function T.Type type_ -> mentions_integer type_ | T.Value _ -> false) arguments
  | T.Function { inputs; output; _ } ->
      List.exists (fun (_, type_) -> mentions_integer type_) inputs
      || (match output with Returns type_ | Yields (_, type_) | Lends (_, type_) -> mentions_integer type_)
  | T.Projection { base; _ } -> mentions_integer base
  | T.Parameter _ | T.Any _ | T.Never | T.Variable _ | T.Literal _ | T.Hole | T.Error -> false

(* A signature, given the generics of the head before it and the type of
   [self]. *)
let signature context ~owner ~head ~self_type (written : signature) : T.signature =
  let own = generics context owner written.generics in
  let generics_ = head @ own in
  let receiver =
    match written.parameters with
    | { kind = Self_parameter written_mode; _ } :: _ ->
        let receiver : Path.receiver =
          match written_mode with None -> Read | Some Mut -> Mut | Some Own -> Own
        in
        Some (receiver, Option.value ~default:T.Error self_type)
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
  let uses =
    capabilities context
      (List.concat_map (fun (clause : clause) -> match clause.kind with Uses paths -> paths | _ -> []) written.clauses)
  in
  let terminates =
    List.exists
      (fun (clause : clause) -> match clause.kind with Cost { resource = Time; _ } -> true | _ -> false)
      written.clauses
  in
  let result_type = match output with Returns type_ | Yields (_, type_) | Lends (_, type_) -> type_ in
  {
    generics = generics_;
    receiver;
    parameters;
    output;
    uses;
    terminates;
    specification_only =
      mentions_integer result_type || List.exists (fun (parameter : T.parameter_info) -> mentions_integer parameter.type_) parameters;
    stores_functions =
      List.filter_map
        (fun (parameter : T.parameter_info) ->
          match (parameter.mode, parameter.type_) with Own, Function _ -> Some parameter.name | _ -> None)
        parameters;
  }
