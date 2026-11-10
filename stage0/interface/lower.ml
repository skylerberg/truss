(* Lowering written types to [Types.ty], from a definition's resolved
   form. Lowering reports what a type position alone shows to be wrong: a name
   that is not a type, a wrong number of arguments, an associated type no
   bound declares. Bounds are checked apart, by [Check]. *)

open Syntax
module T = Types

type context = {
  database : Query.context;
  resolved : Resolve.resolved;
  parameters : (id, T.parameter) Hashtbl.t;
      (** Generic parameters, by the id of the name that binds them. *)
  bounds : (T.parameter, T.trait_reference list) Hashtbl.t;
  self_type : T.ty option;  (** What [Self] means here. *)
  self_trait : T.trait_reference option;  (** In a trait, the trait [Self] implements. *)
  self_associated : (string * T.ty) list;  (** In an [impl], its associated types. *)
  diagnostics : Diagnostic.t list ref;  (** Shared by every copy of the context. *)
  named : (span * T.ty) list ref;  (** Each named type lowered, for checking its bounds. *)
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
    diagnostics = ref [];
    named = ref [];
  }

let reported context code (span : span) message =
  let diagnostic = Diagnostic.make ~code:(Types code) (Source.span span.start span.stop) message in
  context.diagnostics := diagnostic :: !(context.diagnostics);
  Diagnostic.reported diagnostic

let report context code span message = ignore (reported context code span message)
let error context code span message = T.Error (reported context code span message)

(* What resolution and lowering agree on cannot fail; if it does, that is a
   bug in the compiler, and stopping is better than accepting the code. *)
let bug format = Printf.ksprintf (fun message -> invalid_arg ("Lower: " ^ message)) format
let target context (name : name) = context.resolved.names.(name.id)

(* A generic parameter resolution found, by the id of the name that binds
   it. *)
let declared context id (name : name) =
  match Hashtbl.find_opt context.parameters id with
  | Some parameter -> parameter
  | None -> bug "the generic parameter `%s` is not declared" name.text

let parameter_of context (name : name) =
  match target context name with
  | Some (Generic id) -> Ok (declared context id name)
  | Some (Unknown report) -> Error report
  | _ -> bug "`%s` is not resolved as a generic parameter" name.text

let declare context owner (name : name) =
  let parameter : T.parameter = { owner; name = name.text } in
  Hashtbl.replace context.parameters name.id parameter;
  parameter

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
  | Some (Generic id) -> T.Value (T.Value_parameter (declared context id name))
  | Some (Definition path) -> (
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
  | Some (Generic id) ->
      if path.arguments <> [] then begin
        report context Arity path.span
          (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." shown)
      end;
      T.Parameter (declared context id path.path.last)
  | Some (Definition definition_path) -> (
      match Intrinsic.builtin_of_path definition_path with
      | Some Never -> T.Never
      | Some Integer -> T.Integer
      | Some _ ->
          check_arity context path shown
            (Query.demand context.database Summary.generics_of definition_path);
          let type_ = T.Named { path = definition_path; arguments = arguments context path } in
          context.named := (path.span, type_) :: !(context.named);
          type_
      | None -> (
          match Summary.kind_of context.database definition_path with
          | Some Type ->
              check_arity context path shown
                (Query.demand context.database Summary.generics_of definition_path);
              let type_ = T.Named { path = definition_path; arguments = arguments context path } in
              context.named := (path.span, type_) :: !(context.named);
              type_
          | Some (Trait | Capability) ->
              error context Not_a_type path.span
                (Printf.sprintf
                   "`%s` is a trait, not a type. A value of any type with it is `any %s`." shown
                   shown)
          | _ -> error context Not_a_type path.span (Printf.sprintf "`%s` is not a type." shown)))
  | Some (Unknown report) -> T.Error report
  | _ -> bug "`%s` is not resolved as a type" shown

(* A bound, an [impl]'s trait, or the trait after [any]. An [impl] may
   implement a capability too. *)
and trait_reference ?(capability = false) context (path : path_type) :
    (T.trait_reference, Diagnostic.reported) Stdlib.result =
  let shown = show_path path.path in
  match target context path.path.last with
  | Some (Definition trait) -> (
      match Summary.kind_of context.database trait with
      | (Some Trait | Some Capability)
        when capability || Summary.kind_of context.database trait = Some Trait ->
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
      | _ ->
          Error
            (reported context Not_a_trait path.span (Printf.sprintf "`%s` is not a trait." shown)))
  | Some (Generic _) ->
      Error
        (reported context Not_a_trait path.span
           (Printf.sprintf "`%s` is a generic parameter, not a trait." shown))
  | Some (Unknown report) -> Error report
  | _ -> bug "`%s` is not resolved as a trait" shown

and trait_bounds context paths =
  List.filter_map (fun path -> Result.to_option (trait_reference context path)) paths

and capability context (path : path_type) : T.capability option =
  let shown = show_path path.path in
  match target context path.path.last with
  | Some (Generic id) ->
      let parameter = declared context id path.path.last in
      if Hashtbl.mem context.bounds parameter then begin
        report context Not_a_capability path.span
          (Printf.sprintf
             "`%s` is a type parameter. A capability parameter is declared `capability %s`."
             parameter.name parameter.name);
        None
      end
      else Some (T.Capability_parameter parameter)
  | Some (Definition path_) when Summary.kind_of context.database path_ = Some Capability ->
      Some (T.Capability path_)
  | Some (Definition _) ->
      report context Not_a_capability path.span (Printf.sprintf "`%s` is not a capability." shown);
      None
  | _ -> None

and capabilities context paths = List.sort_uniq compare (List.filter_map (capability context) paths)
and mode = function None -> T.Read | Some Mut -> T.Mut | Some Own -> T.Own

and function_type_ context (written : function_type) : T.function_type =
  {
    inputs =
      List.map
        (fun (written_mode, input) -> (mode written_mode, type_ context input))
        written.inputs;
    output =
      T.Returns (match written.output with Some output -> type_ context output | None -> T.unit);
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
          let bounds = trait_bounds context bounds in
          Hashtbl.replace context.bounds parameter bounds;
          { T.generic = parameter; kind = Type_generic bounds }
      | `Value _ -> { T.generic = parameter; kind = Value_generic }
      | `Capability -> { T.generic = parameter; kind = Capability_generic })
    declared

(* The types that exist only in specifications: [Integer], and the
   mathematical collections of [standard::specification]. *)
let specification_type (path : Path.t) =
  match path with
  | Top { module_ = { package = "standard"; modules = [ "specification" ] }; _ } -> true
  | _ -> false

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
  let uses =
    capabilities context
      (List.concat_map
         (fun (clause : clause) -> match clause.kind with Uses paths -> paths | _ -> [])
         written.clauses)
  in
  let terminates =
    List.exists
      (fun (clause : clause) ->
        match clause.kind with Cost { resource = Time; _ } -> true | _ -> false)
      written.clauses
  in
  let result_type =
    match output with Returns type_ | Yields (_, type_) | Lends (_, type_) -> type_
  in
  {
    generics = generics_;
    receiver;
    parameters;
    output;
    uses;
    terminates;
    specification_only =
      (* [Model]'s method gives a value in mathematical terms. *)
      (match owner with
        | Top { module_ = { package = "standard"; modules = [ "core" ] }; name = "Model" } -> true
        | _ -> false)
      || mentions_integer result_type
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
  }
