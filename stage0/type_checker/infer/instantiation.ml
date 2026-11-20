let check_evidence_grants (state : State.state) (span : Source.Definition_span.t) evidence =
  let impls =
    Interface.Grants.list_evidence_uses state.lookups.interface
      ~list_bounds:(State.lookup_bounds state) evidence
  in
  state.evidence_packages <-
    List.map (fun (impl, _, _) -> Path.locate_package impl) impls @ state.evidence_packages;
  List.iter
    (fun message ->
      state.diagnostics <-
        Diagnostic.make ~code:(Capabilities Not_granted) span message :: state.diagnostics)
    (Interface.Grants.describe_missing_in_impls state.lookups.interface ~package:state.package impls)

let make_error_type_at state code (value : Syntax.expression) message =
  match State.find_head state value with
  | Some { target = Unknown report; _ } -> Types.Error report
  | _ -> State.make_error_type state code (State.read_span state value.id) message

type static_ =
  | Static_type of Types.ty
  | Static_trait of Path.t * Types.argument list option
  | Static_capability of Path.t

let check_grants_when_final state at subject (trait : Types.trait_reference) =
  State.check_when_final state (fun () ->
      let subject = State.normalize state subject in
      if not (Types.contains_unsolved subject) then
        Option.iter (check_evidence_grants state at)
          (State.find_evidence state subject { trait with associated = [] }))

let require_bounds state at ?of_type ?projections generics substitution =
  List.iter
    (fun (argument, bound) ->
      Solver.require state (Bound { at; of_type }) ?projections argument bound;
      check_grants_when_final state at argument bound)
    (Interface.Impls.list_required_bounds generics substitution)

let make_fresh_arguments (state : State.state) (path : Path.t) =
  match Interface.Definition.find_type_interface state.lookups.interface path with
  | Some interface -> State.make_fresh_generic_arguments state interface.type_generics
  | None -> []

let make_fresh_trait_reference (state : State.state) (trait : Path.t) =
  Types.make_trait_reference trait
    ~arguments:
      (match Interface.Definition.find_trait_interface state.lookups.interface trait with
      | Some interface -> State.make_fresh_generic_arguments state interface.trait_generics
      | None -> [])

let require_type_bounds (state : State.state) span path arguments =
  match Interface.Definition.find_type_interface state.lookups.interface path with
  | Some interface ->
      require_bounds state span
        ~of_type:(Types.Named { path; arguments })
        interface.type_generics
        (Types.make_substitution interface.type_generics arguments)
  | None -> ()

let instantiate_type state span path =
  let arguments = make_fresh_arguments state path in
  require_type_bounds state span path arguments;
  arguments

let rec find_static state (value : Syntax.expression) : static_ option =
  match (value.kind, State.find_head state value) with
  | Self_type_value, _ ->
      Option.map
        (fun self -> Static_type self)
        (Interface.Elaborator.find_self_type (State.read_context state))
  | _, Some { target = Definition (Type, path); type_arguments; _ } ->
      Some (Static_type (check_named_type state value path type_arguments))
  | _, Some { target = Type_parameter parameter; name; type_arguments } -> (
      match type_arguments with
      | Some _ ->
          Some
            (Static_type
               (State.make_error_type state Arity (State.read_span state value.id)
                  (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." name.text)))
      | None -> Some (Static_type (Types.Parameter parameter)))
  | _, Some { target = Definition (Trait, path); type_arguments; _ } -> (
      match Option.map (check_written_arguments state) type_arguments with
      | None -> Some (Static_trait (path, None))
      | Some (Ok arguments) -> Some (Static_trait (path, Some arguments))
      | Some (Error error) -> Some (Static_type error))
  | _, Some { target = Definition (Capability, path); _ } -> Some (Static_capability path)
  | Parenthesized inner, None -> find_static state inner
  | _ -> None

and check_named_type state (value : Syntax.expression) path type_arguments =
  let make_type arguments =
    match Well_known.find_builtin_type path with
    | Some Never -> Types.Never
    | Some Integer -> Types.Integer
    | _ -> Types.Named { path; arguments }
  in
  match type_arguments with
  | None -> make_type (instantiate_type state (State.read_span state value.id) path)
  | Some items -> (
      match check_written_arguments state items with
      | Error error -> error
      | Ok arguments -> (
          match Resolve.Names.find_generics state.lookups.interface.names path with
          | Some expected when List.length expected <> List.length arguments ->
              State.make_error_type state Arity (State.read_span state value.id)
                (Printf.sprintf "`%s` takes %s, and %s given."
                   (Types.show (Named { path; arguments = [] }))
                   (Diagnostic.show_count (List.length expected) "argument" "arguments")
                   (Diagnostic.show_count (List.length arguments) "is" "are"))
          | _ ->
              require_type_bounds state (State.read_span state value.id) path arguments;
              make_type arguments))

and check_written_arguments state items : (Types.argument list, Types.ty) result =
  let arguments =
    List.filter_map
      (function
        | Syntax.Item item -> Some (check_type_argument state item) | Item_constraint _ -> None)
      items
  in
  let errors =
    List.filter_map
      (function
        | Syntax.Item _ -> None
        | Item_constraint ((name : Syntax.name), _) ->
            Some
              (State.make_error_type state Arity (State.read_span state name.id)
                 "An associated type is fixed where a type is written, as in `any Trait[Name = \
                  Type]`, not among type arguments in an expression."))
      items
  in
  match errors with [] -> Ok arguments | error :: _ -> Error error

and check_type_argument state (value : Syntax.expression) : Types.argument =
  match (value.kind, State.find_head state value) with
  | Integer value, _ -> Types.Value (Known value)
  | _, Some { target = Value_parameter parameter; _ } -> Types.Value (Value_parameter parameter)
  | _, Some { target = Definition (Constant, path); name; _ } -> (
      match Interface.Constants.evaluate_count state.lookups.interface path ~written:name.text with
      | Ok value -> Types.Value (Known value)
      | Error message ->
          Types.Type (State.make_error_type state Arity (State.read_span state value.id) message))
  | _ -> (
      match find_static state value with
      | Some (Static_type type_) -> Types.Type type_
      | Some (Static_trait _ | Static_capability _) | None ->
          Types.Type
            (make_error_type_at state Not_a_type value
               "A type argument is a type, or a `UInt64` value."))

type instance = {
  declared : Types.signature;
  signature : Types.signature;
  substitution : Types.substitution;
  instantiation : Types.instantiation;
  flatten : Types.ty -> Types.ty;
}

let instantiate (state : State.state) (span : Source.Definition_span.t)
    ?(extra = Types.no_substitution) (signature : Types.signature) =
  let instantiation : Types.instantiation =
    {
      type_arguments = State.make_fresh_generic_arguments state signature.generics;
      capability_arguments =
        List.map
          (fun (parameter : Types.parameter) ->
            (parameter.name, Unify.make_fresh_capability_variable state.unifier))
          signature.capability_parameters;
    }
  in
  let substitution =
    Types.combine_substitutions (Types.make_signature_substitution signature instantiation) extra
  in
  let projections = ref [] in
  require_bounds state span ~projections signature.generics substitution;
  let flatten = Solver.flatten state (Bound { at = span; of_type = None }) ~projections in
  let substituted = Types.substitute_signature substitution signature in
  {
    declared = signature;
    signature =
      {
        substituted with
        output =
          (match substituted.output with
          | Returns output -> Returns (flatten output)
          | Lends (mode, part) -> Lends (mode, flatten part));
      };
    substitution;
    instantiation;
    flatten;
  }

let find_intrinsic_signature path =
  Option.map Intrinsic_signatures.make_signature (Intrinsic.find_operation path)

let find_function_signature (lookups : Lookups.t) (path : Path.t) =
  match find_intrinsic_signature path with
  | Some signature -> Some signature
  | None -> Interface.Impls.read_signature lookups.interface path
