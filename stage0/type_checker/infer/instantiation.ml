let check_evidence_grants (state : State.state) (span : Source.Definition_span.t) evidence =
  let impls =
    Interface.Grants.list_evidence_uses state.lookups.interface ~bounds:(State.lookup_bounds state)
      evidence
  in
  state.evidence_packages <-
    List.map (fun (impl, _, _) -> Path.package impl) impls @ state.evidence_packages;
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

let require state ~(at : Source.Definition_span.t) type_ (bound : Types.trait_reference) ~unmet =
  let trait = { bound with associated = [] } in
  State.defer state (fun () ->
      let type_ = State.normalize state type_ in
      if Unify.list_unknowns state.unifier type_ <> [] then false
      else begin
        (match State.implements state type_ trait with
        | None -> unmet type_ None
        | Some evidence ->
            check_evidence_grants state at evidence;
            List.iter
              (fun (name, wanted) ->
                match
                  Interface.Impls.project_associated_type state.lookups.interface
                    ~bounds:(State.lookup_bounds state) type_ trait name
                with
                | Some associated_type when not (State.unify state associated_type wanted) ->
                    unmet type_ (Some (name, associated_type))
                | _ -> ())
              bound.associated);
        true
      end)

let require_bounds state (span : Source.Definition_span.t) ?of_type generics substitution =
  List.iter
    (fun (argument, bound) ->
      require state ~at:span argument bound ~unmet:(fun argument other ->
          let bound = Unify.zonk_trait state.unifier bound in
          let reported =
            match State.find_current_frame state with
            | Some frame ->
                let reported = List.mem (argument, bound) frame.reported_unmet_bounds in
                frame.reported_unmet_bounds <- (argument, bound) :: frame.reported_unmet_bounds;
                reported
            | None -> false
          in
          if not reported then
            let needs =
              Printf.sprintf "%s needs `%s: %s`"
                (match of_type with
                | Some type_ -> Printf.sprintf "`%s`" (State.show state type_)
                | None -> "This")
                (Types.show argument) (Types.show_trait bound)
            in
            State.report state Unsatisfied_bound span
              (match other with
              | None -> needs ^ ", which does not hold."
              | Some (name, associated_type) ->
                  Printf.sprintf "%s, and its `%s` is `%s`." needs name
                    (State.show state associated_type))))
    (Interface.Impls.list_required_bounds generics substitution)

let make_fresh_generic_arguments (state : State.state) (generics : Types.generic list) =
  List.map
    (fun (generic : Types.generic) ->
      match generic.kind with
      | Value_generic -> Types.Value (Unify.make_fresh_value state.unifier)
      | Type_generic _ -> Types.Type (State.make_fresh_type state)
      | Capability_generic ->
          Types.Capabilities (Unify.make_fresh_capability_variable state.unifier))
    generics

let make_fresh_arguments (state : State.state) (path : Path.t) =
  match Interface.Definition.read_type_interface state.lookups.interface path with
  | Some interface -> make_fresh_generic_arguments state interface.type_generics
  | None -> []

let make_fresh_trait_reference (state : State.state) (trait : Path.t) =
  State.make_trait_reference trait
    ~arguments:
      (match Interface.Definition.read_trait_interface state.lookups.interface trait with
      | Some interface -> make_fresh_generic_arguments state interface.trait_generics
      | None -> [])

let require_type_bounds (state : State.state) span path arguments =
  match Interface.Definition.read_type_interface state.lookups.interface path with
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
      Option.map (fun self -> Static_type self) (Interface.Elaborator.find_self_type state.context)
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
  let type_ arguments =
    match Intrinsic.builtin_of_path path with
    | Some Never -> Types.Never
    | Some Integer -> Types.Integer
    | _ -> Types.Named { path; arguments }
  in
  match type_arguments with
  | None -> type_ (instantiate_type state (State.read_span state value.id) path)
  | Some items -> (
      match check_written_arguments state items with
      | Error error -> error
      | Ok arguments -> (
          match Resolve.Names.find_generics state.lookups.interface.names path with
          | Some expected when List.length expected <> List.length arguments ->
              State.make_error_type state Arity (State.read_span state value.id)
                (Printf.sprintf "`%s` takes %d %s, and %d %s given."
                   (Types.show (Named { path; arguments = [] }))
                   (List.length expected)
                   (if List.length expected = 1 then "argument" else "arguments")
                   (List.length arguments)
                   (if List.length arguments = 1 then "is" else "are"))
          | _ ->
              require_type_bounds state (State.read_span state value.id) path arguments;
              type_ arguments))

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
      match state.lookups.interface.constant_value path with
      | Some value -> Types.Value (Known value)
      | None ->
          Types.Type
            (State.make_error_type state Arity (State.read_span state value.id)
               (Printf.sprintf
                  "The value of `%s` cannot be computed: a constant used in a type cannot refer to \
                   itself, and is made of literals, arithmetic, and other such constants."
                  name.text)))
  | _ -> (
      match find_static state value with
      | Some (Static_type type_) -> Types.Type type_
      | Some (Static_trait _ | Static_capability _) | None ->
          Types.Type
            (make_error_type_at state Not_a_type value
               "A type argument is a type, or a `UInt64` value."))

type instance = {
  signature : Types.signature;
  substitution : Types.substitution;
  type_arguments : Types.argument list;
}

let instantiate (state : State.state) (span : Source.Definition_span.t) ?(extra = [])
    (signature : Types.signature) =
  let substitution =
    List.map
      (fun (generic : Types.generic) ->
        ( generic.generic,
          match generic.kind with
          | Value_generic -> Types.Value (Unify.make_fresh_value state.unifier)
          | Type_generic _ -> Types.Type (State.make_fresh_type state)
          | Capability_generic ->
              Types.Capabilities (Unify.make_fresh_capability_variable state.unifier) ))
      signature.generics
    @ extra
  in
  require_bounds state span signature.generics substitution;
  {
    signature = Types.substitute_signature substitution signature;
    substitution;
    type_arguments =
      List.map
        (fun (generic : Types.generic) -> List.assoc generic.generic substitution)
        signature.generics;
  }

let find_intrinsic_signature path =
  Option.map Intrinsic_signatures.make_signature (Intrinsic.operation_of_path path)

let find_function_signature (state : State.state) (path : Path.t) =
  match find_intrinsic_signature path with
  | Some signature -> Some signature
  | None -> Interface.Definition.read_declared_signature state.lookups.interface path
