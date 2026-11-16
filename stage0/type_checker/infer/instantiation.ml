let check_evidence_grants (state : State.state) (span : Source.Definition_span.t) evidence =
  let impls =
    Interface.Grants.list_evidence_uses state.lookups.interface ~bounds:(State.bounds state)
      evidence
  in
  state.evidence_packages <-
    List.map (fun (impl, _, _) -> Path.package impl) impls @ state.evidence_packages;
  List.iter
    (fun message ->
      state.diagnostics <-
        Diagnostic.make ~code:(Capabilities Not_granted) span message :: state.diagnostics)
    (Interface.Grants.describe_missing_in_impls state.lookups.interface ~package:state.package impls)

let error_at state ?fixes code (value : Syntax.expression) message =
  match State.head state value with
  | Some { target = Unknown report; _ } -> Types.Error report
  | _ -> State.error state ?fixes code (State.read_span state value.id) message

type static_ =
  | Static_type of Types.ty
  | Static_trait of Path.t * Types.argument list option
  | Static_capability of Path.t

let require state ~(at : Source.Definition_span.t) type_ (bound : Types.trait_reference) ~unmet =
  let trait = { bound with associated = [] } in
  State.defer state (fun () ->
      let type_ = State.normalize state type_ in
      if Unify.unknowns state.unifier type_ <> [] then false
      else begin
        (match State.implements state type_ trait with
        | None -> unmet type_ None
        | Some evidence ->
            check_evidence_grants state at evidence;
            List.iter
              (fun (name, wanted) ->
                match
                  Interface.Impls.project_associated_type state.lookups.interface
                    ~bounds:(State.bounds state) type_ trait name
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
            match State.current_frame state with
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

let fresh_arguments (state : State.state) (path : Path.t) =
  match Interface.Definition.read_type_interface state.lookups.interface path with
  | Some interface ->
      List.map
        (fun (generic : Types.generic) ->
          match generic.kind with
          | Value_generic -> Types.Value (Unify.fresh_value state.unifier)
          | Type_generic _ -> Types.Type (State.fresh state)
          | Capability_generic -> Types.Capabilities (Unify.fresh_capability_variable state.unifier))
        interface.type_generics
  | None -> []

let require_type_bounds (state : State.state) span path arguments =
  match Interface.Definition.read_type_interface state.lookups.interface path with
  | Some interface ->
      Option.iter
        (require_bounds state span
           ~of_type:(Types.Named { path; arguments })
           interface.type_generics)
        (Types.make_substitution interface.type_generics arguments)
  | None -> ()

let instantiate_type state span path =
  let arguments = fresh_arguments state path in
  require_type_bounds state span path arguments;
  arguments

let rec static_ state (value : Syntax.expression) : static_ option =
  match (value.kind, State.head state value) with
  | Self_type_value, _ -> Option.map (fun self -> Static_type self) state.context.self_type
  | _, Some { target = Definition (Type, path); type_arguments; _ } ->
      Some (Static_type (named_type state value path type_arguments))
  | _, Some { target = Type_parameter parameter; name; type_arguments } ->
      if Option.is_some type_arguments then
        State.report state Arity (State.read_span state value.id)
          (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." name.text);
      Some (Static_type (Types.Parameter parameter))
  | _, Some { target = Definition (Trait, path); type_arguments; _ } ->
      Some (Static_trait (path, Option.map (written_arguments state) type_arguments))
  | _, Some { target = Definition (Capability, path); _ } -> Some (Static_capability path)
  | Parenthesized inner, None -> static_ state inner
  | _ -> None

and named_type state (value : Syntax.expression) path type_arguments =
  let type_ arguments =
    match Intrinsic.builtin_of_path path with
    | Some Never -> Types.Never
    | Some Integer -> Types.Integer
    | _ -> Types.Named { path; arguments }
  in
  match type_arguments with
  | None -> type_ (instantiate_type state (State.read_span state value.id) path)
  | Some items ->
      let arguments = written_arguments state items in
      (match Resolve.Names.generics_of state.lookups.interface.names path with
      | Some expected when List.length expected <> List.length arguments ->
          State.report state Arity (State.read_span state value.id)
            (Printf.sprintf "`%s` takes %d %s, and %d %s given."
               (Types.show (Named { path; arguments = [] }))
               (List.length expected)
               (if List.length expected = 1 then "argument" else "arguments")
               (List.length arguments)
               (if List.length arguments = 1 then "is" else "are"))
      | _ -> require_type_bounds state (State.read_span state value.id) path arguments);
      type_ arguments

and written_arguments state items =
  List.filter_map
    (function
      | Syntax.Item item -> Some (type_argument_of_expression state item)
      | Item_constraint (name, _) ->
          State.report state Arity (State.read_span state name.id)
            "An associated type is fixed where a type is written, as in `any Trait[Name = Type]`, \
             not among type arguments in an expression.";
          None)
    items

and type_argument_of_expression state (value : Syntax.expression) : Types.argument =
  match (value.kind, State.head state value) with
  | Integer value, _ -> Types.Value (Known value)
  | _, Some { target = Value_parameter parameter; _ } -> Types.Value (Value_parameter parameter)
  | _, Some { target = Definition (Constant, path); name; _ } -> (
      match state.lookups.interface.constant_value path with
      | Some value -> Types.Value (Known value)
      | None ->
          Types.Type
            (State.error state Arity (State.read_span state value.id)
               (Printf.sprintf
                  "The value of `%s` cannot be computed: a constant used in a type cannot refer to \
                   itself, and is made of literals, arithmetic, and other such constants."
                  name.text)))
  | _ -> (
      match static_ state value with
      | Some (Static_type type_) -> Types.Type type_
      | Some (Static_trait _ | Static_capability _) | None ->
          Types.Type
            (error_at state Not_a_type value "A type argument is a type, or a `UInt64` value."))

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
          | Value_generic -> Types.Value (Unify.fresh_value state.unifier)
          | Type_generic _ -> Types.Type (State.fresh state)
          | Capability_generic -> Types.Capabilities (Unify.fresh_capability_variable state.unifier)
        ))
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

let intrinsic_signature path =
  Option.map Intrinsic_signatures.signature (Intrinsic.operation_of_path path)

let function_signature (state : State.state) (path : Path.t) =
  match intrinsic_signature path with
  | Some signature -> Some signature
  | None -> Interface.Definition.read_declared_signature state.lookups.interface path
