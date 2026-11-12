open Syntax
open State
module Environment = Interface.Environment

(* A bound that an [impl] satisfies makes this definition depend on the
   [impl]'s code. Checks that the capabilities the [impl] uses are granted
   to its package, and records the package. *)
let check_evidence_grants state (span : span) evidence =
  let impls = Interface.Grants.evidence_uses state.database ~bounds:(bounds state) evidence in
  state.evidence <- List.map (fun (impl, _, _) -> Path.package impl) impls @ state.evidence;
  List.iter
    (fun message ->
      state.diagnostics <-
        Diagnostic.make ~code:(Capabilities Not_granted) span message :: state.diagnostics)
    (Interface.Grants.messages state.database ~package:state.package impls)

(* The error type for an expression that is not valid where it is used.
   If resolution already reported the expression's name as unknown, this
   reuses that report instead of adding a second one. *)
let error_at state ?fixes code (value : expression) message =
  match head state value with
  | Some { target = Unknown report; _ } -> Types.Error report
  | _ -> error state ?fixes code value.span message

(* An expression before a [.] or a [(] that names a type, a trait, or a
   capability instead of a value. *)
type static_ =
  | Static_type of Types.ty
  | Static_trait of Path.t * Types.argument list option
      (** The trait's type arguments, if they are written. *)
  | Static_capability of Path.t

(* Requires a type to satisfy a trait bound. The check is deferred until
   the type is inferred. The type must implement the trait, and each
   associated type that the bound fixes must unify with the one the [impl]
   defines, which can infer other types of the statement.

   [unmet] reports a failure: with [None] if the type does not implement
   the trait, and with the name of an associated type and the type the
   [impl] defines if those differ. A capability that the [impl] uses and
   that its package is not granted is reported at [at]. *)
let require state ~(at : span) type_ (bound : Types.trait_reference) ~unmet =
  let trait = { bound with associated = [] } in
  defer state (fun () ->
      let type_ = normalize state type_ in
      if Unify.unknowns state.unifier type_ <> [] then false
      else begin
        (match implements state type_ trait with
        | None -> unmet type_ None
        | Some evidence ->
            check_evidence_grants state at evidence;
            List.iter
              (fun (name, wanted) ->
                match
                  Impls.associated_type state.database ~bounds:(bounds state) type_ trait name
                with
                | Some associated_type when not (unify state associated_type wanted) ->
                    unmet type_ (Some (name, associated_type))
                | _ -> ())
              bound.associated);
        true
      end)

(* Requires the type arguments of an instantiation to satisfy the bounds
   of their generic parameters. [of_type] is the type that declares the
   parameters. Without it, the parameters are a callee's. *)
let require_bounds state (span : span) ?of_type generics substitution =
  List.iter
    (fun (argument, bound) ->
      require state ~at:span argument bound ~unmet:(fun argument other ->
          let bound = Unify.zonk_trait state.unifier bound in
          let reported =
            match current_frame state with
            | Some frame ->
                let reported = List.mem (argument, bound) frame.unmet in
                frame.unmet <- (argument, bound) :: frame.unmet;
                reported
            | None -> false
          in
          if not reported then
            let needs =
              Printf.sprintf "%s needs `%s: %s`"
                (match of_type with
                | Some type_ -> Printf.sprintf "`%s`" (show state type_)
                | None -> "This")
                (Types.show argument) (Types.show_trait bound)
            in
            report state Unsatisfied_bound span
              (match other with
              | None -> needs ^ ", which does not hold."
              | Some (name, associated_type) ->
                  Printf.sprintf "%s, and its `%s` is `%s`." needs name (show state associated_type))))
    (Impls.required generics substitution)

let fresh_arguments state (path : Path.t) =
  match Query.demand state.database Environment.type_interface path with
  | Some interface ->
      List.map
        (fun (generic : Types.generic) ->
          match generic.kind with
          | Value_generic -> Types.Value (Unify.fresh_value state.unifier)
          | Type_generic _ -> Types.Type (fresh state)
          | Capability_generic -> Types.Capabilities (Unify.fresh_capability_variable state.unifier))
        interface.type_generics
  | None -> []

let require_type_bounds state span path arguments =
  match Query.demand state.database Environment.type_interface path with
  | Some interface ->
      Option.iter
        (require_bounds state span
           ~of_type:(Types.Named { path; arguments })
           interface.type_generics)
        (Types.substitution_of interface.type_generics arguments)
  | None -> ()

(* Fresh inference variables for the generic parameters of a type, each
   required to satisfy the bounds of its parameter. *)
let instantiate_type state span path =
  let arguments = fresh_arguments state path in
  require_type_bounds state span path arguments;
  arguments

let rec static_ state (value : expression) : static_ option =
  match (value.kind, head state value) with
  | Self_type_value, _ -> Option.map (fun self -> Static_type self) state.context.self_type
  | _, Some { target = Definition (Type, path); type_arguments; _ } ->
      Some (Static_type (named_type state value path type_arguments))
  | _, Some { target = Type_parameter parameter; name; type_arguments } ->
      if Option.is_some type_arguments then
        report state Arity value.span
          (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." name.text);
      Some (Static_type (Types.Parameter parameter))
  | _, Some { target = Definition (Trait, path); type_arguments; _ } ->
      Some (Static_trait (path, Option.map (written_arguments state) type_arguments))
  | _, Some { target = Definition (Capability, path); _ } -> Some (Static_capability path)
  | Parenthesized inner, None -> static_ state inner
  | _ -> None

(* A type named in an expression, with the type arguments written after
   it, or with fresh inference variables if none are written. *)
and named_type state (value : expression) path type_arguments =
  let type_ arguments =
    match Intrinsic.builtin_of_path path with
    | Some Never -> Types.Never
    | Some Integer -> Types.Integer
    | _ -> Types.Named { path; arguments }
  in
  match type_arguments with
  | None -> type_ (instantiate_type state value.span path)
  | Some items ->
      let arguments = written_arguments state items in
      (match Query.demand state.database Interface.Summary.generics_of path with
      | Some expected when List.length expected <> List.length arguments ->
          report state Arity value.span
            (Printf.sprintf "`%s` takes %d %s, and %d %s given."
               (Types.show (Named { path; arguments = [] }))
               (List.length expected)
               (if List.length expected = 1 then "argument" else "arguments")
               (List.length arguments)
               (if List.length arguments = 1 then "is" else "are"))
      | _ -> require_type_bounds state value.span path arguments);
      type_ arguments

(* Type arguments written in an expression, as in [List[String].new()]. *)
and written_arguments state items =
  List.filter_map
    (function
      | Item item -> Some (type_argument_of_expression state item)
      | Item_constraint (name, _) ->
          report state Arity name.span
            "An associated type is fixed where a type is written, as in `any Trait[Name = Type]`, \
             not among type arguments in an expression.";
          None)
    items

and type_argument_of_expression state (value : expression) : Types.argument =
  match (value.kind, head state value) with
  | Integer value, _ -> Types.Value (Known value)
  | _, Some { target = Value_parameter parameter; _ } -> Types.Value (Value_parameter parameter)
  | _, Some { target = Definition (Constant, path); name; _ } -> (
      match Query.demand state.database Interface.Constants.value_of path with
      | Some value -> Types.Value (Known value)
      | None ->
          Types.Type
            (error state Arity value.span
               (Printf.sprintf
                  "The value of `%s` cannot be worked out: a constant used in a type cannot refer \
                   to itself, and is made of literals, arithmetic, and other such constants."
                  name.text)))
  | _ -> (
      match static_ state value with
      | Some (Static_type type_) -> Types.Type type_
      | Some (Static_trait _ | Static_capability _) | None ->
          Types.Type
            (error_at state Not_a_type value "A type argument is a type, or a `USize` value."))

type instance = {
  signature : Types.signature;
  substitution : Types.substitution;
  type_arguments : Types.argument list;
}

(* Instantiates a signature at a use: its generic parameters are replaced
   by fresh inference variables, each required to satisfy its bounds. *)
let instantiate state (span : span) ?(extra = []) (signature : Types.signature) =
  let substitution =
    List.map
      (fun (generic : Types.generic) ->
        ( generic.generic,
          match generic.kind with
          | Value_generic -> Types.Value (Unify.fresh_value state.unifier)
          | Type_generic _ -> Types.Type (fresh state)
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

(* The signature of a function. [Error] with the report if the function's
   header did not parse. *)
let function_signature state (path : Path.t) =
  match intrinsic_signature path with
  | Some signature -> Some (Ok signature)
  | None -> Environment.signature_or_report state.database path
