open Syntax
module Names = Resolve.Names
open Checking
open Impl_checks

(* Bounds on the arguments of a written type *)

let bound_diagnostics database ~package ~bounds named =
  let diagnostic code (span : span) message = Diagnostic.make ~code span message in
  List.concat_map
    (fun ((span : span), (type_ : Types.ty)) ->
      match type_ with
      | Named { path; arguments } -> (
          match
            Option.bind (Query.demand database Environment.type_interface path)
              (fun (interface : Types.type_interface) ->
                Option.map
                  (Impls.required interface.type_generics)
                  (Types.substitution_of interface.type_generics arguments))
          with
          | Some required ->
              List.concat_map
                (fun (argument, bound) ->
                  match Impls.implements database ~bounds argument bound with
                  | None ->
                      [
                        diagnostic (Types Unsatisfied_bound) span
                          (Printf.sprintf "`%s` needs `%s: %s`, which does not hold here."
                             (Types.show type_) (Types.show argument) (Types.show_trait bound));
                      ]
                  | Some evidence ->
                      List.map
                        (diagnostic (Capabilities Not_granted) span)
                        (Grants.evidence_messages database ~package ~bounds evidence))
                required
          | None -> [])
      | _ -> [])
    named

let check_bounds state =
  state.diagnostics <-
    bound_diagnostics state.database ~package:state.key.module_.package ~bounds:(bounds state)
      state.lowered.named
    @ state.diagnostics

let rec mentioned = function
  | Types.Named { path; arguments } -> path :: List.concat_map mentioned_argument arguments
  | Types.Function { inputs; output; _ } ->
      List.concat_map (fun (_, type_) -> mentioned type_) inputs
      @ mentioned (Types.result_type output)
  | Types.Any trait -> trait.trait :: List.concat_map mentioned_argument trait.trait_arguments
  | Types.Projection { base; _ } -> mentioned base
  | _ -> []

and mentioned_argument = function
  | Types.Type type_ -> mentioned type_
  | Types.Value _ | Types.Capabilities _ -> []

let visibility_of state (path : Path.t) =
  match path with
  | Top { module_; name } -> (
      match Query.demand state.database Names.find (module_, name) with
      | Some entry -> Some entry.visibility
      | None -> None)
  | _ -> None

(* A public signature cannot mention a private or [internal] type, and nor
   can a public type's visible fields: callers in other packages could never
   name it. *)
let check_private_in_public state types (span : span) =
  if Names.is_public state.definition.visibility then
    List.iter
      (fun path ->
        match visibility_of state path with
        | Some (Private | Internal) ->
            report state Private_in_public span
              (Printf.sprintf
                 "This public definition mentions `%s`, which other packages cannot name. Make \
                  `%s` public, or this definition not."
                 (Path.show path) (Path.show path))
        | _ -> ())
      (List.sort_uniq Path.compare (List.concat_map mentioned types))

let check_method_location state (head : type_head) =
  let owner =
    match state.key.path with
    | Method { owner; _ } | Member_constant { owner; _ } -> Some owner
    | _ -> None
  in
  match owner with
  | Some (Top { module_ = owner_module; name } as owner) -> (
      (* A head that names no type has that as its one error. *)
      match Query.demand state.database Names.find (owner_module, name) with
      | Some { kind = Type; visibility; _ } ->
          if owner_module.package <> state.key.module_.package then
            report state Method_outside_package head.span
              (Printf.sprintf
                 "`%s` is defined in the package `%s`, so its methods and constants must be too. A \
                  function of this package can take it as a parameter instead."
                 (Path.show owner)
                 (Path.show_package owner_module.package))
          else if visibility = Private && owner_module <> state.key.module_ then
            report state Method_outside_package head.span
              (Printf.sprintf
                 "`%s` is private to its file, so its methods and constants must be in that file."
                 (Path.show owner))
      | _ -> ())
  | _ -> ()

(* Every type a signature mentions: its parameters, its result, and the
   bounds of its generic parameters. *)
let signature_types (signature : Types.signature) =
  Types.result_type signature.output
  :: List.map (fun (parameter : Types.parameter_info) -> parameter.type_) signature.parameters
  @ List.concat_map
      (fun (generic : Types.generic) ->
        match generic.kind with
        | Type_generic bounds -> List.map (fun bound -> Types.Any bound) bounds
        | _ -> [])
      signature.generics

let main_message =
  "`main` must have exactly the signature `fn main(arguments: List[String]) -> ExitCode`."

let check_main state (signature : Types.signature) span =
  let list_of_string =
    match signature.parameters with
    | [
     {
       name = "arguments";
       mode = Read;
       type_ = Named { path = list; arguments = [ Type (Named { path = string; arguments = [] }) ] };
       has_default = false;
     };
    ] ->
        Well_known.is List list && Well_known.is String string
    | _ -> false
  in
  let exit_code =
    match signature.output with
    | Returns (Named { path; arguments = [] }) -> Well_known.is Exit_code path
    | _ -> false
  in
  if not (list_of_string && exit_code && signature.generics = [] && signature.receiver = None) then
    report state Main_signature span main_message

let check_duplicates state what (names : name list) =
  ignore
    (List.fold_left
       (fun seen (name : name) ->
         if List.mem name.text seen then
           report state Duplicate_field name.span
             (Printf.sprintf "Another %s of this type is already named `%s`." what name.text);
         name.text :: seen)
       [] names)

let field_names (fields : field list) =
  List.filter_map
    (fun (field : field) ->
      match field.kind with Field_declaration { name; _ } -> Some name | Field_error -> None)
    fields

(* The edit that removes one trait from a [derives] clause, or the whole
   clause when it is the only one. *)
let remove_derived (clause : type_clause) (traits : path_type list) (written : path_type) =
  let delete start stop = Diagnostic.delete (Span.make start stop) in
  match traits with
  | [ _ ] -> delete clause.span.start clause.span.stop
  | _ -> (
      let rec after = function
        | (first : path_type) :: (next :: _ as rest) ->
            if first == written then Some next else after rest
        | _ -> None
      in
      match after traits with
      | Some next -> delete written.span.start next.span.start
      | None -> (
          let rec before = function
            | (previous : path_type) :: (next :: _ as rest) ->
                if next == written then Some previous else before rest
            | _ -> None
          in
          match before traits with
          | Some previous -> delete previous.span.stop written.span.stop
          | None -> delete written.span.start written.span.stop))

let check_derives state (interface : Types.type_interface) (clauses : type_clause list) resolved =
  let field_types =
    match interface.shape with
    | Record fields -> List.map (fun (field : Types.field) -> field.field_type) fields
    | Sum variants ->
        List.concat_map
          (fun (variant : Types.variant) ->
            List.map
              (fun (field : Types.field) -> field.field_type)
              (Option.value ~default:[] variant.fields))
          variants
    | Todo_type | Builtin_type _ | Error_shape _ -> []
  in
  (* The conditions of a derived [impl]: each type parameter bounded by the
     trait, as [impl Equal for Option[Value: Equal]]. *)
  let derived_bounds trait parameter =
    if
      List.exists
        (fun (generic : Types.generic) -> generic.generic = parameter)
        interface.type_generics
    then bounds state parameter @ [ { Types.trait; trait_arguments = []; associated = [] } ]
    else bounds state parameter
  in
  List.iter
    (fun (clause : type_clause) ->
      match clause.kind with
      | Derives traits ->
          List.iter
            (fun (written : path_type) ->
              match (resolved : Resolve.resolved).names.(written.path.last.id) with
              | Some (Definition (_, trait)) ->
                  let shown = Names.spell_path written.path in
                  if
                    not
                      (Impls.derivable trait || Well_known.is Copyable trait
                     || Well_known.is Plain trait)
                  then
                    report state Not_derivable written.span
                      (Printf.sprintf
                         "Only `Equal`, `Hash`, `Ordered`, `Default`, `Copyable`, `Plain`, \
                          `serialization::Serialize`, and `serialization::Deserialize` can be \
                          derived, not `%s`."
                         shown)
                  else if Well_known.is Copyable trait || Well_known.is Plain trait then
                    begin if not interface.opaque then
                      report state Derives_inferred written.span
                        ~fixes:
                          [
                            Diagnostic.fix "Remove the declaration."
                              [ remove_derived clause traits written ];
                          ]
                        (Printf.sprintf
                           "Whether `%s` holds for this type is derived from its fields, which are \
                            visible. Only an opaque type declares it."
                           shown)
                    else
                      let property_holds =
                        List.for_all
                          (fun type_ ->
                            if Well_known.is Plain trait then
                              Impls.plain state.database ~bounds:(derived_bounds trait) type_
                            else Impls.copyable state.database ~bounds:(derived_bounds trait) type_)
                          field_types
                      in
                      let allocates =
                        match interface.shape with
                        | Sum variants ->
                            List.exists (fun (variant : Types.variant) -> variant.indirect) variants
                        | _ -> false
                      in
                      if (not property_holds) || (Well_known.is Plain trait && allocates) then
                        report state Cannot_derive written.span
                          (Printf.sprintf "A field of this type is not `%s`, so the type cannot be."
                             shown)
                    end
                  else begin
                    (* A derived [Default] is each field's, which only a
                       record has: no variant of a sum is its default. *)
                    (if Well_known.is Default trait then
                       match interface.shape with
                       | Sum _ ->
                           report state Cannot_derive written.span
                             "`Default` is derived as each field's default, so only a record can \
                              derive it: no variant of this type is its default. Write the `impl`, \
                              which says which variant is."
                       | Record _ | Todo_type | Builtin_type _ | Error_shape _ -> ());
                    if Well_known.is Ordered trait || Well_known.is Hash trait then
                      if not (List.exists (Well_known.is Equal) interface.derives) then
                        report state Cannot_derive written.span
                          (Printf.sprintf
                             "Deriving `%s` needs `Equal` to be derived too, so that the two agree."
                             shown);
                    List.iter
                      (fun type_ ->
                        let wanted : Types.trait_reference =
                          { trait; trait_arguments = []; associated = [] }
                        in
                        if
                          Option.is_none
                            (Impls.implements state.database ~bounds:(derived_bounds trait) type_
                               wanted)
                        then
                          report state Cannot_derive written.span
                            (Printf.sprintf
                               "A field of type `%s` does not implement `%s`, so `%s` cannot be \
                                derived."
                               (Types.show type_) shown shown))
                      field_types
                  end
              | _ -> ())
            traits
      | _ -> ())
    clauses

(* A type argument is a type or a [USize] value, so no argument can be
   written for a capability parameter of a type or of a trait. A signature
   or a field could then not name the type with the capabilities that its
   value uses. *)
let check_no_capability_parameter state what (name : name) (generics : generic_parameter list) =
  List.iter
    (fun (generic : generic_parameter) ->
      match generic.kind with
      | Capability_parameter parameter ->
          report state Misplaced_capability_parameter generic.span
            (Printf.sprintf
               "Only a function can take a capability parameter. No type argument can \
                be                 written for `%s`, so no signature or field could name %s `%s` \
                with the                 capabilities that it uses. Write the capabilities in the \
                function type, as in                 `(fn() uses Clock)`."
               parameter.text what name.text)
      | Type_parameter _ | Value_parameter _ | Generic_error -> ())
    generics

let check_trait_cycle state (requires : path_type list) =
  let rec reaches seen path =
    if Path.equal path state.key.path then true
    else if List.exists (Path.equal path) seen then false
    else
      match Query.demand state.database Summary.trait_header path with
      | Some header -> List.exists (reaches (path :: seen)) header.required
      | None -> false
  in
  match Query.demand state.database Summary.trait_header state.key.path with
  | Some header when List.exists (reaches []) header.required -> (
      match requires with
      | first :: _ ->
          report state Trait_cycle first.span
            "This trait requires itself through the traits it requires."
      | [] -> ())
  | _ -> ()

(* A method is its name and how it takes [self], so a trait may add a
   version of a method that a trait it requires declares, and may not
   declare the same version again. *)
let check_redeclared state (name : name) (receiver : Path.receiver) ~(trait_path : Path.t)
    (trait : Types.trait_interface) =
  let inherited =
    List.concat_map
      (fun (required : Types.trait_reference) ->
        List.concat_map
          (fun (bound : Types.trait_reference) ->
            match Query.demand state.database Environment.trait_interface bound.trait with
            | Some interface ->
                List.map
                  (fun (method_ : Types.trait_method) ->
                    ((method_.method_name, method_.method_receiver), bound.trait))
                  interface.methods
            | None -> [])
          (Properties.bound_closure state.database
             ~self:(Types.Parameter { owner = trait_path; name = "Self" })
             required))
      trait.requires
  in
  match List.assoc_opt (name.text, receiver) inherited with
  | Some from ->
      report state Redeclared_method name.span
        (Printf.sprintf
           "`%s` already declares a `%s` that takes %s, so a trait that requires it cannot declare \
            it again."
           (Path.show from) name.text (Path.show_receiver receiver))
  | None -> ()

(* The prover checks a law once, for every instantiation of the [impl]'s
   generic parameters, and reads the proof for all of them. So the proof
   can assume of a parameter only the [impl]'s bounds on it: with a
   bound that the [impl] lacks, the law would be taken as proven for types
   that the proof's reasoning does not cover. The proof's parameters are
   the [impl]'s by position. *)
let check_proof_bounds state (written : type_head) (generics : Types.generic list)
    (impl : Types.impl_interface) =
  if List.length generics = List.length impl.impl_generics then begin
    let renaming : Types.substitution =
      List.map2
        (fun (proof : Types.generic) (of_impl : Types.generic) ->
          ( proof.generic,
            match of_impl.kind with
            | Type_generic _ -> Types.Type (Types.Parameter of_impl.generic)
            | Value_generic -> Types.Value (Types.Value_parameter of_impl.generic)
            | Capability_generic ->
                Types.Capabilities [ Types.Capability_parameter of_impl.generic ] ))
        generics impl.impl_generics
    in
    let impl_bounds = Types.bounds_of impl.impl_generics in
    List.iteri
      (fun index ((proof : Types.generic), (of_impl : Types.generic)) ->
        match proof.kind with
        | Type_generic bounds ->
            List.iter
              (fun (bound : Types.trait_reference) ->
                if
                  Option.is_none
                    (Impls.implements state.database ~bounds:impl_bounds
                       (Types.Parameter of_impl.generic)
                       (Types.substitute_trait renaming bound))
                then
                  let span =
                    match List.nth_opt written.generics index with
                    | Some (generic : generic_parameter) -> generic.span
                    | None -> written.span
                  in
                  report state Unsatisfied_bound span
                    (Printf.sprintf
                       "The `impl` does not require `%s: %s`, so this proof cannot assume it: the \
                        law is proven for every type that the `impl` is for."
                       proof.generic.name (Types.show_trait bound)))
              bounds
        | Value_generic | Capability_generic -> ())
      (List.combine generics impl.impl_generics)
  end

let check state =
  let database = state.database in
  let definition = state.definition in
  let broken part = Resolve.Parts.broken definition part in
  check_bounds state;
  match Query.demand database Resolve.resolved state.key with
  | None -> ()
  | Some resolved -> (
      if not (broken Header) then
        match
          (Query.demand database Names.container state.key, definition.kind, state.lowered.interface)
        with
        (* A method written inside a trait or an [impl] is checked against
           the method that the enclosing declaration inherits or implements. *)
        | ( Some container,
            (Function { signature; _ } | Method_declaration signature),
            Function_interface written ) -> (
            let name = Names.signature_name signature in
            match
              ( Query.demand database Names.definition container,
                Option.map
                  (fun (lowered : Environment.lowered_interface) -> lowered.interface)
                  (Query.demand database Environment.lowered_interface container) )
            with
            | Some { kind = Trait _; _ }, Some (Trait_interface trait) ->
                check_redeclared state name
                  (Names.receiver signature.parameters)
                  ~trait_path:container.path trait
            | Some { kind = Impl { trait_; _ }; _ }, Some (Impl_interface impl) ->
                check_impl_method state name
                  (Names.receiver signature.parameters)
                  written impl trait_
            | _ -> ())
        | Some _, _, _ -> ()
        | None, Function { signature; _ }, Function_interface lowered ->
            (match signature.name with
            | Member_name (head, _) -> check_method_location state head
            | Plain_name name ->
                if name.text = "main" && state.key.module_.modules = [ "main" ] then
                  check_main state lowered name.span);
            let span =
              match signature.name with Plain_name name | Member_name (_, name) -> name.span
            in
            check_private_in_public state (signature_types lowered) span
        (* A law's proof is of a law its trait has, as a type that
           implements the trait keeps it. *)
        | None, Law_proof { law; type_; _ }, Law_proof_interface { generics; trait; for_type; _ }
          -> (
            (match Query.demand database Summary.trait_header trait.trait with
            | Some header when not (List.mem law.text header.laws) ->
                report state Unknown_member law.span
                  (Printf.sprintf "`%s` has no law `%s`." (Types.show_trait trait) law.text)
            | _ -> ());
            (* A head with the wrong number of parameters is reported as that. *)
            let arity_matches =
              match for_type with
              | Types.Named { path; _ } -> (
                  match Query.demand database Summary.generics_of path with
                  | Some expected -> List.length expected = List.length generics
                  | None -> true)
              | _ -> true
            in
            if arity_matches && not (Types.is_error for_type) then
              match implements state for_type trait with
              | None ->
                  report state No_impl type_.span
                    (Printf.sprintf "`%s` does not implement `%s`, so it has no law of it to keep."
                       (Types.show for_type) (Types.show_trait trait))
              | Some (Impls.From_impl { impl; _ }) ->
                  Option.iter
                    (check_proof_bounds state type_ generics)
                    (Impls.impl_interface database impl)
              | Some _ -> ())
        | None, Type_definition { name; generics; body; clauses }, Type_interface interface ->
            check_no_capability_parameter state "the type" name generics;
            (match body with
            | Fields fields -> check_duplicates state "field" (field_names fields)
            | Variants variants ->
                check_duplicates state "variant"
                  (List.map (fun (variant : variant) -> variant.name) variants);
                List.iter
                  (fun (variant : variant) ->
                    Option.iter
                      (fun fields -> check_duplicates state "field" (field_names fields))
                      variant.fields)
                  variants
            | Type_todo -> ());
            check_derives state interface clauses resolved;
            if definition.visibility = Public then
              check_private_in_public state
                (match interface.shape with
                | Record fields -> List.map (fun (field : Types.field) -> field.field_type) fields
                | Sum variants ->
                    List.concat_map
                      (fun (variant : Types.variant) ->
                        List.map
                          (fun (field : Types.field) -> field.field_type)
                          (Option.value ~default:[] variant.fields))
                      variants
                | _ -> [])
                name.span
        | None, Trait { name; generics; requires; _ }, Trait_interface trait ->
            check_no_capability_parameter state "the trait" name generics;
            check_trait_cycle state requires;
            check_private_in_public state
              (List.map (fun (bound : Types.trait_reference) -> Types.Any bound) trait.requires
              @ List.concat_map
                  (fun (method_ : Types.trait_method) -> signature_types method_.method_signature)
                  trait.methods)
              name.span
        | None, Constant { name = Plain_name name; _ }, Constant_interface constant ->
            check_private_in_public state [ constant.constant_type ] name.span
        | None, Impl { trait_; members; _ }, Impl_interface impl ->
            check_impl state members impl trait_
        | None, Constant { name = Member_name (head, _); _ }, _ -> check_method_location state head
        | None, _, _ -> ())

let diagnostics =
  Query.query ~name:"interface_diagnostics" ~phase:Phases.interfaces ~saved:true
    ~show:Names.show_key (fun database key ->
      match
        ( Query.demand database Names.definition key,
          Query.demand database Environment.lowered_interface key )
      with
      | Some definition, Some lowered ->
          let state = { database; key; definition; lowered; diagnostics = [] } in
          check state;
          List.sort
            (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
              compare (left.span, left.code) (right.span, right.code))
            (lowered.diagnostics @ state.diagnostics)
      | _ -> [])

let reported database (path : Path.t) =
  match Query.demand database Summary.key path with
  | Some key -> (
      match Query.demand database diagnostics key with
      | first :: _ -> Some (Diagnostic.reported first)
      | [] -> None)
  | None -> None
