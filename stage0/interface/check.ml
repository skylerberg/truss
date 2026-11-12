open Syntax
module T = Types
module Names = Resolve.Names

type state = {
  database : Query.context;
  key : Names.key;
  definition : definition;
  lowered : Environment.lowered;
  mutable diagnostics : Diagnostic.t list;
}

let reported state ?fixes code (span : span) message =
  let diagnostic = Diagnostic.make ?fixes ~code:(Types code) (Syntax.Span.to_source span) message in
  state.diagnostics <- diagnostic :: state.diagnostics;
  Diagnostic.reported diagnostic

let report state ?fixes code span message = ignore (reported state ?fixes code span message)

let bounds state parameter =
  Option.value ~default:[] (List.assoc_opt parameter state.lowered.bounds)

let implements state type_ trait =
  Impls.implements state.database ~bounds:(bounds state) type_ trait

(* Bounds on the arguments of a written type *)

let bound_diagnostics database ~package ~bounds named =
  let diagnostic code (span : span) message =
    Diagnostic.make ~code (Syntax.Span.to_source span) message
  in
  List.concat_map
    (fun ((span : span), (type_ : T.ty)) ->
      match type_ with
      | Named { path; arguments } -> (
          match
            Option.bind (Query.demand database Environment.type_interface path)
              (fun (interface : T.type_interface) ->
                Option.map
                  (Impls.required interface.type_generics)
                  (T.substitution_of interface.type_generics arguments))
          with
          | Some required ->
              List.concat_map
                (fun (argument, bound) ->
                  match Impls.implements database ~bounds argument bound with
                  | None ->
                      [
                        diagnostic (Types Unsatisfied_bound) span
                          (Printf.sprintf "`%s` needs `%s: %s`, which does not hold here."
                             (T.show type_) (T.show argument) (T.show_trait bound));
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

(* Visibility *)

let rec mentioned = function
  | T.Named { path; arguments } -> path :: List.concat_map mentioned_argument arguments
  | T.Function { inputs; output; _ } ->
      List.concat_map (fun (_, type_) -> mentioned type_) inputs @ mentioned (T.result_type output)
  | T.Any trait -> trait.trait :: List.concat_map mentioned_argument trait.trait_arguments
  | T.Projection { base; _ } -> mentioned base
  | _ -> []

and mentioned_argument = function
  | T.Type type_ -> mentioned type_
  | T.Value _ | T.Capabilities _ -> []

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

(* Methods *)

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
let signature_types (signature : T.signature) =
  T.result_type signature.output
  :: List.map (fun (parameter : T.parameter_info) -> parameter.type_) signature.parameters
  @ List.concat_map
      (fun (generic : T.generic) ->
        match generic.kind with
        | Type_generic bounds -> List.map (fun bound -> T.Any bound) bounds
        | _ -> [])
      signature.generics

let main_message =
  "`main` must have exactly the signature `fn main(arguments: List[String]) -> ExitCode`."

let check_main state (signature : T.signature) span =
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

(* Types *)

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
  let delete start stop = Diagnostic.delete (Source.span start stop) in
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

let check_derives state (interface : T.type_interface) (clauses : type_clause list) resolved =
  let field_types =
    match interface.shape with
    | Record fields -> List.map (fun (field : T.field) -> field.field_type) fields
    | Sum variants ->
        List.concat_map
          (fun (variant : T.variant) ->
            List.map
              (fun (field : T.field) -> field.field_type)
              (Option.value ~default:[] variant.fields))
          variants
    | Todo_type | Builtin_type _ | Error_shape _ -> []
  in
  (* The conditions of a derived [impl]: each type parameter bounded by the
     trait, as [impl Equal for Option[Value: Equal]]. *)
  let derived_bounds trait parameter =
    if
      List.exists (fun (generic : T.generic) -> generic.generic = parameter) interface.type_generics
    then bounds state parameter @ [ { T.trait; trait_arguments = []; associated = [] } ]
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
                         "Only `Equal`, `Hash`, `Ordered`, `Default`, `Copyable`, and `Plain` can \
                          be derived, not `%s`."
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
                           "Whether `%s` holds for this type is worked out from its fields, which \
                            are visible. Only an opaque type declares it."
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
                            List.exists (fun (variant : T.variant) -> variant.indirect) variants
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
                        let wanted : T.trait_reference =
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
                               (T.show type_) shown shown))
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

(* Traits *)

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
    (trait : T.trait_interface) =
  let inherited =
    List.concat_map
      (fun (required : T.trait_reference) ->
        List.concat_map
          (fun (bound : T.trait_reference) ->
            match Query.demand state.database Environment.trait_interface bound.trait with
            | Some interface ->
                List.map
                  (fun (method_ : T.trait_method) ->
                    ((method_.method_name, method_.method_receiver), bound.trait))
                  interface.methods
            | None -> [])
          (Properties.bound_closure state.database
             ~self:(T.Parameter { owner = trait_path; name = "Self" })
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

(* [impl]s *)

(* The prover checks a law once, for every instantiation of the [impl]'s
   generic parameters, and reads the proof for all of them. So the proof
   can assume of a parameter only what the [impl] requires of it: with a
   bound that the [impl] lacks, the law would be taken as proven for types
   that the proof's reasoning does not cover. The proof's parameters are
   the [impl]'s by position. *)
let check_proof_bounds state (written : type_head) (generics : T.generic list)
    (impl : T.impl_interface) =
  if List.length generics = List.length impl.impl_generics then begin
    let renaming : T.substitution =
      List.map2
        (fun (proof : T.generic) (of_impl : T.generic) ->
          ( proof.generic,
            match of_impl.kind with
            | Type_generic _ -> T.Type (T.Parameter of_impl.generic)
            | Value_generic -> T.Value (T.Value_parameter of_impl.generic)
            | Capability_generic -> T.Capabilities [ T.Capability_parameter of_impl.generic ] ))
        generics impl.impl_generics
    in
    let impl_bounds = T.bounds_of impl.impl_generics in
    List.iteri
      (fun index ((proof : T.generic), (of_impl : T.generic)) ->
        match proof.kind with
        | Type_generic bounds ->
            List.iter
              (fun (bound : T.trait_reference) ->
                if
                  Option.is_none
                    (Impls.implements state.database ~bounds:impl_bounds
                       (T.Parameter of_impl.generic)
                       (T.substitute_trait renaming bound))
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
                       proof.generic.name (T.show_trait bound)))
              bounds
        | Value_generic | Capability_generic -> ())
      (List.combine generics impl.impl_generics)
  end

let show_signature (signature : T.signature) =
  Printf.sprintf "(%s)%s"
    (String.concat ", "
       ((match signature.receiver with
          | Some (Read, _) -> [ "self" ]
          | Some (Mut, _) -> [ "mut self" ]
          | Some (Own, _) -> [ "own self" ]
          | _ -> [])
       @ List.map
           (fun (parameter : T.parameter_info) ->
             parameter.name ^ ": " ^ T.show_mode parameter.mode ^ T.show parameter.type_)
           signature.parameters))
    (T.show_output signature.output)

(* Whether two types agree, where an error on either side agrees with
   anything, since it was reported already. *)
let rec agrees (left : T.ty) (right : T.ty) =
  match (left, right) with
  | T.Error _, _ | _, T.Error _ -> true
  | T.Named left, T.Named right ->
      Path.equal left.path right.path
      && List.length left.arguments = List.length right.arguments
      && List.for_all2
           (fun left right ->
             match (left, right) with
             | T.Type left, T.Type right -> agrees left right
             | left, right -> left = right)
           left.arguments right.arguments
  | T.Function left, T.Function right ->
      List.length left.inputs = List.length right.inputs
      && List.for_all2
           (fun (left_mode, left) (right_mode, right) ->
             left_mode = right_mode && agrees left right)
           left.inputs right.inputs
      && agrees_result left.output right.output
  | _ -> T.equal left right

and agrees_result (left : T.result) (right : T.result) =
  match (left, right) with
  | Returns left, Returns right -> agrees left right
  | Yields (left_mode, left), Yields (right_mode, right)
  | Lends (left_mode, left), Lends (right_mode, right) ->
      left_mode = right_mode && agrees left right
  | _ -> false

(* An [impl]'s view of its trait: the trait, the substitution for the
   trait's [Self] and parameters, and the trait's types under that
   substitution, in which [Self] is the [impl]'s type and each associated
   type of [Self] is the definition given by this [impl] or by the [impl] of
   a required trait. An associated type that the trait declares and the
   [impl] does not define is an error wherever a method's signature mentions
   it. The [impl] itself reports it, once. The trait's sets of capabilities
   are read in the same way: each associated capability set of [Self] is the
   set that this [impl] defines. *)
type view = {
  trait : T.trait_interface;
  shown_trait : string;
  substitution : T.substitution;
  impl_bounds : T.parameter -> T.trait_reference list;
  normalize : T.ty -> T.ty;
  normalize_capabilities : T.capability list -> T.capability list;
  missing_associated : (string * Diagnostic.t) list;
}

let compiler_implements (impl : T.impl_interface) =
  Path.equal impl.implements.trait Properties.copyable_trait
  || Path.equal impl.implements.trait Properties.plain_trait
  || Path.equal impl.implements.trait Properties.storable_trait

let impl_view database ~bounds (impl : T.impl_interface) (trait_path : path_type) =
  let shown_trait = Names.spell_path trait_path.path in
  let impl_bounds parameter =
    match
      List.find_opt (fun (generic : T.generic) -> generic.generic = parameter) impl.impl_generics
    with
    | Some { kind = Type_generic bounds; _ } -> bounds
    | _ -> bounds parameter
  in
  if Well_known.is Panic impl.implements.trait || compiler_implements impl then None
  else
    Option.map
      (fun (trait : T.trait_interface) ->
        let substitution =
          Properties.trait_substitution trait ~self:impl.for_type impl.implements
        in
        let missing_associated =
          List.filter_map
            (fun (associated : T.associated_type) ->
              if List.mem_assoc associated.associated_name impl.implements.associated then None
              else
                Some
                  ( associated.associated_name,
                    Diagnostic.make ~code:(Types Missing_member)
                      (Syntax.Span.to_source trait_path.span)
                      (Printf.sprintf "This `impl` must give `type %s`, which `%s` declares."
                         associated.associated_name shown_trait) ))
            trait.associated_types
        in
        let normalize type_ =
          T.map
            (function
              | T.Projection { base; trait = projected; name } when T.equal base impl.for_type -> (
                  match
                    ( List.assoc_opt name impl.implements.associated,
                      List.assoc_opt name missing_associated )
                  with
                  | Some fixed, _ -> Some fixed
                  | None, Some missing when Path.equal projected.trait impl.implements.trait ->
                      Some (T.Error (Diagnostic.reported missing))
                  | None, _ ->
                      Impls.associated_type database ~bounds:impl_bounds impl.for_type projected
                        name)
              | _ -> None)
            (T.substitute substitution type_)
        in
        let normalize_capabilities capabilities =
          List.sort_uniq compare
            (List.concat_map
               (function
                 | T.Capability_projection { base; trait = projected; name }
                   when T.equal base impl.for_type
                        && Path.equal projected.trait impl.implements.trait ->
                     Option.value ~default:[] (List.assoc_opt name impl.capability_sets)
                 | capability ->
                     Impls.normalize_capabilities database ~bounds:impl_bounds [ capability ])
               (T.substitute_capabilities substitution capabilities))
        in
        {
          trait;
          shown_trait;
          substitution;
          impl_bounds;
          normalize;
          normalize_capabilities;
          missing_associated;
        })
      (Query.demand database Environment.trait_interface impl.implements.trait)

(* The checks of an [impl]'s own header: it defines every member that its
   trait requires, and its type implements the traits that the trait
   requires. Each method written inside it is checked against the trait's
   method as a definition of its own. *)
let check_impl state (written_members : impl_member line list) (impl : T.impl_interface)
    (trait_path : path_type) =
  let database = state.database in
  if Well_known.is Panic impl.implements.trait then
    report state Implements_panic trait_path.span
      "Nothing can implement `Panic`, since a panic cannot be caught."
  else if compiler_implements impl then
    report state Implements_built_in trait_path.span
      (Printf.sprintf
         "The compiler implements `%s` from a type's fields; no `impl` of it can be written."
         (Names.spell_path trait_path.path))
  else
    match impl_view database ~bounds:(bounds state) impl trait_path with
    | None -> ()
    | Some { trait; shown_trait; substitution; impl_bounds; normalize; missing_associated; _ } ->
        let check_evidence_grants (span : span) evidence =
          state.diagnostics <-
            List.map
              (Diagnostic.make ~code:(Capabilities Not_granted) (Syntax.Span.to_source span))
              (Grants.evidence_messages database ~package:state.key.module_.package
                 ~bounds:impl_bounds evidence)
            @ state.diagnostics
        in
        state.diagnostics <- List.map snd missing_associated @ state.diagnostics;
        let given =
          List.filter_map
            (fun (member : Names.key) ->
              match member.path with
              | Method { name; receiver; _ } -> Some (name, receiver)
              | _ -> None)
            (Query.demand database Names.contained state.key)
        in
        (* The [impl] must define every method without a body. For a
           capability that is every method, because a capability's methods
           have no bodies. *)
        List.iter
          (fun (method_ : T.trait_method) ->
            let given =
              List.exists
                (fun (name, receiver) ->
                  name = method_.method_name
                  && (trait.is_capability || receiver = method_.method_receiver))
                given
            in
            if (not given) && not method_.provided then
              report state Missing_member trait_path.span
                (Printf.sprintf "This `impl` must give `%s%s`, which `%s` declares."
                   method_.method_name
                   (show_signature (T.map_signature normalize method_.method_signature))
                   shown_trait))
          trait.methods;
        List.iter
          (fun (associated : T.associated_type) ->
            match List.assoc_opt associated.associated_name impl.implements.associated with
            | None -> ()
            | Some chosen ->
                (* Each associated type that the [impl] defines must satisfy
                   the bounds that the trait declares for it. *)
                List.iter
                  (fun bound ->
                    let bound = T.substitute_trait substitution bound in
                    match Impls.implements database ~bounds:impl_bounds chosen bound with
                    | None ->
                        report state Unsatisfied_bound trait_path.span
                          (Printf.sprintf "`%s` declares `type %s: %s`, and `%s` is not one."
                             shown_trait associated.associated_name (T.show_trait bound)
                             (T.show chosen))
                    | Some evidence -> check_evidence_grants trait_path.span evidence)
                  associated.associated_bounds)
          trait.associated_types;
        ignore
          (List.fold_left
             (fun defined (line : impl_member line) ->
               match line.kind with
               | Associated_definition (name, _) ->
                   if
                     not
                       (List.exists
                          (fun (associated : T.associated_type) ->
                            associated.associated_name = name.text)
                          trait.associated_types)
                   then
                     report state Extra_member name.span
                       (Printf.sprintf "`%s` declares no associated type `%s`." shown_trait
                          name.text);
                   defined
               | Capability_definition (name, _) ->
                   if not (List.mem name.text trait.associated_capabilities) then
                     report state Extra_member name.span
                       (Printf.sprintf "`%s` declares no associated capability set `%s`."
                          shown_trait name.text)
                   else if List.mem name.text defined then
                     report state Extra_member name.span
                       (Printf.sprintf
                          "This `impl` already defines `%s`. List every capability in one \
                           definition, separated by commas."
                          name.text);
                   name.text :: defined
               | Impl_member_error -> defined)
             [] written_members);
        (* The traits a trait requires are implemented for the same type. *)
        List.iter
          (fun (required : T.trait_reference) ->
            let required = T.substitute_trait substitution required in
            match Impls.implements database ~bounds:impl_bounds impl.for_type required with
            | None ->
                report state Missing_required_impl trait_path.span
                  (Printf.sprintf "`%s` requires `%s`, which `%s` does not implement." shown_trait
                     (T.show_trait required) (T.show impl.for_type))
            | Some evidence -> check_evidence_grants trait_path.span evidence)
          trait.requires;
        if (not trait.is_capability) && impl.impl_uses <> [] then
          report state Impl_uses trait_path.span
            "Only an `impl` of a capability can have `uses`. A trait's methods can use only what \
             the trait declares."

(* A method written inside an [impl], against the method its trait
   declares. *)
let check_impl_method state (name : name) (receiver : Path.receiver) (given : T.signature)
    (impl : T.impl_interface) (trait_path : path_type) =
  match impl_view state.database ~bounds:(bounds state) impl trait_path with
  | None -> ()
  | Some { trait; shown_trait; normalize; normalize_capabilities; _ } -> (
      let declared =
        List.find_opt
          (fun (method_ : T.trait_method) ->
            method_.method_name = name.text
            && (trait.is_capability || method_.method_receiver = receiver))
          trait.methods
      in
      match declared with
      | None ->
          report state Extra_member name.span
            (Printf.sprintf "`%s` declares no method `%s` with this receiver." shown_trait name.text)
      | Some declared ->
          let replaceable (signature : T.signature) =
            signature.uses = [] && signature.terminates
            && List.for_all
                 (fun (info : T.parameter_info) -> info.mode <> T.Mut)
                 signature.parameters
            && match signature.receiver with Some (Mut, _) -> false | _ -> true
          in
          if declared.provided && not (replaceable declared.method_signature) then
            report state Not_replaceable name.span
              (Printf.sprintf
                 "`%s` gives `%s` a body, which an `impl` can replace only by a version proven to \
                  give the same result, and so only when the provided one is pure, has a `time` \
                  clause, and changes none of its arguments, so that its body is what it means."
                 shown_trait name.text);
          if trait.is_capability && not (receiver = Read || receiver = Mut) then
            report state Wrong_receiver name.span
              "A capability's implementation takes `self`, or `mut self` if it changes its own \
               state."
          else begin
            (* The method's own generic parameters and [uses], after the
               [impl]'s, which every method written inside it has. *)
            let given =
              {
                given with
                generics =
                  List.filteri
                    (fun index _ -> index >= List.length impl.impl_generics)
                    given.generics;
                uses =
                  List.filter
                    (fun capability -> not (List.mem capability impl.impl_uses))
                    given.uses;
              }
            in
            (* The trait method's own generic parameters are substituted by
               the [impl] method's, by position. *)
            let expected =
              T.map_signature normalize
                (T.substitute_signature
                   (Option.value ~default:[]
                      (T.substitution_of declared.method_signature.generics
                         (Types.generic_arguments given.generics)))
                   declared.method_signature)
            in
            let expected =
              if trait.is_capability then { expected with receiver = given.receiver } else expected
            in
            let expected = { expected with uses = normalize_capabilities expected.uses } in
            let parameters_agree =
              List.length expected.parameters = List.length given.parameters
              && List.for_all2
                   (fun (left : T.parameter_info) (right : T.parameter_info) ->
                     left.name = right.name && left.mode = right.mode
                     && agrees left.type_ right.type_)
                   expected.parameters given.parameters
            in
            let receivers_agree =
              Option.map fst expected.receiver = Option.map fst given.receiver
            in
            let generics_agree =
              List.length expected.generics = List.length given.generics
              && List.for_all2
                   (fun (expected_generic : T.generic) (given_generic : T.generic) ->
                     match (expected_generic.kind, given_generic.kind) with
                     | Type_generic expected_bounds, Type_generic given_bounds ->
                         (* No stronger bounds than the trait's. *)
                         List.for_all
                           (fun (bound : T.trait_reference) ->
                             List.exists
                               (fun (allowed : T.trait_reference) ->
                                 Path.equal allowed.trait bound.trait)
                               expected_bounds)
                           given_bounds
                     | left, right -> left = right)
                   expected.generics given.generics
            in
            if
              not
                (parameters_agree && receivers_agree && generics_agree
                && agrees_result expected.output given.output)
            then
              report state Signature_mismatch name.span
                (Printf.sprintf "`%s` must have the signature `%s%s` that `%s` declares." name.text
                   name.text (show_signature expected) shown_trait)
            else
              (* A caller of a capability holds only that capability, so the
                 implementation can use the capabilities that its [impl]
                 declares and no others. *)
              let allowed = if trait.is_capability then [] else expected.uses in
              if
                not
                  (List.for_all
                     (fun capability -> List.mem capability allowed)
                     (normalize_capabilities given.uses))
              then
                report state Impl_uses name.span
                  (if trait.is_capability then
                     Printf.sprintf
                       "`%s` implements a capability, so it can use only what its `impl` declares \
                        with `uses`."
                       name.text
                   else
                     Printf.sprintf "`%s` can use only the capabilities `%s` declares for it."
                       name.text shown_trait)
          end)

(* The definition *)

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
            Function_interface given ) -> (
            let name = Names.signature_name signature in
            match
              ( Query.demand database Names.definition container,
                Option.map
                  (fun (lowered : Environment.lowered) -> lowered.interface)
                  (Query.demand database Environment.lowered container) )
            with
            | Some { kind = Trait _; _ }, Some (Trait_interface trait) ->
                check_redeclared state name
                  (Names.receiver signature.parameters)
                  ~trait_path:container.path trait
            | Some { kind = Impl { trait_; _ }; _ }, Some (Impl_interface impl) ->
                check_impl_method state name (Names.receiver signature.parameters) given impl trait_
            | _ -> ())
        | Some _, _, _ -> ()
        | None, Function { signature; _ }, Function_interface lowered ->
            (* The proofs of callers in other packages read a [transparent]
               function's body as its definition, which only the body of a
               function in the logic is. *)
            (if lowered.transparent && not (T.body_is_definition lowered) then
               let span =
                 match signature.name with Plain_name name | Member_name (_, name) -> name.span
               in
               report state Not_a_definition span
                 "A `transparent` function's body is its definition in callers' proofs, so the \
                  function needs a `time` clause, no `uses` clause, no `mut` parameter, and a \
                  result that it returns.");
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
                  (Printf.sprintf "`%s` has no law `%s`." (T.show_trait trait) law.text)
            | _ -> ());
            (* A head with the wrong number of parameters is reported as that. *)
            let arity_matches =
              match for_type with
              | T.Named { path; _ } -> (
                  match Query.demand database Summary.generics_of path with
                  | Some expected -> List.length expected = List.length generics
                  | None -> true)
              | _ -> true
            in
            if arity_matches && not (T.is_error for_type) then
              match implements state for_type trait with
              | None ->
                  report state No_impl type_.span
                    (Printf.sprintf "`%s` does not implement `%s`, so it has no law of it to keep."
                       (T.show for_type) (T.show_trait trait))
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
                | Record fields -> List.map (fun (field : T.field) -> field.field_type) fields
                | Sum variants ->
                    List.concat_map
                      (fun (variant : T.variant) ->
                        List.map
                          (fun (field : T.field) -> field.field_type)
                          (Option.value ~default:[] variant.fields))
                      variants
                | _ -> [])
                name.span
        | None, Trait { name; generics; requires; _ }, Trait_interface trait ->
            check_no_capability_parameter state "the trait" name generics;
            check_trait_cycle state requires;
            check_private_in_public state
              (List.map (fun (bound : T.trait_reference) -> T.Any bound) trait.requires
              @ List.concat_map
                  (fun (method_ : T.trait_method) -> signature_types method_.method_signature)
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
        (Query.demand database Names.definition key, Query.demand database Environment.lowered key)
      with
      | Some definition, Some lowered ->
          let state = { database; key; definition; lowered; diagnostics = [] } in
          check state;
          List.sort
            (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
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
