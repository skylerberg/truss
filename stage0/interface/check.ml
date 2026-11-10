(* Checking each definition's outward-facing part.

   These checks read other definitions' interfaces, such as the [impl]s
   that decide whether a bound holds, so they run apart from lowering: an
   interface never waits on a check of itself. *)

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
  let diagnostic =
    Diagnostic.make ?fixes ~code:(Types code) (Source.span span.start span.stop) message
  in
  state.diagnostics <- diagnostic :: state.diagnostics;
  Diagnostic.reported diagnostic

let report state ?fixes code span message = ignore (reported state ?fixes code span message)

let bounds state parameter =
  Option.value ~default:[] (List.assoc_opt parameter state.lowered.bounds)

let implements state type_ trait =
  Impls.implements state.database ~bounds:(bounds state) type_ trait

(* Bounds a type's arguments must meet *)

(* The bounds each written type's arguments must meet, each as a diagnostic
   where it does not hold, or where the [impl] it is met by uses what its
   package is not granted. Bodies check the types their annotations write
   the same way. *)
let bound_diagnostics database ~package ~bounds named =
  let diagnostic code (span : span) message =
    Diagnostic.make ~code (Source.span span.start span.stop) message
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
  | T.Function { inputs; output; _ } -> (
      List.concat_map (fun (_, type_) -> mentioned type_) inputs
      @ match output with Returns type_ | Yields (_, type_) | Lends (_, type_) -> mentioned type_)
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
  if state.definition.visibility = Public || state.definition.visibility = Public_opaque then
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
                 (Path.show owner) owner_module.package)
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
  (match signature.output with Returns type_ | Yields (_, type_) | Lends (_, type_) -> type_)
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
       type_ =
         Named
           {
             path = Top { name = "List"; module_ };
             arguments = [ Type (Named { path = Top { name = "String"; _ }; arguments = [] }) ];
           };
       has_default = false;
     };
    ] ->
        module_.package = "standard"
    | _ -> false
  in
  let exit_code =
    match signature.output with
    | Returns (Named { path = Top { name = "ExitCode"; module_ }; arguments = [] }) ->
        module_.package = "standard"
    | _ -> false
  in
  if not (list_of_string && exit_code && signature.generics = [] && signature.receiver = None) then
    report state Main_signature span main_message

(* Defaults are constant expressions that name no parameter. *)
let rec constant_expression state (resolved : Resolve.resolved) (value : expression) =
  let recurse = constant_expression state resolved in
  match value.kind with
  | Integer _ | Float _ | True | False -> true
  | String literal -> literal.rest = []
  | Parenthesized inner | Prefix (_, inner) -> recurse inner
  | Binary { left; right; _ } -> recurse left && recurse right
  | Name path -> (
      match resolved.names.(path.last.id) with
      | Some (Definition _ | Variant _) -> true
      | Some (Local _ | Type_parameter _ | Capability_parameter _ | Value_parameter _) -> false
      | _ -> true)
  | Member (base, _) -> recurse base
  | Bracket (base, items) ->
      recurse base
      && List.for_all (function Item item -> recurse item | Item_constraint _ -> true) items
  | Call (callee, arguments) ->
      (* Building a record or variant, never running code: an UpperCamelCase
         name before the parentheses. *)
      let builds =
        match callee.kind with
        | Name path ->
            String.length path.last.text > 0
            && Char.uppercase_ascii path.last.text.[0] = path.last.text.[0]
        | Member (_, member) -> Char.uppercase_ascii member.text.[0] = member.text.[0]
        | _ -> false
      in
      builds && List.for_all (fun (argument : argument) -> recurse argument.value) arguments
  | List items -> List.for_all recurse items
  | Map entries -> List.for_all (fun (key, item) -> recurse key && recurse item) entries
  | _ -> false

let check_default state resolved (value : expression) =
  if not (constant_expression state resolved value) then
    report state Default_not_constant value.span
      "A default must be a constant expression: literals, arithmetic, constants, and records, \
       variants, and collections built from them. It cannot call a function or name a parameter."

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

let trait_named (path : Path.t) name =
  match path with
  | Top { name = found; module_ } -> found = name && module_.package = "standard"
  | _ -> false

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
                      (Impls.derivable trait || trait_named trait "Copyable"
                     || trait_named trait "Plain")
                  then
                    report state Not_derivable written.span
                      (Printf.sprintf
                         "Only `Equal`, `Hash`, `Ordered`, `Default`, `Copyable`, and `Plain` can \
                          be derived, not `%s`."
                         shown)
                  else if trait_named trait "Copyable" || trait_named trait "Plain" then
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
                            if trait_named trait "Plain" then
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
                      if (not property_holds) || (trait_named trait "Plain" && allocates) then
                        report state Cannot_derive written.span
                          (Printf.sprintf "A field of this type is not `%s`, so the type cannot be."
                             shown)
                    end
                  else begin
                    if trait_named trait "Ordered" || trait_named trait "Hash" then
                      if
                        not
                          (List.exists
                             (fun derived -> trait_named derived "Equal")
                             interface.derives)
                      then
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

let check_redeclared state (members : trait_member line list) (trait : T.trait_interface) =
  let inherited =
    List.concat_map
      (fun (required : T.trait_reference) ->
        List.concat_map
          (fun (bound : T.trait_reference) ->
            match Query.demand state.database Environment.trait_interface bound.trait with
            | Some interface ->
                List.map
                  (fun (method_ : T.trait_method) -> (method_.method_name, bound.trait))
                  interface.methods
            | None -> [])
          (Properties.bound_closure state.database
             ~self:(T.Parameter { owner = state.key.path; name = "Self" })
             required))
      trait.requires
  in
  List.iter
    (fun (line : trait_member line) ->
      match line.kind with
      | Trait_method { signature = { name = Plain_name name | Member_name (_, name); _ }; _ } -> (
          match List.assoc_opt name.text inherited with
          | Some from ->
              report state Redeclared_method name.span
                (Printf.sprintf
                   "`%s` already declares `%s`, so a trait that requires it cannot declare it \
                    again."
                   (Path.show from) name.text)
          | None -> ())
      | _ -> ())
    members

(* [impl]s *)

let panic_path : Path.t =
  Top { module_ = { package = "standard"; modules = [ "capabilities" ] }; name = "Panic" }

let show_signature (signature : T.signature) =
  let mode = function T.Read -> "" | Mut -> "mut " | Own -> "own " in
  Printf.sprintf "(%s)%s"
    (String.concat ", "
       ((match signature.receiver with
          | Some (Read, _) -> [ "self" ]
          | Some (Mut, _) -> [ "mut self" ]
          | Some (Own, _) -> [ "own self" ]
          | _ -> [])
       @ List.map
           (fun (parameter : T.parameter_info) ->
             parameter.name ^ ": " ^ mode parameter.mode ^ T.show parameter.type_)
           signature.parameters))
    (match signature.output with
    | Returns type_ when type_ = T.unit -> ""
    | Returns type_ -> " -> " ^ T.show type_
    | Yields (written, type_) -> " yields " ^ mode written ^ T.show type_
    | Lends (written, type_) -> " lends " ^ mode written ^ T.show type_)

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

let map_signature f (signature : T.signature) =
  {
    signature with
    receiver = Option.map (fun (receiver, type_) -> (receiver, f type_)) signature.receiver;
    parameters =
      List.map
        (fun (parameter : T.parameter_info) -> { parameter with type_ = f parameter.type_ })
        signature.parameters;
    output =
      (match signature.output with
      | Returns type_ -> Returns (f type_)
      | Yields (mode, type_) -> Yields (mode, f type_)
      | Lends (mode, type_) -> Lends (mode, f type_));
  }

let check_impl state (written_members : impl_member line list) (impl : T.impl_interface)
    (trait_path : path_type) =
  let database = state.database in
  let shown_trait = Names.spell_path trait_path.path in
  let impl_bounds parameter =
    match
      List.find_opt (fun (generic : T.generic) -> generic.generic = parameter) impl.impl_generics
    with
    | Some { kind = Type_generic bounds; _ } -> bounds
    | _ -> bounds state parameter
  in
  let check_evidence_grants (span : span) evidence =
    state.diagnostics <-
      List.map
        (Diagnostic.make ~code:(Capabilities Not_granted) (Source.span span.start span.stop))
        (Grants.evidence_messages database ~package:state.key.module_.package ~bounds:impl_bounds
           evidence)
      @ state.diagnostics
  in
  if Path.equal impl.implements.trait panic_path then
    report state Implements_panic trait_path.span
      "Nothing can implement `Panic`, since a panic cannot be caught."
  else if
    Path.equal impl.implements.trait Properties.copyable_trait
    || Path.equal impl.implements.trait Properties.plain_trait
  then
    report state Implements_built_in trait_path.span
      (Printf.sprintf
         "The compiler implements `%s` from a type's fields; no `impl` of it can be written."
         shown_trait)
  else
    match Query.demand database Environment.trait_interface impl.implements.trait with
    | None -> ()
    | Some trait ->
        let substitution =
          Properties.trait_substitution trait ~self:impl.for_type impl.implements
        in
        (* An associated type the trait declares and this [impl] does not
           give is reported once, here, and is an error wherever a method's
           signature mentions it. *)
        let missing_associated =
          List.filter_map
            (fun (associated : T.associated_type) ->
              if List.mem_assoc associated.associated_name impl.implements.associated then None
              else
                Some
                  ( associated.associated_name,
                    reported state Missing_member trait_path.span
                      (Printf.sprintf "This `impl` must give `type %s`, which `%s` declares."
                         associated.associated_name shown_trait) ))
            trait.associated_types
        in
        (* The trait's types as this [impl] sees them: [Self] its type, and
           each associated type of [Self] what this [impl], or the [impl] of
           a trait it requires, chooses. *)
        let normalize type_ =
          T.map
            (function
              | T.Projection { base; trait = projected; name } when T.equal base impl.for_type -> (
                  match
                    ( List.assoc_opt name impl.implements.associated,
                      List.assoc_opt name missing_associated )
                  with
                  | Some fixed, _ -> Some fixed
                  | None, Some report when Path.equal projected.trait impl.implements.trait ->
                      Some (T.Error report)
                  | None, _ ->
                      Impls.associated_type database ~bounds:impl_bounds impl.for_type projected
                        name)
              | _ -> None)
            (T.substitute substitution type_)
        in
        let given_names =
          List.filter_map
            (fun (line : impl_member line) ->
              match line.kind with
              | Impl_method { signature; _ } ->
                  let name =
                    match signature.name with Plain_name name | Member_name (_, name) -> name
                  in
                  Some (`Method (name, Names.receiver signature.parameters))
              | Associated_definition (name, _) -> Some (`Associated name)
              | Impl_member_error -> None)
            written_members
        in
        (* Every method without a body is given, and for a capability every
           method, since a capability's methods have none. *)
        List.iter
          (fun (method_ : T.trait_method) ->
            let given =
              List.exists
                (function
                  | `Method ((name : name), receiver) ->
                      name.text = method_.method_name
                      && (trait.is_capability || receiver = method_.method_receiver)
                  | `Associated _ -> false)
                given_names
            in
            if (not given) && not method_.provided then
              report state Missing_member trait_path.span
                (Printf.sprintf "This `impl` must give `%s%s`, which `%s` declares."
                   method_.method_name
                   (show_signature (map_signature normalize method_.method_signature))
                   shown_trait))
          trait.methods;
        List.iter
          (fun (associated : T.associated_type) ->
            match List.assoc_opt associated.associated_name impl.implements.associated with
            | None -> ()
            | Some chosen ->
                (* What an [impl] chooses meets the bounds the trait declares. *)
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
        List.iter
          (function
            | `Method ((name : name), receiver) -> (
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
                      (Printf.sprintf "`%s` declares no method `%s` with this receiver." shown_trait
                         name.text)
                | Some declared -> (
                    match
                      List.find_opt
                        (fun (method_name, method_receiver, _) ->
                          method_name = name.text && method_receiver = receiver)
                        impl.impl_methods
                    with
                    | None -> ()
                    | Some (_, _, given) ->
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
                               "`%s` gives `%s` a body, which an `impl` can replace only by a \
                                version proven to give the same result, and so only when the \
                                provided one is pure, has a `time` clause, and changes none of its \
                                arguments, so that its body is what it means."
                               shown_trait name.text);
                        if trait.is_capability && not (receiver = Read || receiver = Mut) then
                          report state Wrong_receiver name.span
                            "A capability's implementation takes `self`, or `mut self` if it \
                             changes its own state."
                        else begin
                          (* The trait method's own generic parameters stand for
                             the [impl] method's, by position. *)
                          let generic_substitution =
                            if
                              List.length declared.method_signature.generics
                              = List.length given.generics
                            then
                              List.map2
                                (fun (expected : T.generic) (actual : T.generic) ->
                                  (expected.generic, T.Type (T.Parameter actual.generic)))
                                declared.method_signature.generics given.generics
                            else []
                          in
                          let expected =
                            map_signature
                              (fun type_ -> normalize (T.substitute generic_substitution type_))
                              declared.method_signature
                          in
                          let expected =
                            if trait.is_capability then { expected with receiver = given.receiver }
                            else expected
                          in
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
                                             (List.map
                                                (T.substitute_trait generic_substitution)
                                                expected_bounds))
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
                              (Printf.sprintf
                                 "`%s` must have the signature `%s%s` that `%s` declares." name.text
                                 name.text (show_signature expected) shown_trait)
                          else if not trait.is_capability then
                            let allowed =
                              List.map
                                (function
                                  | T.Capability_parameter parameter -> (
                                      match List.assoc_opt parameter generic_substitution with
                                      | Some (T.Type (T.Parameter actual)) ->
                                          T.Capability_parameter actual
                                      | _ -> T.Capability_parameter parameter)
                                  | capability -> capability)
                                declared.method_signature.uses
                            in
                            if
                              not
                                (List.for_all
                                   (fun capability -> List.mem capability allowed)
                                   given.uses)
                            then
                              report state Impl_uses name.span
                                (Printf.sprintf
                                   "`%s` can use only the capabilities `%s` declares for it."
                                   name.text shown_trait)
                        end))
            | `Associated (name : name) ->
                if
                  not
                    (List.exists
                       (fun (associated : T.associated_type) ->
                         associated.associated_name = name.text)
                       trait.associated_types)
                then
                  report state Extra_member name.span
                    (Printf.sprintf "`%s` declares no associated type `%s`." shown_trait name.text))
          given_names;
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
        match (definition.kind, state.lowered.interface) with
        | Function { signature; _ }, Function_interface lowered ->
            (match signature.name with
            | Member_name (head, _) -> check_method_location state head
            | Plain_name name ->
                if name.text = "main" && state.key.module_.modules = [ "main" ] then
                  check_main state lowered name.span);
            List.iter
              (fun (parameter : parameter) ->
                match parameter.kind with
                | Named_parameter { default = Some value; _ } -> check_default state resolved value
                | _ -> ())
              signature.parameters;
            let span =
              match signature.name with Plain_name name | Member_name (_, name) -> name.span
            in
            check_private_in_public state (signature_types lowered) span
        | Type_definition { name; body; clauses; _ }, Type_interface interface ->
            (match body with
            | Fields fields ->
                check_duplicates state "field" (field_names fields);
                List.iter
                  (fun (field : field) ->
                    match field.kind with
                    | Field_declaration { default = Some value; _ } ->
                        check_default state resolved value
                    | _ -> ())
                  fields
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
        | Trait { name; requires; members; _ }, Trait_interface trait ->
            check_trait_cycle state requires;
            check_redeclared state members trait;
            check_private_in_public state
              (List.map (fun (bound : T.trait_reference) -> T.Any bound) trait.requires
              @ List.concat_map
                  (fun (method_ : T.trait_method) -> signature_types method_.method_signature)
                  trait.methods)
              name.span
        | Constant { name = Plain_name name; _ }, Constant_interface constant ->
            check_private_in_public state [ constant.constant_type ] name.span
        | Impl { trait_; members; _ }, Impl_interface impl -> check_impl state members impl trait_
        | Constant { name = Member_name (head, _); _ }, _ -> check_method_location state head
        | _ -> ())

let diagnostics =
  Query.query ~name:"interface_diagnostics" ~phase:Interfaces ~saved:true ~show:Names.show_key
    (fun database key ->
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

(* The report of a definition whose interface has an error, for a use of it
   that the error leaves nothing to check against. *)
let reported database (path : Path.t) =
  match Query.demand database Summary.key path with
  | Some key -> (
      match Query.demand database diagnostics key with
      | first :: _ -> Some (Diagnostic.reported first)
      | [] -> None)
  | None -> None
