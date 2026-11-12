(* Whether a release of a package is compatible with the previous release,
   by comparing the two releases' public definitions. A signature's types
   are compared after type checking, and a contract syntactically: a
   release may remove [requires] clauses and add [ensures] and cost
   clauses. Whether a yielding method can be pulled is the only property
   inferred from a body. *)

open Syntax
module Names = Resolve.Names
module Environment = Interface.Environment

type change = Breaks of string | Grows of string
type public_change = { path : Path.t; change : change }

(* A method declared inside a trait or a capability is compared as part of
   its trait or capability, not separately. *)
let public (declaration : Names.declaration) =
  declaration.ordinal = 0 && declaration.container = None && Names.is_public declaration.visibility

let declarations database package = Query.demand database Names.package_declarations package

let definition database declaration =
  Query.demand database Names.definition (Names.key_of declaration)

let written kind (clauses : clause list) =
  List.filter_map
    (fun (clause : clause) ->
      match (kind, clause.kind) with
      | `Requires, Requires _ | `Ensures, Ensures _ | `Cost, Cost _ ->
          Some (Syntax_print.clause clause)
      | _ -> None)
    clauses

let missing_from present wanted = List.filter (fun clause -> not (List.mem clause present)) wanted

let contract ~(before : clause list) ~(after : clause list) =
  let pair kind = (written kind before, written kind after) in
  let requires_before, requires_after = pair `Requires in
  let ensures_before, ensures_after = pair `Ensures in
  let cost_before, cost_after = pair `Cost in
  List.concat
    [
      (if missing_from requires_before requires_after <> [] then
         [ Breaks "has a `requires` clause it did not have" ]
       else if missing_from requires_after requires_before <> [] then
         [ Grows "has fewer `requires` clauses" ]
       else []);
      (if missing_from ensures_after ensures_before <> [] then [ Breaks "lost an `ensures` clause" ]
       else if missing_from ensures_before ensures_after <> [] then
         [ Grows "has more `ensures` clauses" ]
       else []);
      (if missing_from cost_after cost_before <> [] then [ Breaks "lost a `cost` clause" ]
       else if missing_from cost_before cost_after <> [] then [ Grows "has more `cost` clauses" ]
       else []);
    ]

let uses_more : Types.capability -> change = function
  | Capability path -> Breaks (Printf.sprintf "now uses `%s`" (Path.show path))
  | (Capability_parameter _ | Capability_projection _) as capability ->
      Breaks (Printf.sprintf "now uses `%s`" (Types.show_capability capability))
  | Capability_variable _ ->
      Compiler_bug.bug ~stage:"Compatibility" "a signature holds an unknown set of capabilities"

let signature ~(before : Types.signature) ~(after : Types.signature) =
  let same_parameters =
    List.length before.parameters = List.length after.parameters
    && List.for_all2
         (fun (was : Types.parameter_info) (now : Types.parameter_info) ->
           was.name = now.name && was.mode = now.mode && was.type_ = now.type_
           && (now.has_default || not was.has_default))
         before.parameters after.parameters
  in
  let gained_default =
    same_parameters
    && List.exists2
         (fun (was : Types.parameter_info) (now : Types.parameter_info) ->
           now.has_default && not was.has_default)
         before.parameters after.parameters
  in
  let more = Types.capability_difference after.uses before.uses
  and fewer = Types.capability_difference before.uses after.uses in
  List.concat
    [
      (if
         before.generics = after.generics && before.receiver = after.receiver && same_parameters
         && before.output = after.output
         && before.specification_only = after.specification_only
         && before.stores_functions = after.stores_functions
       then []
       else [ Breaks "changed its parameters or its result" ]);
      (if before.transparent && not after.transparent then
         [ Breaks "is no longer `transparent`, so callers' proofs cannot read its body" ]
       else if after.transparent && not before.transparent then [ Grows "is `transparent`" ]
       else []);
      (if before.terminates && not after.terminates then
         [ Breaks "no longer promises to terminate" ]
       else if after.terminates && not before.terminates then [ Grows "promises to terminate" ]
       else []);
      List.map uses_more (more :> Types.capability list);
      (if fewer <> Types.no_capabilities then [ Grows "uses fewer capabilities" ] else []);
      (if gained_default then [ Grows "gained a default" ] else []);
    ]

(* Whether a yielding method can be pulled as a cursor: for every element
   type, only for an element type that copies implicitly, or not at all. A
   caller that pulls the method relies on this, although it is inferred
   from the method's body. *)
let pulled database path (signature : Types.signature) =
  match (Query.demand database Ownership.pullable path, signature.output) with
  | Pullable, _ -> 2
  | Yields_places, Yields (_, element)
    when Interface.Impls.plain database ~bounds:(fun _ -> []) element ->
      2
  | Yields_places, _ -> 1
  | (Yields_mut | Recursive), _ -> 0

let pulling ~before ~after path (old_signature : Types.signature) (new_signature : Types.signature)
    =
  match (old_signature.output, new_signature.output) with
  | Yields _, Yields _ ->
      let was = pulled before path old_signature and is = pulled after path new_signature in
      if is < was then [ Breaks "can be pulled as a cursor in fewer cases" ]
      else if is > was then [ Grows "can be pulled as a cursor in more cases" ]
      else []
  | _ -> []

(* The proofs of callers in other packages read a [transparent] function's
   body as its definition, so a changed body can invalidate those
   proofs. *)
let transparent_body ~(before : Types.signature) ~(after : Types.signature)
    ~(before_definition : definition option) ~(after_definition : definition option) =
  let written (definition : definition option) =
    match definition with
    | Some { kind = Function { body; _ }; _ } ->
        Some (List.map Syntax_print.statement body.statements)
    | _ -> None
  in
  if
    before.transparent && after.transparent && written before_definition <> written after_definition
  then [ Breaks "changed its body, which callers' proofs read" ]
  else []

let clauses_of (definition : definition option) =
  match definition with
  | Some { kind = Function { signature; _ }; _ } -> signature.clauses
  | Some { kind = Theorem { clauses; _ }; _ } -> clauses
  | _ -> []

let type_clauses (definition : definition option) select =
  match definition with
  | Some { kind = Type_definition { clauses; _ }; _ } ->
      List.filter_map (fun (clause : type_clause) -> select clause.kind) clauses
  | _ -> []

let invariants definition =
  type_clauses definition (function
    | Type_invariant value -> Some (Syntax_print.expression value)
    | _ -> None)

let type_ ~(before : Types.type_interface) ~(after : Types.type_interface) ~before_definition
    ~after_definition =
  List.concat
    [
      (if before.type_generics <> after.type_generics then
         [ Breaks "changed its generic parameters" ]
       else []);
      (match (before.opaque, after.opaque) with
      | true, true -> []
      | true, false -> [ Grows "made its fields visible" ]
      | false, true -> [ Breaks "hid its fields" ]
      | false, false ->
          (if before.shape <> after.shape then [ Breaks "changed its fields or variants" ] else [])
          @
          if invariants before_definition <> invariants after_definition then
            [ Breaks "changed its invariant" ]
          else []);
      (if missing_from after.derives before.derives <> [] then
         [ Breaks "no longer derives a trait" ]
       else if missing_from before.derives after.derives <> [] then
         [ Grows "derives another trait" ]
       else []);
    ]

(* The clauses of a method declared inside a trait or a capability, which
   is a separate definition. *)
let member_clauses database (owner : Path.t) name receiver =
  match Interface.Summary.definition database (Method { owner; name; receiver }) with
  | Some (_, { kind = Function { signature; _ } | Method_declaration signature; _ }) ->
      Some signature.clauses
  | _ -> None

let laws (definition : definition option) =
  match definition with
  | Some { kind = Trait { members; _ }; _ } ->
      List.sort String.compare
        (List.filter_map
           (fun (member : trait_member line) ->
             match member.kind with Law law -> Some (Syntax_print.law law) | _ -> None)
           members)
  | _ -> []

let trait ~(before : Types.trait_interface) ~(after : Types.trait_interface) ~before_definition
    ~after_definition ~clauses_before ~clauses_after =
  let same (was : Types.trait_method) (now : Types.trait_method) =
    was.method_name = now.method_name && was.method_receiver = now.method_receiver
  in
  let methods =
    List.concat_map
      (fun (was : Types.trait_method) ->
        let named change =
          match change with
          | Breaks description ->
              Breaks (Printf.sprintf "its method `%s` %s" was.method_name description)
          | Grows description ->
              Grows (Printf.sprintf "its method `%s` %s" was.method_name description)
        in
        match List.find_opt (same was) after.methods with
        | None -> [ Breaks (Printf.sprintf "no longer has the method `%s`" was.method_name) ]
        | Some now ->
            List.map named
              (signature ~before:was.method_signature ~after:now.method_signature
              @ contract
                  ~before:
                    (Option.value ~default:[] (clauses_before was.method_name was.method_receiver))
                  ~after:
                    (Option.value ~default:[] (clauses_after now.method_name now.method_receiver))
              @ if was.provided && not now.provided then [ Breaks "lost its default body" ] else []
              ))
      before.methods
  in
  let gained =
    List.filter_map
      (fun (now : Types.trait_method) ->
        if List.exists (fun was -> same was now) before.methods then None
        else if now.provided then
          Some (Grows (Printf.sprintf "gained the method `%s`" now.method_name))
        else
          Some
            (Breaks
               (Printf.sprintf
                  "gained the method `%s` without a default body, which every `impl` must then \
                   define"
                  now.method_name)))
      after.methods
  in
  List.concat
    [
      (if before.trait_generics <> after.trait_generics then
         [ Breaks "changed its generic parameters" ]
       else []);
      (if before.requires <> after.requires then [ Breaks "changed its supertraits" ] else []);
      (if before.associated_types <> after.associated_types then
         [ Breaks "changed its associated types" ]
       else []);
      (if missing_from after.associated_capabilities before.associated_capabilities <> [] then
         [ Breaks "lost an associated capability set" ]
       else if missing_from before.associated_capabilities after.associated_capabilities <> [] then
         [ Grows "gained an associated capability set" ]
       else []);
      (if laws before_definition <> laws after_definition then [ Breaks "changed its laws" ] else []);
      methods;
      gained;
    ]

let constant_value database path (definition : definition option) =
  match Query.demand database Interface.Constants.value_of path with
  | Some _ as value -> `Value value
  | None -> (
      match definition with
      | Some { kind = Constant { value; _ }; _ } -> `Written (Syntax_print.expression value)
      | _ -> `Value None)

let impls database package =
  List.filter_map
    (fun (declaration : Names.declaration) ->
      if declaration.kind = Impl && declaration.ordinal = 0 then
        match Query.demand database Environment.impl_interface declaration.path with
        | Some (impl : Types.impl_interface) when not impl.impl_broken ->
            Some
              ( declaration.path,
                Printf.sprintf "the `impl` of `%s` for `%s`"
                  (Types.show_trait impl.implements)
                  (Types.show impl.for_type),
                impl.capability_sets )
        | _ -> None
      else None)
    (declarations database package)

let compare ~before ~after package =
  let old = List.filter public (declarations before package) in
  let now = List.filter public (declarations after package) in
  let public_change path change = { path; change } in
  let definitions =
    List.concat_map
      (fun (was : Names.declaration) ->
        let path = was.path in
        match List.find_opt (fun (other : Names.declaration) -> Path.equal other.path path) now with
        | None -> [ public_change path (Breaks "was removed or is no longer public") ]
        | Some is when is.kind <> was.kind ->
            [ public_change path (Breaks "became another kind of definition") ]
        | Some is ->
            let before_definition = definition before was
            and after_definition = definition after is in
            List.map (public_change path)
              (match
                 ( Query.demand before Environment.interface path,
                   Query.demand after Environment.interface path )
               with
              | ( Some (Function_interface old_signature | Theorem_interface old_signature),
                  Some (Function_interface new_signature | Theorem_interface new_signature) ) ->
                  signature ~before:old_signature ~after:new_signature
                  @ contract ~before:(clauses_of before_definition)
                      ~after:(clauses_of after_definition)
                  @ pulling ~before ~after path old_signature new_signature
                  @ transparent_body ~before:old_signature ~after:new_signature ~before_definition
                      ~after_definition
              | Some (Type_interface old_type), Some (Type_interface new_type) ->
                  type_ ~before:old_type ~after:new_type ~before_definition ~after_definition
              | Some (Trait_interface old_trait), Some (Trait_interface new_trait) ->
                  trait ~before:old_trait ~after:new_trait ~before_definition ~after_definition
                    ~clauses_before:(member_clauses before path)
                    ~clauses_after:(member_clauses after path)
              | Some (Constant_interface old_constant), Some (Constant_interface new_constant) ->
                  (if old_constant.constant_type <> new_constant.constant_type then
                     [ Breaks "changed its type" ]
                   else [])
                  @
                  if
                    constant_value before path before_definition
                    <> constant_value after path after_definition
                  then [ Breaks "changed its value" ]
                  else []
              | _ -> []))
      old
  in
  let added =
    List.filter_map
      (fun (is : Names.declaration) ->
        if List.exists (fun (was : Names.declaration) -> Path.equal was.path is.path) old then None
        else Some (public_change is.path (Grows "is new")))
      now
  in
  let old_impls = impls before package and new_impls = impls after package in
  let impl_changes =
    (* A caller of the trait's methods on the type needs every capability
       in an associated capability set, so adding a capability to the set
       is incompatible. *)
    List.concat_map
      (fun (path, shown, old_sets) ->
        match List.find_opt (fun (_, other, _) -> other = shown) new_impls with
        | None -> [ public_change path (Breaks (Printf.sprintf "was removed: %s" shown)) ]
        | Some (_, _, new_sets) ->
            let set name sets =
              Option.value ~default:Types.no_capabilities (List.assoc_opt name sets)
            in
            List.concat_map
              (fun name ->
                let was = set name old_sets and is = set name new_sets in
                List.map
                  (fun capability ->
                    public_change path
                      (Breaks
                         (Printf.sprintf "added `%s` to its `%s`: %s"
                            (Types.show_capability capability)
                            name shown)))
                  (Types.capability_difference is was :> Types.capability list)
                @
                if Types.capability_difference was is <> Types.no_capabilities then
                  [
                    public_change path
                      (Grows (Printf.sprintf "removed capabilities from its `%s`: %s" name shown));
                  ]
                else [])
              (List.sort_uniq String.compare (List.map fst (old_sets @ new_sets))))
      old_impls
    @ List.filter_map
        (fun (path, shown, _) ->
          if List.exists (fun (_, other, _) -> other = shown) old_impls then None
          else Some (public_change path (Grows (Printf.sprintf "is new: %s" shown))))
        new_impls
  in
  let targets =
    Query.demand before Workspace.exists package
    && Query.demand after Workspace.exists package
    && Query.demand before Workspace.usize_bits package = 32
    && Query.demand after Workspace.usize_bits package = 64
  in
  (definitions @ added @ impl_changes, targets)

let breaks changes =
  List.filter_map
    (fun { path; change } ->
      match change with Breaks description -> Some (path, description) | Grows _ -> None)
    changes

let grows changes =
  List.filter_map
    (fun { path; change } ->
      match change with Grows description -> Some (path, description) | Breaks _ -> None)
    changes
