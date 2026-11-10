(* Whether a release of a package keeps what the release before it offered,
   read from the two releases' public definitions. The types of a signature
   are compared as the checker worked them out, and a contract as it is
   written: a `requires` may lose clauses, an `ensures` and a cost may gain
   them. Whether a yielding method can be pulled is the one thing read from
   a body. *)

open Syntax
module T = Types
module Names = Resolve.Names
module Environment = Interface.Environment

type change = Breaks of string | Grows of string
type found = { path : Path.t; change : change }

(* A method written inside a trait or a capability is compared with that
   one, not on its own. *)
let public (declaration : Names.declaration) =
  declaration.ordinal = 0 && declaration.container = None
  &&
  match declaration.visibility with
  | Public | Public_opaque -> true
  | Private | Internal -> false

let declarations database package = Query.demand database Names.package_declarations package

let definition database declaration =
  Query.demand database Names.definition (Names.key_of declaration)

(* Contracts, as written *)

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
         [ Breaks "requires what it did not" ]
       else if missing_from requires_after requires_before <> [] then [ Grows "requires less" ]
       else []);
      (if missing_from ensures_after ensures_before <> [] then
         [ Breaks "no longer ensures what it did" ]
       else if missing_from ensures_before ensures_after <> [] then [ Grows "ensures more" ]
       else []);
      (if missing_from cost_after cost_before <> [] then
         [ Breaks "no longer promises a cost it did" ]
       else if missing_from cost_before cost_after <> [] then [ Grows "promises a cost more" ]
       else []);
    ]

(* Signatures *)

let signature ~(before : T.signature) ~(after : T.signature) =
  let same_parameters =
    List.length before.parameters = List.length after.parameters
    && List.for_all2
         (fun (was : T.parameter_info) (now : T.parameter_info) ->
           was.name = now.name && was.mode = now.mode && was.type_ = now.type_
           && (now.has_default || not was.has_default))
         before.parameters after.parameters
  in
  let gained_default =
    same_parameters
    && List.exists2
         (fun (was : T.parameter_info) (now : T.parameter_info) ->
           now.has_default && not was.has_default)
         before.parameters after.parameters
  in
  let more = missing_from before.uses after.uses and fewer = missing_from after.uses before.uses in
  List.concat
    [
      (if
         before.generics = after.generics && before.receiver = after.receiver && same_parameters
         && before.output = after.output
         && before.specification_only = after.specification_only
         && before.stores_functions = after.stores_functions
       then []
       else [ Breaks "has other parameters or another result" ]);
      (if before.terminates && not after.terminates then [ Breaks "no longer promises to end" ]
       else if after.terminates && not before.terminates then [ Grows "promises to end" ]
       else []);
      List.map
        (function
          | T.Capability path ->
              Breaks (Printf.sprintf "uses `%s`, which it did not" (Path.show path))
          | T.Capability_parameter parameter ->
              Breaks (Printf.sprintf "uses `%s`, which it did not" parameter.name))
        more;
      (if fewer <> [] then [ Grows "uses fewer capabilities" ] else []);
      (if gained_default then [ Grows "has a default it did not" ] else []);
    ]

(* How far a yielding method can be pulled as a cursor: for every element,
   for one that copies implicitly, or not at all. A user that pulls it
   relies on that, though it is worked out from the method's body. *)
let pulled database path (signature : T.signature) =
  match (Query.demand database Ownership.pullable path, signature.output) with
  | Pullable, _ -> 2
  | Yields_places, Yields (_, element)
    when Interface.Impls.plain database ~bounds:(fun _ -> []) element ->
      2
  | Yields_places, _ -> 1
  | (Yields_mut | Recursive), _ -> 0

let pulling ~before ~after path (old_signature : T.signature) (new_signature : T.signature) =
  match (old_signature.output, new_signature.output) with
  | Yields _, Yields _ ->
      let was = pulled before path old_signature and is = pulled after path new_signature in
      if is < was then [ Breaks "can no longer be pulled as it could" ]
      else if is > was then [ Grows "can be pulled where it could not" ]
      else []
  | _ -> []

let clauses_of (definition : definition option) =
  match definition with
  | Some { kind = Function { signature; _ }; _ } -> signature.clauses
  | Some { kind = Theorem { clauses; _ }; _ } -> clauses
  | _ -> []

(* Types *)

let type_clauses (definition : definition option) select =
  match definition with
  | Some { kind = Type_definition { clauses; _ }; _ } ->
      List.filter_map (fun (clause : type_clause) -> select clause.kind) clauses
  | _ -> []

let invariants definition =
  type_clauses definition (function
    | Type_invariant value -> Some (Syntax_print.expression value)
    | _ -> None)

let type_ ~(before : T.type_interface) ~(after : T.type_interface) ~before_definition
    ~after_definition =
  List.concat
    [
      (if before.type_generics <> after.type_generics then [ Breaks "has other generic parameters" ]
       else []);
      (match (before.opaque, after.opaque) with
      | true, true -> []
      | true, false -> [ Grows "shows its fields" ]
      | false, true -> [ Breaks "hides fields it showed" ]
      | false, false ->
          (if before.shape <> after.shape then [ Breaks "has other fields or variants" ] else [])
          @
          if invariants before_definition <> invariants after_definition then
            [ Breaks "has another invariant" ]
          else []);
      (if missing_from after.derives before.derives <> [] then
         [ Breaks "no longer derives a trait it did" ]
       else if missing_from before.derives after.derives <> [] then [ Grows "derives a trait more" ]
       else []);
    ]

(* Traits and capabilities *)

(* The clauses of a method written inside a trait or a capability, which
   is a definition of its own. *)
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

let trait ~(before : T.trait_interface) ~(after : T.trait_interface) ~before_definition
    ~after_definition ~clauses_before ~clauses_after =
  let same (was : T.trait_method) (now : T.trait_method) =
    was.method_name = now.method_name && was.method_receiver = now.method_receiver
  in
  let methods =
    List.concat_map
      (fun (was : T.trait_method) ->
        let named change =
          match change with
          | Breaks what -> Breaks (Printf.sprintf "its method `%s` %s" was.method_name what)
          | Grows what -> Grows (Printf.sprintf "its method `%s` %s" was.method_name what)
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
              @ if was.provided && not now.provided then [ Breaks "has no body any more" ] else []))
      before.methods
  in
  let gained =
    List.filter_map
      (fun (now : T.trait_method) ->
        if List.exists (fun was -> same was now) before.methods then None
        else if now.provided then
          Some (Grows (Printf.sprintf "has the method `%s`" now.method_name))
        else
          Some
            (Breaks
               (Printf.sprintf
                  "has the method `%s` without a body, which every `impl` of it would have to add"
                  now.method_name)))
      after.methods
  in
  List.concat
    [
      (if before.trait_generics <> after.trait_generics then
         [ Breaks "has other generic parameters" ]
       else []);
      (if before.requires <> after.requires then [ Breaks "requires other traits" ] else []);
      (if before.associated_types <> after.associated_types then
         [ Breaks "has other associated types" ]
       else []);
      (if laws before_definition <> laws after_definition then [ Breaks "has other laws" ] else []);
      methods;
      gained;
    ]

(* Constants *)

let constant_value database path (definition : definition option) =
  match Query.demand database Interface.Constants.value_of path with
  | Some _ as value -> `Value value
  | None -> (
      match definition with
      | Some { kind = Constant { value; _ }; _ } -> `Written (Syntax_print.expression value)
      | _ -> `Value None)

(* [impl]s *)

let impls database package =
  List.filter_map
    (fun (declaration : Names.declaration) ->
      if declaration.kind = Impl && declaration.ordinal = 0 then
        match Query.demand database Environment.impl_interface declaration.path with
        | Some (impl : T.impl_interface) when not impl.impl_broken ->
            Some
              ( declaration.path,
                Printf.sprintf "the `impl` of `%s` for `%s`" (T.show_trait impl.implements)
                  (T.show impl.for_type) )
        | _ -> None
      else None)
    (declarations database package)

let compare ~before ~after package =
  let old = List.filter public (declarations before package) in
  let now = List.filter public (declarations after package) in
  let found path change = { path; change } in
  let definitions =
    List.concat_map
      (fun (was : Names.declaration) ->
        let path = was.path in
        match List.find_opt (fun (other : Names.declaration) -> Path.equal other.path path) now with
        | None -> [ found path (Breaks "is gone, or is no longer public") ]
        | Some is when is.kind <> was.kind ->
            [ found path (Breaks "is another kind of definition") ]
        | Some is ->
            let before_definition = definition before was
            and after_definition = definition after is in
            List.map (found path)
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
              | Some (Type_interface old_type), Some (Type_interface new_type) ->
                  type_ ~before:old_type ~after:new_type ~before_definition ~after_definition
              | Some (Trait_interface old_trait), Some (Trait_interface new_trait) ->
                  trait ~before:old_trait ~after:new_trait ~before_definition ~after_definition
                    ~clauses_before:(member_clauses before path)
                    ~clauses_after:(member_clauses after path)
              | Some (Constant_interface old_constant), Some (Constant_interface new_constant) ->
                  (if old_constant.constant_type <> new_constant.constant_type then
                     [ Breaks "has another type" ]
                   else [])
                  @
                  if
                    constant_value before path before_definition
                    <> constant_value after path after_definition
                  then [ Breaks "has another value" ]
                  else []
              | _ -> []))
      old
  in
  let added =
    List.filter_map
      (fun (is : Names.declaration) ->
        if List.exists (fun (was : Names.declaration) -> Path.equal was.path is.path) old then None
        else Some (found is.path (Grows "is new")))
      now
  in
  let old_impls = impls before package and new_impls = impls after package in
  let impl_changes =
    List.filter_map
      (fun (path, shown) ->
        if List.exists (fun (_, other) -> other = shown) new_impls then None
        else Some (found path (Breaks (Printf.sprintf "is gone: %s" shown))))
      old_impls
    @ List.filter_map
        (fun (path, shown) ->
          if List.exists (fun (_, other) -> other = shown) old_impls then None
          else Some (found path (Grows (Printf.sprintf "is new: %s" shown))))
        new_impls
  in
  let targets =
    Query.demand before Workspace.exists package
    && Query.demand after Workspace.exists package
    && Query.demand before Workspace.usize_bits package = 32
    && Query.demand after Workspace.usize_bits package = 64
  in
  (definitions @ added @ impl_changes, targets)

let breaks found =
  List.filter_map
    (fun { path; change } -> match change with Breaks what -> Some (path, what) | Grows _ -> None)
    found

let grows found =
  List.filter_map
    (fun { path; change } -> match change with Grows what -> Some (path, what) | Breaks _ -> None)
    found
