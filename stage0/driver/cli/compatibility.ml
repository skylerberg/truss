type change = Breaks of string | Grows of string
type public_change = { path : Path.t; change : change }
type side = { database : Database.t; lookups : Interface.Lookups.t }

let is_public (side : side) (declaration : Resolve.Names.declaration) =
  declaration.ordinal = 0
  && side.lookups.names.find_container (Resolve.Names.make_key declaration) = None
  && Resolve.Names.is_public declaration.visibility

let list_declarations (side : side) package = side.lookups.names.list_package_declarations package

let read_form (side : side) key =
  Option.map
    (fun (checked : Infer.checked) -> checked.form.definition)
    (Database.read_checked_body side.database key)

let no_contract : Core.contract = { requires = []; ensures = []; decreases = []; costs = [] }

let read_contract side key =
  match read_form side key with
  | Some (Function { parameters; contract; _ }) -> (parameters, contract)
  | _ -> ([], no_contract)

let loses ~equal ~before ~after =
  List.exists (fun was -> not (List.exists (fun now -> equal was now) after)) before

let gains ~equal ~before ~after =
  List.exists (fun now -> not (List.exists (fun was -> equal was now) before)) after

let compare_contracts ~before:(before_parameters, (before : Core.contract))
    ~after:(after_parameters, (after : Core.contract)) =
  let parameters = (before_parameters, after_parameters) in
  let compute_difference equal before after =
    (loses ~equal ~before ~after, gains ~equal ~before ~after)
  in
  let lost_requires, gained_requires =
    compute_difference (Core_equivalence.equal_condition ~parameters) before.requires after.requires
  and lost_ensures, gained_ensures =
    compute_difference (Core_equivalence.equal_expression ~parameters) before.ensures after.ensures
  and lost_costs, gained_costs =
    compute_difference (Core_equivalence.equal_cost ~parameters) before.costs after.costs
  in
  List.concat
    [
      (if gained_requires then [ Breaks "has a `requires` clause it did not have" ]
       else if lost_requires then [ Grows "has fewer `requires` clauses" ]
       else []);
      (if lost_ensures then [ Breaks "lost an `ensures` clause" ]
       else if gained_ensures then [ Grows "has more `ensures` clauses" ]
       else []);
      (if lost_costs then [ Breaks "lost a `cost` clause" ]
       else if gained_costs then [ Grows "has more `cost` clauses" ]
       else []);
    ]

let make_uses_more : Types.capability -> change = function
  | Capability path -> Breaks (Printf.sprintf "now uses `%s`" (Path.show path))
  | (Capability_parameter _ | Capability_projection _) as capability ->
      Breaks (Printf.sprintf "now uses `%s`" (Types.show_capability capability))
  | Capability_variable _ | Divergence (Of_variable _) ->
      Compiler_bug.raise_bug ~stage:"Compatibility"
        "a signature holds an unknown set of capabilities"
  | Capability_error _ ->
      Compiler_bug.raise_bug ~stage:"Compatibility" "a signature holds a capability with an error"
  | Divergence Always -> Breaks "no longer promises to terminate"
  | Divergence (Of_parameter { name; _ }) ->
      Breaks (Printf.sprintf "may not terminate where `%s` may not" name)

let converts ~(actual : Types.function_type) ~(expected : Types.function_type) =
  actual.inputs = expected.inputs
  && Types.equal actual.output expected.output
  && Types.subtract_capabilities actual.uses expected.uses = Types.no_capabilities
  && Types.costs_imply ~provided:actual.costs ~required:expected.costs

type parameter_change = Unchanged | Generalized of string | Widened of string | Incompatible

let compare_parameter ~instantiate ((was : Types.parameter_info), (now : Types.parameter_info)) =
  if was.name <> now.name || was.mode <> now.mode || (was.has_default && not now.has_default) then
    Incompatible
  else
    match (was.type_, now.type_) with
    | old_type, new_type when Types.equal old_type new_type -> Unchanged
    | Function old_type, Function new_type ->
        let instance = { new_type with uses = instantiate new_type.uses } in
        if not (converts ~actual:old_type ~expected:instance) then Incompatible
        else if converts ~actual:new_type ~expected:old_type then Unchanged
        else if converts ~actual:instance ~expected:old_type then Generalized now.name
        else Widened now.name
    | _ -> Incompatible

let list_added_capability_generics ~(before : Types.signature) ~(after : Types.signature) =
  let old_count = List.length before.generics in
  let added_generics = List.drop old_count after.generics in
  if
    List.take old_count after.generics = before.generics
    && List.for_all
         (fun (generic : Types.generic) -> generic.kind = Capability_generic)
         added_generics
  then added_generics
  else []

let names_generic (uses : Types.capability_set) (generic : Types.generic) =
  List.exists
    (function
      | Types.Capability_parameter parameter | Divergence (Of_parameter parameter) ->
          parameter = generic.generic
      | _ -> false)
    (uses :> Types.capability list)

let infer_added_generics (added_generics : Types.generic list) parameters : Types.substitution =
  List.map
    (fun (generic : Types.generic) ->
      ( generic.generic,
        Types.Capabilities
          (List.fold_left
             (fun unlisted ((was : Types.parameter_info), (now : Types.parameter_info)) ->
               match (was.type_, now.type_) with
               | Function old_type, Function new_type when names_generic new_type.uses generic ->
                   Types.union_capabilities unlisted
                     (Types.subtract_capabilities old_type.uses new_type.uses)
               | _ -> unlisted)
             Types.no_capabilities parameters) ))
    added_generics

let compare_signatures ~is_trait_method ~added_generics ~(before : Types.signature)
    ~(after : Types.signature) =
  let has_same_arity = List.compare_lengths before.parameters after.parameters = 0 in
  let parameters = if has_same_arity then List.combine before.parameters after.parameters else [] in
  let instantiate =
    Types.substitute_capabilities (infer_added_generics added_generics parameters)
  in
  let parameter_changes = List.map (compare_parameter ~instantiate) parameters in
  let same_parameters = has_same_arity && not (List.mem Incompatible parameter_changes) in
  let gained_default =
    same_parameters
    && List.exists
         (fun ((was : Types.parameter_info), (now : Types.parameter_info)) ->
           now.has_default && not was.has_default)
         parameters
  in
  let new_uses = instantiate after.uses in
  let added_uses = Types.subtract_capabilities new_uses before.uses
  and removed_uses = Types.subtract_capabilities before.uses new_uses in
  List.concat
    [
      (if
         after.generics = before.generics @ added_generics
         && before.receiver = after.receiver && same_parameters && before.output = after.output
         && before.specification_only = after.specification_only
         && before.capture_free_parameters = after.capture_free_parameters
       then []
       else [ Breaks "changed its parameters or its result" ]);
      List.map make_uses_more (added_uses :> Types.capability list);
      (if Types.list_divergence removed_uses <> Types.no_capabilities then
         [ Grows "promises to terminate" ]
       else []);
      (if Types.remove_divergence removed_uses <> Types.no_capabilities then
         [ Grows "uses fewer capabilities" ]
       else []);
      (if gained_default then [ Grows "gained a default" ] else []);
      List.filter_map
        (function
          | Generalized name -> Some (Grows (Printf.sprintf "takes more functions for `%s`" name))
          | Widened name when is_trait_method ->
              Some
                (Breaks
                   (Printf.sprintf
                      "takes more functions for `%s`, which every `impl` that defines the method \
                       must then take"
                      name))
          | Widened name ->
              Some
                (Breaks
                   (Printf.sprintf
                      "takes more functions for `%s`, and so has another type where it is named as \
                       a value"
                      name))
          | Unchanged | Incompatible -> None)
        parameter_changes;
    ]

let compare_function_signatures ~(before : Types.signature) ~(after : Types.signature) =
  let added_generics = list_added_capability_generics ~before ~after in
  List.map
    (fun (generic : Types.generic) ->
      Grows (Printf.sprintf "gained the capability parameter `%s`" generic.generic.name))
    added_generics
  @ compare_signatures ~is_trait_method:false ~added_generics ~before ~after

let read_effective_signature (side : side) path =
  match Interface.Impls.read_signature side.lookups path with
  | Some signature -> signature
  | None ->
      Compiler_bug.raise_bug ~stage:"Compatibility" "%s has an interface and no signature"
        (Path.show path)

let read_invariants side key =
  match read_form side key with Some (Type { invariants; _ }) -> invariants | _ -> []

let has_changed_invariant ~before ~after =
  let equal = Core_equivalence.equal_condition ~parameters:([], []) in
  loses ~equal ~before ~after || gains ~equal ~before ~after

let compare_types ~(before : Types.type_interface) ~(after : Types.type_interface)
    ~before_invariants ~after_invariants =
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
          if has_changed_invariant ~before:before_invariants ~after:after_invariants then
            [ Breaks "changed its invariant" ]
          else []);
      (if loses ~equal:Path.equal ~before:before.derives ~after:after.derives then
         [ Breaks "no longer derives a trait" ]
       else if gains ~equal:Path.equal ~before:before.derives ~after:after.derives then
         [ Grows "derives another trait" ]
       else []);
    ]

let read_method_contract (side : side) (owner : Path.t) name receiver =
  match side.lookups.names.find_key (Method { owner; name; receiver }) with
  | Some key -> read_contract side key
  | None -> ([], no_contract)

let read_laws side key = match read_form side key with Some (Trait laws) -> laws | _ -> []

let has_changed_laws ~before ~after =
  List.length before <> List.length after
  || not (List.for_all (fun was -> List.exists (Core_equivalence.equal_law was) after) before)

let compare_traits ~(before : Types.trait_interface) ~(after : Types.trait_interface) ~before_laws
    ~after_laws ~read_signature_before ~read_signature_after ~read_contract_before
    ~read_contract_after =
  let is_same (was : Types.trait_method) (now : Types.trait_method) =
    was.method_name = now.method_name && was.method_receiver = now.method_receiver
  in
  let methods =
    List.concat_map
      (fun (was : Types.trait_method) ->
        let name_change change =
          match change with
          | Breaks description ->
              Breaks (Printf.sprintf "its method `%s` %s" was.method_name description)
          | Grows description ->
              Grows (Printf.sprintf "its method `%s` %s" was.method_name description)
        in
        match List.find_opt (is_same was) after.methods with
        | None -> [ Breaks (Printf.sprintf "no longer has the method `%s`" was.method_name) ]
        | Some now ->
            List.map name_change
              (compare_signatures ~is_trait_method:true ~added_generics:[]
                 ~before:(read_signature_before was) ~after:(read_signature_after now)
              @ compare_contracts
                  ~before:(read_contract_before was.method_name was.method_receiver)
                  ~after:(read_contract_after now.method_name now.method_receiver)
              @ if was.provided && not now.provided then [ Breaks "lost its default body" ] else []
              ))
      before.methods
  in
  let gained =
    List.filter_map
      (fun (now : Types.trait_method) ->
        if List.exists (fun was -> is_same was now) before.methods then None
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
      (if
         loses ~equal:String.equal ~before:before.associated_capabilities
           ~after:after.associated_capabilities
       then [ Breaks "lost an associated capability set" ]
       else if
         gains ~equal:String.equal ~before:before.associated_capabilities
           ~after:after.associated_capabilities
       then [ Grows "gained an associated capability set" ]
       else []);
      (if has_changed_laws ~before:before_laws ~after:after_laws then [ Breaks "changed its laws" ]
       else []);
      methods;
      gained;
    ]

let has_changed_value (before : side) (after : side) path ~before_key ~after_key =
  match (before.lookups.find_constant_value path, after.lookups.find_constant_value path) with
  | Some before, Some after -> before <> after
  | Some _, None | None, Some _ -> true
  | None, None -> (
      match (read_form before before_key, read_form after after_key) with
      | Some (Constant (Some before)), Some (Constant (Some after)) ->
          not (Core_equivalence.equal_expression ~parameters:([], []) before after)
      | _ -> false)

let is_same_impl (before : Path.t) (after : Path.t) =
  match (before, after) with
  | Impl before, Impl after ->
      before.trait = after.trait && Path.equal before.for_type after.for_type
  | _ -> Path.equal before after

let list_impls (side : side) package =
  List.filter_map
    (fun (declaration : Resolve.Names.declaration) ->
      if declaration.kind = Impl && declaration.ordinal = 0 then
        match Interface.Definition.find_impl_interface side.lookups declaration.path with
        | Some (impl : Types.impl_interface) ->
            Some
              ( declaration.path,
                Printf.sprintf "the `impl` of `%s` for `%s`"
                  (Types.show_trait impl.implements)
                  (Types.show impl.for_type),
                impl.capability_sets )
        | _ -> None
      else None)
    (list_declarations side package)

let compare ~before ~after package =
  let before = { database = before; lookups = Database.make_interface_lookups before [ package ] }
  and after = { database = after; lookups = Database.make_interface_lookups after [ package ] } in
  let old = List.filter (is_public before) (list_declarations before package) in
  let now = List.filter (is_public after) (list_declarations after package) in
  let make_public_change path change = { path; change } in
  let definitions =
    List.concat_map
      (fun (was : Resolve.Names.declaration) ->
        let path = was.path in
        match
          List.find_opt (fun (other : Resolve.Names.declaration) -> Path.equal other.path path) now
        with
        | None -> [ make_public_change path (Breaks "was removed or is no longer public") ]
        | Some is when is.kind <> was.kind ->
            [ make_public_change path (Breaks "became another kind of definition") ]
        | Some is ->
            let before_key = Resolve.Names.make_key was and after_key = Resolve.Names.make_key is in
            List.map (make_public_change path)
              (match
                 ( Interface.Definition.find_interface before.lookups path,
                   Interface.Definition.find_interface after.lookups path )
               with
              | ( Some (Function_interface _ | Theorem_interface _),
                  Some (Function_interface _ | Theorem_interface _) ) ->
                  compare_function_signatures
                    ~before:(read_effective_signature before path)
                    ~after:(read_effective_signature after path)
                  @ compare_contracts ~before:(read_contract before before_key)
                      ~after:(read_contract after after_key)
              | Some (Type_interface old_type), Some (Type_interface new_type) ->
                  compare_types ~before:old_type ~after:new_type
                    ~before_invariants:(read_invariants before before_key)
                    ~after_invariants:(read_invariants after after_key)
              | Some (Trait_interface old_trait), Some (Trait_interface new_trait) ->
                  compare_traits ~before:old_trait ~after:new_trait
                    ~before_laws:(read_laws before before_key)
                    ~after_laws:(read_laws after after_key)
                    ~read_signature_before:
                      (Interface.Definition.read_method_signature before.lookups ~owner:path)
                    ~read_signature_after:
                      (Interface.Definition.read_method_signature after.lookups ~owner:path)
                    ~read_contract_before:(read_method_contract before path)
                    ~read_contract_after:(read_method_contract after path)
              | Some (Constant_interface old_constant), Some (Constant_interface new_constant) ->
                  (if old_constant.constant_type <> new_constant.constant_type then
                     [ Breaks "changed its type" ]
                   else [])
                  @
                  if has_changed_value before after path ~before_key ~after_key then
                    [ Breaks "changed its value" ]
                  else []
              | _ -> []))
      old
  in
  let added =
    List.filter_map
      (fun (is : Resolve.Names.declaration) ->
        if List.exists (fun (was : Resolve.Names.declaration) -> Path.equal was.path is.path) old
        then None
        else Some (make_public_change is.path (Grows "is new")))
      now
  in
  let old_impls = list_impls before package and new_impls = list_impls after package in
  let impl_changes =
    List.concat_map
      (fun (path, shown, old_sets) ->
        match List.find_opt (fun (other, _, _) -> is_same_impl path other) new_impls with
        | None -> [ make_public_change path (Breaks (Printf.sprintf "was removed: %s" shown)) ]
        | Some (_, _, new_sets) ->
            let set name sets =
              Option.value ~default:Types.no_capabilities (List.assoc_opt name sets)
            in
            List.concat_map
              (fun name ->
                let was = set name old_sets and is = set name new_sets in
                List.map
                  (fun capability ->
                    make_public_change path
                      (Breaks
                         (Printf.sprintf "added `%s` to its `%s`: %s"
                            (Types.show_capability capability)
                            name shown)))
                  (Types.subtract_capabilities is was :> Types.capability list)
                @
                if Types.subtract_capabilities was is <> Types.no_capabilities then
                  [
                    make_public_change path
                      (Grows (Printf.sprintf "removed capabilities from its `%s`: %s" name shown));
                  ]
                else [])
              (List.sort_uniq String.compare (List.map fst (old_sets @ new_sets))))
      old_impls
    @ List.filter_map
        (fun (path, shown, _) ->
          if List.exists (fun (other, _, _) -> is_same_impl other path) old_impls then None
          else Some (make_public_change path (Grows (Printf.sprintf "is new: %s" shown))))
        new_impls
  in
  definitions @ added @ impl_changes

let list_breaking_changes changes =
  List.filter_map
    (fun { path; change } ->
      match change with Breaks description -> Some (path, description) | Grows _ -> None)
    changes

let list_growing_changes changes =
  List.filter_map
    (fun { path; change } ->
      match change with Grows description -> Some (path, description) | Breaks _ -> None)
    changes
