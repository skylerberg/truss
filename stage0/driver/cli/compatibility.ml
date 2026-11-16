type change = Breaks of string | Grows of string
type public_change = { path : Path.t; change : change }
type side = { database : Database.t; lookups : Interface.Lookups.t }

let public (side : side) (declaration : Resolve.Names.declaration) =
  declaration.ordinal = 0
  && side.lookups.names.container (Resolve.Names.key_of declaration) = None
  && Resolve.Names.is_public declaration.visibility

let declarations (side : side) package = side.lookups.names.package_declarations package

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

let contract ~before:(before_parameters, (before : Core.contract))
    ~after:(after_parameters, (after : Core.contract)) =
  let parameters = (before_parameters, after_parameters) in
  let differ equal before after = (loses ~equal ~before ~after, gains ~equal ~before ~after) in
  let lost_requires, gained_requires =
    differ (Core_equivalence.equal_condition ~parameters) before.requires after.requires
  and lost_ensures, gained_ensures =
    differ (Core_equivalence.equal_expression ~parameters) before.ensures after.ensures
  and lost_costs, gained_costs =
    differ (Core_equivalence.equal_cost ~parameters) before.costs after.costs
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

let uses_more : Types.capability -> change = function
  | Capability path -> Breaks (Printf.sprintf "now uses `%s`" (Path.show path))
  | (Capability_parameter _ | Capability_projection _) as capability ->
      Breaks (Printf.sprintf "now uses `%s`" (Types.show_capability capability))
  | Capability_variable _ ->
      Compiler_bug.bug ~stage:"Compatibility" "a signature holds an unknown set of capabilities"
  | Capability_error _ ->
      Compiler_bug.bug ~stage:"Compatibility" "a signature holds a capability with an error"

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
  let more = Types.subtract_capabilities after.uses before.uses
  and fewer = Types.subtract_capabilities before.uses after.uses in
  List.concat
    [
      (if
         before.generics = after.generics && before.receiver = after.receiver && same_parameters
         && before.output = after.output
         && before.specification_only = after.specification_only
         && before.capture_free_parameters = after.capture_free_parameters
       then []
       else [ Breaks "changed its parameters or its result" ]);
      (if before.terminates && not after.terminates then
         [ Breaks "no longer promises to terminate" ]
       else if after.terminates && not before.terminates then [ Grows "promises to terminate" ]
       else []);
      List.map uses_more (more :> Types.capability list);
      (if fewer <> Types.no_capabilities then [ Grows "uses fewer capabilities" ] else []);
      (if gained_default then [ Grows "gained a default" ] else []);
    ]

let read_invariants side key =
  match read_form side key with Some (Type { invariants; _ }) -> invariants | _ -> []

let has_changed_invariant ~before ~after =
  let equal = Core_equivalence.equal_condition ~parameters:([], []) in
  loses ~equal ~before ~after || gains ~equal ~before ~after

let type_ ~(before : Types.type_interface) ~(after : Types.type_interface) ~before_invariants
    ~after_invariants =
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
  match side.lookups.names.key (Method { owner; name; receiver }) with
  | Some key -> read_contract side key
  | None -> ([], no_contract)

let read_laws side key = match read_form side key with Some (Trait laws) -> laws | _ -> []

let has_changed_laws ~before ~after =
  List.length before <> List.length after
  || not (List.for_all (fun was -> List.exists (Core_equivalence.equal_law was) after) before)

let trait ~(before : Types.trait_interface) ~(after : Types.trait_interface) ~before_laws
    ~after_laws ~signature_before ~signature_after ~contract_before ~contract_after =
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
              (signature ~before:(signature_before was) ~after:(signature_after now)
              @ contract
                  ~before:(contract_before was.method_name was.method_receiver)
                  ~after:(contract_after now.method_name now.method_receiver)
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
  match (before.lookups.constant_value path, after.lookups.constant_value path) with
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

let impls (side : side) package =
  List.filter_map
    (fun (declaration : Resolve.Names.declaration) ->
      if declaration.kind = Impl && declaration.ordinal = 0 then
        match Interface.Definition.read_impl_interface side.lookups declaration.path with
        | Some (impl : Types.impl_interface) ->
            Some
              ( declaration.path,
                Printf.sprintf "the `impl` of `%s` for `%s`"
                  (Types.show_trait impl.implements)
                  (Types.show impl.for_type),
                impl.capability_sets )
        | _ -> None
      else None)
    (declarations side package)

let compare ~before ~after package =
  let before = { database = before; lookups = Database.make_interface_lookups before [ package ] }
  and after = { database = after; lookups = Database.make_interface_lookups after [ package ] } in
  let old = List.filter (public before) (declarations before package) in
  let now = List.filter (public after) (declarations after package) in
  let public_change path change = { path; change } in
  let definitions =
    List.concat_map
      (fun (was : Resolve.Names.declaration) ->
        let path = was.path in
        match
          List.find_opt (fun (other : Resolve.Names.declaration) -> Path.equal other.path path) now
        with
        | None -> [ public_change path (Breaks "was removed or is no longer public") ]
        | Some is when is.kind <> was.kind ->
            [ public_change path (Breaks "became another kind of definition") ]
        | Some is ->
            let before_key = Resolve.Names.key_of was and after_key = Resolve.Names.key_of is in
            List.map (public_change path)
              (match
                 ( Interface.Definition.read_interface before.lookups path,
                   Interface.Definition.read_interface after.lookups path )
               with
              | ( Some (Function_interface old_signature | Theorem_interface old_signature),
                  Some (Function_interface new_signature | Theorem_interface new_signature) ) ->
                  signature ~before:old_signature ~after:new_signature
                  @ contract ~before:(read_contract before before_key)
                      ~after:(read_contract after after_key)
              | Some (Type_interface old_type), Some (Type_interface new_type) ->
                  type_ ~before:old_type ~after:new_type
                    ~before_invariants:(read_invariants before before_key)
                    ~after_invariants:(read_invariants after after_key)
              | Some (Trait_interface old_trait), Some (Trait_interface new_trait) ->
                  trait ~before:old_trait ~after:new_trait
                    ~before_laws:(read_laws before before_key)
                    ~after_laws:(read_laws after after_key)
                    ~signature_before:
                      (Interface.Definition.read_method_signature before.lookups ~owner:path)
                    ~signature_after:
                      (Interface.Definition.read_method_signature after.lookups ~owner:path)
                    ~contract_before:(read_method_contract before path)
                    ~contract_after:(read_method_contract after path)
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
        else Some (public_change is.path (Grows "is new")))
      now
  in
  let old_impls = impls before package and new_impls = impls after package in
  let impl_changes =
    List.concat_map
      (fun (path, shown, old_sets) ->
        match List.find_opt (fun (other, _, _) -> is_same_impl path other) new_impls with
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
                  (Types.subtract_capabilities is was :> Types.capability list)
                @
                if Types.subtract_capabilities was is <> Types.no_capabilities then
                  [
                    public_change path
                      (Grows (Printf.sprintf "removed capabilities from its `%s`: %s" name shown));
                  ]
                else [])
              (List.sort_uniq String.compare (List.map fst (old_sets @ new_sets))))
      old_impls
    @ List.filter_map
        (fun (path, shown, _) ->
          if List.exists (fun (other, _, _) -> is_same_impl other path) old_impls then None
          else Some (public_change path (Grows (Printf.sprintf "is new: %s" shown))))
        new_impls
  in
  definitions @ added @ impl_changes

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
