let raise_bug format = Compiler_bug.raise_bug ~stage:"Interface" format

let read_declaring_type_trait lookups ~base (trait : Types.trait_reference) name =
  match Properties.find_trait_declaring_type lookups ~base trait name with
  | Some declaring -> declaring
  | None ->
      raise_bug "no trait among `%s` and its requirements declares `%s`" (Types.show_trait trait)
        name

let read_declaring_capability_trait lookups ~base (trait : Types.trait_reference) name =
  match Properties.find_trait_declaring_capability_set lookups ~base trait name with
  | Some declaring -> declaring
  | None ->
      raise_bug "no trait among `%s` and its requirements declares `%s`" (Types.show_trait trait)
        name

let find_head = function Types.Named { path; _ } -> Some path | _ -> None

let list_impls_for_type (lookups : Lookups.t) (type_ : Path.t) package =
  lookups.names.list_impls_of_type package type_

let list_impls_of_trait_for_type lookups ~trait ~type_ package =
  List.filter_map
    (fun (indexed_trait, impl) -> if Path.equal indexed_trait trait then Some impl else None)
    (list_impls_for_type lookups type_ package)

let list_impls_of_trait (lookups : Lookups.t) ~trait package =
  List.sort_uniq Path.compare (lookups.names.list_impls_of_trait package trait)

let derive_interface lookups ~type_ ~trait =
  match
    (Definition.find_type_interface lookups type_, Definition.find_trait_interface lookups trait)
  with
  | Some type_interface, Some trait_interface ->
      let trait_reference : Types.trait_reference =
        { trait; trait_arguments = []; associated = [] }
      in
      let impl_generics =
        List.map
          (fun (generic : Types.generic) ->
            match generic.kind with
            | Type_generic bounds ->
                { generic with kind = Type_generic (bounds @ [ trait_reference ]) }
            | Value_generic -> generic)
          type_interface.type_generics
      in
      let for_type =
        Types.Named
          { path = type_; arguments = Types.list_generic_arguments type_interface.type_generics }
      in
      Some
        {
          Types.impl_generics;
          implements = trait_reference;
          for_type;
          impl_uses = Types.no_capabilities;
          capability_sets = [];
          impl_methods =
            List.map
              (fun (method_ : Types.trait_method) -> (method_.method_name, method_.method_receiver))
              trait_interface.methods;
        }
  | _ -> None

type implementation = {
  impl : Types.impl_interface;
  trait : Types.trait_interface;
  substitution : Types.substitution;
}

let find_implementation_of lookups (impl : Types.impl_interface) =
  Option.map
    (fun trait ->
      {
        impl;
        trait;
        substitution =
          Types.make_trait_substitution trait.trait_generics ~self:impl.for_type impl.implements;
      })
    (Definition.find_trait_interface lookups impl.implements.trait)

let find_implementation lookups (impl : Path.t) =
  Option.bind (Definition.find_impl_interface lookups impl) (find_implementation_of lookups)

type implemented_method = {
  implementation : implementation;
  declared : Types.trait_method;
  declaration : Path.t;
}

let find_method_implemented_by (implementation : implementation) ~name ~receiver =
  Option.map
    (fun (declared : Types.trait_method) ->
      {
        implementation;
        declared;
        declaration =
          Method
            {
              owner = implementation.impl.implements.trait;
              name = declared.method_name;
              receiver = declared.method_receiver;
            };
      })
    (Definition.find_method_of_trait implementation.trait ~name ~receiver)

let find_implemented_method lookups (path : Path.t) =
  match path with
  | Method { owner = (Impl _ | Derived _) as owner; name; receiver } ->
      Option.bind (find_implementation lookups owner) (find_method_implemented_by ~name ~receiver)
  | Top _ | Method _ | Member_constant _ | Impl _ | Derived _ | Test _ | Law_proof _ | Unresolved _
    ->
      None

let is_open_value = function
  | Types.Value_variable _ -> true
  | Types.Known _ | Value_parameter _ -> false

let rec match_type ~variables (substitution : Types.substitution) pattern type_ =
  match (pattern, type_) with
  | Types.Parameter parameter, _ when List.mem parameter variables -> (
      match Types.find_argument parameter substitution with
      | Some (Types.Type bound) ->
          if Types.equal bound type_ || Types.is_open_type type_ then Some substitution
          else if Types.is_open_type bound then
            Some (Types.bind_argument parameter (Types.Type type_) substitution)
          else None
      | Some (Types.Value _) -> None
      | None -> Some (Types.bind_argument parameter (Types.Type type_) substitution))
  | _, argument_type when Types.is_open_type argument_type -> Some substitution
  | Types.Named left, Types.Named right when Path.equal left.path right.path ->
      match_arguments ~variables substitution left.arguments right.arguments
  | _ -> if Types.equal pattern type_ then Some substitution else None

and match_arguments ~variables substitution patterns arguments =
  if List.length patterns <> List.length arguments then None
  else
    List.fold_left2
      (fun substitution pattern argument ->
        match substitution with
        | None -> None
        | Some substitution -> (
            match (pattern, argument) with
            | Types.Type pattern, Types.Type argument ->
                match_type ~variables substitution pattern argument
            | Types.Value (Types.Value_parameter parameter), Types.Value value
              when List.mem parameter variables -> (
                match Types.find_argument parameter substitution with
                | Some (Types.Value bound) -> if bound = value then Some substitution else None
                | _ -> Some (Types.bind_argument parameter (Types.Value value) substitution))
            | Types.Value left, Types.Value right -> (
                if left = right then Some substitution
                else match right with Types.Value_variable _ -> Some substitution | _ -> None)
            | _ -> None))
      (Some substitution) patterns arguments

type solution = Evidence of Types.evidence | Built_in | Accepted of Types.ty
type bounds = Properties.Bounds.t

let list_no_bounds = Properties.Bounds.none

let list_required_bounds (generics : Types.generic list) (substitution : Types.substitution) =
  List.concat_map
    (fun (generic : Types.generic) ->
      match (generic.kind, Types.find_argument generic.generic substitution) with
      | Type_generic generic_bounds, Some (Types.Type argument) ->
          List.map
            (fun bound -> (argument, Types.substitute_trait substitution bound))
            generic_bounds
      | _ -> [])
    generics

let list_impl_bounds lookups (impl : Types.impl_interface) ~(list_bounds : bounds) : bounds =
  Properties.Bounds.override list_bounds
    ~for_:
      (List.filter_map
         (fun (generic : Types.generic) ->
           match generic.kind with Type_generic _ -> Some generic.generic | Value_generic -> None)
         impl.impl_generics)
    (Properties.Bounds.close lookups (Types.list_bounds impl.impl_generics))

let read_trait_signature lookups (implemented : implemented_method) =
  Definition.read_method_signature lookups ~owner:implemented.implementation.impl.implements.trait
    implemented.declared

let rename_as_written (declared : Types.signature) (written : Types.signature) =
  let capability_renaming =
    Types.make_capability_substitution declared.capability_parameters
      (Types.list_capability_arguments written.capability_parameters)
  in
  let renaming =
    if List.length declared.generics = List.length written.generics then
      Types.combine_substitutions
        (Types.make_substitution declared.generics (Types.list_generic_arguments written.generics))
        capability_renaming
    else capability_renaming
  in
  let renamed = Types.substitute_signature renaming declared in
  {
    renamed with
    generics =
      List.map
        (fun (generic : Types.generic) ->
          match (generic.kind, Types.find_argument generic.generic renaming) with
          | Type_generic _, Some (Type (Parameter written_parameter))
          | Value_generic, Some (Value (Value_parameter written_parameter)) ->
              { generic with generic = written_parameter }
          | (Type_generic _ | Value_generic), _ -> generic)
        renamed.generics;
    capability_parameters =
      List.map
        (fun (parameter : Types.parameter) ->
          Option.value ~default:parameter
            (List.find_opt
               (fun (written_parameter : Types.parameter) ->
                 written_parameter.name = parameter.name)
               written.capability_parameters))
        renamed.capability_parameters;
  }

let find_built_in_solution : Properties.decision -> solution option = function
  | Holds -> Some Built_in
  | Fails -> None
  | Depends_on open_type -> Some (Accepted open_type)

let list_candidate_impls lookups ~head (wanted : Types.trait_reference) =
  let packages =
    List.sort_uniq compare
      (Path.locate_package wanted.trait :: Path.locate_package head
      :: List.filter_map
           (function
             | Types.Type (Types.Named { path; _ }) -> Some (Path.locate_package path) | _ -> None)
           wanted.trait_arguments)
  in
  List.concat_map
    (fun package -> list_impls_of_trait_for_type lookups ~trait:wanted.trait ~type_:head package)
    packages

let list_impl_variables (impl : Types.impl_interface) =
  List.map (fun (generic : Types.generic) -> generic.generic) impl.impl_generics

type matched_impl = {
  impl_path : Path.t;
  impl : Types.impl_interface;
  substitution : Types.substitution;
}

let list_matching_impls lookups type_ (wanted : Types.trait_reference) =
  List.filter_map
    (fun impl_path ->
      Option.bind (Definition.find_impl_interface lookups impl_path) (fun impl ->
          let variables = list_impl_variables impl in
          Option.map
            (fun substitution -> { impl_path; impl; substitution })
            (Option.bind (match_type ~variables Types.no_substitution impl.for_type type_)
               (fun substitution ->
                 match_arguments ~variables substitution impl.implements.trait_arguments
                   wanted.trait_arguments))))
    (Option.fold ~none:[]
       ~some:(fun head -> list_candidate_impls lookups ~head wanted)
       (find_head type_))

let check_recursion_depth ~depth type_ trait =
  if depth > Properties.recursion_limit then
    raise
      (Properties.Recursion_limit
         (Recursion_limit
            { limit = Properties.recursion_limit; recursion = Evidence { type_; trait } }))

let rec find_evidence lookups ~(list_bounds : bounds) ?(depth = 0) ?(checks_conditions = true)
    (type_ : Types.ty) (wanted : Types.trait_reference) : solution option =
  let broken_trait =
    match Definition.find_interface lookups wanted.trait with
    | Some (Error_interface report) -> Some report
    | _ -> None
  in
  check_recursion_depth ~depth type_ wanted;
  if Option.is_some broken_trait then
    Option.map (fun report -> Accepted (Types.Error report)) broken_trait
  else
    match decide_property_trait lookups ~list_bounds wanted.trait type_ with
    | Some _ when not checks_conditions -> Some Built_in
    | Some decision -> find_built_in_solution decision
    | None -> (
        match type_ with
        | Types.Error _ | Types.Hole | Types.Variable _ -> Some (Accepted type_)
        | Types.Never | Types.Integer | Types.Function _ -> None
        | Types.Parameter _ | Types.Projection _ ->
            if list_matching_bounds lookups ~list_bounds type_ wanted <> [] then
              Some (Evidence Bound)
            else None
        | Types.Named _ ->
            List.find_map
              (fun { impl_path; impl; substitution } ->
                let associated =
                  List.map
                    (fun (name, type_) -> (name, Types.substitute substitution type_))
                    impl.implements.associated
                in
                let associated =
                  associated
                  @ List.filter_map
                      (fun (name, _) ->
                        if List.mem_assoc name associated then None
                        else
                          Some
                            ( name,
                              normalize lookups ~list_bounds
                                (Types.Projection
                                   { base = type_; trait = { wanted with associated = [] }; name })
                            ))
                      wanted.associated
                in
                let conditions_hold =
                  (not checks_conditions)
                  || List.for_all
                       (fun (argument, bound) ->
                         Option.is_some
                           (find_evidence lookups ~list_bounds ~depth:(depth + 1) argument bound))
                       (list_required_bounds impl.impl_generics substitution)
                in
                if
                  conditions_hold
                  && has_matching_associated_types lookups ~list_bounds wanted ~base:None associated
                then Some (Evidence (Impl { impl = impl_path; substitution }))
                else None)
              (list_matching_impls lookups type_ wanted))

and decide_property_trait lookups ~list_bounds trait type_ =
  let normalize = normalize lookups ~list_bounds in
  if Well_known.is Copyable trait then
    Some (Properties.decide_property lookups ~list_bounds ~normalize Copyable type_)
  else if Well_known.is Plain trait then
    Some (Properties.decide_property lookups ~list_bounds ~normalize Plain type_)
  else if Well_known.is Storable trait then
    Some (Properties.decide_storable lookups ~list_bounds ~normalize type_)
  else None

and list_matching_bounds lookups ~list_bounds (type_ : Types.ty) (wanted : Types.trait_reference) =
  let arguments_match actual_arguments =
    List.length actual_arguments = List.length wanted.trait_arguments
    && List.for_all2
         (fun wanted actual ->
           match (wanted, actual) with
           | Types.Type wanted, Types.Type actual ->
               Types.is_open_type wanted || Types.is_open_type actual
               || Types.equal
                    (normalize lookups ~list_bounds wanted)
                    (normalize lookups ~list_bounds actual)
           | Types.Value wanted, Types.Value actual ->
               is_open_value wanted || is_open_value actual || wanted = actual
           | _ -> false)
         wanted.trait_arguments actual_arguments
  in
  List.filter
    (fun (bound : Types.trait_reference) ->
      Path.equal bound.trait wanted.trait
      && arguments_match bound.trait_arguments
      && has_matching_associated_types lookups ~list_bounds wanted ~base:(Some type_)
           bound.associated)
    (Properties.list_known_bounds lookups ~list_bounds type_)

and has_matching_associated_types lookups ~list_bounds (wanted : Types.trait_reference) ~base fixed
    =
  List.for_all
    (fun (name, wanted_type) ->
      let wanted_type = normalize lookups ~list_bounds wanted_type in
      if Types.is_open_type wanted_type then true
      else
        match List.assoc_opt name fixed with
        | Some defined ->
            Types.is_open_type defined
            || Types.equal (normalize lookups ~list_bounds defined) wanted_type
        | None -> (
            match (base, wanted_type) with
            | Some base, Types.Projection { base = projected; name = projected_name; _ } ->
                Types.equal base projected && projected_name = name
            | _ -> false))
    wanted.associated

and project_associated_type lookups ~list_bounds ?defining type_ (trait : Types.trait_reference)
    name =
  project_declared_type lookups ~list_bounds ?defining type_
    (read_declaring_type_trait lookups ~base:type_ trait name)
    name

and project_declared_type lookups ~list_bounds ?defining type_ (trait : Types.trait_reference) name
    =
  match List.assoc_opt name trait.associated with
  | Some fixed -> Some fixed
  | None -> (
      match find_evidence lookups ~list_bounds ~checks_conditions:false type_ trait with
      | Some (Evidence (Impl { impl; substitution })) -> (
          match Definition.find_impl_interface lookups impl with
          | Some interface ->
              Option.iter (fun defining -> defining := impl :: !defining) defining;
              Option.map (Types.substitute substitution)
                (List.assoc_opt name interface.implements.associated)
          | None -> None)
      | Some (Evidence Bound) -> (
          match
            List.find_map
              (fun (bound : Types.trait_reference) ->
                if Path.equal bound.trait trait.trait then List.assoc_opt name bound.associated
                else None)
              (Properties.list_known_bounds lookups ~list_bounds type_)
          with
          | Some fixed -> Some fixed
          | None -> Some (Types.Projection { base = type_; trait; name }))
      | Some Built_in -> None
      | Some (Accepted unknown) -> Some unknown
      | None -> None)

and project_capability_set lookups ~list_bounds ?(depth = 0) type_ (trait : Types.trait_reference)
    name =
  let trait = read_declaring_capability_trait lookups ~base:type_ trait name in
  let projection =
    Types.make_capability_set [ Types.Capability_projection { base = type_; trait; name } ]
  in
  if depth > Properties.recursion_limit then
    raise
      (Properties.Recursion_limit
         (Recursion_limit
            {
              limit = Properties.recursion_limit;
              recursion = Capability_set (Capability_projection { base = type_; trait; name });
            }))
  else
    match find_evidence lookups ~list_bounds ~checks_conditions:false type_ trait with
    | Some (Evidence (Impl { impl; substitution })) -> (
        match Definition.find_impl_interface lookups impl with
        | Some interface ->
            normalize_capabilities lookups ~list_bounds ~depth:(depth + 1)
              (Types.substitute_capabilities substitution
                 (Option.value ~default:Types.no_capabilities
                    (List.assoc_opt name interface.capability_sets)))
        | None -> Types.no_capabilities)
    | Some (Evidence Bound) | Some (Accepted (Types.Variable _)) | None -> projection
    | Some (Built_in | Accepted _) -> Types.no_capabilities

and normalize_capabilities lookups ~list_bounds ?depth (capabilities : Types.capability_set) =
  let reads_an_impl : Types.capability -> bool = function
    | Capability_projection _ -> true
    | _ -> false
  in
  let is_conditional : Types.capability -> bool = function
    | Capability_unless _ -> true
    | _ -> false
  in
  let capabilities =
    if not (Types.exists_capability reads_an_impl capabilities) then capabilities
    else
      Types.replace_capabilities
        (function
          | Types.Capability_projection { base; trait; name } ->
              Some
                (project_capability_set lookups ~list_bounds ?depth
                   (normalize lookups ~list_bounds base)
                   { trait with associated = [] } name)
          | _ -> None)
        capabilities
  in
  if not (List.exists is_conditional (Types.list_capabilities capabilities)) then capabilities
  else
    Types.make_capability_set
      (List.concat_map
         (fun (capability : Types.capability) ->
           match capability with
           | Capability_unless { capability; unless } -> (
               match decide_condition lookups ~list_bounds ?depth unless with
               | None -> [ capability ]
               | Some [] -> []
               | Some unless -> [ Types.Capability_unless { capability; unless } ])
           | _ -> [ capability ])
         (Types.list_capabilities capabilities))

and decide_condition lookups ~list_bounds ?(depth = 0) (condition : Types.condition) =
  List.fold_left
    (fun decided (bound : Types.bound_condition) ->
      match (decided, decide_bound_condition lookups ~list_bounds ~depth bound) with
      | Some remaining, Some undecided -> Some (remaining @ undecided)
      | _ -> None)
    (Some []) condition
  |> Option.map Types.make_condition

and add_condition_bounds lookups (list_bounds : bounds) (condition : Types.condition) : bounds =
  Properties.Bounds.append list_bounds
    (Properties.Bounds.close lookups (fun parameter ->
         List.filter_map
           (fun (bound : Types.bound_condition) ->
             match bound.subject with
             | Types.Parameter subject when subject = parameter -> Some bound.bound
             | _ -> None)
           condition))

and implies_condition lookups ~list_bounds (premise : Types.condition)
    (conclusion : Types.condition) =
  decide_condition lookups
    ~list_bounds:(add_condition_bounds lookups list_bounds premise)
    conclusion
  = Some []

and decide_bound_condition lookups ~list_bounds ~depth (bound : Types.bound_condition) =
  let subject = normalize lookups ~list_bounds bound.subject in
  let holds () = Option.is_some (find_evidence lookups ~list_bounds ~depth subject bound.bound) in
  match subject with
  | Types.Error _ -> Some []
  | Types.Variable _ | Types.Hole -> Some [ { bound with subject } ]
  | Types.Parameter _ | Types.Projection _ ->
      if holds () then Some [] else Some [ { bound with subject } ]
  | Types.Named _ -> (
      if holds () then Some []
      else
        match
          find_evidence lookups ~list_bounds ~depth ~checks_conditions:false subject bound.bound
        with
        | Some (Evidence (Impl { impl; substitution })) -> (
            match Definition.find_impl_interface lookups impl with
            | Some interface ->
                decide_condition lookups ~list_bounds ~depth:(depth + 1)
                  (List.map
                     (fun (argument, required) -> { Types.subject = argument; bound = required })
                     (list_required_bounds interface.impl_generics substitution))
            | None -> None)
        | _ -> None)
  | Types.Function _ | Types.Never | Types.Integer -> if holds () then Some [] else None

and normalize lookups ~list_bounds ?defining (type_ : Types.ty) : Types.ty =
  let normalize = normalize lookups ~list_bounds ?defining in
  let project_declared_type = project_declared_type lookups ~list_bounds ?defining in
  Types.map
    ~map_capabilities:(normalize_capabilities lookups ~list_bounds)
    (function
      | Types.Projection { base; trait; name } -> (
          let base = normalize base in
          let trait = read_declaring_type_trait lookups ~base trait name in
          match base with
          | Types.Hole -> Some (Types.Projection { base; trait; name })
          | Types.Error _ -> Some base
          | Types.Parameter _ | Types.Projection _ -> (
              match project_declared_type base trait name with
              | Some (Types.Projection _ as projection) -> Some projection
              | Some fixed when not (Types.is_error fixed) -> Some (normalize fixed)
              | _ -> Some (Types.Projection { base; trait; name }))
          | _ -> (
              match project_declared_type base trait name with
              | Some fixed -> Some (normalize fixed)
              | None -> Some (Types.Projection { base; trait; name })))
      | _ -> None)
    type_

and normalize_in_impl lookups ~list_bounds (impl : Types.impl_interface) type_ =
  Types.map
    ~map_capabilities:(normalize_capabilities_in_impl lookups ~list_bounds impl)
    (function
      | Types.Projection { base; trait = projected; name } when Types.equal base impl.for_type ->
          let projected = read_declaring_type_trait lookups ~base projected name in
          if Path.equal projected.trait impl.implements.trait then
            match List.assoc_opt name impl.implements.associated with
            | Some chosen -> Some chosen
            | None -> Some (Types.Error Catalog.reported_elsewhere)
          else
            project_associated_type lookups
              ~list_bounds:(list_impl_bounds lookups impl ~list_bounds)
              impl.for_type projected name
      | _ -> None)
    type_

and normalize_capabilities_in_impl lookups ~list_bounds (impl : Types.impl_interface) capabilities =
  normalize_capabilities lookups
    ~list_bounds:(list_impl_bounds lookups impl ~list_bounds)
    (Types.replace_capabilities
       (function
         | Types.Capability_projection { base; trait = projected; name }
           when Types.equal base impl.for_type
                && Path.equal (read_declaring_capability_trait lookups ~base projected name).trait
                     impl.implements.trait ->
             Some
               (Option.value ~default:Types.no_capabilities
                  (List.assoc_opt name impl.capability_sets))
         | _ -> None)
       capabilities)

and normalize_signature_in_impl lookups ~list_bounds (implementation : implementation)
    (signature : Types.signature) =
  let signature = Types.substitute_signature implementation.substitution signature in
  let normalized =
    Types.map_signature (normalize_in_impl lookups ~list_bounds implementation.impl) signature
  in
  {
    normalized with
    uses = normalize_capabilities_in_impl lookups ~list_bounds implementation.impl signature.uses;
    specification_only =
      signature.specification_only
      || Types.mentions_specification_only_type normalized.parameters normalized.output;
    capture_free_parameters = Types.list_capture_free_parameters normalized.parameters;
  }

and make_expected_signature lookups ?written (implemented : implemented_method) =
  let implementation = implemented.implementation in
  let declared = read_trait_signature lookups implemented in
  let declared = Option.fold ~none:declared ~some:(rename_as_written declared) written in
  let expected =
    normalize_signature_in_impl lookups
      ~list_bounds:
        (Properties.Bounds.close lookups
           (Types.list_bounds (implementation.impl.impl_generics @ declared.generics)))
      implementation declared
  in
  match written with
  | Some written ->
      {
        expected with
        receiver =
          (if implementation.trait.is_capability then written.receiver else expected.receiver);
        parameters =
          List.map
            (fun (parameter : Types.parameter_info) -> { parameter with has_default = false })
            expected.parameters;
      }
  | None -> expected

and combine_modifies ~(declared : Types.signature option) ~(stated : Types.signature) =
  let is_stated position =
    List.exists (fun (part : Types.modified) -> part.position = position) stated.modifies
  in
  match declared with
  | Some declared ->
      stated.modifies
      @ List.filter (fun (part : Types.modified) -> not (is_stated part.position)) declared.modifies
  | None -> stated.modifies

and read_signature lookups (path : Path.t) =
  let ( let* ) = Option.bind in
  match path with
  | Method { owner = (Impl _ | Derived _) as owner; name; receiver } ->
      let* impl = Definition.find_impl_interface lookups owner in
      let written = Definition.find_declared_signature lookups path in
      let declared =
        Option.map
          (make_expected_signature lookups ?written)
          (Option.bind
             (find_implementation_of lookups impl)
             (find_method_implemented_by ~name ~receiver))
      in
      let* stated = if Option.is_some written then written else declared in
      let signature =
        Types.add_impl_generics_and_uses ~impl_generics:impl.impl_generics ~impl_uses:impl.impl_uses
          {
            (Option.value declared ~default:stated) with
            uses = stated.uses;
            costs = stated.costs;
            modifies = combine_modifies ~declared ~stated;
          }
      in
      let uses =
        normalize_capabilities_in_impl lookups
          ~list_bounds:(Properties.Bounds.close lookups (Types.list_bounds signature.generics))
          impl signature.uses
      in
      Some
        {
          signature with
          uses;
          costs =
            (match declared with
            | Some declared -> List.sort_uniq compare (signature.costs @ declared.costs)
            | None -> signature.costs);
        }
  | Top _ | Method _ | Member_constant _ | Impl _ | Derived _ | Test _ | Law_proof _ | Unresolved _
    ->
      Definition.find_declared_signature lookups path

module Conformance = struct
  let find_implementation_of = find_implementation_of
  let list_impl_bounds = list_impl_bounds
  let normalize_capabilities_in_impl = normalize_capabilities_in_impl
  let normalize_signature_in_impl = normalize_signature_in_impl
  let make_expected_signature = make_expected_signature
end

let resolve_evidence lookups substitution ~self_type ~trait (evidence : Types.evidence) :
    Types.evidence =
  match Types.substitute_evidence substitution evidence with
  | Bound -> (
      let normalize type_ = normalize lookups ~list_bounds:list_no_bounds type_ in
      match
        find_evidence lookups ~list_bounds:list_no_bounds ~checks_conditions:false
          (normalize (Types.substitute substitution self_type))
          (Types.map_trait normalize (Types.substitute_trait substitution trait))
      with
      | Some (Evidence evidence) -> evidence
      | Some (Built_in | Accepted _) | None -> Bound)
  | Impl _ as evidence -> evidence

let read_scope (lookups : Lookups.t) (key : Resolve.Names.key) :
    Environment.known_bounds Environment.scope =
  let scope = (lookups.read_elaborated_interface key).scope in
  match key.path with
  | Method { owner = Impl _ | Derived _; _ } -> (
      match read_signature lookups key.path with
      | None -> scope
      | Some signature ->
          {
            scope with
            bounds =
              List.map
                (fun (parameter, known) ->
                  ( parameter,
                    match
                      List.find_opt
                        (fun (generic : Types.generic) -> generic.generic = parameter)
                        signature.generics
                    with
                    | Some { kind = Type_generic bounds; _ } ->
                        List.concat_map
                          (Properties.list_bound_closure lookups ~self:(Types.Parameter parameter))
                          bounds
                    | Some { kind = Value_generic; _ } | None -> known ))
                scope.bounds;
          })
  | Top _ | Method _ | Member_constant _ | Impl _ | Derived _ | Test _ | Law_proof _ | Unresolved _
    ->
      scope

type declaring_clause = Catalog.Capabilities.declaring_clause =
  | Own_uses
  | Impl_uses
  | Associated_capability_set of { name : string; is_defined : bool; is_named : bool }

type capability_declaration = Catalog.Capabilities.declaration =
  | Declared_by of declaring_clause
  | Fixed_by_trait of { trait : Types.trait_reference; method_name : string }

let find_self_capability_set (implemented : implemented_method) (declared : Types.signature) =
  let trait = implemented.implementation.trait in
  let trait_path = implemented.implementation.impl.implements.trait in
  List.find_map
    (function
      | Types.Capability_projection { base = Parameter parameter; name; _ }
        when Path.equal parameter.owner trait_path
             && Types.is_self_parameter parameter
             && List.mem name trait.associated_capabilities ->
          Some name
      | _ -> None)
    (Types.list_capabilities declared.uses)

let names_capability_set (impl : Types.impl_interface) name (own : Types.signature) =
  Types.exists_capability
    (function
      | Types.Capability_projection { base; name = named; _ } ->
          Types.equal base impl.for_type && named = name
      | _ -> false)
    own.uses

let find_capability_declaration lookups (path : Path.t) (capability : Types.capability) =
  let ( let* ) = Option.bind in
  match path with
  | Method { owner = Impl _ | Derived _; name; _ } ->
      let* implemented = find_implemented_method lookups path in
      let impl = implemented.implementation.impl in
      if implemented.implementation.trait.is_capability then Some (Declared_by Impl_uses)
      else if
        Types.is_capability_subset
          ~implies:
            (implies_condition lookups
               ~list_bounds:(Properties.Bounds.close lookups (Types.list_bounds impl.impl_generics)))
          (Types.make_capability_set [ capability ])
          (make_expected_signature lookups implemented).uses
      then Some (Declared_by Own_uses)
      else
        Some
          (match
             find_self_capability_set implemented (read_trait_signature lookups implemented)
           with
          | Some set ->
              Declared_by
                (Associated_capability_set
                   {
                     name = set;
                     is_defined = List.mem_assoc set impl.capability_sets;
                     is_named =
                       (match Definition.find_declared_signature lookups path with
                       | Some own -> names_capability_set impl set own
                       | None -> false);
                   })
          | None -> Fixed_by_trait { trait = impl.implements; method_name = name })
  | Top _ | Method _ | Test _ -> Some (Declared_by Own_uses)
  | Member_constant _ | Impl _ | Derived _ | Law_proof _ | Unresolved _ ->
      raise_bug "%s declares no capabilities" (Path.show path)

let decide_property property lookups ~list_bounds type_ =
  Properties.decide_property lookups ~list_bounds ~normalize:(normalize lookups ~list_bounds)
    property type_

let has_property property lookups ~list_bounds type_ =
  match decide_property property lookups ~list_bounds type_ with
  | Holds -> true
  | Fails -> false
  | Depends_on open_type ->
      raise_bug "whether `%s` %s depends on the open type `%s`, so it has no bool answer"
        (Types.show type_)
        (Catalog.Typing_description.show_property property)
        (Types.show open_type)

let is_copyable = has_property Copyable
let is_plain = has_property Plain
let is_view = has_property View
let holds_function = has_property Holds_function

let binding_may_alias lookups ~list_bounds (mode : Language.Mode.t) type_ =
  match mode with
  | Mut -> true
  | Read | Own -> is_view lookups ~list_bounds type_ || not (is_plain lookups ~list_bounds type_)

let collect_contents lookups ~list_bounds type_ =
  Properties.collect_contents lookups
    ~normalize:(fun type_ ->
      let defining = ref [] in
      let normalized = normalize lookups ~list_bounds ~defining type_ in
      (normalized, !defining))
    type_
