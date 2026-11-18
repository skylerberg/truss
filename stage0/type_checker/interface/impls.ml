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

let find_implemented_method lookups (path : Path.t) =
  let ( let* ) = Option.bind in
  match path with
  | Method { owner = (Impl _ | Derived _) as owner; name; receiver } ->
      let* implementation = find_implementation lookups owner in
      let trait = implementation.impl.implements.trait in
      let* declared = Definition.find_trait_method lookups trait ~name ~receiver in
      Some
        {
          implementation;
          declared;
          declaration =
            Method
              { owner = trait; name = declared.method_name; receiver = declared.method_receiver };
        }
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
          if Types.equal bound type_ || Types.is_open_type type_ then Some substitution else None
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

type evidence =
  | From_impl of { impl : Path.t; substitution : Types.substitution }
  | From_bound
  | From_any
  | Built_in
  | Accepted of Types.ty

type through_any = Callable | Has_generics | Names_self

let classify_through_any lookups ~(trait : Path.t) (method_ : Types.trait_method) : through_any =
  let self = Types.make_self_parameter trait in
  let names_self type_ =
    let mentions_self = ref false in
    ignore
      (Types.map
         (function
           | Types.Projection { base = Types.Parameter base; _ } as projected when base = self ->
               Some projected
           | Types.Parameter parameter as named when parameter = self ->
               mentions_self := true;
               Some named
           | _ -> None)
         type_);
    !mentions_self
  in
  let signature = Definition.read_method_signature lookups ~owner:trait method_ in
  let result = Types.extract_result_type signature.output in
  if signature.generics <> [] || signature.capability_parameters <> [] then Has_generics
  else if
    List.exists (fun (info : Types.parameter_info) -> names_self info.type_) signature.parameters
    || names_self result
  then Names_self
  else Callable

type bounds = Types.parameter -> Types.trait_reference list

let list_no_bounds _ = []

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

let list_impl_bounds (impl : Types.impl_interface) ~list_bounds parameter =
  match
    List.find_opt (fun (generic : Types.generic) -> generic.generic = parameter) impl.impl_generics
  with
  | Some { kind = Type_generic bounds; _ } -> bounds
  | _ -> list_bounds parameter

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

let find_built_in_evidence : Properties.decision -> evidence option = function
  | Holds -> Some Built_in
  | Fails -> None
  | Depends_on open_type -> Some (Accepted open_type)

let rec find_evidence lookups ~(list_bounds : bounds) ?(depth = 0) ?(checks_conditions = true)
    (type_ : Types.ty) (wanted : Types.trait_reference) : evidence option =
  let broken_trait =
    match Definition.find_interface lookups wanted.trait with
    | Some (Error_interface report) -> Some report
    | _ -> None
  in
  if depth > Properties.recursion_limit then
    raise
      (Properties.Recursion_limit
         (Printf.sprintf
            "Deciding whether `%s` implements `%s` needs more than %d nested impls. The compiler \
             stops there: bounds that ask for ever larger types never finish."
            (Types.show type_) (Types.show_trait wanted) Properties.recursion_limit))
  else if Option.is_some broken_trait then
    Option.map (fun report -> Accepted (Types.Error report)) broken_trait
  else if Well_known.is Copyable wanted.trait || Well_known.is Plain wanted.trait then
    let property : Properties.property =
      if Well_known.is Plain wanted.trait then Plain else Copyable
    in
    if not checks_conditions then Some Built_in
    else
      find_built_in_evidence
        (Properties.decide_property lookups ~list_bounds ~normalize:(normalize lookups ~list_bounds)
           property type_)
  else if Well_known.is Storable wanted.trait then
    if not checks_conditions then Some Built_in
    else
      find_built_in_evidence
        (Properties.decide_storable lookups ~list_bounds ~normalize:(normalize lookups ~list_bounds)
           type_)
  else
    match type_ with
    | Types.Error _ | Types.Hole | Types.Variable _ -> Some (Accepted type_)
    | Types.Literal (kind, _) ->
        if
          List.for_all
            (fun candidate ->
              Option.is_some
                (find_evidence lookups ~list_bounds ~depth:(depth + 1) ~checks_conditions candidate
                   wanted))
            (Types.list_literal_types kind)
        then Some (Accepted type_)
        else None
    | Types.Never | Types.Integer | Types.Function _ -> None
    | Types.Parameter _ | Types.Projection _ ->
        if list_matching_bounds lookups ~list_bounds type_ wanted <> [] then Some From_bound
        else None
    | Types.Any _ ->
        if list_matching_bounds lookups ~list_bounds type_ wanted <> [] then Some From_any else None
    | Types.Named { path; _ } ->
        let packages =
          List.sort_uniq compare
            (Path.locate_package wanted.trait :: Path.locate_package path
            :: List.filter_map
                 (function
                   | Types.Type (Types.Named { path; _ }) -> Some (Path.locate_package path)
                   | _ -> None)
                 wanted.trait_arguments)
        in
        let candidates =
          List.concat_map
            (fun package ->
              list_impls_of_trait_for_type lookups ~trait:wanted.trait ~type_:path package)
            packages
        in
        List.find_map
          (fun impl_path ->
            match Definition.find_impl_interface lookups impl_path with
            | None -> None
            | Some impl -> (
                let variables =
                  List.map (fun (generic : Types.generic) -> generic.generic) impl.impl_generics
                in
                match match_type ~variables Types.no_substitution impl.for_type type_ with
                | None -> None
                | Some substitution -> (
                    match
                      match_arguments ~variables substitution impl.implements.trait_arguments
                        wanted.trait_arguments
                    with
                    | None -> None
                    | Some substitution ->
                        let associated =
                          List.map
                            (fun (name, type_) -> (name, Types.substitute substitution type_))
                            impl.implements.associated
                        in
                        let conditions_hold =
                          (not checks_conditions)
                          || List.for_all
                               (fun (argument, bound) ->
                                 Option.is_some
                                   (find_evidence lookups ~list_bounds ~depth:(depth + 1) argument
                                      bound))
                               (list_required_bounds impl.impl_generics substitution)
                        in
                        if
                          conditions_hold
                          && has_matching_associated_types lookups ~list_bounds wanted ~base:None
                               associated
                        then Some (From_impl { impl = impl_path; substitution })
                        else None)))
          candidates

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
  let matches ~base ~associated (bound : Types.trait_reference) =
    Path.equal bound.trait wanted.trait
    && arguments_match bound.trait_arguments
    && has_matching_associated_types lookups ~list_bounds wanted ~base associated
  in
  match type_ with
  | Types.Any trait ->
      List.filter
        (fun (bound : Types.trait_reference) ->
          matches ~base:None
            ~associated:
              (if Path.equal bound.trait trait.trait then trait.associated else bound.associated)
            bound)
        (Properties.list_bound_closure lookups ~self:type_ trait)
  | _ ->
      List.filter
        (fun (bound : Types.trait_reference) ->
          matches ~base:(Some type_) ~associated:bound.associated bound)
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
  match (List.assoc_opt name trait.associated, type_) with
  | Some fixed, _ -> Some fixed
  | None, Types.Literal (kind, _) ->
      project_for_every_type_of_kind lookups ~list_bounds ?defining type_ kind trait name
  | None, _ -> (
      match find_evidence lookups ~list_bounds ~checks_conditions:false type_ trait with
      | Some (From_impl { impl; substitution }) -> (
          match Definition.find_impl_interface lookups impl with
          | Some interface ->
              Option.iter (fun defining -> defining := impl :: !defining) defining;
              Option.map (Types.substitute substitution)
                (List.assoc_opt name interface.implements.associated)
          | None -> None)
      | Some From_bound -> (
          match
            List.find_map
              (fun (bound : Types.trait_reference) ->
                if Path.equal bound.trait trait.trait then List.assoc_opt name bound.associated
                else None)
              (Properties.list_known_bounds lookups ~list_bounds type_)
          with
          | Some fixed -> Some fixed
          | None -> Some (Types.Projection { base = type_; trait; name }))
      | Some From_any -> (
          match type_ with
          | Types.Any any ->
              List.find_map
                (fun (bound : Types.trait_reference) -> List.assoc_opt name bound.associated)
                (any :: Properties.list_bound_closure lookups ~self:type_ any)
          | _ -> None)
      | Some Built_in -> None
      | Some (Accepted (Types.Variable _)) -> None
      | Some (Accepted unknown) -> Some unknown
      | None -> None)

and project_for_every_type_of_kind lookups ~list_bounds ?defining literal kind
    (trait : Types.trait_reference) name =
  let replace ~from ~into type_ =
    Types.map (fun part -> if Types.equal part from then Some into else None) type_
  in
  let replace_in_trait ~from ~into (reference : Types.trait_reference) : Types.trait_reference =
    {
      reference with
      trait_arguments =
        List.map
          (function
            | Types.Type argument -> Types.Type (replace ~from ~into argument) | value -> value)
          reference.trait_arguments;
      associated =
        List.map (fun (name, type_) -> (name, replace ~from ~into type_)) reference.associated;
    }
  in
  match
    List.map
      (fun candidate ->
        Option.map
          (replace ~from:candidate ~into:literal)
          (project_declared_type lookups ~list_bounds ?defining candidate
             (replace_in_trait ~from:literal ~into:candidate trait)
             name))
      (Types.list_literal_types kind)
  with
  | Some projected :: rest when List.for_all (Option.equal Types.equal (Some projected)) rest ->
      Some projected
  | _ -> None

and project_capability_set lookups ~list_bounds ?(depth = 0) type_ (trait : Types.trait_reference)
    name =
  let trait = read_declaring_capability_trait lookups ~base:type_ trait name in
  let projection =
    Types.make_capability_set [ Types.Capability_projection { base = type_; trait; name } ]
  in
  if depth > Properties.recursion_limit then
    raise
      (Properties.Recursion_limit
         (Printf.sprintf
            "Finding the capabilities in `%s` needs more than %d nested capability sets. The \
             compiler stops there: capability sets defined from each other never finish."
            (Types.show_capability (Capability_projection { base = type_; trait; name }))
            Properties.recursion_limit))
  else
    match find_evidence lookups ~list_bounds ~checks_conditions:false type_ trait with
    | Some (From_impl { impl; substitution }) -> (
        match Definition.find_impl_interface lookups impl with
        | Some interface ->
            normalize_capabilities lookups ~list_bounds ~depth:(depth + 1)
              (Types.substitute_capabilities substitution
                 (Option.value ~default:Types.no_capabilities
                    (List.assoc_opt name interface.capability_sets)))
        | None -> Types.no_capabilities)
    | Some From_bound | Some (Accepted (Types.Variable _)) | None -> projection
    | Some (From_any | Built_in | Accepted _) -> Types.no_capabilities

and normalize_capabilities lookups ~list_bounds ?depth (capabilities : Types.capability_set) =
  let reads_an_impl : Types.capability -> bool = function
    | Capability_projection _ -> true
    | _ -> false
  in
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
          | Types.Variable _ | Types.Hole -> Some (Types.Projection { base; trait; name })
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
            | None -> Some (Types.Error Diagnostic.reported_elsewhere)
          else
            project_associated_type lookups
              ~list_bounds:(list_impl_bounds impl ~list_bounds)
              impl.for_type projected name
      | _ -> None)
    type_

and normalize_capabilities_in_impl lookups ~list_bounds (impl : Types.impl_interface) capabilities =
  normalize_capabilities lookups
    ~list_bounds:(list_impl_bounds impl ~list_bounds)
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
      ~list_bounds:(Types.list_bounds (implementation.impl.impl_generics @ declared.generics))
      implementation declared
  in
  match written with
  | Some written when implementation.trait.is_capability ->
      {
        expected with
        receiver = written.receiver;
        parameters =
          List.map
            (fun (parameter : Types.parameter_info) -> { parameter with has_default = false })
            expected.parameters;
      }
  | Some _ | None -> expected

and read_signature lookups (path : Path.t) =
  let ( let* ) = Option.bind in
  match path with
  | Method { owner = (Impl _ | Derived _) as owner; _ } ->
      let* impl = Definition.find_impl_interface lookups owner in
      let written = Definition.find_declared_signature lookups path in
      let declared =
        Option.map (make_expected_signature lookups ?written) (find_implemented_method lookups path)
      in
      let* stated = if Option.is_some written then written else declared in
      let signature =
        Types.add_impl_generics_and_uses ~impl_generics:impl.impl_generics ~impl_uses:impl.impl_uses
          { (Option.value declared ~default:stated) with uses = stated.uses; costs = stated.costs }
      in
      let uses =
        normalize_capabilities_in_impl lookups
          ~list_bounds:(Types.list_bounds signature.generics)
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

let read_scope (lookups : Lookups.t) (key : Resolve.Names.key) : Environment.scope =
  let scope = (lookups.read_elaborated_interface key).scope in
  match read_signature lookups key.path with
  | None -> scope
  | Some signature ->
      {
        scope with
        bounds =
          List.map
            (fun (parameter, written_bounds) ->
              ( parameter,
                match
                  List.find_opt
                    (fun (generic : Types.generic) -> generic.generic = parameter)
                    signature.generics
                with
                | Some { kind = Type_generic bounds; _ } -> bounds
                | Some { kind = Value_generic; _ } | None -> written_bounds ))
            scope.bounds;
      }

type declaring_clause =
  | Own_uses
  | Impl_uses
  | Associated_capability_set of { name : string; is_defined : bool; is_named : bool }

type capability_declaration =
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

let show_declaring_clause clause capability =
  match clause with
  | Own_uses -> Printf.sprintf "`uses %s`" capability
  | Impl_uses -> Printf.sprintf "`uses %s` on the `impl`" capability
  | Associated_capability_set { name; is_defined; is_named } ->
      let set =
        if is_defined then Printf.sprintf "`%s` in the `impl`'s `capability %s`" capability name
        else Printf.sprintf "`capability %s = %s` in the `impl`" name capability
      in
      if is_named then set else Printf.sprintf "%s and `uses Self.%s` on the method" set name

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
        (Properties.show_property property)
        (Types.show open_type)

let is_copyable = has_property Copyable
let is_plain = has_property Plain
let is_view = has_property View
let holds_function = has_property Holds_function

let collect_contents lookups ~list_bounds type_ =
  Properties.collect_contents lookups
    ~normalize:(fun type_ ->
      let defining = ref [] in
      let normalized = normalize lookups ~list_bounds ~defining type_ in
      (normalized, !defining))
    type_
