module Lookups = Lookups
module Path_table = Hashtbl.Make (Path)

module Parameter_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Types.parameter
end))

module Occurrence_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.t * Interface.Properties.occurrence
end))

module Grown_node_table = Hashtbl.Make (Structural_key.Make (struct
  type t = (Path.t * int) * bool
end))

let raise_bug format = Compiler_bug.raise_bug ~stage:"Package_checks" format

type placed = { key : Resolve.Names.key; description : Catalog.description }

let place (key : Resolve.Names.key) diagnostic =
  { key; description = Catalog.Package.describe diagnostic }

let read_definition (lookups : Lookups.t) (declaration : Resolve.Names.declaration) =
  lookups.interface.names.read_definition declaration.key

let find_header (definition : Syntax.definition) : Core.origin =
  match definition.kind with
  | Impl { trait_; _ } -> Written trait_.id
  | Type_definition { name; _ } -> Written name.id
  | _ -> Written definition.id

let list_outer_packages (impl : Types.impl_interface) =
  Path.locate_package impl.implements.trait
  :: (match impl.for_type with Types.Named { path; _ } -> [ Path.locate_package path ] | _ -> [])
  @ List.filter_map
      (function
        | Types.Type (Types.Named { path; _ }) -> Some (Path.locate_package path) | _ -> None)
      impl.implements.trait_arguments

let check_location (declaration : Resolve.Names.declaration) (definition : Syntax.definition)
    (impl : Types.impl_interface) =
  let key = declaration.key in
  let package = key.module_.package in
  if List.mem package (list_outer_packages impl) then None
  else
    Some
      (place key
         (Impl_location
            { header = find_header definition; trait = impl.implements; for_type = impl.for_type }))

let check_sealed (lookups : Lookups.t) (declaration : Resolve.Names.declaration) =
  let is_sealed =
    match declaration.key.path with
    | Impl { trait; _ } -> Option.is_some (Types.find_sealed_implementors trait.path)
    | _ -> false
  in
  match
    if is_sealed then Resolve.Namespace.find_impl_heads lookups.interface.names declaration.key.path
    else None
  with
  | Some (trait, type_) -> (
      match (Types.find_sealed_implementors trait, Well_known.find_builtin_type type_) with
      | Some builtins, Some builtin when List.mem builtin builtins -> []
      | Some _, _ ->
          [
            place declaration.key
              (Sealed_trait_impl
                 {
                   header = find_header (read_definition lookups declaration);
                   trait;
                   type_;
                   is_floating_point = Well_known.is Floating_point trait;
                 });
          ]
      | None, _ -> [])
  | None -> []

let impls_overlap (first : Types.impl_interface) (second : Types.impl_interface) =
  let variables =
    List.map
      (fun (generic : Types.generic) -> generic.generic)
      (first.impl_generics @ second.impl_generics)
  in
  let bindings = Parameter_table.create 8 in
  let rec resolve (type_ : Types.ty) =
    match type_ with
    | Types.Parameter parameter when List.mem parameter variables -> (
        match Parameter_table.find_opt bindings parameter with
        | Some bound -> resolve bound
        | None -> type_)
    | _ -> type_
  in
  let occurs parameter =
    Types.exists ~resolve (function Types.Parameter other -> other = parameter | _ -> false)
  in
  let bind parameter other =
    if other = Types.Parameter parameter then true
    else if occurs parameter other then false
    else begin
      Parameter_table.replace bindings parameter other;
      true
    end
  in
  let rec unify left right =
    match (resolve left, resolve right) with
    | Types.Parameter parameter, other when List.mem parameter variables -> bind parameter other
    | other, Types.Parameter parameter when List.mem parameter variables -> bind parameter other
    | Types.Named left, Types.Named right ->
        Path.equal left.path right.path
        && List.length left.arguments = List.length right.arguments
        && List.for_all2 occurs_in_argument left.arguments right.arguments
    | left, right -> Types.equal left right
  and occurs_in_argument left right =
    match (left, right) with
    | Types.Type left, Types.Type right -> unify left right
    | Types.Value (Types.Value_parameter parameter), _
    | _, Types.Value (Types.Value_parameter parameter) ->
        List.mem parameter variables || left = right
    | left, right -> left = right
  in
  unify first.for_type second.for_type
  && List.length first.implements.trait_arguments = List.length second.implements.trait_arguments
  && List.for_all2 occurs_in_argument first.implements.trait_arguments
       second.implements.trait_arguments

let check_method_names (lookups : Lookups.t) (declaration : Resolve.Names.declaration)
    (definition : Syntax.definition) (impl : Types.impl_interface) =
  match
    ( impl.for_type,
      Interface.Definition.find_trait_interface lookups.interface impl.implements.trait )
  with
  | Types.Named { path; _ }, Some trait when not trait.is_capability ->
      let view = Types.find_view impl.for_type in
      let list_counted_members owner =
        Resolve.Names.list_members_visible_to_package lookups.interface.names
          ~package:declaration.key.module_.package owner
      in
      List.filter_map
        (fun (method_ : Types.trait_method) ->
          let own = list_counted_members path method_.method_name
          and of_view =
            match view with
            | Some (Types.Named view) ->
                List.filter
                  (fun (key : Resolve.Names.key) ->
                    match key.path with Method { receiver; _ } -> receiver <> Static | _ -> false)
                  (list_counted_members view.path method_.method_name)
            | _ -> []
          in
          let find_holder ~is_own : Catalog.Package.holder =
            match view with Some view when not is_own -> Of_view view | _ -> Own
          in
          let is_same_version (key : Resolve.Names.key) =
            match key.path with
            | Method { receiver; _ } -> receiver = method_.method_receiver
            | _ -> true
          in
          let written =
            List.exists
              (fun (name, receiver) ->
                name = method_.method_name && receiver = method_.method_receiver)
              impl.impl_methods
          in
          let make_clash ~is_own clash =
            Some
              (place declaration.key
                 (Method_name_clash
                    {
                      header = find_header definition;
                      for_type = impl.for_type;
                      method_name = method_.method_name;
                      holder = find_holder ~is_own;
                      clash;
                    }))
          in
          let is_own_version = List.exists is_same_version own in
          if is_own_version || List.exists is_same_version of_view then
            make_clash ~is_own:is_own_version
              (Same_receiver { receiver = method_.method_receiver; trait = impl.implements })
          else if own = [] && of_view = [] then None
          else if declaration.key.module_.package <> Path.locate_package path then
            make_clash ~is_own:(own <> []) Other_package
          else if not written then
            make_clash ~is_own:(own <> []) (Unwritten { trait = impl.implements })
          else None)
        trait.methods
  | _ -> []

let list_type_fields (lookups : Lookups.t) path =
  match Interface.Definition.find_type_interface lookups.interface path with
  | Some interface ->
      let parameters =
        List.map (fun (generic : Types.generic) -> generic.generic) interface.type_generics
      in
      let fields =
        match interface.shape with
        | Record fields -> List.map (fun field -> (None, field)) fields
        | Sum variants ->
            List.concat_map
              (fun (variant : Types.variant) ->
                List.map
                  (fun field -> (Some variant, field))
                  (Option.value ~default:[] variant.fields))
              variants
        | _ -> []
      in
      (parameters, fields)
  | None -> ([], [])

let list_type_arguments arguments =
  List.filter_map (function Types.Type type_ -> Some type_ | _ -> None) arguments

let list_contained_types (lookups : Lookups.t) path =
  let list_bounds =
    match Interface.Definition.find_type_interface lookups.interface path with
    | Some interface ->
        Interface.Properties.Bounds.close lookups.interface
          (Types.list_bounds interface.type_generics)
    | None -> Interface.Properties.Bounds.none
  in
  List.concat_map
    (fun (((variant : Types.variant option), (field : Types.field)) as written) ->
      let indirect = match variant with Some variant -> variant.indirect | None -> false in
      List.filter_map
        (function
          | Types.Named { path; _ }, occurrence ->
              Some
                ( written,
                  path,
                  Interface.Properties.compose_occurrences
                    (if indirect then Indirect else In_place)
                    occurrence )
          | _ -> None)
        (Interface.Impls.collect_contents lookups.interface ~list_bounds field.field_type).contained)
    (snd (list_type_fields lookups path))

let memoize compute =
  let table = Path_table.create 64 in
  fun path ->
    match Path_table.find_opt table path with
    | Some value -> value
    | None ->
        let value = compute path in
        Path_table.replace table path value;
        value

let list_self_occurrences ~list_contained (start : Path.t) =
  let visited = Occurrence_table.create 16 in
  let rec trace_from path occurrence =
    if Path.equal path start then [ occurrence ]
    else if
      Path.locate_package path <> Path.locate_package start
      || Occurrence_table.mem visited (path, occurrence)
    then []
    else begin
      Occurrence_table.replace visited (path, occurrence) ();
      List.concat_map
        (fun (_, target, step) ->
          trace_from target (Interface.Properties.compose_occurrences occurrence step))
        (list_contained path)
    end
  in
  List.concat_map
    (fun (field, target, occurrence) ->
      List.map (fun path -> (field, path)) (trace_from target occurrence))
    (list_contained start)

let grows lookups (start : Path.t) =
  let list_edges (path, index) =
    let parameters, fields = list_type_fields lookups path in
    match List.nth_opt parameters index with
    | None -> []
    | Some parameter ->
        let mentions =
          Types.exists (function Types.Parameter other -> other = parameter | _ -> false)
        in
        let rec list_targets (type_ : Types.ty) =
          match type_ with
          | Types.Named { path = target; arguments } ->
              let arguments = list_type_arguments arguments in
              List.concat
                (List.mapi
                   (fun position argument ->
                     if mentions argument then
                       [ ((target, position), argument <> Types.Parameter parameter) ]
                     else [])
                   arguments)
              @ List.concat_map list_targets arguments
          | Types.Function { inputs; output; _ } ->
              List.concat_map (fun (_, type_) -> list_targets type_) inputs @ list_targets output
          | _ -> []
        in
        List.concat_map (fun (_, (field : Types.field)) -> list_targets field.field_type) fields
  in
  let visited = Grown_node_table.create 16 in
  let rec walk ((path, _) as node) grown =
    if Path.equal path start && grown then true
    else if Grown_node_table.mem visited (node, grown) then false
    else begin
      Grown_node_table.replace visited (node, grown) ();
      List.exists (fun (target, growing) -> walk target (grown || growing)) (list_edges node)
    end
  in
  let parameters, _ = list_type_fields lookups start in
  List.exists
    (fun index ->
      List.exists (fun (target, growing) -> walk target growing) (list_edges (start, index)))
    (List.init (List.length parameters) Fun.id)

let read_written_variant (variants : Syntax.variant list) (variant : Types.variant) =
  match
    List.find_opt
      (fun (written : Syntax.variant) -> written.name.text = variant.variant_name)
      variants
  with
  | Some written -> written
  | None -> raise_bug "the variant `%s` is not in its type's definition" variant.variant_name

let find_field (body : Syntax.type_body) ((variant : Types.variant option), (field : Types.field)) :
    Core.origin =
  let raise_missing () =
    raise_bug "the field `%s` is not in its type's definition" field.field_name
  in
  let locate_among (fields : Syntax.field list) =
    match
      List.find_map
        (fun (written : Syntax.field) ->
          match written.kind with
          | Field_declaration { name; _ } when name.text = field.field_name ->
              Some (Core.Written written.id)
          | _ -> None)
        fields
    with
    | Some origin -> origin
    | None -> raise_missing ()
  in
  match (body, variant) with
  | Fields fields, None -> locate_among fields
  | Variants variants, Some variant -> (
      match (read_written_variant variants variant).fields with
      | Some fields -> locate_among fields
      | None -> raise_missing ())
  | _ -> raise_missing ()

let check_recursion lookups ~list_contained (declaration : Resolve.Names.declaration)
    (definition : Syntax.definition) =
  match definition.kind with
  | Type_definition _ when grows lookups declaration.key.path ->
      [ place declaration.key (Growing_type { header = find_header definition }) ]
  | Type_definition { name; body; _ } ->
      let key = declaration.key in
      let occurrences = list_self_occurrences ~list_contained key.path in
      let find_first (wanted : Interface.Properties.occurrence) =
        List.find_map
          (fun (field, occurrence) -> if occurrence = wanted then Some field else None)
          occurrences
      in
      let in_place =
        Option.map
          (fun ((variant : Types.variant option), _) ->
            match (body, variant) with
            | Variants variants, Some variant ->
                place key
                  (Variant_in_place
                     { variant = Written (read_written_variant variants variant).name.id })
            | Fields _, None -> place key (Record_in_place { header = find_header definition })
            | _ ->
                raise_bug
                  "the interface of `%s` and its definition disagree on whether it is a sum type"
                  name.text)
          (find_first In_place)
      in
      let function_input =
        Option.map
          (fun field ->
            place key
              (Function_input_field { field = find_field body field; type_name = name.text }))
          (find_first Function_input)
      in
      Option.to_list in_place @ Option.to_list function_input
  | _ -> []

let check_associated_types (lookups : Lookups.t) ~list_contained
    (declaration : Resolve.Names.declaration) (definition : Syntax.definition)
    (impl : Types.impl_interface) =
  let key = declaration.key in
  let list_bounds =
    Interface.Properties.Bounds.close lookups.interface (Types.list_bounds impl.impl_generics)
  in
  let find_written name =
    match definition.kind with
    | Impl { members; _ } ->
        List.find_map
          (fun (member : Syntax.impl_member Syntax.node) ->
            match member.kind with
            | Associated_definition (written, _) when written.text = name ->
                Some (Core.Written member.id)
            | _ -> None)
          members
    | _ -> None
  in
  let is_reported_at_definition (recursion : Interface.Properties.recursion) =
    match recursion.recursive with
    | Types.Named { path; _ } ->
        List.exists
          (fun (_, occurrence) -> occurrence = recursion.occurrence)
          (list_self_occurrences ~list_contained path)
    | _ -> false
  in
  List.concat_map
    (fun (name, type_) ->
      let member =
        match find_written name with
        | Some member -> member
        | None -> raise_bug "the associated type `%s` is not in its impl's definition" name
      in
      List.filter_map
        (fun (recursive, (occurrence : Interface.Properties.occurrence)) ->
          match occurrence with
          | In_place -> Some (place key (Associated_type_in_place { member; name; recursive }))
          | Function_input ->
              Some (place key (Associated_function_input { member; name; recursive }))
          | Indirect -> None)
        (List.sort_uniq compare
           (List.filter_map
              (fun (recursion : Interface.Properties.recursion) ->
                if
                  List.exists (Path.equal declaration.key.path) recursion.defining
                  && not (is_reported_at_definition recursion)
                then Some (recursion.recursive, recursion.occurrence)
                else None)
              (Interface.Impls.collect_contents lookups.interface ~list_bounds type_).recursions)))
    impl.implements.associated

let list_instantiations (key : Resolve.Names.key) (form : Core.t) =
  let grows = function
    | Types.Type (Types.Named { arguments; _ }) ->
        let mentions =
          Types.exists (function
            | Types.Parameter { owner; _ } -> Path.equal owner key.path
            | _ -> false)
        in
        List.exists (function Types.Type type_ -> mentions type_ | _ -> false) arguments
    | _ -> false
  in
  let edges = ref [] in
  Core_walk.walk_definition
    {
      Core_walk.ignore_all with
      callee =
        (fun callee ->
          match callee.target with
          | Function { path; instantiation = { type_arguments; _ } }
            when Path.locate_package path = key.module_.package && type_arguments <> [] ->
              edges := (path, List.exists grows type_arguments) :: !edges
          | _ -> ());
    }
    form.definition;
  List.rev !edges

let find_growing_cycles (lookups : Lookups.t) (stale : Resolve.Names.declaration list) =
  let keys = Path_table.create 64 and calls = Path_table.create 64 in
  List.iter
    (fun (declaration : Resolve.Names.declaration) ->
      Path_table.replace keys declaration.key.path declaration.key)
    stale;
  let list_calls path =
    match Path_table.find_opt calls path with
    | Some listed -> listed
    | None ->
        let listed = lookups.list_instantiations (Path_table.find keys path) in
        List.iter
          (fun ((callee : Resolve.Names.key), _) -> Path_table.replace keys callee.path callee)
          listed;
        Path_table.replace calls path listed;
        listed
  in
  let component = Path_table.create 64 in
  List.iteri
    (fun index members -> List.iter (fun path -> Path_table.replace component path index) members)
    (Strongly_connected.list_components
       (module Path)
       ~list_successors:(fun path ->
         List.map (fun ((callee : Resolve.Names.key), _) -> callee.path) (list_calls path))
       (List.map (fun (declaration : Resolve.Names.declaration) -> declaration.key.path) stale));
  let grows_on_a_cycle path =
    List.exists
      (fun ((callee : Resolve.Names.key), grows) ->
        grows && Path_table.find component callee.path = Path_table.find component path)
      (list_calls path)
  in
  let stale_paths = Path_table.create 64 in
  List.iter
    (fun (declaration : Resolve.Names.declaration) ->
      Path_table.replace stale_paths declaration.key.path ())
    stale;
  List.sort
    (fun ((left : Resolve.Names.key), _) ((right : Resolve.Names.key), _) ->
      Path.compare left.path right.path)
    (Path_table.fold
       (fun path _ found ->
         let grows = grows_on_a_cycle path in
         if grows || Path_table.mem stale_paths path then
           (Path_table.find keys path, grows) :: found
         else found)
       calls [])

let report_growing_cycle (lookups : Lookups.t) (declaration : Resolve.Names.declaration) =
  [
    place declaration.key
      (Instantiation_cycle { header = find_header (read_definition lookups declaration) });
  ]

let check_test (lookups : Lookups.t) (declaration : Resolve.Names.declaration) =
  match declaration.key.path with
  | Test { name; _ } -> (
      match lookups.list_tests declaration.key.module_.package name with
      | first :: _ when not (Path.equal first.path declaration.key.path) ->
          [ place declaration.key (Duplicate_test { name }) ]
      | _ -> [])
  | _ -> []

let check_overlaps (lookups : Lookups.t) (declaration : Resolve.Names.declaration) definition
    (impl : Types.impl_interface) =
  let package = declaration.key.module_.package in
  match Interface.Impls.find_head impl.for_type with
  | Some type_ when List.mem package (list_outer_packages impl) ->
      let trait = impl.implements.trait in
      let rec list_before = function
        | [] -> []
        | impl :: rest ->
            if Path.equal impl declaration.key.path then [] else impl :: list_before rest
      in
      let earlier =
        List.filter
          (fun (other : Types.impl_interface) -> List.mem package (list_outer_packages other))
          (List.filter_map
             (Interface.Definition.find_impl_interface lookups.interface)
             (list_before
                (Interface.Impls.list_impls_of_trait_for_type lookups.interface ~trait ~type_
                   package)))
      in
      let dependencies =
        List.concat_map
          (fun name ->
            List.filter_map
              (Interface.Definition.find_impl_interface lookups.interface)
              (Interface.Impls.list_impls_of_trait_for_type lookups.interface ~trait ~type_ name))
          (Resolve.Names.list_transitive_dependencies lookups.interface.names package)
      in
      List.filter_map
        (fun (other : Types.impl_interface) ->
          if impls_overlap impl other then
            Some
              (place declaration.key
                 (Overlapping_impls
                    {
                      header = find_header definition;
                      trait = other.implements;
                      for_type = other.for_type;
                    }))
          else None)
        (earlier @ dependencies)
  | _ -> []

let check_impl (lookups : Lookups.t) ~list_contained (declaration : Resolve.Names.declaration) =
  match
    ( Interface.Definition.find_impl_interface lookups.interface declaration.key.path,
      read_definition lookups declaration )
  with
  | Some impl, definition ->
      Option.to_list (check_location declaration definition impl)
      @ check_method_names lookups declaration definition impl
      @ check_overlaps lookups declaration definition impl
      @ check_associated_types lookups ~list_contained declaration definition impl
  | _ -> []

let check_type lookups ~list_contained (declaration : Resolve.Names.declaration) =
  check_recursion lookups ~list_contained declaration (read_definition lookups declaration)

let must_be_used (lookups : Lookups.t) (declaration : Resolve.Names.declaration) =
  (match declaration.visibility with Private | Internal -> true | Public | Public_opaque -> false)
  && declaration.key.ordinal = 0
  && Option.is_none (lookups.interface.names.find_container declaration.key)
  && Option.is_none (Well_known.of_path declaration.key.path)
  && (not (Path.is_entry_point declaration.key.path))
  &&
  match declaration.kind with
  | Function | Method | Constant | Member_constant -> true
  | Type | Trait | Capability | Theorem | Impl | Test | Law_proof -> false

let list_uses (form : Core.t) =
  let used = ref [] in
  let use path = used := path :: !used in
  let use_constant : Core.pattern_constant -> unit = function
    | Named_constant path -> use path
    | Boolean_constant _ | Integer_constant _ | String_constant _ -> ()
  in
  let use_bound : Core.range_bound -> unit = function
    | Constant_bound path -> use path
    | Integer_bound _ -> ()
  in
  let use_callee (callee : Core.callee) =
    match callee.target with
    | Function { path; _ } -> use path
    | Trait_method _ | Capability_method _ | Intrinsic _ | Indirect _ -> ()
  in
  Core_walk.walk_definition
    {
      Core_walk.ignore_all with
      callee = use_callee;
      expression =
        (fun (node : Core.expression) ->
          match node.kind with Function_value { path; _ } -> use path | _ -> ());
      place =
        (function
        | Constant { path; _ } -> use path
        | Local _ | Field _ | Element _ | Range _ | Lent _ | Temporary _ -> ());
      pattern =
        (fun (node : Core.pattern) ->
          match node.kind with
          | Literal value | Equal_to { value; _ } -> use_constant value
          | Range { start; stop; _ } ->
              use_bound start;
              use_bound stop
          | Wildcard | Bind _ | Variant _ | Record _ | Alternatives _ -> ());
    }
    form.definition;
  !used

let find_name (definition : Syntax.definition) : Core.origin =
  match definition.kind with
  | Function { signature; _ } | Method_declaration signature ->
      Written (Resolve.Names.extract_signature_name signature).id
  | Constant { name = Plain_name name | Member_name (_, name); _ }
  | Definition_error { name = Some (Plain_name name | Member_name (_, name)); _ } ->
      Written name.id
  | _ -> raise_bug "an unused definition that is neither a function nor a constant"

let report_unused (lookups : Lookups.t) (declaration : Resolve.Names.declaration) ~is_named =
  let kind : Catalog.Usage.definition_kind =
    match declaration.kind with Constant | Member_constant -> Constant | _ -> Function
  and visibility : Catalog.Usage.visibility =
    match declaration.visibility with
    | Internal -> Internal
    | Private -> Private
    | Public | Public_opaque -> raise_bug "an unused definition that is public"
  in
  {
    key = declaration.key;
    description =
      Catalog.Usage.describe
        (Unused_definition
           {
             name = find_name (read_definition lookups declaration);
             definition = declaration.key.path;
             kind;
             visibility;
             is_used_by_unused = is_named;
           });
  }

type use = Used | Unused of { is_named : bool }

exception Is_used

let classify_uses (lookups : Lookups.t) (stale : Resolve.Names.declaration list) =
  let was_unused = memoize lookups.was_unused in
  let decided = Path_table.create 64 in
  let stale_paths = Path_table.create 64 in
  let unsettled = Path_table.create 64 in
  let queued = Queue.create () in
  let enqueue (declaration : Resolve.Names.declaration) =
    match Path_table.find_opt decided declaration.key.path with
    | Some (_, Used) -> ()
    | Some (_, Unused _) | None ->
        Path_table.replace unsettled declaration.key.path ();
        Queue.add declaration queued
  in
  List.iter
    (fun (declaration : Resolve.Names.declaration) ->
      Path_table.replace stale_paths declaration.key.path ();
      enqueue declaration)
    stale;
  let is_believed_unused path =
    match Path_table.find_opt decided path with
    | Some (_, Unused _) -> true
    | Some (_, Used) -> false
    | None -> was_unused path
  in
  let decide (declaration : Resolve.Names.declaration) use =
    let path = declaration.key.path in
    let flips = is_believed_unused path <> (use <> Used) in
    Path_table.remove unsettled path;
    Path_table.replace decided path (declaration, use);
    if flips then List.iter enqueue (lookups.list_used declaration.key)
  in
  let search (start : Resolve.Names.declaration) =
    let low_link = Path_table.create 16 in
    let index_on_stack = Path_table.create 16 in
    let named_by_another = Path_table.create 16 in
    let stack = ref [] in
    let rec visit (declaration : Resolve.Names.declaration) =
      let path = declaration.key.path in
      let index = Path_table.length low_link in
      Path_table.replace low_link path index;
      Path_table.replace index_on_stack path index;
      stack := declaration :: !stack;
      let lower other =
        Path_table.replace low_link path (min (Path_table.find low_link path) other)
      in
      Seq.iter
        (fun (user : Resolve.Names.declaration) ->
          let user_path = user.key.path in
          if not (Path.equal user_path path && user.key.ordinal = 0) then begin
            Path_table.replace named_by_another path ();
            if not (must_be_used lookups user) then raise Is_used;
            match
              (Path_table.find_opt index_on_stack user_path, Path_table.find_opt decided user_path)
            with
            | Some user_index, _ -> lower user_index
            | None, Some (_, Used) -> raise Is_used
            | None, verdict ->
                let is_settled_unused =
                  (not (Path_table.mem unsettled user_path))
                  && match verdict with Some _ -> true | None -> was_unused user_path
                in
                if not is_settled_unused then begin
                  visit user;
                  lower (Path_table.find low_link user_path)
                end
          end)
        (lookups.list_users path);
      if Path_table.find low_link path = index then
        let rec emit () =
          match !stack with
          | (member : Resolve.Names.declaration) :: rest ->
              stack := rest;
              Path_table.remove index_on_stack member.key.path;
              decide member (Unused { is_named = Path_table.mem named_by_another member.key.path });
              if not (Path.equal member.key.path path) then emit ()
          | [] -> ()
        in
        emit ()
    in
    match visit start with
    | () -> ()
    | exception Is_used -> List.iter (fun member -> decide member Used) !stack
  in
  let rec settle () =
    match Queue.take_opt queued with
    | None -> ()
    | Some (declaration : Resolve.Names.declaration) ->
        if Path_table.mem unsettled declaration.key.path then
          if must_be_used lookups declaration then search declaration else decide declaration Used;
        settle ()
  in
  settle ();
  List.sort
    (fun ((left : Resolve.Names.declaration), _) ((right : Resolve.Names.declaration), _) ->
      Path.compare left.key.path right.key.path)
    (Path_table.fold
       (fun path (declaration, use) classified ->
         if Path_table.mem stale_paths path || was_unused path <> (use <> Used) then
           (declaration, use) :: classified
         else classified)
       decided [])

let check_unexported (lookups : Lookups.t) use (declaration : Resolve.Names.declaration) =
  if must_be_used lookups declaration then
    match use with
    | Unused { is_named } -> [ report_unused lookups declaration ~is_named ]
    | Used -> []
  else []

type check =
  | Sealed of Resolve.Names.key
  | Impl of Resolve.Names.key
  | Type of Resolve.Names.key
  | Instantiation of Resolve.Names.key
  | Test of Resolve.Names.key
  | Unexported of Resolve.Names.key * use
  | Dependency of Path.package

type outcome = Placed of placed list | Dependency_used of bool

let check_definition (lookups : Lookups.t) key check_declaration =
  let names = lookups.interface.names in
  match check_declaration (names.read_declaration key) with
  | placed -> Placed placed
  | exception Interface.Properties.Recursion_limit diagnostic ->
      Placed [ { key; description = Catalog.Typing.describe diagnostic } ]

let run (lookups : Lookups.t) package check =
  let list_contained = memoize (list_contained_types lookups) in
  match check with
  | Sealed key -> check_definition lookups key (check_sealed lookups)
  | Impl key -> check_definition lookups key (check_impl lookups ~list_contained)
  | Type key -> check_definition lookups key (check_type lookups ~list_contained)
  | Instantiation key -> check_definition lookups key (report_growing_cycle lookups)
  | Test key -> check_definition lookups key (check_test lookups)
  | Unexported (key, use) -> check_definition lookups key (check_unexported lookups use)
  | Dependency dependency -> Dependency_used (lookups.is_package_used ~by:package dependency)
