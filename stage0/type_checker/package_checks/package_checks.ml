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

type placed = { key : Resolve.Names.key; diagnostic : Diagnostic.in_definition }

let make_diagnostic (key : Resolve.Names.key) ?(fixes = []) code (span : Source.Definition_span.t)
    message =
  { key; diagnostic = Diagnostic.make ~fixes ~code:(Package code) span message }

let read_definition (lookups : Lookups.t) (declaration : Resolve.Names.declaration) =
  let key = declaration.key in
  (lookups.interface.names.read_definition key, lookups.interface.names.read_spans key)

let locate_header spans definition =
  Source.Definition_span.locate spans (Resolve.Names.extract_header_id definition)

let list_outer_packages (impl : Types.impl_interface) =
  Path.locate_package impl.implements.trait
  :: (match impl.for_type with Types.Named { path; _ } -> [ Path.locate_package path ] | _ -> [])
  @ List.filter_map
      (function
        | Types.Type (Types.Named { path; _ }) -> Some (Path.locate_package path) | _ -> None)
      impl.implements.trait_arguments

let check_location (declaration : Resolve.Names.declaration) spans (definition : Syntax.definition)
    (impl : Types.impl_interface) =
  let key = declaration.key in
  let package = key.module_.package in
  if List.mem package (list_outer_packages impl) then None
  else
    Some
      (make_diagnostic key Impl_location (locate_header spans definition)
         (Printf.sprintf
            "This `impl` must be in the package of `%s`, of `%s`, or of a type its trait's \
             arguments name, so that only one place can hold it."
            (Types.show_trait impl.implements)
            (Types.show impl.for_type)))

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
          let definition, spans = read_definition lookups declaration in
          let implementors, reason =
            if Well_known.is Floating_point trait then
              ( "the built-in float types",
                "the trait describes the IEEE 754 formats of `Float32` and `Float64`, which its \
                 `Bits` and methods such as `is_nan` expose" )
            else
              ( "the built-in integer types",
                "generic code over the trait is proven for each of them" )
          in
          [
            make_diagnostic declaration.key Sealed_trait_impl (locate_header spans definition)
              (Printf.sprintf "Only %s implement `%s`, so `%s` cannot: %s." implementors
                 (Path.show trait) (Path.show type_) reason);
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

let check_method_names (lookups : Lookups.t) (declaration : Resolve.Names.declaration) spans
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
          let describe_method ~is_own =
            match view with
            | Some view when not is_own ->
                Printf.sprintf "the `%s` of its view `%s`" method_.method_name (Types.show view)
            | _ -> Printf.sprintf "a `%s` of its own" method_.method_name
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
          let make_clash message =
            Some
              (make_diagnostic declaration.key Method_name_clash (locate_header spans definition)
                 message)
          in
          let is_own_version = List.exists is_same_version own in
          if is_own_version || List.exists is_same_version of_view then
            make_clash
              (Printf.sprintf "`%s` has %s, which takes %s, so it cannot also get one from `%s`."
                 (Types.show impl.for_type)
                 (describe_method ~is_own:is_own_version)
                 (Path.show_receiver method_.method_receiver)
                 (Types.show_trait impl.implements))
          else if own = [] && of_view = [] then None
          else if declaration.key.module_.package <> Path.locate_package path then
            make_clash
              (Printf.sprintf
                 "`%s` has %s, so only an `impl` in its own package can give it another."
                 (Types.show impl.for_type)
                 (describe_method ~is_own:(own <> [])))
          else if not written then
            make_clash
              (Printf.sprintf
                 "`%s` has %s, so this `impl` can give it another only by writing it, and `%s` is \
                  left to the body `%s` provides."
                 (Types.show impl.for_type)
                 (describe_method ~is_own:(own <> []))
                 method_.method_name
                 (Types.show_trait impl.implements))
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

let not_strictly_positive_message =
  "A function stored in such a value could be called on the value and call itself through it, so a \
   function without `RunForever` might run forever. Add `RunForever` to the function type's \
   `uses`, or pass the function the fields that it needs instead of the whole value."

let read_written_variant (variants : Syntax.variant list) (variant : Types.variant) =
  match
    List.find_opt
      (fun (written : Syntax.variant) -> written.name.text = variant.variant_name)
      variants
  with
  | Some written -> written
  | None -> raise_bug "the variant `%s` is not in its type's definition" variant.variant_name

let locate_field (spans : Source.Definition_span.t array) (body : Syntax.type_body)
    ((variant : Types.variant option), (field : Types.field)) =
  let raise_missing () =
    raise_bug "the field `%s` is not in its type's definition" field.field_name
  in
  let locate_among (fields : Syntax.field list) =
    match
      List.find_map
        (fun (written : Syntax.field) ->
          match written.kind with
          | Field_declaration { name; _ } when name.text = field.field_name ->
              Some spans.(written.id)
          | _ -> None)
        fields
    with
    | Some span -> span
    | None -> raise_missing ()
  in
  match (body, variant) with
  | Fields fields, None -> locate_among fields
  | Variants variants, Some variant -> (
      match (read_written_variant variants variant).fields with
      | Some fields -> locate_among fields
      | None -> raise_missing ())
  | _ -> raise_missing ()

let check_recursion lookups ~list_contained (declaration : Resolve.Names.declaration) spans
    (definition : Syntax.definition) =
  match definition.kind with
  | Type_definition _ when grows lookups declaration.key.path ->
      [
        make_diagnostic declaration.key Growing_type (locate_header spans definition)
          "This type contains itself with different type arguments, so it has no fixed set of \
           instances, and generic code is compiled once for each set of arguments.";
      ]
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
                let span = spans.((read_written_variant variants variant).name.id) in
                make_diagnostic key Needs_indirect span
                  ~fixes:
                    [
                      Diagnostic.fix "Declare the variant `indirect`."
                        [
                          Diagnostic.insert
                            (Source.Definition_span.make_zero_width span.start)
                            "indirect ";
                        ];
                    ]
                  "This type contains itself in place, so it would be infinitely large. Declare \
                   the variant `indirect` to keep its fields on the heap."
            | Fields _, None ->
                make_diagnostic key Needs_indirect (locate_header spans definition)
                  "This record contains itself in place, so it would be infinitely large. A record \
                   has no variant to declare `indirect`; use a sum type with an `indirect` \
                   variant, or a collection."
            | _ ->
                raise_bug
                  "the interface of `%s` and its definition disagree on whether it is a sum type"
                  name.text)
          (find_first In_place)
      in
      let function_input =
        Option.map
          (fun field ->
            make_diagnostic key Not_strictly_positive (locate_field spans body field)
              (Printf.sprintf
                 "Through this field, `%s` contains a function type that has a `time` clause and \
                  whose input contains `%s`. %s"
                 name.text name.text not_strictly_positive_message))
          (find_first Function_input)
      in
      Option.to_list in_place @ Option.to_list function_input
  | _ -> []

let check_associated_types (lookups : Lookups.t) ~list_contained
    (declaration : Resolve.Names.declaration) spans (definition : Syntax.definition)
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
            | Associated_definition (written, _) when written.text = name -> Some spans.(member.id)
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
      let span =
        match find_written name with
        | Some span -> span
        | None -> raise_bug "the associated type `%s` is not in its impl's definition" name
      in
      List.filter_map
        (fun (recursive, (occurrence : Interface.Properties.occurrence)) ->
          match occurrence with
          | In_place ->
              Some
                (make_diagnostic key Needs_indirect span
                   (Printf.sprintf
                      "With this definition of `%s`, `%s` contains itself in place, so it would be \
                       infinitely large. Define `%s` as a type that holds it in a collection or in \
                       an `indirect` variant."
                      name (Types.show recursive) name))
          | Function_input ->
              Some
                (make_diagnostic key Not_strictly_positive span
                   (Printf.sprintf
                      "With this definition of `%s`, `%s` contains a function type that has a \
                       `time` clause and whose input contains `%s`. %s"
                      name (Types.show recursive) (Types.show recursive)
                      not_strictly_positive_message))
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
  let definition, spans = read_definition lookups declaration in
  [
    make_diagnostic declaration.key Instantiation_cycle (locate_header spans definition)
      "This generic code instantiates itself with type arguments that grow each time around, so it \
       would be compiled without end.";
  ]

let check_test (lookups : Lookups.t) (declaration : Resolve.Names.declaration) =
  match declaration.key.path with
  | Test { name; _ } -> (
      match lookups.list_tests declaration.key.module_.package name with
      | first :: _ when not (Path.equal first.path declaration.key.path) ->
          let definition, spans = read_definition lookups declaration in
          [
            make_diagnostic declaration.key Duplicate_test spans.(definition.id)
              (Printf.sprintf "Another test of this package is named %S." name);
          ]
      | _ -> [])
  | _ -> []

let check_overlaps (lookups : Lookups.t) (declaration : Resolve.Names.declaration) spans definition
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
              (make_diagnostic declaration.key Overlapping_impls (locate_header spans definition)
                 (Printf.sprintf
                    "This `impl` overlaps another `impl` of `%s` for `%s`: a type has at most one \
                     `impl` of a trait for each set of its arguments."
                    (Types.show_trait other.implements)
                    (Types.show other.for_type)))
          else None)
        (earlier @ dependencies)
  | _ -> []

let check_impl (lookups : Lookups.t) ~list_contained (declaration : Resolve.Names.declaration) =
  match
    ( Interface.Definition.find_impl_interface lookups.interface declaration.key.path,
      read_definition lookups declaration )
  with
  | Some impl, (definition, spans) ->
      Option.to_list (check_location declaration spans definition impl)
      @ check_method_names lookups declaration spans definition impl
      @ check_overlaps lookups declaration spans definition impl
      @ check_associated_types lookups ~list_contained declaration spans definition impl
  | _ -> []

let check_type lookups ~list_contained (declaration : Resolve.Names.declaration) =
  let definition, spans = read_definition lookups declaration in
  check_recursion lookups ~list_contained declaration spans definition

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

let locate_name (spans : Source.Definition_span.t array) (definition : Syntax.definition) =
  match definition.kind with
  | Function { signature; _ } | Method_declaration signature ->
      spans.((Resolve.Names.extract_signature_name signature).id)
  | Constant { name = Plain_name name | Member_name (_, name); _ }
  | Definition_error { name = Some (Plain_name name | Member_name (_, name)); _ } ->
      spans.(name.id)
  | _ -> raise_bug "an unused definition that is neither a function nor a constant"

let report_unused (lookups : Lookups.t) (declaration : Resolve.Names.declaration) ~is_named =
  let (code : Diagnostic.Code.usage), noun =
    match declaration.kind with
    | Constant | Member_constant -> (Unused_constant, "constant")
    | _ -> (Unused_function, "function")
  in
  let visibility, (severity : Diagnostic.severity) =
    match declaration.visibility with
    | Internal -> ("internal", Error)
    | Private -> ("private", Warning)
    | Public | Public_opaque -> raise_bug "an unused definition that is public"
  in
  let message =
    if is_named then
      Printf.sprintf "Only unused definitions use the %s %s `%s`. Delete it with them." visibility
        noun (Path.show declaration.key.path)
    else
      Printf.sprintf "Nothing in `%s` uses the %s %s `%s`. Delete it."
        (Path.show_package declaration.key.module_.package)
        visibility noun (Path.show declaration.key.path)
  in
  let definition, spans = read_definition lookups declaration in
  {
    key = declaration.key;
    diagnostic = Diagnostic.make ~severity ~code:(Usage code) (locate_name spans definition) message;
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

let describe_unused_dependency ~package dependency =
  Printf.sprintf "Nothing in `%s` uses `%s`. Delete its entry." (Path.show_package package)
    (Path.show_package dependency)

type outcome = Placed of placed list | Dependency_used of bool

let check_definition (lookups : Lookups.t) key check_declaration =
  let names = lookups.interface.names in
  match check_declaration (names.read_declaration key) with
  | placed -> Placed placed
  | exception Interface.Properties.Recursion_limit message ->
      Placed
        [
          {
            key;
            diagnostic =
              Diagnostic.make ~code:(Types Recursion_limit)
                (Resolve.Names.locate_definition names key)
                message;
          };
        ]

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
