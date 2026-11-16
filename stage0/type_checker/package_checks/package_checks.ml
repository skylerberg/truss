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

module Field_default_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.t * string option * string
end))

let raise_bug format = Compiler_bug.raise_bug ~stage:"Package_checks" format

type placed = { key : Resolve.Names.key; diagnostic : Diagnostic.in_definition }

let make_diagnostic (key : Resolve.Names.key) ?(fixes = []) code (span : Source.Definition_span.t)
    message =
  { key; diagnostic = Diagnostic.make ~fixes ~code:(Package code) span message }

let read_definition (lookups : Lookups.t) (declaration : Resolve.Names.declaration) =
  let key = Resolve.Names.make_key declaration in
  (lookups.interface.names.definition key, lookups.interface.names.spans key)

let locate_header (spans : Source.Definition_span.t array) (definition : Syntax.definition) =
  match definition.kind with
  | Impl { trait_; _ } -> spans.(trait_.id)
  | Type_definition { name; _ } -> spans.(name.id)
  | _ -> spans.(definition.id)

let list_outer_packages (impl : Types.impl_interface) =
  Path.locate_package impl.implements.trait
  :: (match impl.for_type with Types.Named { path; _ } -> [ Path.locate_package path ] | _ -> [])
  @ List.filter_map
      (function
        | Types.Type (Types.Named { path; _ }) -> Some (Path.locate_package path) | _ -> None)
      impl.implements.trait_arguments

let check_location (declaration : Resolve.Names.declaration) spans (definition : Syntax.definition)
    (impl : Types.impl_interface) =
  let key = Resolve.Names.make_key declaration in
  let package = declaration.module_.package in
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
  let package = declaration.module_.package in
  match
    ( List.find_opt
        (fun (_, impl) -> Path.equal impl declaration.path)
        (lookups.interface.names.impls package),
      read_definition lookups declaration )
  with
  | Some ((trait, type_), _), (definition, spans) -> (
      match (Types.find_integer_implementors trait, Intrinsic.builtin_of_path type_) with
      | Some builtins, Some builtin when List.mem builtin builtins -> []
      | Some _, _ ->
          [
            make_diagnostic
              (Resolve.Names.make_key declaration)
              Sealed_trait_impl (locate_header spans definition)
              (Printf.sprintf
                 "Only the built-in integer types implement `%s`, so `%s` cannot: generic code \
                  over the trait is proven for each of them."
                 (Path.show trait) (Path.show type_));
          ]
      | None, _ -> [])
  | _ -> []

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
        && List.for_all2 argument left.arguments right.arguments
    | left, right -> Types.equal left right
  and argument left right =
    match (left, right) with
    | Types.Type left, Types.Type right -> unify left right
    | Types.Value (Types.Value_parameter parameter), _
    | _, Types.Value (Types.Value_parameter parameter) ->
        List.mem parameter variables || left = right
    | left, right -> left = right
  in
  unify first.for_type second.for_type
  && List.length first.implements.trait_arguments = List.length second.implements.trait_arguments
  && List.for_all2 argument first.implements.trait_arguments second.implements.trait_arguments

let check_method_names (lookups : Lookups.t) (declaration : Resolve.Names.declaration) spans
    (definition : Syntax.definition) (impl : Types.impl_interface) =
  match
    ( impl.for_type,
      Interface.Definition.read_trait_interface lookups.interface impl.implements.trait )
  with
  | Types.Named { path; _ }, Some trait when not trait.is_capability ->
      List.filter_map
        (fun (method_ : Types.trait_method) ->
          let own = lookups.interface.names.members path method_.method_name in
          let same_version (key : Resolve.Names.key) =
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
          let clash message =
            Some
              (make_diagnostic
                 (Resolve.Names.make_key declaration)
                 Method_name_clash (locate_header spans definition) message)
          in
          if own = [] then None
          else if List.exists same_version own then
            clash
              (Printf.sprintf
                 "`%s` has a `%s` of its own that takes %s, so it cannot also get one from `%s`."
                 (Types.show impl.for_type) method_.method_name
                 (Path.show_receiver method_.method_receiver)
                 (Types.show_trait impl.implements))
          else if declaration.module_.package <> Path.locate_package path then
            clash
              (Printf.sprintf
                 "`%s` has a `%s` of its own, so only an `impl` in its own package can give it \
                  another."
                 (Types.show impl.for_type) method_.method_name)
          else if not written then
            clash
              (Printf.sprintf
                 "`%s` has a `%s` of its own, so this `impl` can give it another only by writing \
                  it, and `%s` is left to the body `%s` provides."
                 (Types.show impl.for_type) method_.method_name method_.method_name
                 (Types.show_trait impl.implements))
          else None)
        trait.methods
  | _ -> []

let list_type_fields (lookups : Lookups.t) path =
  match Interface.Definition.read_type_interface lookups.interface path with
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
  let bounds =
    match Interface.Definition.read_type_interface lookups.interface path with
    | Some interface -> Types.list_bounds interface.type_generics
    | None -> fun _ -> []
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
        (Interface.Impls.list_contents lookups.interface ~bounds field.field_type).contained)
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

let list_self_occurrences ~contained (start : Path.t) =
  let visited = Occurrence_table.create 16 in
  let rec from path occurrence =
    if Path.equal path start then [ occurrence ]
    else if
      Path.locate_package path <> Path.locate_package start
      || Occurrence_table.mem visited (path, occurrence)
    then []
    else begin
      Occurrence_table.replace visited (path, occurrence) ();
      List.concat_map
        (fun (_, target, step) ->
          from target (Interface.Properties.compose_occurrences occurrence step))
        (contained path)
    end
  in
  List.concat_map
    (fun (field, target, occurrence) ->
      List.map (fun path -> (field, path)) (from target occurrence))
    (contained start)

let grows lookups (start : Path.t) =
  let edges (path, index) =
    let parameters, fields = list_type_fields lookups path in
    match List.nth_opt parameters index with
    | None -> []
    | Some parameter ->
        let mentions =
          Types.exists (function Types.Parameter other -> other = parameter | _ -> false)
        in
        let rec targets (type_ : Types.ty) =
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
              @ List.concat_map targets arguments
          | Types.Function { inputs; output; _ } ->
              List.concat_map (fun (_, type_) -> targets type_) inputs @ targets output
          | _ -> []
        in
        List.concat_map (fun (_, (field : Types.field)) -> targets field.field_type) fields
  in
  let visited = Grown_node_table.create 16 in
  let rec walk ((path, _) as node) grown =
    if Path.equal path start && grown then true
    else if Grown_node_table.mem visited (node, grown) then false
    else begin
      Grown_node_table.replace visited (node, grown) ();
      List.exists (fun (target, growing) -> walk target (grown || growing)) (edges node)
    end
  in
  let parameters, _ = list_type_fields lookups start in
  List.exists
    (fun index -> List.exists (fun (target, growing) -> walk target growing) (edges (start, index)))
    (List.init (List.length parameters) Fun.id)

let not_strictly_positive_message =
  "A function stored in such a value could be called on the value and call itself through it, so a \
   function with a `time` clause might not terminate. Remove the `time` clause from the function \
   type, or pass the function the fields that it needs instead of the whole value."

let find_written_variant (variants : Syntax.variant list) (variant : Types.variant) =
  match
    List.find_opt
      (fun (written : Syntax.variant) -> written.name.text = variant.variant_name)
      variants
  with
  | Some written -> written
  | None -> raise_bug "the variant `%s` is not in its type's definition" variant.variant_name

let locate_field (spans : Source.Definition_span.t array) (body : Syntax.type_body)
    ((variant : Types.variant option), (field : Types.field)) =
  let missing () = raise_bug "the field `%s` is not in its type's definition" field.field_name in
  let among (fields : Syntax.field list) =
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
    | None -> missing ()
  in
  match (body, variant) with
  | Fields fields, None -> among fields
  | Variants variants, Some variant -> (
      match (find_written_variant variants variant).fields with
      | Some fields -> among fields
      | None -> missing ())
  | _ -> missing ()

let check_recursion lookups ~contained (declaration : Resolve.Names.declaration) spans
    (definition : Syntax.definition) =
  match definition.kind with
  | Type_definition _ when grows lookups declaration.path ->
      [
        make_diagnostic
          (Resolve.Names.make_key declaration)
          Growing_type (locate_header spans definition)
          "This type contains itself with different type arguments, so it has no fixed set of \
           instances, and generic code is compiled once for each set of arguments.";
      ]
  | Type_definition { name; body; _ } ->
      let key = Resolve.Names.make_key declaration in
      let occurrences = list_self_occurrences ~contained declaration.path in
      let first (wanted : Interface.Properties.occurrence) =
        List.find_map
          (fun (field, occurrence) -> if occurrence = wanted then Some field else None)
          occurrences
      in
      let in_place =
        Option.map
          (fun ((variant : Types.variant option), _) ->
            match (body, variant) with
            | Variants variants, Some variant ->
                let span = spans.((find_written_variant variants variant).name.id) in
                make_diagnostic key Needs_indirect span
                  ~fixes:
                    [
                      Diagnostic.fix "Declare the variant `indirect`."
                        [
                          Diagnostic.insert
                            (Source.Definition_span.zero_width span.start)
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
          (first In_place)
      in
      let function_input =
        Option.map
          (fun field ->
            make_diagnostic key Not_strictly_positive (locate_field spans body field)
              (Printf.sprintf
                 "Through this field, `%s` contains a function type that has a `time` clause and \
                  whose input contains `%s`. %s"
                 name.text name.text not_strictly_positive_message))
          (first Function_input)
      in
      Option.to_list in_place @ Option.to_list function_input
  | _ -> []

let check_associated_types (lookups : Lookups.t) ~contained
    (declaration : Resolve.Names.declaration) spans (definition : Syntax.definition)
    (impl : Types.impl_interface) =
  let key = Resolve.Names.make_key declaration in
  let bounds = Types.list_bounds impl.impl_generics in
  let written name =
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
  let reported_at_definition (recursion : Interface.Properties.recursion) =
    match recursion.recursive with
    | Types.Named { path; _ } ->
        List.exists
          (fun (_, occurrence) -> occurrence = recursion.occurrence)
          (list_self_occurrences ~contained path)
    | _ -> false
  in
  List.concat_map
    (fun (name, type_) ->
      let span =
        match written name with
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
                  List.exists (Path.equal declaration.path) recursion.defining
                  && not (reported_at_definition recursion)
                then Some (recursion.recursive, recursion.occurrence)
                else None)
              (Interface.Impls.list_contents lookups.interface ~bounds type_).recursions)))
    impl.implements.associated

let list_instantiation_edges (lookups : Lookups.t) (key : Resolve.Names.key) =
  let form = lookups.core key in
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
    (Core_walk.make_callee_visitor (function
      | Function { path; type_arguments }
        when Path.locate_package path = key.module_.package && type_arguments <> [] ->
          edges := (path, List.exists grows type_arguments) :: !edges
      | _ -> ()))
    form.definition;
  List.rev !edges

let check_instantiation (lookups : Lookups.t) (package : Path.package) =
  let generic =
    List.filter
      (fun (declaration : Resolve.Names.declaration) ->
        declaration.generic && declaration.ordinal = 0
        && (declaration.kind = Function || declaration.kind = Method))
      (lookups.interface.names.package_declarations package)
  in
  let edges = Path_table.create 64 in
  List.iter
    (fun (declaration : Resolve.Names.declaration) ->
      Path_table.replace edges declaration.path
        (list_instantiation_edges lookups (Resolve.Names.make_key declaration)))
    generic;
  let outgoing path = Option.value ~default:[] (Path_table.find_opt edges path) in
  let component_index = Path_table.create 64 in
  List.iteri
    (fun index members ->
      List.iter (fun path -> Path_table.replace component_index path index) members)
    (Strongly_connected.find_components
       (module Path)
       ~successors:(fun path -> List.map fst (outgoing path))
       (List.map (fun (declaration : Resolve.Names.declaration) -> declaration.path) generic));
  let grows_on_cycle path (callee, grows) =
    grows && Path_table.find component_index callee = Path_table.find component_index path
  in
  List.filter_map
    (fun (declaration : Resolve.Names.declaration) ->
      if List.exists (grows_on_cycle declaration.path) (outgoing declaration.path) then
        let definition, spans = read_definition lookups declaration in
        Some
          (make_diagnostic
             (Resolve.Names.make_key declaration)
             Instantiation_cycle (locate_header spans definition)
             "This generic code instantiates itself with type arguments that grow each time \
              around, so it would be compiled without end.")
      else None)
    generic

let check_tests (lookups : Lookups.t) (package : Path.package) =
  let tests =
    List.filter
      (fun (declaration : Resolve.Names.declaration) ->
        declaration.kind = Test && declaration.ordinal = 0)
      (lookups.interface.names.package_declarations package)
  in
  snd
    (List.fold_left
       (fun (seen, diagnostics) (declaration : Resolve.Names.declaration) ->
         let name = match declaration.path with Test { name; _ } -> name | _ -> "" in
         if List.mem name seen then
           let definition, spans = read_definition lookups declaration in
           ( seen,
             diagnostics
             @ [
                 make_diagnostic
                   (Resolve.Names.make_key declaration)
                   Duplicate_test spans.(definition.id)
                   (Printf.sprintf "Another test of this package is named %S." name);
               ] )
         else (name :: seen, diagnostics))
       ([], []) tests)

let check_overlaps (lookups : Lookups.t) (declaration : Resolve.Names.declaration) spans definition
    (impl : Types.impl_interface) =
  let package = declaration.module_.package in
  match Interface.Impls.find_head impl.for_type with
  | Some type_ when List.mem package (list_outer_packages impl) ->
      let trait = impl.implements.trait in
      let rec before = function
        | [] -> []
        | ((indexed_trait, indexed_type), path) :: rest ->
            if Path.equal path declaration.path then []
            else if Path.equal indexed_trait trait && Path.equal indexed_type type_ then
              path :: before rest
            else before rest
      in
      let earlier =
        List.filter
          (fun (other : Types.impl_interface) -> List.mem package (list_outer_packages other))
          (List.filter_map
             (Interface.Definition.read_impl_interface lookups.interface)
             (before (lookups.interface.names.impls package)))
      in
      let dependencies =
        List.concat_map
          (fun name ->
            List.filter_map
              (Interface.Definition.read_impl_interface lookups.interface)
              (Interface.Impls.list_impls_of_trait_for_type lookups.interface ~trait ~type_ name))
          (Resolve.Names.list_transitive_dependencies lookups.interface.names package)
      in
      List.filter_map
        (fun (other : Types.impl_interface) ->
          if impls_overlap impl other then
            Some
              (make_diagnostic
                 (Resolve.Names.make_key declaration)
                 Overlapping_impls (locate_header spans definition)
                 (Printf.sprintf
                    "This `impl` overlaps another `impl` of `%s` for `%s`: a type has at most one \
                     `impl` of a trait for each set of its arguments."
                    (Types.show_trait other.implements)
                    (Types.show other.for_type)))
          else None)
        (earlier @ dependencies)
  | _ -> []

let check_impl (lookups : Lookups.t) ~contained (declaration : Resolve.Names.declaration) =
  match
    ( Interface.Definition.read_impl_interface lookups.interface declaration.path,
      read_definition lookups declaration )
  with
  | Some impl, (definition, spans) ->
      Option.to_list (check_location declaration spans definition impl)
      @ check_method_names lookups declaration spans definition impl
      @ check_overlaps lookups declaration spans definition impl
      @ check_associated_types lookups ~contained declaration spans definition impl
  | _ -> []

let check_type lookups ~contained (declaration : Resolve.Names.declaration) =
  let definition, spans = read_definition lookups declaration in
  check_recursion lookups ~contained declaration spans definition

let read_constant_value (lookups : Lookups.t) path =
  match Option.map lookups.core (lookups.interface.names.key path) with
  | Some { definition = Constant (Some value) } -> Some value
  | _ -> None

let find_field_default (lookups : Lookups.t) (type_ : Types.ty) variant field =
  match type_ with
  | Named { path; _ } -> (
      match Option.map lookups.core (lookups.interface.names.key path) with
      | Some { definition = Type { defaults; _ } } ->
          List.find_map
            (fun (default_variant, default_field, value) ->
              if
                Option.equal String.equal default_variant variant
                && String.equal default_field field
              then Some (path, value)
              else None)
            defaults
      | _ -> None)
  | _ -> None

type named_constant = { origin : Core.origin; constant : Path.t; omitted_field : string option }

let list_named_constants (lookups : Lookups.t) (value : Core.expression) =
  let named = ref [] in
  let entered_defaults = Field_default_table.create 8 in
  let rec visit ~through (value : Core.expression) =
    Core_walk.walk_expression
      {
        Core_walk.ignore_all with
        place =
          (function
          | Constant { path; origin; _ } ->
              let origin, omitted_field =
                match through with
                | Some (origin, field) -> (origin, Some field)
                | None -> (origin, None)
              in
              named := { origin; constant = path; omitted_field } :: !named
          | Local _ | Field _ | Lent _ | Temporary _ -> ());
        expression =
          (fun (node : Core.expression) ->
            match node.kind with
            | Construct { variant; fields } ->
                List.iter
                  (fun (field, operand) ->
                    if Option.is_none operand then
                      match find_field_default lookups node.type_ variant field with
                      | Some (type_path, default) ->
                          let entered = (type_path, variant, field) in
                          if not (Field_default_table.mem entered_defaults entered) then begin
                            Field_default_table.replace entered_defaults entered ();
                            let through =
                              match through with
                              | Some _ -> through
                              | None -> Some (node.origin, field)
                            in
                            visit ~through default
                          end
                      | None -> ())
                  fields
            | _ -> ());
      }
      value
  in
  visit ~through:None value;
  List.sort_uniq compare !named

let describe_constant_cycle ~cyclic (named : named_constant) =
  let is_itself = Path.equal named.constant cyclic in
  let constant = Path.show named.constant and cyclic = Path.show cyclic in
  let consequence = Printf.sprintf "so `%s` would be computed from itself." cyclic in
  match (named.omitted_field, is_itself) with
  | None, true -> Printf.sprintf "This reads `%s` in its own value, %s" constant consequence
  | None, false ->
      Printf.sprintf "This reads `%s`, whose value depends on `%s`, %s" constant cyclic consequence
  | Some field, true ->
      Printf.sprintf "This leaves out the field `%s`, whose default reads `%s`, %s" field constant
        consequence
  | Some field, false ->
      Printf.sprintf
        "This leaves out the field `%s`, whose default reads `%s`. The value of `%s` depends on \
         `%s`, %s"
        field constant constant cyclic consequence

let check_constant (lookups : Lookups.t) (declaration : Resolve.Names.declaration) =
  let path = declaration.path in
  match read_constant_value lookups path with
  | None -> []
  | Some value ->
      let visited = Path_table.create 16 in
      let rec depends_on_constant named =
        Path.equal named path
        || (not (Path_table.mem visited named))
           && begin
             Path_table.replace visited named ();
             match read_constant_value lookups named with
             | Some named_value ->
                 List.exists
                   (fun (further : named_constant) -> depends_on_constant further.constant)
                   (list_named_constants lookups named_value)
             | None -> false
           end
      in
      let key = Resolve.Names.make_key declaration in
      let spans = lookups.interface.names.spans key in
      List.filter_map
        (fun (named : named_constant) ->
          if depends_on_constant named.constant then
            Some
              (make_diagnostic key Constant_cycle spans.(named.origin)
                 (describe_constant_cycle ~cyclic:path named))
          else None)
        (list_named_constants lookups value)

type check =
  | Sealed of Resolve.Names.key
  | Impl of Resolve.Names.key
  | Type of Resolve.Names.key
  | Constant of Resolve.Names.key
  | Instantiations
  | Tests
  | Dependencies

let list_checks (declarations : Resolve.Names.declaration list) =
  List.concat_map
    (fun (declaration : Resolve.Names.declaration) ->
      if declaration.ordinal <> 0 then []
      else
        match declaration.kind with
        | Impl ->
            [
              Sealed (Resolve.Names.make_key declaration); Impl (Resolve.Names.make_key declaration);
            ]
        | Type -> [ Type (Resolve.Names.make_key declaration) ]
        | Constant | Member_constant -> [ Constant (Resolve.Names.make_key declaration) ]
        | _ -> [])
    declarations
  @ [ Instantiations; Tests; Dependencies ]

let describe_unused_dependency ~package dependency =
  Printf.sprintf "Nothing in `%s` uses `%s`. Delete its entry." (Path.show_package package)
    (Path.show_package dependency)

let list_unused_dependencies (lookups : Lookups.t) package =
  let used =
    List.concat_map
      (fun (declaration : Resolve.Names.declaration) ->
        lookups.used_packages (Resolve.Names.make_key declaration))
      (lookups.interface.names.package_declarations package)
  in
  List.filter
    (fun dependency -> not (List.mem dependency used))
    (lookups.interface.names.dependency_names package)

type outcome = Placed of placed list | Unused_dependencies of Path.package list

let run (lookups : Lookups.t) package check =
  let contained = memoize (list_contained_types lookups) in
  match check with
  | Sealed key -> Placed (check_sealed lookups (lookups.interface.names.declaration key))
  | Impl key -> Placed (check_impl lookups ~contained (lookups.interface.names.declaration key))
  | Type key -> Placed (check_type lookups ~contained (lookups.interface.names.declaration key))
  | Constant key -> Placed (check_constant lookups (lookups.interface.names.declaration key))
  | Instantiations -> Placed (check_instantiation lookups package)
  | Tests -> Placed (check_tests lookups package)
  | Dependencies -> Unused_dependencies (list_unused_dependencies lookups package)
