module Lookups = Lookups
open Syntax
module Names = Resolve.Names
module Properties = Interface.Properties

type placed = { key : Names.key; diagnostic : Diagnostic.in_definition }

let make_diagnostic ?(fixes = []) code (span : Source.Definition_span.t) message =
  Diagnostic.make ~fixes ~code:(Package code) span message

let place_diagnostic (key : Names.key) code (span : Source.Definition_span.t) message =
  { key; diagnostic = make_diagnostic code span message }

let header_span (definition : definition) =
  match definition.kind with
  | Impl { trait_; _ } -> trait_.span
  | Type_definition { name; _ } -> name.span
  | _ -> definition.span

let outer_packages (impl : Types.impl_interface) =
  Path.package impl.implements.trait
  :: (match impl.for_type with Types.Named { path; _ } -> [ Path.package path ] | _ -> [])
  @ List.filter_map
      (function Types.Type (Types.Named { path; _ }) -> Some (Path.package path) | _ -> None)
      impl.implements.trait_arguments

let check_location (declaration : Names.declaration) (definition : definition)
    (impl : Types.impl_interface) =
  let package = declaration.module_.package in
  if List.mem package (outer_packages impl) then None
  else
    Some
      (make_diagnostic Impl_location (header_span definition)
         (Printf.sprintf
            "This `impl` must be in the package of `%s`, of `%s`, or of a type its trait's \
             arguments name, so that only one place can hold it."
            (Types.show_trait impl.implements)
            (Types.show impl.for_type)))

let check_sealed (lookups : Lookups.t) (declaration : Names.declaration) =
  let package = declaration.module_.package in
  match
    ( List.find_opt
        (fun (_, impl) -> Path.equal impl declaration.path)
        (lookups.interface.names.impls package),
      lookups.interface.names.definition (Names.key_of declaration) )
  with
  | Some ((trait, type_), _), Some definition -> (
      let implementors =
        if Well_known.is Signed_integer trait then Some Intrinsic.[ Int8; Int16; Int32; Int64 ]
        else if Well_known.is Unsigned_integer trait then
          Some Intrinsic.[ UInt8; UInt16; UInt32; UInt64 ]
        else if Well_known.is Fixed_width_integer trait then
          Some
            (List.filter
               (fun builtin -> Types.is_integer_type (Types.builtin builtin))
               Intrinsic.builtins)
        else None
      in
      match (implementors, Intrinsic.builtin_of_path type_) with
      | Some builtins, Some builtin when List.mem builtin builtins -> []
      | Some _, _ ->
          [
            make_diagnostic Sealed_trait_impl (header_span definition)
              (Printf.sprintf
                 "Only the built-in integer types implement `%s`, so `%s` cannot: generic code \
                  over the trait is proven for each of them."
                 (Path.show trait) (Path.show type_));
          ]
      | None, _ -> [])
  | _ -> []

let overlap (first : Types.impl_interface) (second : Types.impl_interface) =
  let variables =
    List.map
      (fun (generic : Types.generic) -> generic.generic)
      (first.impl_generics @ second.impl_generics)
  in
  let bindings = Hashtbl.create 8 in
  let rec resolve (type_ : Types.ty) =
    match type_ with
    | Types.Parameter parameter when List.mem parameter variables -> (
        match Hashtbl.find_opt bindings parameter with Some bound -> resolve bound | None -> type_)
    | _ -> type_
  in
  let occurs parameter =
    Types.exists ~resolve (function Types.Parameter other -> other = parameter | _ -> false)
  in
  let bind parameter other =
    if other = Types.Parameter parameter then true
    else if occurs parameter other then false
    else begin
      Hashtbl.replace bindings parameter other;
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

let check_method_names (lookups : Lookups.t) (declaration : Names.declaration)
    (definition : definition) (impl : Types.impl_interface) =
  match
    (impl.for_type, Interface.Definition.trait_interface lookups.interface impl.implements.trait)
  with
  | Types.Named { path; _ }, Some trait when not trait.is_capability ->
      List.filter_map
        (fun (method_ : Types.trait_method) ->
          let own = lookups.interface.names.members path method_.method_name in
          let same_version (key : Names.key) =
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
            Some (make_diagnostic Method_name_clash (header_span definition) message)
          in
          if own = [] then None
          else if List.exists same_version own then
            clash
              (Printf.sprintf
                 "`%s` has a `%s` of its own that takes %s, so it cannot also get one from `%s`."
                 (Types.show impl.for_type) method_.method_name
                 (Path.show_receiver method_.method_receiver)
                 (Types.show_trait impl.implements))
          else if declaration.module_.package <> Path.package path then
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

let type_fields (lookups : Lookups.t) path =
  match Interface.Definition.type_interface lookups.interface path with
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

let type_arguments arguments =
  List.filter_map (function Types.Type type_ -> Some type_ | _ -> None) arguments

let contained_types (lookups : Lookups.t) path =
  let bounds =
    match Interface.Definition.type_interface lookups.interface path with
    | Some interface -> Types.bounds_of interface.type_generics
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
                  Properties.through (if indirect then Indirect else In_place) occurrence )
          | _ -> None)
        (Interface.Impls.contents lookups.interface ~bounds field.field_type).contained)
    (snd (type_fields lookups path))

let memoized compute =
  let table = Hashtbl.create 64 in
  fun path ->
    match Hashtbl.find_opt table path with
    | Some value -> value
    | None ->
        let value = compute path in
        Hashtbl.replace table path value;
        value

let self_occurrences ~contained (start : Path.t) =
  let visited = Hashtbl.create 16 in
  let rec from path occurrence =
    if Path.equal path start then [ occurrence ]
    else if Path.package path <> Path.package start || Hashtbl.mem visited (path, occurrence) then
      []
    else begin
      Hashtbl.replace visited (path, occurrence) ();
      List.concat_map
        (fun (_, target, step) -> from target (Properties.through occurrence step))
        (contained path)
    end
  in
  List.concat_map
    (fun (field, target, occurrence) ->
      List.map (fun path -> (field, path)) (from target occurrence))
    (contained start)

let grows lookups (start : Path.t) =
  let edges (path, index) =
    let parameters, fields = type_fields lookups path in
    match List.nth_opt parameters index with
    | None -> []
    | Some parameter ->
        let mentions =
          Types.exists (function Types.Parameter other -> other = parameter | _ -> false)
        in
        let rec targets (type_ : Types.ty) =
          match type_ with
          | Types.Named { path = target; arguments } ->
              let arguments = type_arguments arguments in
              List.concat
                (List.mapi
                   (fun position argument ->
                     if mentions argument then
                       [ ((target, position), argument <> Types.Parameter parameter) ]
                     else [])
                   arguments)
              @ List.concat_map targets arguments
          | Types.Function { inputs; output; _ } ->
              List.concat_map (fun (_, type_) -> targets type_) inputs
              @ targets (Types.result_type output)
          | _ -> []
        in
        List.concat_map (fun (_, (field : Types.field)) -> targets field.field_type) fields
  in
  let visited = Hashtbl.create 16 in
  let rec walk ((path, _) as node) grown =
    if Path.equal path start && grown then true
    else if Hashtbl.mem visited (node, grown) then false
    else begin
      Hashtbl.replace visited (node, grown) ();
      List.exists (fun (target, growing) -> walk target (grown || growing)) (edges node)
    end
  in
  let parameters, _ = type_fields lookups start in
  List.exists
    (fun index -> List.exists (fun (target, growing) -> walk target growing) (edges (start, index)))
    (List.init (List.length parameters) Fun.id)

let not_strictly_positive_message =
  "A function stored in such a value could be called on the value and call itself through it, so a \
   function with a `time` clause might not terminate. Remove the `time` clause from the function \
   type, or pass the function the fields that it needs instead of the whole value."

let field_span (body : type_body) ((variant : Types.variant option), (field : Types.field)) =
  let among (fields : Syntax.field list) =
    List.find_map
      (fun (written : Syntax.field) ->
        match written.kind with
        | Field_declaration { name; _ } when name.text = field.field_name -> Some written.span
        | _ -> None)
      fields
  in
  match (body, variant) with
  | Fields fields, None -> among fields
  | Variants variants, Some variant ->
      Option.bind
        (List.find_opt
           (fun (written : Syntax.variant) -> written.name.text = variant.variant_name)
           variants)
        (fun written -> Option.bind written.fields among)
  | _ -> None

let check_recursion lookups ~contained (declaration : Names.declaration) (definition : definition) =
  match definition.kind with
  | Type_definition _ when grows lookups declaration.path ->
      [
        make_diagnostic Growing_type (header_span definition)
          "This type contains itself with different type arguments, so it has no fixed set of \
           instances, and generic code is compiled once for each set of arguments.";
      ]
  | Type_definition { name; body; _ } ->
      let occurrences = self_occurrences ~contained declaration.path in
      let first (wanted : Properties.occurrence) =
        List.find_map
          (fun (field, occurrence) -> if occurrence = wanted then Some field else None)
          occurrences
      in
      let in_place =
        Option.bind (first In_place) (fun (variant, _) ->
            let variant_span =
              match (body, variant) with
              | Variants variants, Some (variant : Types.variant) ->
                  Option.map
                    (fun (written : variant) -> written.name.span)
                    (List.find_opt
                       (fun (written : variant) -> written.name.text = variant.variant_name)
                       variants)
              | _ -> None
            in
            match variant_span with
            | Some span ->
                Some
                  (make_diagnostic Needs_indirect span
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
                      the variant `indirect` to keep its fields on the heap.")
            | None ->
                Some
                  (make_diagnostic Needs_indirect (header_span definition)
                     "This record contains itself in place, so it would be infinitely large. A \
                      record has no variant to declare `indirect`; use a sum type with an \
                      `indirect` variant, or a collection."))
      in
      let function_input =
        Option.map
          (fun field ->
            make_diagnostic Not_strictly_positive
              (Option.value ~default:(header_span definition) (field_span body field))
              (Printf.sprintf
                 "Through this field, `%s` contains a function type that has a `time` clause and \
                  whose input contains `%s`. %s"
                 name.text name.text not_strictly_positive_message))
          (first Function_input)
      in
      Option.to_list in_place @ Option.to_list function_input
  | _ -> []

let check_associated_types (lookups : Lookups.t) ~contained (declaration : Names.declaration)
    (definition : definition) (impl : Types.impl_interface) =
  let bounds = Types.bounds_of impl.impl_generics in
  let written name =
    match definition.kind with
    | Impl { members; _ } ->
        List.find_map
          (fun (member : impl_member node) ->
            match member.kind with
            | Associated_definition (written, _) when written.text = name -> Some member.span
            | _ -> None)
          members
    | _ -> None
  in
  let reported_at_definition (recursion : Properties.recursion) =
    match recursion.recursive with
    | Types.Named { path; _ } ->
        List.exists
          (fun (_, occurrence) -> occurrence = recursion.occurrence)
          (self_occurrences ~contained path)
    | _ -> false
  in
  List.concat_map
    (fun (name, type_) ->
      let span = Option.value ~default:(header_span definition) (written name) in
      List.filter_map
        (fun (recursive, (occurrence : Properties.occurrence)) ->
          match occurrence with
          | In_place ->
              Some
                (make_diagnostic Needs_indirect span
                   (Printf.sprintf
                      "With this definition of `%s`, `%s` contains itself in place, so it would be \
                       infinitely large. Define `%s` as a type that holds it in a collection or in \
                       an `indirect` variant."
                      name (Types.show recursive) name))
          | Function_input ->
              Some
                (make_diagnostic Not_strictly_positive span
                   (Printf.sprintf
                      "With this definition of `%s`, `%s` contains a function type that has a \
                       `time` clause and whose input contains `%s`. %s"
                      name (Types.show recursive) (Types.show recursive)
                      not_strictly_positive_message))
          | Indirect -> None)
        (List.sort_uniq compare
           (List.filter_map
              (fun (recursion : Properties.recursion) ->
                if
                  List.exists (Path.equal declaration.path) recursion.defining
                  && not (reported_at_definition recursion)
                then Some (recursion.recursive, recursion.occurrence)
                else None)
              (Interface.Impls.contents lookups.interface ~bounds type_).recursions)))
    impl.implements.associated

let instantiation_edges (lookups : Lookups.t) (key : Names.key) =
  match lookups.core key with
  | None -> []
  | Some form ->
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
      Core_walk.definition
        (Core_walk.callees (function
          | Function { path; type_arguments }
            when Path.package path = key.module_.package && type_arguments <> [] ->
              edges := (path, List.exists grows type_arguments) :: !edges
          | _ -> ()))
        form.definition;
      List.rev !edges

let check_instantiation (lookups : Lookups.t) (package : Path.package) =
  let generic =
    List.filter
      (fun (declaration : Names.declaration) ->
        declaration.generic && declaration.ordinal = 0
        && (declaration.kind = Function || declaration.kind = Method))
      (lookups.interface.names.package_declarations package)
  in
  let edges =
    List.map
      (fun (declaration : Names.declaration) ->
        (declaration, instantiation_edges lookups (Names.key_of declaration)))
      generic
  in
  let reaches from target =
    let rec reaches_from seen path =
      if Path.equal path target then true
      else if List.exists (Path.equal path) seen then false
      else
        match
          List.find_opt
            (fun ((declaration : Names.declaration), _) -> Path.equal declaration.path path)
            edges
        with
        | Some (_, outgoing) ->
            List.exists (fun (next, _) -> reaches_from (path :: seen) next) outgoing
        | None -> false
    in
    reaches_from [] from
  in
  List.filter_map
    (fun ((declaration : Names.declaration), outgoing) ->
      if List.exists (fun (callee, grows) -> grows && reaches callee declaration.path) outgoing then
        match lookups.interface.names.definition (Names.key_of declaration) with
        | Some definition ->
            Some
              (place_diagnostic (Names.key_of declaration) Instantiation_cycle
                 (header_span definition)
                 "This generic code instantiates itself with type arguments that grow each time \
                  around, so it would be compiled without end.")
        | None -> None
      else None)
    edges

let check_tests (lookups : Lookups.t) (package : Path.package) =
  let tests =
    List.filter
      (fun (declaration : Names.declaration) -> declaration.kind = Test && declaration.ordinal = 0)
      (lookups.interface.names.package_declarations package)
  in
  snd
    (List.fold_left
       (fun (seen, diagnostics) (declaration : Names.declaration) ->
         let name = match declaration.path with Test { name; _ } -> name | _ -> "" in
         if List.mem name seen then
           match lookups.interface.names.definition (Names.key_of declaration) with
           | Some definition ->
               ( seen,
                 diagnostics
                 @ [
                     place_diagnostic (Names.key_of declaration) Duplicate_test definition.span
                       (Printf.sprintf "Another test of this package is named %S." name);
                   ] )
           | None -> (seen, diagnostics)
         else (name :: seen, diagnostics))
       ([], []) tests)

let visible_packages (lookups : Lookups.t) package =
  let dependency_names = lookups.interface.names.dependency_names in
  let rec packages seen = function
    | [] -> seen
    | name :: rest when List.mem name seen -> packages seen rest
    | name :: rest -> packages (name :: seen) (dependency_names name @ rest)
  in
  let standard = if package = Path.standard_package then [] else [ Path.standard_package ] in
  List.filter (fun name -> name <> package) (packages [] (standard @ dependency_names package))

let check_overlaps (lookups : Lookups.t) (declaration : Names.declaration) definition
    (impl : Types.impl_interface) =
  let package = declaration.module_.package in
  match Interface.Impls.head impl.for_type with
  | Some type_ when List.mem package (outer_packages impl) ->
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
          (fun (other : Types.impl_interface) -> List.mem package (outer_packages other))
          (List.filter_map
             (Interface.Impls.impl_interface lookups.interface)
             (before (lookups.interface.names.impls package)))
      in
      let dependencies =
        List.concat_map
          (fun name ->
            List.filter_map
              (Interface.Impls.impl_interface lookups.interface)
              (Interface.Impls.impls_in lookups.interface ~trait ~type_ name))
          (visible_packages lookups package)
      in
      List.filter_map
        (fun (other : Types.impl_interface) ->
          if overlap impl other then
            Some
              (make_diagnostic Overlapping_impls (header_span definition)
                 (Printf.sprintf
                    "This `impl` overlaps another `impl` of `%s` for `%s`: a type has at most one \
                     `impl` of a trait for each set of its arguments."
                    (Types.show_trait other.implements)
                    (Types.show other.for_type)))
          else None)
        (earlier @ dependencies)
  | _ -> []

let check_impl lookups ~contained (declaration : Names.declaration) =
  match
    ( Interface.Impls.impl_interface lookups.Lookups.interface declaration.path,
      lookups.interface.names.definition (Names.key_of declaration) )
  with
  | Some impl, Some definition ->
      Option.to_list (check_location declaration definition impl)
      @ check_method_names lookups declaration definition impl
      @ check_overlaps lookups declaration definition impl
      @ check_associated_types lookups ~contained declaration definition impl
  | _ -> []

let check_type lookups ~contained (declaration : Names.declaration) =
  match lookups.Lookups.interface.names.definition (Names.key_of declaration) with
  | Some definition -> check_recursion lookups ~contained declaration definition
  | None -> []

type check =
  | Sealed of Names.key
  | Impl of Names.key
  | Type of Names.key
  | Instantiations
  | Tests
  | Grants
  | Dependencies
  | Code_packages

let list_declaration_checks (declaration : Names.declaration) =
  if declaration.ordinal <> 0 then []
  else
    match declaration.kind with
    | Impl -> [ Sealed (Names.key_of declaration); Impl (Names.key_of declaration) ]
    | Type -> [ Type (Names.key_of declaration) ]
    | _ -> []

let package_wide_checks = [ Instantiations; Tests; Grants; Dependencies; Code_packages ]

let used_packages (resolved : Resolve.resolved) ~evidence_packages (form : Core.t) =
  let named =
    List.filter_map
      (function
        | Some (Resolve.Definition (_, path) | Variant (path, _)) -> Some (Path.package path)
        | Some (Module module_) -> Some module_.package
        | _ -> None)
      (Array.to_list resolved.names)
  in
  let called = ref evidence_packages in
  Core_walk.definition
    (Core_walk.callees (function
      | Trait_method { trait; evidence; _ } ->
          called :=
            Path.package trait.trait
            :: (match evidence with Impl { impl; _ } -> [ Path.package impl ] | _ -> [])
            @ !called
      | _ -> ()))
    form.definition;
  List.sort_uniq compare (named @ !called)

type manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
  | Unused of Path.package

let manifest_sentence ~package = function
  | Not_a_capability { dependency; name } ->
      Printf.sprintf
        "`%s`, in the entry for `%s`, names no capability. A grant names a capability of the \
         prelude by its name, such as `Clock`, and any other by its full path."
        name (Path.show_package dependency)
  | Unused dependency ->
      Printf.sprintf "Nothing in `%s` uses `%s`. Delete its entry." (Path.show_package package)
        (Path.show_package dependency)

let grant_problems (lookups : Lookups.t) package =
  List.concat_map
    (fun dependency ->
      match lookups.interface.granted package dependency with
      | Some grant -> List.map (fun name -> Not_a_capability { dependency; name }) grant.unknown
      | None -> [])
    (lookups.interface.names.dependency_names package)

let used_by_declarations (lookups : Lookups.t) package =
  List.map
    (fun (declaration : Names.declaration) ->
      (declaration, lookups.used_packages (Names.key_of declaration)))
    (lookups.interface.names.package_declarations package)

let unused_dependencies (lookups : Lookups.t) package =
  let used = List.concat_map snd (used_by_declarations lookups package) in
  List.filter_map
    (fun dependency -> if List.mem dependency used then None else Some (Unused dependency))
    (lookups.interface.names.dependency_names package)

let code_packages (lookups : Lookups.t) package =
  List.sort_uniq compare
    (List.concat_map
       (fun ((declaration : Names.declaration), packages) ->
         match declaration.path with Test _ -> [] | _ -> packages)
       (used_by_declarations lookups package))

type outcome =
  | Declared of Diagnostic.in_definition list
  | Placed of placed list
  | Problems of manifest_problem list
  | Packages of Path.package list

let run (lookups : Lookups.t) package check =
  let declared key =
    match lookups.interface.names.declaration key with
    | Some declaration -> declaration
    | None -> Compiler_bug.bug ~stage:"Package_checks" "%s is not declared" (Names.show_key key)
  in
  let contained = memoized (contained_types lookups) in
  match check with
  | Sealed key -> Declared (check_sealed lookups (declared key))
  | Impl key -> Declared (check_impl lookups ~contained (declared key))
  | Type key -> Declared (check_type lookups ~contained (declared key))
  | Instantiations -> Placed (check_instantiation lookups package)
  | Tests -> Placed (check_tests lookups package)
  | Grants -> Problems (grant_problems lookups package)
  | Dependencies -> Problems (unused_dependencies lookups package)
  | Code_packages -> Packages (code_packages lookups package)
