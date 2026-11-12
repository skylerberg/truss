(* The checks that look at more than one definition of a package: where an
   [impl] may live, overlapping [impl]s, a type's method sharing a name
   with a trait's, types that contain themselves in place or in a function
   type's input, instantiation cycles, and tests with one name. Packages
   cannot depend on each other in a cycle, so every cycle these find is
   within one package. *)

open Syntax
module T = Types
module Names = Resolve.Names
module Environment = Interface.Environment
module Properties = Interface.Properties

(* A diagnostic at a place inside a definition, moved to its file. *)
type placed = { module_ : Path.module_; diagnostic : Diagnostic.t }

let diagnostic_at database (key : Names.key) ?(fixes = []) code (span : span) message =
  match Query.demand database Names.base key with
  | Some (module_, base) ->
      Some
        {
          module_;
          diagnostic =
            Diagnostic.map_spans (Span.to_source ~base)
              (Diagnostic.make ~fixes ~code:(Package code) span message);
        }
  | None -> None

let declarations database package = Query.demand database Names.package_declarations package

let dependencies database package =
  List.map
    (fun (dependency : Manifest.dependency) -> dependency.package)
    (Query.demand database Workspace.dependencies package)

let header_span (definition : definition) =
  match definition.kind with
  | Impl { trait_; _ } -> trait_.span
  | Type_definition { name; _ } -> name.span
  | _ -> definition.span

(* Where an [impl] may live *)

let outer_packages (impl : T.impl_interface) =
  Path.package impl.implements.trait
  :: (match impl.for_type with T.Named { path; _ } -> [ Path.package path ] | _ -> [])
  @ List.filter_map
      (function T.Type (T.Named { path; _ }) -> Some (Path.package path) | _ -> None)
      impl.implements.trait_arguments

let check_location database (declaration : Names.declaration) (definition : definition)
    (impl : T.impl_interface) =
  let key = Names.key_of declaration in
  let package = declaration.module_.package in
  if impl.impl_broken || List.mem package (outer_packages impl) then None
  else
    diagnostic_at database key Impl_location (header_span definition)
      (Printf.sprintf
         "This `impl` must be in the package of `%s`, of `%s`, or of a type its trait's arguments \
          name, so that only one place can hold it."
         (T.show_trait impl.implements) (T.show impl.for_type))

(* Sealed traits *)

(* Only the built-in integer types implement the integer traits, each the
   traits of its own signedness. Generic code over one is proven for each
   built-in type, which would be unsound if any other type could implement
   it. *)
let check_sealed database (declaration : Names.declaration) (definition : definition)
    (impl : T.impl_interface) =
  let implementors =
    if Well_known.is Signed_integer impl.implements.trait then
      Some Intrinsic.[ Int8; Int16; Int32; Int64; ISize ]
    else if Well_known.is Unsigned_integer impl.implements.trait then
      Some Intrinsic.[ UInt8; UInt16; UInt32; UInt64; USize ]
    else if Well_known.is Fixed_width_integer impl.implements.trait then
      Some (List.filter (fun builtin -> T.is_integer_type (T.builtin builtin)) Intrinsic.builtins)
    else None
  in
  match (implementors, T.builtin_of impl.for_type) with
  | Some builtins, Some builtin when List.mem builtin builtins -> None
  | Some _, _ ->
      diagnostic_at database (Names.key_of declaration) Sealed_trait_impl (header_span definition)
        (Printf.sprintf
           "Only the built-in integer types implement `%s`, so `%s` cannot: generic code over the \
            trait is proven for each of them."
           (T.show_trait { impl.implements with associated = [] })
           (T.show impl.for_type))
  | None, _ -> None

(* Overlap *)

(* Whether two [impl]s' heads unify, each [impl]'s generic parameters as
   variables of their own. *)
let overlap (first : T.impl_interface) (second : T.impl_interface) =
  let variables =
    List.map
      (fun (generic : T.generic) -> generic.generic)
      (first.impl_generics @ second.impl_generics)
  in
  let bindings = Hashtbl.create 8 in
  let rec resolve (type_ : T.ty) =
    match type_ with
    | T.Parameter parameter when List.mem parameter variables -> (
        match Hashtbl.find_opt bindings parameter with Some bound -> resolve bound | None -> type_)
    | _ -> type_
  in
  (* Binding a variable to a type that holds it would make an infinite
     type, which no head can be. *)
  let occurs parameter =
    T.exists ~resolve (function T.Parameter other -> other = parameter | _ -> false)
  in
  let bind parameter other =
    if other = T.Parameter parameter then true
    else if occurs parameter other then false
    else begin
      Hashtbl.replace bindings parameter other;
      true
    end
  in
  let rec unify left right =
    match (resolve left, resolve right) with
    | T.Parameter parameter, other when List.mem parameter variables -> bind parameter other
    | other, T.Parameter parameter when List.mem parameter variables -> bind parameter other
    | T.Named left, T.Named right ->
        Path.equal left.path right.path
        && List.length left.arguments = List.length right.arguments
        && List.for_all2 argument left.arguments right.arguments
    | left, right -> T.equal left right
  and argument left right =
    match (left, right) with
    | T.Type left, T.Type right -> unify left right
    | T.Value (T.Value_parameter parameter), _ | _, T.Value (T.Value_parameter parameter) ->
        List.mem parameter variables || left = right
    | left, right -> left = right
  in
  unify first.for_type second.for_type
  && List.length first.implements.trait_arguments = List.length second.implements.trait_arguments
  && List.for_all2 argument first.implements.trait_arguments second.implements.trait_arguments

(* Method names *)

(* A method is its name and how it takes [self]. An [impl] in a type's own
   package may write another version of a method the type has: one name,
   taking [self] another way. Nothing else may use a name the type's methods
   have: not an [impl] in another package, and not a method an [impl] leaves
   to its trait's body, since either can arrive in an upgrade that the
   type's author never saw, and would then change which method a call
   means. Neither may a method share a constant's name. *)
let check_method_names database (declaration : Names.declaration) (definition : definition)
    (impl : T.impl_interface) =
  match
    (impl.for_type, Query.demand database Environment.trait_interface impl.implements.trait)
  with
  | T.Named { path; _ }, Some trait when not trait.is_capability ->
      List.filter_map
        (fun (method_ : T.trait_method) ->
          let own = Query.demand database Names.members (path, method_.method_name) in
          let same_version (key : Names.key) =
            match key.path with
            | Method { receiver; _ } -> receiver = method_.method_receiver
            | _ -> true
          in
          let written =
            List.exists
              (fun (name, receiver, (_ : T.signature)) ->
                name = method_.method_name && receiver = method_.method_receiver)
              impl.impl_methods
          in
          let clash message =
            diagnostic_at database (Names.key_of declaration) Method_name_clash
              (header_span definition) message
          in
          if own = [] then None
          else if List.exists same_version own then
            clash
              (Printf.sprintf
                 "`%s` has a `%s` of its own that takes %s, so it cannot also get one from `%s`."
                 (T.show impl.for_type) method_.method_name
                 (Path.show_receiver method_.method_receiver)
                 (T.show_trait impl.implements))
          else if declaration.module_.package <> Path.package path then
            clash
              (Printf.sprintf
                 "`%s` has a `%s` of its own, so only an `impl` in its own package can give it \
                  another."
                 (T.show impl.for_type) method_.method_name)
          else if not written then
            clash
              (Printf.sprintf
                 "`%s` has a `%s` of its own, so this `impl` can give it another only by writing \
                  it, and `%s` is left to the body `%s` provides."
                 (T.show impl.for_type) method_.method_name method_.method_name
                 (T.show_trait impl.implements))
          else None)
        trait.methods
  | _ -> []

(* Recursive types *)

(* A type definition's generic parameters, and its fields, each with the
   variant that it is in. *)
let type_fields database path =
  match Query.demand database Environment.type_interface path with
  | Some interface ->
      let parameters =
        List.map (fun (generic : T.generic) -> generic.generic) interface.type_generics
      in
      let fields =
        match interface.shape with
        | Record fields -> List.map (fun field -> (None, field)) fields
        | Sum variants ->
            List.concat_map
              (fun (variant : T.variant) ->
                List.map
                  (fun field -> (Some variant, field))
                  (Option.value ~default:[] variant.fields))
              variants
        | _ -> []
      in
      (parameters, fields)
  | None -> ([], [])

let type_arguments arguments =
  List.filter_map (function T.Type type_ -> Some type_ | _ -> None) arguments

(* The named types that a type definition's fields contain, each with its
   field and how it occurs in a value of the type. *)
let contained =
  Query.query ~name:"contained_types" ~phase:Phases.interfaces ~show:Path.show (fun database path ->
      let bounds =
        match Query.demand database Environment.type_interface path with
        | Some interface -> T.bounds_of interface.type_generics
        | None -> fun _ -> []
      in
      List.concat_map
        (fun (((variant : T.variant option), (field : T.field)) as written) ->
          let indirect = match variant with Some variant -> variant.indirect | None -> false in
          List.filter_map
            (function
              | T.Named { path; _ }, occurrence ->
                  Some
                    ( written,
                      path,
                      Properties.through (if indirect then Indirect else In_place) occurrence )
              | _ -> None)
            (Interface.Impls.contents database ~bounds field.field_type).contained)
        (snd (type_fields database path)))

(* How a type contains itself through the fields of type definitions: the
   occurrence of the type in itself along each cycle of definitions, with
   the field of the type that the cycle starts at. A cycle is within one
   package. Each type is visited once with each occurrence. *)
let self_occurrences database (start : Path.t) =
  let visited = Hashtbl.create 16 in
  let rec from path occurrence =
    if Path.equal path start then [ occurrence ]
    else if Path.package path <> Path.package start || Hashtbl.mem visited (path, occurrence) then
      []
    else begin
      Hashtbl.replace visited (path, occurrence) ();
      List.concat_map
        (fun (_, target, step) -> from target (Properties.through occurrence step))
        (Query.demand database contained path)
    end
  in
  List.concat_map
    (fun (field, target, occurrence) ->
      List.map (fun path -> (field, path)) (from target occurrence))
    (Query.demand database contained start)

(* Whether a generic type contains itself with growing type arguments,
   through any field at all, so that it has no fixed set of instances. As in
   Go's check, the graph's nodes are the parameters of generic types: a
   parameter goes to each argument position of a type named in a field that
   mentions it, growing when the argument is more than the parameter itself.
   The type grows when a path from its parameters back to them takes a
   growing edge. Each node is visited once with each answer to whether the
   path has grown. *)
let grows database (start : Path.t) =
  let edges (path, index) =
    let parameters, fields = type_fields database path in
    match List.nth_opt parameters index with
    | None -> []
    | Some parameter ->
        let mentions = T.exists (function T.Parameter other -> other = parameter | _ -> false) in
        let rec targets (type_ : T.ty) =
          match type_ with
          | T.Named { path = target; arguments } ->
              let arguments = type_arguments arguments in
              List.concat
                (List.mapi
                   (fun position argument ->
                     if mentions argument then
                       [ ((target, position), argument <> T.Parameter parameter) ]
                     else [])
                   arguments)
              @ List.concat_map targets arguments
          | T.Function { inputs; output; _ } ->
              List.concat_map (fun (_, type_) -> targets type_) inputs
              @ targets (T.result_type output)
          | _ -> []
        in
        List.concat_map (fun (_, (field : T.field)) -> targets field.field_type) fields
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
  let parameters, _ = type_fields database start in
  List.exists
    (fun index -> List.exists (fun (target, growing) -> walk target growing) (edges (start, index)))
    (List.init (List.length parameters) Fun.id)

let not_strictly_positive_message =
  "A function stored in such a value could be called on the value and call itself through it, so a \
   function with a `time` clause might not terminate. Remove the `time` clause from the function \
   type, or pass the function the fields that it needs instead of the whole value."

(* Where a field of a type definition is written. *)
let field_span (body : type_body) ((variant : T.variant option), (field : T.field)) =
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

let check_recursion database (declaration : Names.declaration) (definition : definition) =
  match definition.kind with
  | Type_definition _ when grows database declaration.path ->
      Option.to_list
        (diagnostic_at database (Names.key_of declaration) Growing_type (header_span definition)
           "This type contains itself with different type arguments, so it has no fixed set of \
            instances, and generic code is compiled once for each set of arguments.")
  | Type_definition { name; body; _ } ->
      let key = Names.key_of declaration in
      let occurrences = self_occurrences database declaration.path in
      let first (wanted : Properties.occurrence) =
        List.find_map
          (fun (field, occurrence) -> if occurrence = wanted then Some field else None)
          occurrences
      in
      let in_place =
        Option.bind (first In_place) (fun (variant, _) ->
            let variant_span =
              match (body, variant) with
              | Variants variants, Some (variant : T.variant) ->
                  Option.map
                    (fun (written : variant) -> written.name.span)
                    (List.find_opt
                       (fun (written : variant) -> written.name.text = variant.variant_name)
                       variants)
              | _ -> None
            in
            match variant_span with
            | Some span ->
                diagnostic_at database key Needs_indirect span
                  ~fixes:
                    [
                      Diagnostic.fix "Mark the variant `indirect`."
                        [ Diagnostic.insert (Span.zero_width span.start) "indirect " ];
                    ]
                  "This type contains itself in place, so it would be infinitely large. Mark the \
                   variant `indirect` to keep its fields on the heap."
            | None ->
                diagnostic_at database key Needs_indirect (header_span definition)
                  "This record contains itself in place, so it would be infinitely large. A record \
                   has no variant to mark `indirect`; use a sum type with an `indirect` variant, \
                   or a collection.")
      in
      let function_input =
        Option.bind (first Function_input) (fun field ->
            diagnostic_at database key Not_strictly_positive
              (Option.value ~default:(header_span definition) (field_span body field))
              (Printf.sprintf
                 "Through this field, `%s` contains a function type that has a `time` clause and \
                  whose input contains `%s`. %s"
                 name.text name.text not_strictly_positive_message))
      in
      Option.to_list in_place @ Option.to_list function_input
  | _ -> []

(* An [impl]'s associated type can make a type contain itself though no type
   definition's fields do. With [type Kept[Source: Shown](part:
   Source.Part)], defining [Part] as [Kept[Marker]] in [impl Shown for
   Marker] makes [Kept[Marker]] infinitely large. A type that contains
   itself the same way through its definition's fields is reported there. *)
let check_associated_types database (declaration : Names.declaration) (definition : definition)
    (impl : T.impl_interface) =
  let key = Names.key_of declaration in
  let bounds = T.bounds_of impl.impl_generics in
  let written name =
    match definition.kind with
    | Impl { members; _ } ->
        List.find_map
          (fun (member : impl_member line) ->
            match member.kind with
            | Associated_definition (written, _) when written.text = name -> Some member.span
            | _ -> None)
          members
    | _ -> None
  in
  let reported_at_definition (recursion : Properties.recursion) =
    match recursion.recursive with
    | T.Named { path; _ } ->
        List.exists
          (fun (_, occurrence) -> occurrence = recursion.occurrence)
          (self_occurrences database path)
    | _ -> false
  in
  List.concat_map
    (fun (name, type_) ->
      let span = Option.value ~default:(header_span definition) (written name) in
      List.filter_map
        (fun (recursive, (occurrence : Properties.occurrence)) ->
          match occurrence with
          | In_place ->
              diagnostic_at database key Needs_indirect span
                (Printf.sprintf
                   "With this definition of `%s`, `%s` contains itself in place, so it would be \
                    infinitely large. Define `%s` as a type that holds it in a collection or in an \
                    `indirect` variant."
                   name (T.show recursive) name)
          | Function_input ->
              diagnostic_at database key Not_strictly_positive span
                (Printf.sprintf
                   "With this definition of `%s`, `%s` contains a function type that has a `time` \
                    clause and whose input contains `%s`. %s"
                   name (T.show recursive) (T.show recursive) not_strictly_positive_message)
          | Indirect -> None)
        (List.sort_uniq compare
           (List.filter_map
              (fun (recursion : Properties.recursion) ->
                if
                  List.exists (Path.equal declaration.path) recursion.defining
                  && not (reported_at_definition recursion)
                then Some (recursion.recursive, recursion.occurrence)
                else None)
              (Interface.Impls.contents database ~bounds type_).recursions)))
    impl.implements.associated

(* Instantiation cycles *)

(* A generic definition's calls to generic definitions of the same package,
   each with whether a type argument puts one of the caller's parameters
   inside a type constructor, which makes the arguments grow around a
   cycle. *)
let instantiation_edges database (key : Names.key) =
  match Query.demand database Infer.core key with
  | None -> []
  | Some form ->
      let grows = function
        | T.Type (T.Named { arguments; _ }) ->
            let mentions =
              T.exists (function
                | T.Parameter { owner; _ } -> Path.equal owner key.path
                | _ -> false)
            in
            List.exists (function T.Type type_ -> mentions type_ | _ -> false) arguments
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

let check_instantiation database (package : Path.package) =
  let generic =
    List.filter
      (fun (declaration : Names.declaration) ->
        declaration.generic && declaration.ordinal = 0
        && (declaration.kind = Function || declaration.kind = Method))
      (declarations database package)
  in
  let edges =
    List.map
      (fun (declaration : Names.declaration) ->
        (declaration, instantiation_edges database (Names.key_of declaration)))
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
        match Query.demand database Names.definition (Names.key_of declaration) with
        | Some definition ->
            diagnostic_at database (Names.key_of declaration) Instantiation_cycle
              (header_span definition)
              "This generic code instantiates itself with type arguments that grow each time \
               around, so it would be compiled without end."
        | None -> None
      else None)
    edges

(* Tests *)

(* Two tests with one name in one file are already a duplicate definition;
   this is for two in different files of the package. *)
let check_tests database (package : Path.package) =
  let tests =
    List.filter
      (fun (declaration : Names.declaration) -> declaration.kind = Test && declaration.ordinal = 0)
      (declarations database package)
  in
  snd
    (List.fold_left
       (fun (seen, diagnostics) (declaration : Names.declaration) ->
         let name = match declaration.path with Test { name; _ } -> name | _ -> "" in
         if List.mem name seen then
           match Query.demand database Names.definition (Names.key_of declaration) with
           | Some definition ->
               ( seen,
                 diagnostics
                 @ Option.to_list
                     (diagnostic_at database (Names.key_of declaration) Duplicate_test
                        definition.span
                        (Printf.sprintf "Another test of this package is named %S." name)) )
           | None -> (seen, diagnostics)
         else (name :: seen, diagnostics))
       ([], []) tests)

(* A package's errors, by its name. *)
let check =
  Query.query ~name:"package_checks" ~phase:Phases.checks ~show:Path.show_package ~saved:true
    (fun database package_name ->
      let package = package_name in
      let declarations = declarations database package in
      let impls =
        List.filter_map
          (fun (declaration : Names.declaration) ->
            if declaration.kind = Impl && declaration.ordinal = 0 then
              match
                ( Query.demand database Environment.impl_interface declaration.path,
                  Query.demand database Names.definition (Names.key_of declaration) )
              with
              | Some impl, Some definition when not impl.impl_broken ->
                  Some (declaration, definition, impl)
              | _ -> None
            else None)
          declarations
      in
      let location =
        List.filter_map
          (fun (declaration, definition, impl) ->
            check_location database declaration definition impl)
          impls
      in
      let sealed =
        List.filter_map
          (fun (declaration, definition, impl) -> check_sealed database declaration definition impl)
          impls
      in
      (* An impl in the wrong place reports that alone. *)
      let placed =
        List.filter
          (fun ((declaration : Names.declaration), _, impl) ->
            List.mem declaration.module_.package (outer_packages impl))
          impls
      in
      let names =
        List.concat_map
          (fun (declaration, definition, impl) ->
            check_method_names database declaration definition impl)
          impls
      in
      (* The impls of the packages this one depends on, directly or not:
             one of this package's may overlap one of theirs, though each
             is where the location rule lets it be. *)
      let dependency_impls =
        let rec packages seen = function
          | [] -> seen
          | name :: rest when List.mem name seen -> packages seen rest
          | name :: rest -> packages (name :: seen) (dependencies database name @ rest)
        in
        let direct = dependencies database package in
        let standard =
          if package_name = Path.standard_package then [] else [ Path.standard_package ]
        in
        List.concat_map
          (fun name ->
            List.filter_map
              (fun (_, impl) -> Query.demand database Environment.impl_interface impl)
              (Query.demand database Interface.Impls.index name))
          (List.filter (fun name -> name <> package_name) (packages [] (standard @ direct)))
      in
      (* Two impls can overlap only if they implement one trait for one
             type, since an impl's type is always a named type: so each is
             compared only with the impls before it in its trait and type's
             group, here and in the packages depended on. *)
      let group (impl : T.impl_interface) =
        (impl.implements.trait, Interface.Impls.head impl.for_type)
      in
      let grouped impls =
        let table = Hashtbl.create 64 in
        List.iter
          (fun impl ->
            let key = group impl in
            Hashtbl.replace table key (impl :: Option.value ~default:[] (Hashtbl.find_opt table key)))
          impls;
        fun impl -> List.rev (Option.value ~default:[] (Hashtbl.find_opt table (group impl)))
      in
      let dependencies_like = grouped dependency_impls in
      let earlier = Hashtbl.create 64 in
      let overlaps =
        List.concat_map
          (fun ((declaration : Names.declaration), definition, (impl : T.impl_interface)) ->
            let key = group impl in
            let before = List.rev (Option.value ~default:[] (Hashtbl.find_opt earlier key)) in
            Hashtbl.replace earlier key
              (impl :: Option.value ~default:[] (Hashtbl.find_opt earlier key));
            List.filter_map
              (fun (other : T.impl_interface) ->
                if overlap impl other then
                  diagnostic_at database (Names.key_of declaration) Overlapping_impls
                    (header_span definition)
                    (Printf.sprintf
                       "This `impl` overlaps another `impl` of `%s` for `%s`: a type has at most \
                        one `impl` of a trait for each set of its arguments."
                       (T.show_trait other.implements) (T.show other.for_type))
                else None)
              (before @ dependencies_like impl))
          placed
      in
      let recursion =
        List.concat_map
          (fun (declaration : Names.declaration) ->
            if declaration.kind = Type && declaration.ordinal = 0 then
              match Query.demand database Names.definition (Names.key_of declaration) with
              | Some definition -> check_recursion database declaration definition
              | None -> []
            else [])
          declarations
        @ List.concat_map
            (fun (declaration, definition, impl) ->
              check_associated_types database declaration definition impl)
            impls
      in
      location @ sealed @ names @ overlaps @ recursion
      @ check_instantiation database package
      @ check_tests database package)

(* The manifest *)

(* The packages a definition uses: those it names in a path, those with a
   trait whose method it calls with a dot, and those with an [impl] that
   answers a call or meets a bound in it. *)
let used_packages =
  Query.query ~name:"used_packages" ~phase:Phases.bodies ~saved:true ~show:Names.show_key
    (fun database (key : Names.key) ->
      let named =
        match Query.demand database Resolve.resolved key with
        | Some resolved ->
            List.filter_map
              (function
                | Some (Resolve.Definition (_, path) | Variant (path, _)) ->
                    Some (Path.package path)
                | Some (Module module_) -> Some module_.package
                | _ -> None)
              (Array.to_list resolved.names)
        | None -> []
      in
      let called = ref (Query.demand database Infer.evidence_packages key) in
      Option.iter
        (fun (form : Core.t) ->
          Core_walk.definition
            (Core_walk.callees (function
              | Trait_method { trait; evidence; _ } ->
                  called :=
                    Path.package trait.trait
                    :: (match evidence with Impl { impl; _ } -> [ Path.package impl ] | _ -> [])
                    @ !called
              | _ -> ()))
            form.definition)
        (Query.demand database Infer.core key);
      List.sort_uniq compare (named @ !called))

(* The packages a package's code uses, its tests apart. A dependency that is
   not among them is one only its tests use, which a project that uses the
   package once it is published does not take on. *)
let code_packages =
  Query.query ~name:"code_packages" ~phase:Phases.checks ~saved:true ~show:Path.show_package
    (fun database package_name ->
      let package = package_name in
      List.sort_uniq compare
        (List.concat_map
           (fun (declaration : Names.declaration) ->
             match declaration.path with
             | Test _ -> []
             | _ -> Query.demand database used_packages (Names.key_of declaration))
           (declarations database package)))

(* What only a package's code shows to be wrong with its manifest. *)
type manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
      (** A grant's entry that names no capability *)
  | Unused of Path.package  (** A dependency that nothing in the package uses *)

let manifest_sentence ~package = function
  | Not_a_capability { dependency; name } ->
      Printf.sprintf
        "`%s`, in the entry for `%s`, names no capability. A grant names a capability of the \
         prelude by its name, such as `Clock`, and any other by its full path."
        name (Path.show_package dependency)
  | Unused dependency ->
      Printf.sprintf "Nothing in `%s` uses `%s`. Delete its entry." (Path.show_package package)
        (Path.show_package dependency)

(* Which dependencies a package uses is known only once all of its code
   checks: a call in a body with an error may not have been worked out. So a
   package with an error elsewhere is not told that a dependency is unused,
   which a fix would then delete. *)
let manifest_problems =
  Query.query ~name:"manifest_problems" ~phase:Phases.checks ~saved:true ~show:Path.show_package
    (fun database package_name ->
      let package = package_name in
      let keys = List.map Names.key_of (declarations database package) in
      let checks = List.for_all (Infer.is_clean database) keys in
      let used = List.concat_map (Query.demand database used_packages) keys in
      List.concat_map
        (fun (dependency : Manifest.dependency) ->
          (match
             Query.demand database Interface.Grants.granted (package_name, dependency.package)
           with
            | Some grant ->
                List.map
                  (fun name -> Not_a_capability { dependency = dependency.package; name })
                  grant.unknown
            | None -> [])
          @
          if checks && not (List.mem dependency.package used) then [ Unused dependency.package ]
          else [])
        (Query.demand database Workspace.dependencies package))

let diagnostics database (module_ : Path.module_) =
  List.filter_map
    (fun placed -> if placed.module_ = module_ then Some placed.diagnostic else None)
    (Query.demand database check module_.package)
  |> List.sort (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare left.span right.span)
