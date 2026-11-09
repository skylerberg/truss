(* The checks that look at more than one definition of a package: where an
   [impl] may live, overlapping [impl]s, a type's method sharing a name
   with a trait's, recursive types without [indirect], instantiation
   cycles, and tests with one name. See TYPECHECKER.md, "Traits and impls
   across a package" and "Recursive types". Packages cannot depend on each
   other in a cycle, so every cycle these find is within one package. *)

open Syntax
module T = Types
module Names = Resolve.Names
module Environment = Interface.Environment

(* A diagnostic at a place inside a definition, moved to its file. *)
type placed = { module_ : Path.module_; diagnostic : Diagnostic.t }

let at database (key : Names.key) ?(fixes = []) code (span : span) message =
  match Query.demand database Names.base key with
  | Some (module_, base) ->
      Some
        {
          module_;
          diagnostic =
            Diagnostic.move base
              (Diagnostic.make ~fixes ~code:(Package code)
                 (Source.span span.start span.stop)
                 message);
        }
  | None -> None

let declarations database (package : Workspace.package) =
  List.concat_map (fun module_ -> Query.demand database Names.declarations module_) package.modules

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
    at database key Impl_location (header_span definition)
      (Printf.sprintf
         "This `impl` must be in the package of `%s`, of `%s`, or of a type its trait's arguments \
          name, so that only one place can hold it."
         (T.show_trait impl.implements) (T.show impl.for_type))

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
  let rec occurs parameter (type_ : T.ty) =
    match resolve type_ with
    | T.Parameter found -> found = parameter
    | T.Named { arguments; _ } ->
        List.exists (function T.Type type_ -> occurs parameter type_ | _ -> false) arguments
    | _ -> false
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

(* A type's own method and a method of a trait it implements cannot share
   a name, wherever the [impl] is. *)
let check_method_names database (declaration : Names.declaration) (definition : definition)
    (impl : T.impl_interface) =
  match
    (impl.for_type, Query.demand database Environment.trait_interface impl.implements.trait)
  with
  | T.Named { path; _ }, Some trait when not trait.is_capability ->
      List.filter_map
        (fun (method_ : T.trait_method) ->
          match Query.demand database Names.members (path, method_.method_name) with
          | [] -> None
          | _ ->
              at database (Names.key_of declaration) Method_name_clash (header_span definition)
                (Printf.sprintf
                   "`%s` has a method `%s` of its own, so it cannot also get one from `%s`."
                   (T.show impl.for_type) method_.method_name (T.show_trait impl.implements)))
        trait.methods
  | _ -> []

(* Recursive types *)

(* A type definition's generic parameters, and its fields, each with the
   variant it is in and whether that variant is [indirect]. *)
let type_fields database path =
  match Query.demand database Environment.type_interface path with
  | Some interface ->
      let parameters =
        List.map (fun (generic : T.generic) -> generic.generic) interface.type_generics
      in
      let fields =
        match interface.shape with
        | Record written ->
            List.map (fun (field : T.field) -> (None, false, field.field_type)) written
        | Sum variants ->
            List.concat_map
              (fun (variant : T.variant) ->
                List.map
                  (fun (field : T.field) ->
                    (Some variant.variant_name, variant.indirect, field.field_type))
                  (Option.value ~default:[] variant.fields))
              variants
        | _ -> []
      in
      (parameters, fields)
  | None -> ([], [])

let output_type : T.result -> T.ty = function
  | Returns type_ | Yields (_, type_) | Lends (_, type_) -> type_

let type_arguments arguments =
  List.filter_map (function T.Type type_ -> Some type_ | _ -> None) arguments

(* Whether a generic type holds its [index]th parameter in place: in a field
   of a variant that is not [indirect], outside collections' storage,
   functions, and [any]. [visiting] cuts recursion, as the least answer. *)
let rec holds database visiting (path, index) =
  if List.mem (path, index) visiting then false
  else
    let parameters, fields = type_fields database path in
    match List.nth_opt parameters index with
    | None -> false
    | Some parameter ->
        let visiting = (path, index) :: visiting in
        List.exists
          (fun (_, indirect, field_type) ->
            (not indirect)
            && List.exists
                 (function `Parameter found -> found = parameter | `Path _ -> false)
                 (in_place database visiting field_type))
          fields

(* What a value of a type holds in place: the named types, and the
   generic parameters, through the arguments of generic types that hold them
   in place. *)
and in_place database visiting (type_ : T.ty) =
  match type_ with
  | T.Parameter parameter -> [ `Parameter parameter ]
  | T.Named { path; arguments } -> (
      let arguments = type_arguments arguments in
      match Intrinsic.builtin_of_path path with
      | Some Array -> List.concat_map (in_place database visiting) arguments
      | Some _ -> []
      | None ->
          `Path path
          :: List.concat
               (List.mapi
                  (fun index argument ->
                    if holds database visiting (path, index) then
                      in_place database visiting argument
                    else [])
                  arguments))
  | _ -> []

(* A cycle of types that hold each other in place, from a type back to it:
   [Some variant] with the variant of [start] where the cycle leaves it,
   [None] for a record's field. Each type is visited once. *)
let find_cycle database (start : Path.t) =
  let visited = Hashtbl.create 16 in
  let rec reaches path =
    Path.equal path start
    || (not (Hashtbl.mem visited path))
       && begin
         Hashtbl.replace visited path ();
         List.exists
           (fun (_, indirect, field_type) -> (not indirect) && reaches_any field_type)
           (snd (type_fields database path))
       end
  and reaches_any field_type =
    List.exists
      (function `Path path -> reaches path | `Parameter _ -> false)
      (in_place database [] field_type)
  in
  List.find_map
    (fun (variant, indirect, field_type) ->
      if (not indirect) && reaches_any field_type then Some variant else None)
    (snd (type_fields database start))

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
        let rec mentions (type_ : T.ty) =
          match type_ with
          | T.Parameter found -> found = parameter
          | T.Named { arguments; _ } -> List.exists mentions (type_arguments arguments)
          | T.Function { inputs; output; _ } ->
              List.exists (fun (_, type_) -> mentions type_) inputs || mentions (output_type output)
          | _ -> false
        in
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
              @ targets (output_type output)
          | _ -> []
        in
        List.concat_map (fun (_, _, field_type) -> targets field_type) fields
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

let check_recursion database (declaration : Names.declaration) (definition : definition) =
  match definition.kind with
  | Type_definition _ when grows database declaration.path ->
      at database (Names.key_of declaration) Growing_type (header_span definition)
        "This type contains itself with different type arguments, so it has no fixed set of \
         instances, and generic code is compiled once for each set of arguments."
  | Type_definition { body; _ } -> (
      let key = Names.key_of declaration in
      match find_cycle database declaration.path with
      | None -> None
      | Some variant -> (
          let variant_span =
            match (body, variant) with
            | Variants variants, Some name ->
                Option.map
                  (fun (written : variant) -> written.name.span)
                  (List.find_opt (fun (written : variant) -> written.name.text = name) variants)
            | _ -> None
          in
          match variant_span with
          | Some span ->
              at database key Needs_indirect span
                ~fixes:
                  [
                    Diagnostic.fix "Mark the variant `indirect`."
                      [ Diagnostic.insert span.start "indirect " ];
                  ]
                "This type contains itself in place, so it would be infinitely large. Mark the \
                 variant `indirect` to keep its fields on the heap."
          | None ->
              at database key Needs_indirect (header_span definition)
                "This record contains itself in place, so it would be infinitely large. A record \
                 has no variant to mark `indirect`; use a sum type with an `indirect` variant, or \
                 a collection."))
  | _ -> None

(* Instantiation cycles *)

(* A generic definition's calls to generic definitions of the same package,
   each with whether a type argument puts one of the caller's parameters
   inside a type constructor, which makes the arguments grow around a
   cycle. *)
let instantiation_edges database (key : Names.key) =
  match Query.demand database Infer.checked key with
  | None -> []
  | Some result ->
      let grows = function
        | T.Type (T.Named { arguments; _ }) ->
            let rec mentions = function
              | T.Parameter { owner; _ } -> Path.equal owner key.path
              | T.Named { arguments; _ } ->
                  List.exists (function T.Type type_ -> mentions type_ | _ -> false) arguments
              | _ -> false
            in
            List.exists (function T.Type type_ -> mentions type_ | _ -> false) arguments
        | _ -> false
      in
      List.filter_map
        (fun call ->
          match call with
          | Some ({ callee = Function { path; type_arguments }; _ } : Checked.call)
            when Path.package path = key.module_.package && type_arguments <> [] ->
              Some (path, List.exists grows type_arguments)
          | _ -> None)
        (Array.to_list result.checked.calls)

let check_instantiation database (package : Workspace.package) =
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
    let rec go seen path =
      if Path.equal path target then true
      else if List.exists (Path.equal path) seen then false
      else
        match
          List.find_opt
            (fun ((declaration : Names.declaration), _) -> Path.equal declaration.path path)
            edges
        with
        | Some (_, outgoing) -> List.exists (fun (next, _) -> go (path :: seen) next) outgoing
        | None -> false
    in
    go [] from
  in
  List.filter_map
    (fun ((declaration : Names.declaration), outgoing) ->
      if List.exists (fun (callee, grows) -> grows && reaches callee declaration.path) outgoing then
        match Query.demand database Names.definition (Names.key_of declaration) with
        | Some definition ->
            at database (Names.key_of declaration) Instantiation_cycle (header_span definition)
              "This generic code instantiates itself with type arguments that grow each time \
               around, so it would be compiled without end."
        | None -> None
      else None)
    edges

(* Tests *)

(* Two tests with one name in one file are already a duplicate definition;
   this is for two in different files of the package. *)
let check_tests database (package : Workspace.package) =
  let tests =
    List.filter
      (fun (declaration : Names.declaration) -> declaration.kind = Test && declaration.ordinal = 0)
      (declarations database package)
  in
  snd
    (List.fold_left
       (fun (seen, found) (declaration : Names.declaration) ->
         let name = match declaration.path with Test { name; _ } -> name | _ -> "" in
         if List.mem name seen then
           match Query.demand database Names.definition (Names.key_of declaration) with
           | Some definition ->
               ( seen,
                 found
                 @ Option.to_list
                     (at database (Names.key_of declaration) Duplicate_test definition.span
                        (Printf.sprintf "Another test of this package is named %S." name)) )
           | None -> (seen, found)
         else (name :: seen, found))
       ([], []) tests)

(* The package *)

let check =
  Query.query ~name:"package_checks" ~show:Fun.id (fun database package_name ->
      match Workspace.package database package_name with
      | None -> []
      | Some package ->
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
              | name :: rest ->
                  let direct =
                    match Workspace.package database name with
                    | Some found ->
                        List.map
                          (fun (dependency : Workspace.dependency) -> dependency.package)
                          found.dependencies
                    | None -> []
                  in
                  packages (name :: seen) (direct @ rest)
            in
            let direct =
              List.map
                (fun (dependency : Workspace.dependency) -> dependency.package)
                package.dependencies
            in
            let standard =
              if package_name = Resolve.Prelude.standard then [] else [ Resolve.Prelude.standard ]
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
                Hashtbl.replace table key
                  (impl :: Option.value ~default:[] (Hashtbl.find_opt table key)))
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
                      at database (Names.key_of declaration) Overlapping_impls
                        (header_span definition)
                        (Printf.sprintf
                           "This `impl` overlaps another `impl` of `%s` for `%s`: a type has at \
                            most one `impl` of a trait for each set of its arguments."
                           (T.show_trait other.implements) (T.show other.for_type))
                    else None)
                  (before @ dependencies_like impl))
              placed
          in
          let recursion =
            List.filter_map
              (fun (declaration : Names.declaration) ->
                if declaration.kind = Type && declaration.ordinal = 0 then
                  match Query.demand database Names.definition (Names.key_of declaration) with
                  | Some definition -> check_recursion database declaration definition
                  | None -> None
                else None)
              declarations
          in
          location @ names @ overlaps @ recursion
          @ check_instantiation database package
          @ check_tests database package)

let diagnostics database (module_ : Path.module_) =
  List.filter_map
    (fun placed -> if placed.module_ = module_ then Some placed.diagnostic else None)
    (Query.demand database check module_.package)
  |> List.sort (fun (left : Diagnostic.t) (right : Diagnostic.t) -> compare left.span right.span)
