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
  let rec unify left right =
    match (resolve left, resolve right) with
    | T.Parameter parameter, other when List.mem parameter variables ->
        if other <> T.Parameter parameter then Hashtbl.replace bindings parameter other;
        true
    | other, T.Parameter parameter when List.mem parameter variables ->
        if other <> T.Parameter parameter then Hashtbl.replace bindings parameter other;
        true
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

(* The types a value of a type holds in place: its fields' types, through
   type arguments held in place, but not through an [indirect] variant, a
   collection's storage, a function, or [any]. *)
let rec in_place database (type_ : T.ty) : (Path.t * T.ty list) list =
  match type_ with
  | T.Named { path; arguments } -> (
      match Intrinsic.builtin_of_path path with
      | Some Array ->
          List.concat_map
            (function T.Type element -> in_place database element | _ -> [])
            arguments
      | Some _ -> []
      | None ->
          [ (path, List.filter_map (function T.Type type_ -> Some type_ | _ -> None) arguments) ])
  | _ -> []

let fields_in_place database path arguments =
  match Query.demand database Environment.type_interface path with
  | Some interface -> (
      let substitution =
        if List.length interface.type_generics = List.length arguments then
          List.combine
            (List.map (fun (generic : T.generic) -> generic.generic) interface.type_generics)
            (List.map (fun type_ -> T.Type type_) arguments)
        else []
      in
      let fields (written : T.field list) =
        List.map (fun (field : T.field) -> T.substitute substitution field.field_type) written
      in
      match interface.shape with
      | Record written -> List.map (fun type_ -> (None, type_)) (fields written)
      | Sum variants ->
          List.concat_map
            (fun (variant : T.variant) ->
              if variant.indirect then []
              else
                List.map
                  (fun type_ -> (Some variant.variant_name, type_))
                  (fields (Option.value ~default:[] variant.fields)))
            variants
      | _ -> [])
  | None -> []

(* A cycle of types that contain each other in place, from a type back to
   it, with the variant where the cycle leaves the type, if one. *)
let find_cycle database (start : Path.t) =
  let rec walk depth visited (path, arguments) =
    if depth > 16 then `Growing
    else
      let result = ref `None in
      List.iter
        (fun (variant, field_type) ->
          if !result = `None then
            List.iter
              (fun (inner_path, inner_arguments) ->
                if !result = `None then
                  if Path.equal inner_path start then result := `Cycle variant
                  else if
                    List.exists
                      (fun (seen, seen_arguments) ->
                        Path.equal seen inner_path && seen_arguments = inner_arguments)
                      visited
                  then ()
                  else if
                    List.exists (fun (seen, _) -> Path.equal seen inner_path) visited && depth > 8
                  then result := `Growing
                  else
                    match
                      walk (depth + 1)
                        ((inner_path, inner_arguments) :: visited)
                        (inner_path, inner_arguments)
                    with
                    | `Cycle _ -> result := `Cycle variant
                    | `Growing -> result := `Growing
                    | `None -> ())
              (in_place database field_type))
        (fields_in_place database path arguments);
      !result
  in
  let generics =
    match Query.demand database Environment.type_interface start with
    | Some interface ->
        List.map (fun (generic : T.generic) -> T.Parameter generic.generic) interface.type_generics
    | None -> []
  in
  walk 0 [ (start, generics) ] (start, generics)

(* Whether a generic type contains itself with different arguments,
   through any field at all, [indirect] or in a collection, so that it has
   no fixed set of instances. *)
let grows database (start : Path.t) =
  let rec mentions (type_ : T.ty) =
    match type_ with
    | T.Named { path; arguments } ->
        (path, List.filter_map (function T.Type type_ -> Some type_ | _ -> None) arguments)
        :: List.concat_map (function T.Type type_ -> mentions type_ | _ -> []) arguments
    | _ -> []
  in
  let all_fields path arguments =
    match Query.demand database Environment.type_interface path with
    | Some interface -> (
        let substitution =
          if List.length interface.type_generics = List.length arguments then
            List.combine
              (List.map (fun (generic : T.generic) -> generic.generic) interface.type_generics)
              (List.map (fun type_ -> T.Type type_) arguments)
          else []
        in
        let fields (written : T.field list) =
          List.map (fun (field : T.field) -> T.substitute substitution field.field_type) written
        in
        match interface.shape with
        | Record written -> fields written
        | Sum variants ->
            List.concat_map
              (fun (variant : T.variant) -> fields (Option.value ~default:[] variant.fields))
              variants
        | _ -> [])
    | None -> []
  in
  let generics =
    match Query.demand database Environment.type_interface start with
    | Some interface ->
        List.map (fun (generic : T.generic) -> T.Parameter generic.generic) interface.type_generics
    | None -> []
  in
  let rec walk depth seen (path, arguments) =
    depth < 12
    && List.exists
         (fun (inner_path, inner_arguments) ->
           if Path.equal inner_path start then inner_arguments <> generics
           else if List.mem (inner_path, inner_arguments) seen then false
           else
             walk (depth + 1) ((inner_path, inner_arguments) :: seen) (inner_path, inner_arguments))
         (List.concat_map mentions (all_fields path arguments))
  in
  generics <> [] && walk 0 [ (start, generics) ] (start, generics)

let check_recursion database (declaration : Names.declaration) (definition : definition) =
  match definition.kind with
  | Type_definition _ when grows database declaration.path ->
      at database (Names.key_of declaration) Growing_type (header_span definition)
        "This type contains itself with different type arguments, so it has no fixed set of \
         instances, and generic code is compiled once for each set of arguments."
  | Type_definition { body; _ } -> (
      let key = Names.key_of declaration in
      match find_cycle database declaration.path with
      | `None -> None
      | `Growing ->
          at database key Growing_type (header_span definition)
            "This type contains itself with growing type arguments, so it has no fixed size, and \
             generic code is compiled once for each set of arguments."
      | `Cycle variant -> (
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
          let names =
            List.concat_map
              (fun (declaration, definition, impl) ->
                check_method_names database declaration definition impl)
              impls
          in
          let overlaps =
            List.concat
              (List.mapi
                 (fun index
                      ((declaration : Names.declaration), definition, (impl : T.impl_interface)) ->
                   List.filter_map
                     (fun (_, _, (other : T.impl_interface)) ->
                       if
                         Path.equal impl.implements.trait other.implements.trait
                         && overlap impl other
                       then
                         at database (Names.key_of declaration) Overlapping_impls
                           (header_span definition)
                           (Printf.sprintf
                              "This `impl` overlaps another `impl` of `%s` for `%s`: a type has at \
                               most one `impl` of a trait for each set of its arguments."
                              (T.show_trait other.implements) (T.show other.for_type))
                       else None)
                     (List.filteri (fun other _ -> other < index) impls))
                 impls)
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
