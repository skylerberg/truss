open Syntax
module Names = Resolve.Names

type edge =
  | Calls of Path.t  (** A call, or a function named as a value. *)
  | Uses_impl of Path.t  (** An [impl] given where a bound or [any] needs one. *)

type t = (Path.t * edge list) list

let head_of (ty : Types.ty) = match ty with Named { path; _ } -> Some path | _ -> None

(* The traits a trait requires, and itself, so that using an [impl] of
   [Ordered] also uses one of [Equal]. *)
let rec traits_with_required database (trait : Path.t) =
  match Query.demand database Interface.Environment.interface trait with
  | Some (Interface.Environment.Trait_interface interface) ->
      trait
      :: List.concat_map
           (fun (required : Types.trait_reference) -> traits_with_required database required.trait)
           interface.requires
  | _ -> [ trait ]

(* Every [impl] in a package, with its trait, the head of its type, and
   its methods' paths. *)
let impls database (modules : Path.module_ list) =
  List.concat_map
    (fun module_ ->
      List.filter_map
        (fun (declaration : Names.declaration) ->
          match declaration.kind with
          | Impl -> (
              let key = Names.key_of declaration in
              match
                ( Query.demand database Interface.Environment.interface declaration.path,
                  Query.demand database Names.definition key )
              with
              | Some (Interface.Environment.Impl_interface interface), Some { kind = Impl _; _ } ->
                  let methods =
                    List.map
                      (fun (member : Names.key) -> member.path)
                      (Query.demand database Names.contained key)
                  in
                  Some
                    ( declaration.path,
                      interface.implements.trait,
                      head_of interface.for_type,
                      methods )
              | _ -> None)
          | _ -> None)
        (Query.demand database Names.declarations module_))
    modules

let package_impls =
  Query.query ~phase:Phases.proofs ~name:"package_impls" ~show:Path.show_package
    (fun database package -> impls database (Query.demand database Packages.modules package))

(* The [impl]s of a package that a value of a type, given where one of
   these traits is needed, could use. Matched by the type's head, which may
   find more than the one used, so the graph may have more edges than the
   program, never fewer. *)
let impls_for impls traits ty =
  match head_of ty with
  | Some head ->
      List.filter_map
        (fun (impl, trait, impl_head, _) ->
          if List.exists (Path.equal trait) traits && impl_head = Some head then Some impl else None)
        impls
  | None -> []

(* The [impl]s a call uses: for each of the callee's generic parameters
   with bounds, the [impl]s of those bounds for the type it is given. *)
let impls_used database impls (callee : _ Core.target) =
  match callee with
  | Function { path; type_arguments } -> (
      match Query.demand database Interface.Environment.signature path with
      | Some (signature : Types.signature) ->
          let rec pairs generics arguments =
            match (generics, arguments) with
            | (generic : Types.generic) :: generics, Types.Type ty :: arguments ->
                (generic, ty) :: pairs generics arguments
            | _ :: generics, _ :: arguments -> pairs generics arguments
            | _ -> []
          in
          List.concat_map
            (fun ((generic : Types.generic), ty) ->
              match generic.kind with
              | Type_generic bounds ->
                  let traits =
                    List.concat_map
                      (fun (bound : Types.trait_reference) ->
                        traits_with_required database bound.trait)
                      bounds
                  in
                  impls_for impls traits ty
              | Value_generic | Capability_generic -> [])
            (pairs signature.generics type_arguments)
      | None -> [])
  | _ -> []

(* The traits that only the built-in integer types implement, and those
   types. *)
let integer_trait owner =
  Well_known.is Fixed_width_integer owner
  || Well_known.is Signed_integer owner
  || Well_known.is Unsigned_integer owner

let integer_types =
  List.filter (fun builtin -> Types.is_integer_type (Types.builtin builtin)) Intrinsic.builtins

let dispatched (called : _ Core.target) =
  match called with
  | Trait_method { evidence = Dynamic; _ } -> true
  | Trait_method { evidence = Bound; self_type = Parameter { name = "Self"; _ }; _ } -> true
  | _ -> false

(* The edges of the code of one definition: each call, each function named
   as a value, and each [impl] an [any] value is made with. *)
let edges database impls (code : Mir.t) =
  let code_edges = ref [] in
  let add edges = code_edges := List.rev_append edges !code_edges in
  let callee (called : Mir.callee) =
    match called with
    | Function { path; _ } ->
        add (Calls path :: List.map (fun impl -> Uses_impl impl) (impls_used database impls called))
    | Trait_method { evidence = Impl { impl; _ }; trait; name; receiver; _ } ->
        let own = Path.Method { owner = impl; name; receiver } in
        let writes =
          List.exists
            (fun (written, _, _, methods) ->
              Path.equal written impl && List.exists (Path.equal own) methods)
            impls
        in
        add [ Calls (if writes then own else Path.Method { owner = trait.trait; name; receiver }) ]
    | Trait_method
        {
          trait;
          name;
          receiver;
          evidence = Bound;
          self_type = Parameter { owner; name = "Self" };
          _;
        }
      when integer_trait owner ->
        (* [Self] in an integer trait's provided body is a built-in integer
           type, so the call reaches that type's [impl], not every one. *)
        let own =
          List.concat_map
            (fun builtin ->
              List.concat_map
                (fun impl ->
                  let method_ = Path.Method { owner = impl; name; receiver } in
                  if
                    List.exists
                      (fun (written, _, _, methods) ->
                        Path.equal written impl && List.exists (Path.equal method_) methods)
                      impls
                  then [ method_ ]
                  else [])
                (impls_for impls [ trait.trait ] (Types.builtin builtin)))
            integer_types
        in
        add
          (if own = [] then [ Calls (Path.Method { owner = trait.trait; name; receiver }) ]
           else List.map (fun method_ -> Calls method_) own)
    | Trait_method { trait; name; receiver; _ } when dispatched called ->
        add [ Calls (Path.Method { owner = trait.trait; name; receiver }) ]
    | Trait_method _ -> ()
    | Capability_method _ | Intrinsic _ | Indirect _ -> ()
  in
  Mir.iter_code code
    ~statement:(fun (statement : Mir.statement) ->
      match statement.kind with
      | Call { call; _ } | Lend { call; _ } | Slice { call; _ } | Template { call; _ } ->
          callee call.callee
      | Assign { value = Function_value { path; _ }; _ } -> add [ Calls path ]
      | Assign { value = To_any { value; trait; _ }; _ } ->
          add
            (List.map
               (fun impl -> Uses_impl impl)
               (impls_for impls
                  (traits_with_required database trait.trait)
                  (Mir.operand_type value)))
      | _ -> ())
    ~terminator:(function For { iteration = Pull { next; _ }; _ } -> callee next | _ -> ());
  List.rev !code_edges

let build database package =
  let modules = Query.demand database Packages.modules package in
  let impls = Query.demand database package_impls package in
  List.concat_map
    (fun module_ ->
      List.concat_map
        (fun (declaration : Names.declaration) ->
          let key = Names.key_of declaration in
          match (declaration.kind, Query.demand database Mir.mir key) with
          | (Function | Method | Theorem), Some code ->
              [ (declaration.path, edges database impls code) ]
          | _ -> [])
        (Query.demand database Names.declarations module_))
    modules

let graph = Query.query ~phase:Phases.proofs ~name:"call_graph" ~show:Path.show_package build

let impl_methods database impl =
  List.concat_map
    (fun (written, _, _, methods) -> if Path.equal written impl then methods else [])
    (Query.demand database package_impls (Path.package impl))

(* The packages a walk from [package] can reach: it and every package it
   depends on, the standard library among them. *)
let reachable_packages database package =
  let seen = Hashtbl.create 8 in
  let rec visit package =
    if not (Hashtbl.mem seen package) then begin
      Hashtbl.replace seen package ();
      List.iter
        (fun (dependency : Manifest.dependency) -> visit dependency.package)
        (Query.demand database Packages.dependencies package)
    end
  in
  visit package;
  visit Path.standard_package;
  Hashtbl.fold (fun package () packages -> package :: packages) seen []

let successors database ~packages (path : Path.t) =
  let own =
    match
      List.find_opt
        (fun (node, _) -> Path.equal node path)
        (Query.demand database graph (Path.package path))
    with
    | Some (_, edges) -> edges
    | None -> []
  in
  let targets = function Calls path -> [ path ] | Uses_impl impl -> impl_methods database impl in
  let implementations =
    match path with
    | Method { owner; name; receiver } -> (
        match Query.demand database Interface.Environment.interface owner with
        | Some (Interface.Environment.Trait_interface _) ->
            List.concat_map
              (fun package ->
                List.filter_map
                  (fun (impl, trait, _, methods) ->
                    let method_ = Path.Method { owner = impl; name; receiver } in
                    if Path.equal trait owner && List.exists (Path.equal method_) methods then
                      Some method_
                    else None)
                  (Query.demand database package_impls package))
              packages
        | _ -> [])
    | _ -> []
  in
  List.concat_map targets own @ implementations

(* Whether [from] can reach [target] along the graph's edges, in the
   program [package] is part of. *)
let reaches database ~package ~from ~target =
  let packages = reachable_packages database package in
  let visited = Hashtbl.create 16 in
  let rec visit path =
    Path.equal path target
    || (not (Hashtbl.mem visited path))
       && begin
         Hashtbl.replace visited path ();
         List.exists visit (successors database ~packages path)
       end
  in
  visit from

(* Whether a function can call itself again: whether something it calls
   reaches back to it. *)
let recursive database ~package path =
  let packages = reachable_packages database package in
  List.exists
    (fun from -> reaches database ~package ~from ~target:path)
    (successors database ~packages path)
