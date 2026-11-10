(* Each package's call graph, for termination.

   A node is a function, a method, or an [impl]'s method. Its edges are
   every way it can reach another: a call, naming a function as a value,
   and using an [impl] where a bound or [any] needs one, which reaches
   every method of that [impl]. A function reaches another package's
   functions only through what its own package names, so every cycle lies
   within one package's graph. *)

open Syntax
module Names = Resolve.Names
module C = Checked
module T = Types

type edge =
  | Calls of Path.t  (** A call, or a function named as a value. *)
  | Uses_impl of Path.t  (** An [impl] given where a bound or [any] needs one. *)

type t = (Path.t * edge list) list

let receiver_of (parameters : parameter list) : Path.receiver =
  match parameters with
  | { kind = Self_parameter None; _ } :: _ -> Read
  | { kind = Self_parameter (Some Mut); _ } :: _ -> Mut
  | { kind = Self_parameter (Some Own); _ } :: _ -> Own
  | _ -> Static

let name_of (signature : signature) =
  match signature.name with Plain_name name | Member_name (_, name) -> name.text

let head_of (ty : T.ty) = match ty with Named { path; _ } -> Some path | _ -> None

(* The trait, the [impl], or the capability a method is written inside. *)
let container database (key : Names.key) =
  Option.bind (Query.demand database Names.container key) (fun (container : Names.key) ->
      Option.map
        (fun definition -> (container, definition))
        (Query.demand database Names.definition container))

(* Whether a definition is a method written inside a trait. *)
let in_trait database key =
  match container database key with Some (_, { kind = Trait _; _ }) -> true | _ -> false

(* The traits a trait requires, and itself, so that using an [impl] of
   [Ordered] also uses one of [Equal]. *)
let rec traits_with_required database (trait : Path.t) =
  match Query.demand database Interface.Environment.interface trait with
  | Some (Interface.Environment.Trait_interface interface) ->
      trait
      :: List.concat_map
           (fun (required : T.trait_reference) -> traits_with_required database required.trait)
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
  Query.query ~phase:Proofs ~name:"package_impls" ~show:Fun.id (fun database package ->
      impls database (Query.demand database Workspace.modules package))

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
let impls_used database impls (callee : Core.callee) =
  match callee with
  | Function { path; type_arguments } -> (
      match Query.demand database Interface.Environment.signature path with
      | Some (signature : T.signature) ->
          let rec pairs generics arguments =
            match (generics, arguments) with
            | (generic : T.generic) :: generics, T.Type ty :: arguments ->
                (generic, ty) :: pairs generics arguments
            | _ :: generics, _ :: arguments -> pairs generics arguments
            | _ -> []
          in
          List.concat_map
            (fun ((generic : T.generic), ty) ->
              match generic.kind with
              | Type_generic bounds ->
                  let traits =
                    List.concat_map
                      (fun (bound : T.trait_reference) -> traits_with_required database bound.trait)
                      bounds
                  in
                  impls_for impls traits ty
              | Value_generic | Capability_generic -> [])
            (pairs signature.generics type_arguments)
      | None -> [])
  | _ -> []

(* The edges of one body: each call, each function named as a value, and
   each [impl] an [any] value is made with. *)
let edges database impls (body : Core.block) =
  let found = ref [] in
  let add edges = found := List.rev_append edges !found in
  let callee (called : Core.callee) =
    match called with
    | Function { path; _ } ->
        add (Calls path :: List.map (fun impl -> Uses_impl impl) (impls_used database impls called))
    | Trait_method { evidence = Impl { impl; _ }; name; receiver; _ } ->
        add [ Calls (Path.Method { owner = impl; name; receiver }) ]
    | Trait_method _ | Capability_method _ | Intrinsic _ | Indirect _ -> ()
  in
  Core_walk.block
    (Core_walk.deep
       {
         Core_walk.ignore_all with
         expression =
           (fun (node : Core.expression) ->
             match node.kind with
             | Call { callee = called; _ } -> callee called
             | Function_value { path; _ } -> add [ Calls path ]
             | To_any { value; trait; _ } ->
                 (* It builds the table of the [impl] of its trait, and of the
                    traits that one requires, for the value's type. *)
                 add
                   (List.map
                      (fun impl -> Uses_impl impl)
                      (impls_for impls (traits_with_required database trait.trait) value.type_))
             | _ -> ());
         callee;
       })
    body;
  List.rev !found

let build database package =
  let modules = Query.demand database Workspace.modules package in
  let impls = Query.demand database package_impls package in
  List.concat_map
    (fun module_ ->
      List.concat_map
        (fun (declaration : Names.declaration) ->
          let key = Names.key_of declaration in
          match (declaration.kind, Query.demand database Infer.core key) with
          (* A trait's own method is reached through an [impl], as it always
             was, and is no node of its own. *)
          | (Function | Method | Theorem), Some { definition = Function { body = Some body; _ }; _ }
            when not (in_trait database key) ->
              [ (declaration.path, edges database impls body) ]
          | _ -> [])
        (Query.demand database Names.declarations module_))
    modules

let graph = Query.query ~phase:Proofs ~name:"call_graph" ~show:Fun.id build

(* The paths an [impl] edge reaches: every method of the [impl]. *)
let targets graph = function
  | Calls path -> [ path ]
  | Uses_impl impl ->
      List.filter_map
        (fun (path, _) ->
          match path with
          | Path.Method { owner; _ } when Path.equal owner impl -> Some path
          | _ -> None)
        graph

(* Whether [from] can reach [target] along the graph's edges. *)
let reaches (graph : t) ~from ~target =
  let visited = Hashtbl.create 16 in
  let rec go path =
    Path.equal path target
    || (not (Hashtbl.mem visited path))
       && begin
         Hashtbl.replace visited path ();
         match List.find_opt (fun (node, _) -> Path.equal node path) graph with
         | Some (_, edges) -> List.exists (fun edge -> List.exists go (targets graph edge)) edges
         | None -> false
       end
  in
  go from

(* Whether a function can call itself again: whether something it calls
   reaches back to it. *)
let recursive (graph : t) path =
  match List.find_opt (fun (node, _) -> Path.equal node path) graph with
  | Some (_, edges) ->
      List.exists
        (fun edge ->
          List.exists (fun from -> reaches graph ~from ~target:path) (targets graph edge))
        edges
  | None -> false
