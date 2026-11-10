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
      match Workspace.package database package with
      | Some { modules; _ } -> impls database modules
      | None -> [])

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
let impls_used database impls (call : C.call) =
  match call.callee with
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

(* The edges of the expressions of one body. *)
let edges database impls (checked : C.t) ids =
  List.concat_map
    (fun id ->
      let from_call =
        match checked.calls.(id) with
        | Some ({ callee = Function { path; _ }; _ } as call) ->
            Calls path :: List.map (fun impl -> Uses_impl impl) (impls_used database impls call)
        | Some { callee = Trait_method { evidence = Impl { impl; _ }; name; receiver; _ }; _ } ->
            [ Calls (Path.Method { owner = impl; name; receiver }) ]
        | _ -> []
      in
      let from_meaning =
        match checked.meanings.(id) with Some (Global { path; _ }) -> [ Calls path ] | _ -> []
      in
      from_call @ from_meaning)
    ids

(* [any value] builds the table of the [impl] of its trait for the value's
   type. *)
let any_edges database impls (checked : C.t) anys =
  List.concat_map
    (fun (outer, inner) ->
      match (checked.types.(outer), checked.types.(inner)) with
      | Some (T.Any trait), Some ty ->
          List.map
            (fun impl -> Uses_impl impl)
            (impls_for impls (traits_with_required database trait.trait) ty)
      | _ -> [])
    anys

(* The ids of every expression in a block, and each [any value], as the
   ids of the [any] and of its value. *)
let expression_ids (written : block) =
  let ids = ref [] and anys = ref [] in
  let rec visit_expression (expression : expression) =
    ids := expression.id :: !ids;
    (match expression.kind with Any inner -> anys := (expression.id, inner.id) :: !anys | _ -> ());
    Syntax_walk.expression_parts ~expression:visit_expression ~statement:visit_statement expression
  and visit_statement (statement : statement) =
    Syntax_walk.statement_parts ~expression:visit_expression ~statement:visit_statement statement
  in
  List.iter visit_statement written.statements;
  (List.rev !ids, List.rev !anys)

let build database package =
  match Workspace.package database package with
  | None -> []
  | Some { modules; _ } ->
      let impls = Query.demand database package_impls package in
      ignore modules;
      List.concat_map
        (fun module_ ->
          List.concat_map
            (fun (declaration : Names.declaration) ->
              let key = Names.key_of declaration in
              match (Query.demand database Names.definition key, Infer.clean database key) with
              | Some definition, Some checked -> (
                  let node path body =
                    let ids, anys = expression_ids body in
                    (path, edges database impls checked ids @ any_edges database impls checked anys)
                  in
                  match definition.kind with
                  (* A trait's own method is reached through an [impl], as
                     it always was, and is no node of its own. *)
                  | Function { body; _ } when not (in_trait database key) ->
                      [ node declaration.path body ]
                  | Theorem { body; _ } -> [ node declaration.path body ]
                  | _ -> [])
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
