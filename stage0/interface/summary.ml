(* What other definitions can learn about a definition from its syntax
   alone: where it is, and its generic parameters and associated type
   names. Lowering types reads these rather than whole interfaces, so a
   recursive type, whose fields name itself, never makes a cycle of
   queries. *)

open Syntax
module Names = Resolve.Names

(* The definition a path names, with ordinal 0. A method or a member
   constant is found among its owner's members, since it may be written in
   any file of its package. *)
let key =
  Query.query ~name:"key" ~show:Path.show (fun database (path : Path.t) ->
      let find module_ =
        Option.map Names.key_of
          (Names.Declaration_map.find_opt (path, 0)
             (Query.demand database Names.declaration_index module_))
      in
      match path with
      | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ } ->
          if module_ = Intrinsic.module_ || not (Names.module_exists database module_) then None
          else find module_
      | Method { owner; name; _ } | Member_constant { owner; name } ->
          List.find_opt
            (fun (key : Names.key) -> Path.equal key.path path)
            (Query.demand database Names.members (owner, name))
      | Derived _ -> None)

let definition database path =
  match Query.demand database key path with
  | Some key -> (
      match Query.demand database Names.definition key with
      | Some definition -> Some (key, definition)
      | None -> None)
  | None -> None

type generic_kind = Type_kind | Value_kind | Capability_kind

let generic_kinds (generics : generic_parameter list) =
  List.filter_map
    (fun (generic : generic_parameter) ->
      match generic.kind with
      | Type_parameter (name, _) -> Some (name.text, Type_kind)
      | Value_parameter (name, _) -> Some (name.text, Value_kind)
      | Capability_parameter name -> Some (name.text, Capability_kind)
      | Generic_error -> None)
    generics

(* The generic parameters a type, trait, or capability takes, which is what
   naming it with arguments needs. [None] for a definition whose header did
   not parse, which accepts any arguments. *)
let generics_of =
  Query.query ~name:"generics_of" ~show:Path.show (fun database (path : Path.t) ->
      match Intrinsic.builtin_of_path path with
      | Some Array -> Some [ ("Element", Type_kind); ("count", Value_kind) ]
      | Some (Storage | View) -> Some [ ("Element", Type_kind) ]
      | Some _ -> Some []
      | None -> (
          match definition database path with
          | Some (_, definition) -> (
              if Resolve.Parts.broken definition Header then None
              else
                match definition.kind with
                | Type_definition { generics; _ } | Trait { generics; _ } ->
                    Some (generic_kinds generics)
                | Capability _ -> Some []
                | _ -> None)
          | None -> None))

type trait_header = { associated : string list; required : Path.t list }

(* A trait's associated type names, and the traits it requires, as
   resolution named them. *)
let trait_header =
  Query.query ~name:"trait_header" ~show:Path.show (fun database (path : Path.t) ->
      match definition database path with
      | Some (key, { kind = Trait { requires; members; _ }; _ }) ->
          let resolved = Query.demand database Resolve.resolved key in
          let required =
            List.filter_map
              (fun (bound : path_type) ->
                match resolved with
                | Some resolved -> (
                    match resolved.names.(bound.path.last.id) with
                    | Some (Definition path) -> Some path
                    | _ -> None)
                | None -> None)
              requires
          in
          let associated =
            List.filter_map
              (fun (line : trait_member line) ->
                match line.kind with Associated_type (name, _) -> Some name.text | _ -> None)
              members
          in
          Some { associated; required }
      | _ -> None)

(* The traits a trait requires, directly or not, with itself first. Stops
   at a cycle, which [Check] reports. *)
let rec trait_closure database ?(seen = []) path =
  if List.exists (Path.equal path) seen then []
  else
    match Query.demand database trait_header path with
    | None -> [ path ]
    | Some header ->
        path
        :: List.concat_map
             (fun required -> trait_closure database ~seen:(path :: seen) required)
             header.required
        |> List.fold_left
             (fun acc path -> if List.exists (Path.equal path) acc then acc else acc @ [ path ])
             []

let kind_of database (path : Path.t) =
  match path with
  | Top { module_; name } -> (
      match Query.demand database Names.find (module_, name) with
      | Some entry -> Some entry.kind
      | None -> None)
  | _ -> None
