(* Moves, loans, and views, within each function. See TYPECHECKER.md,
   "Ownership: moves, loans, and views".

   Truss has only structured control flow, so the analysis follows the
   tree in evaluation order: the places that may have been moved flow
   forward, joined by union where branches meet, and loops run until
   nothing changes. A loan is live while the value that holds it may still
   be used: a later use reaches a point unless the two are in different
   arms of one branch, and a loop's back edge reaches the uses before a
   point in its body. *)

open Syntax
module T = Types
module C = Checked
module Properties = Interface.Properties
open Context
open Flow
open Walk
open Prepare
open Yields

type pulling = Yields.pulling = Pullable | Yields_mut | Recursive | Yields_places

let pullable = Yields.pullable

type result = { diagnostics : Diagnostic.t list; moves : id list; obligations : C.obligation list }

(* The receiver a written signature declares. *)
let receiver_of (written : signature) : Path.receiver =
  match
    List.find_map
      (fun (parameter : parameter) ->
        match parameter.kind with Self_parameter mode -> Some mode | _ -> None)
      written.parameters
  with
  | None -> Static
  | Some None -> Read
  | Some (Some Mut) -> Mut
  | Some (Some Own) -> Own

let name_of (written : signature) =
  match written.name with Plain_name name | Member_name (_, name) -> name

(* Sets up the context for one body: its parameters' modes, which the
   lowered signature gives, and [self]'s. *)
let enter context (written : signature) (lowered : T.signature option) =
  let named =
    match lowered with
    | Some lowered ->
        List.filter_map
          (fun (parameter : parameter) ->
            match parameter.kind with
            | Named_parameter { name; _ } ->
                Option.map
                  (fun (info : T.parameter_info) -> (name.id, info.mode))
                  (List.find_opt
                     (fun (info : T.parameter_info) -> info.name = name.text)
                     lowered.parameters)
            | _ -> None)
          written.parameters
    | None -> []
  in
  List.iter
    (fun (id, mode) ->
      Hashtbl.replace context.kinds id
        (match mode with T.Own -> Owned | Mut -> Mut_access | Read -> Viewing))
    named;
  context.parameters <- List.map fst named;
  context.mutable_parameters <-
    List.filter_map (fun (id, mode) -> if mode = T.Mut then Some id else None) named;
  context.self_kind <-
    (match receiver_of written with
    | Own -> Some Owned
    | Mut -> Some Mut_access
    | Read -> Some Viewing
    | Static -> None)

let check database (key : Resolve.Names.key) =
  match
    ( Query.demand database Resolve.Names.definition key,
      Query.demand database Resolve.resolved key,
      Query.demand database Infer.checked key,
      Query.demand database Interface.Environment.lowered key )
  with
  | Some definition, Some resolved, Some checked, Some lowered ->
      let names = Hashtbl.create 32 in
      List.iter
        (fun (name : name) -> Hashtbl.replace names name.id name.text)
        (Syntax_walk.names definition);
      let nodes = Hashtbl.create 64 in
      let rec visit (value : expression) =
        Hashtbl.replace nodes value.id value;
        Syntax_walk.children visit value
      in
      Syntax_walk.definition visit definition;
      let context =
        {
          database;
          definition;
          resolved;
          checked = checked.checked;
          bounds =
            (fun parameter -> Option.value ~default:[] (List.assoc_opt parameter lowered.bounds));
          kinds = Hashtbl.create 32;
          names;
          nodes;
          parameters = [];
          mutable_parameters = [];
          self_kind = None;
          paths = Hashtbl.create 64;
          loops = Hashtbl.create 64;
          uses = Hashtbl.create 32;
          declared = Hashtbl.create 32;
          diagnostics = [];
          reported = [];
          moves = [];
          obligations = [];
          marks = Hashtbl.create 8;
        }
      in
      (* A function's, an [impl]'s, or a trait's method with a body: each
         with the signature its parameters' modes come from. *)
      let method_body (written : signature) lowered (body : block) =
        enter context written lowered;
        let state = new_state context in
        let flow = function_body state body in
        check_restored state flow body.span;
        match written.result with
        | Some (Lends _) -> lends_count context body ~report_span:(name_of written).span
        | _ -> ()
      in
      let find_method methods (written : signature) =
        List.find_map
          (fun (name, receiver, signature) ->
            if name = (name_of written).text && receiver = receiver_of written then Some signature
            else None)
          methods
      in
      if Option.is_some (Infer.clean database key) then begin
        prepare context;
        (match (definition.kind, lowered.interface) with
        | Function { body; signature = written }, Function_interface signature ->
            method_body written (Some signature) body
        | Function { body; signature = written }, _ -> method_body written None body
        | (Test { body; _ } | Theorem { body; _ } | Law_proof { body; _ }), _ ->
            ignore (block (new_state context) (Some []) body)
        | Impl { members; _ }, interface ->
            let methods =
              match interface with Impl_interface impl -> impl.impl_methods | _ -> []
            in
            List.iter
              (fun (line : impl_member line) ->
                match line.kind with
                | Impl_method { body; signature = written } ->
                    method_body written (find_method methods written) body
                | _ -> ())
              members
        | Trait { members; _ }, interface ->
            let methods =
              match interface with
              | Trait_interface trait ->
                  List.map
                    (fun (method_ : T.trait_method) ->
                      (method_.method_name, method_.method_receiver, method_.method_signature))
                    trait.methods
              | _ -> []
            in
            List.iter
              (fun (line : trait_member line) ->
                match line.kind with
                | Trait_method { body = Some body; signature = written } ->
                    method_body written (find_method methods written) body
                | _ -> ())
              members
        | _ -> ());
        check_pulls context
      end;
      Some
        {
          diagnostics =
            List.sort_uniq
              (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
                compare (left.span, left.message) (right.span, right.message))
              context.diagnostics;
          moves = List.sort_uniq compare context.moves;
          obligations = List.rev context.obligations;
        }
  | _ -> None

let ownership =
  Query.query ~name:"ownership" ~show:Resolve.Names.show_key ~saved:true
    ~about:(fun (key : Resolve.Names.key) ->
      Some { Query.path = key.path; part = Some "ownership" })
    check

let diagnostics database module_ =
  Resolve.Names.per_definition database module_ (fun key ->
      match Query.demand database ownership key with
      | Some result -> result.diagnostics
      | None -> [])
