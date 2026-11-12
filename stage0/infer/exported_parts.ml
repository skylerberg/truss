(* The parts of a definition that the proofs of callers in other packages
   read: the contract of a definition that those packages can call, and the
   body of a [transparent] function.

   A function or a constant that such a part names and those packages cannot
   see is no part of the package's interface: a release could change its
   contract or its value, and break those proofs, while the compatibility
   check reports no change. So these parts name only functions and constants
   that are public. Reading a field that is hidden is allowed in a
   [transparent] body, since a change to the field is a change to the body. *)

open Syntax
module T = Types
module Names = Resolve.Names
module Environment = Interface.Environment
open State

let public database (module_ : Path.module_) name =
  match Query.demand database Names.find (module_, name) with
  | Some entry -> Names.is_public entry.visibility
  | None -> true

(* Whether code in another package can name a function or a constant. A
   method of an [impl] is reached through its trait. *)
let visible_to_other_packages database (path : Path.t) =
  match path with
  | Top { module_; name } -> module_ = Intrinsic.module_ || public database module_ name
  | Method { owner = Top { module_; name }; _ }
  | Member_constant { owner = Top { module_; name }; _ } -> (
      public database module_ name
      &&
      match Interface.Summary.definition database path with
      | Some (_, definition) -> Names.is_public definition.visibility
      | None -> true)
  | Method _ | Member_constant _ | Impl _ | Derived _ | Test _ | Law_proof _ -> true

(* Whether code in another package can call the definition, so that its
   proofs read the definition's contract: a public function, method, or
   theorem; a method of a public trait or capability; and a method of an
   [impl] of a public trait for a type that is public. *)
let called_from_other_packages (state : state) =
  match Query.demand state.database Names.container state.key with
  | None -> Names.is_public state.definition.visibility
  | Some container -> (
      (* The container's interface, and not its definition: the definition
         changes with an edit to any method written inside it. *)
      match Query.demand state.database Environment.interface container.path with
      | Some (Trait_interface _) -> visible_to_other_packages state.database container.path
      | Some (Impl_interface impl) -> (
          visible_to_other_packages state.database impl.implements.trait
          &&
          match impl.for_type with
          | T.Named { path; _ } -> visible_to_other_packages state.database path
          | _ -> true)
      | _ -> false)

(* Reports each function and each constant that the definition names
   inside [parts] and that other packages cannot see. *)
let check_names (state : state) (parts : span list) ~message =
  if parts <> [] then begin
    let spans = Syntax_walk.spans state.definition in
    let named id (path : Path.t) =
      let span = spans.(id) in
      if
        List.exists (fun (part : span) -> part.start <= span.start && span.stop <= part.stop) parts
        && not (visible_to_other_packages state.database path)
      then report state Private_in_public span (message (Path.show path))
    in
    Array.iteri
      (fun id (call : Tables.call option) ->
        match call with Some { callee = Function { path; _ }; _ } -> named id path | _ -> ())
      state.tables.calls;
    Array.iteri
      (fun id (resolution : Tables.resolution option) ->
        match resolution with Some (Global { path; _ }) -> named id path | _ -> ())
      state.tables.resolutions
  end

let check (state : state) (lowered : Environment.lowered_interface) =
  let clauses, name, body =
    match state.definition.kind with
    | Function { signature; body } -> (signature.clauses, Names.signature_name signature, Some body)
    | Method_declaration signature -> (signature.clauses, Names.signature_name signature, None)
    | Theorem { name; clauses; _ } -> (clauses, name, None)
    | _ -> ([], { text = ""; span = state.definition.span; id = state.definition.id }, None)
  in
  if called_from_other_packages state then
    check_names state
      (List.filter_map
         (fun (clause : clause) ->
           match clause.kind with
           | Requires _ | Ensures _ | Cost _ -> Some clause.span
           | Uses _ | Decreases _ | Clause_error -> None)
         clauses)
      ~message:(fun hidden ->
        Printf.sprintf
          "Other packages can call `%s`, so the proofs of its callers there read this clause, and \
           those packages cannot see `%s`. Make `%s` public, or state the clause with functions \
           and constants that are public."
          name.text hidden hidden);
  match (lowered.interface, body) with
  | Function_interface { transparent = true; _ }, Some body ->
      check_names state [ body.span ] ~message:(fun hidden ->
          Printf.sprintf
            "`%s` is `transparent`, so the proofs of callers in other packages read this body, and \
             those packages cannot see `%s`. Make `%s` public, or remove `transparent` from `%s` \
             and state its result in an `ensures`."
            name.text hidden hidden name.text)
  | _ -> ()
