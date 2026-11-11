(* The body of a [transparent] function.

   The proofs of callers in other packages read the body. A function or a
   constant that the body names and those packages cannot see is no part of
   the package's interface: a release could change its contract or its
   value, and break those proofs, while the compatibility check reports no
   change. So the body names only functions and constants that are public.
   Reading a field that is hidden is allowed, since a change to it is a
   change to the body. *)

open Syntax
module T = Types
module Names = Resolve.Names
open State

let public database (module_ : Path.module_) name =
  match Query.demand database Names.find (module_, name) with
  | Some entry -> is_public entry.visibility
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
      | Some (_, definition) -> is_public definition.visibility
      | None -> true)
  | Method _ | Member_constant _ | Impl _ | Derived _ | Test _ | Law_proof _ -> true

let check (state : state) =
  match state.definition.kind with
  | Function { signature; body } ->
      let spans = Syntax_walk.spans state.definition in
      let in_body id =
        let span = spans.(id) in
        body.span.start <= span.start && span.stop <= body.span.stop
      in
      let function_name =
        match signature.name with Plain_name name | Member_name (_, name) -> name.text
      in
      let named id (path : Path.t) =
        if in_body id && not (visible_to_other_packages state.database path) then
          report state Private_in_transparent spans.(id)
            (Printf.sprintf
               "`%s` is `transparent`, so the proofs of callers in other packages read this body, \
                and those packages cannot see `%s`. Make `%s` public, or remove `transparent` from \
                `%s` and state its result in an `ensures`."
               function_name (Path.show path) (Path.show path) function_name)
      in
      Array.iteri
        (fun id (call : Tables.call option) ->
          match call with Some { callee = Function { path; _ }; _ } -> named id path | _ -> ())
        state.tables.calls;
      Array.iteri
        (fun id (meaning : Tables.meaning option) ->
          match meaning with Some (Global { path; _ }) -> named id path | _ -> ())
        state.tables.meanings
  | _ -> ()
