(* The values of integer constants, worked out exactly where the checker
   needs them: a [USize] in a type argument, as in [Array[UInt8, size]].
   See TYPECHECKER.md, "Constants". Every other constant is built by code
   generation. Constants that refer to each other in a cycle have no
   value. *)

open Syntax

let rec expression database resolved (value : expression) : Z.t option =
  let recurse = expression database resolved in
  match value.kind with
  | Integer value -> Some value
  | Parenthesized inner -> recurse inner
  | Prefix (Negate, inner) -> Option.map Z.neg (recurse inner)
  | Binary { operator; left; right; _ } -> (
      match (recurse left, recurse right) with
      | Some left, Some right -> (
          match operator with
          | Add -> Some (Z.add left right)
          | Subtract -> Some (Z.sub left right)
          | Multiply -> Some (Z.mul left right)
          | Divide -> if Z.equal right Z.zero then None else Some (Z.div left right)
          | Remainder -> if Z.equal right Z.zero then None else Some (Z.rem left right)
          | _ -> None)
      | _ -> None)
  | Name path -> (
      match (resolved : Resolve.resolved).names.(path.last.id) with
      | Some (Definition path) -> Query.demand database (Lazy.force value_of) path
      | _ -> None)
  | Member ({ kind = Name owner; _ }, member) -> (
      match resolved.names.(owner.last.id) with
      | Some (Definition owner) ->
          Query.demand database (Lazy.force value_of)
            (Member_constant { owner; name = member.text })
      | _ -> None)
  | _ -> None

and value_of =
  lazy
    (Query.query ~name:"constant_value" ~show:Path.show (fun database path ->
         match Summary.definition database path with
         | Some (key, { kind = Constant { value; _ }; _ }) -> (
             match Query.demand database Resolve.resolved key with
             | Some resolved -> (
                 try expression database resolved value with Query.Cycle _ -> None)
             | None -> None)
         | _ -> None))

let value_of = Lazy.force value_of

(* Whether a constant is declared a [USize], as a type argument needs. *)
let is_usize database path =
  match Summary.definition database path with
  | Some (key, { kind = Constant { type_ = { kind = Path_type written; _ }; _ }; _ }) -> (
      match Query.demand database Resolve.resolved key with
      | Some resolved ->
          resolved.names.(written.path.last.id) = Some (Definition (Intrinsic.builtin_path USize))
      | None -> false)
  | _ -> false
