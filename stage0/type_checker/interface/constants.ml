open Syntax

let definition (lookups : Lookups.t) path =
  Option.bind (lookups.names.key path) (fun key ->
      Option.map (fun tree -> (key, tree)) (lookups.names.definition key))

let rec expression lookups ~visiting resolved (value : expression) : Z.t option =
  let recurse = expression lookups ~visiting resolved in
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
      | Some (Definition (Constant, path)) -> evaluate lookups ~visiting path
      | _ -> None)
  | Member ({ kind = Name owner; _ }, member) -> (
      match resolved.names.(owner.last.id) with
      | Some (Definition (Type, owner)) ->
          evaluate lookups ~visiting (Member_constant { owner; name = member.text })
      | _ -> None)
  | _ -> None

and evaluate (lookups : Lookups.t) ~visiting path =
  if List.exists (Path.equal path) visiting then None
  else
    match definition lookups path with
    | Some (key, { kind = Constant { value; _ }; _ }) -> (
        match lookups.resolved Body key with
        | Some resolved -> expression lookups ~visiting:(path :: visiting) resolved value
        | None -> None)
    | _ -> None

let value_of lookups path = evaluate lookups ~visiting:[] path

let is_uint64 (lookups : Lookups.t) path =
  match definition lookups path with
  | Some (key, { kind = Constant { type_ = { kind = Path_type written; _ }; _ }; _ }) -> (
      match lookups.resolved Interface key with
      | Some resolved ->
          resolved.names.(written.path.last.id)
          = Some (Definition (Type, Intrinsic.builtin_path UInt64))
      | None -> false)
  | _ -> false
