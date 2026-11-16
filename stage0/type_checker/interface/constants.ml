open Syntax

let rec evaluate_expression lookups ~visiting resolved (value : expression) : Z.t option =
  let recurse = evaluate_expression lookups ~visiting resolved in
  match value.kind with
  | Integer value -> Some value
  | Parenthesized inner -> recurse inner
  | Prefix (Negate, inner) -> Option.map Z.neg (recurse inner)
  | Binary { operator; left; right; _ } -> (
      match (recurse left, recurse right) with
      | Some left, Some right -> (
          match operator with
          | Operation (Arithmetic Add) -> Some (Z.add left right)
          | Operation (Arithmetic Subtract) -> Some (Z.sub left right)
          | Operation (Arithmetic Multiply) -> Some (Z.mul left right)
          | Operation (Arithmetic Divide) ->
              if Z.equal right Z.zero then None else Some (Z.div left right)
          | Operation (Arithmetic Remainder) ->
              if Z.equal right Z.zero then None else Some (Z.rem left right)
          | Operation (Bitwise _ | Shift _) | Comparison _ | Connective _ -> None)
      | _ -> None)
  | Name path -> (
      match (resolved : Resolve.resolved).names.(path.last.id) with
      | Some (Definition (Constant, path)) -> evaluate_path lookups ~visiting path
      | _ -> None)
  | Member ({ kind = Name owner; _ }, member) -> (
      match resolved.names.(owner.last.id) with
      | Some (Definition (Type, owner)) ->
          evaluate_path lookups ~visiting (Member_constant { owner; name = member.text })
      | _ -> None)
  | _ -> None

and evaluate_path (lookups : Lookups.t) ~visiting path =
  if List.exists (Path.equal path) visiting then None
  else
    match Resolve.Names.definition_of_path lookups.names path with
    | Some (key, { kind = Constant { value; _ }; _ }) ->
        evaluate_expression lookups ~visiting:(path :: visiting) (lookups.resolved Body key) value
    | _ -> None

let evaluate_constant lookups path = evaluate_path lookups ~visiting:[] path
