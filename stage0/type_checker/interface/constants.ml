open Syntax

let rec expression database ~visiting resolved (value : expression) : Z.t option =
  let recurse = expression database ~visiting resolved in
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
      | Some (Definition (Constant, path)) -> evaluate database ~visiting path
      | _ -> None)
  | Member ({ kind = Name owner; _ }, member) -> (
      match resolved.names.(owner.last.id) with
      | Some (Definition (Type, owner)) ->
          evaluate database ~visiting (Member_constant { owner; name = member.text })
      | _ -> None)
  | _ -> None

and evaluate database ~visiting path =
  if List.exists (Path.equal path) visiting then None
  else
    match Summary.definition database path with
    | Some (key, { kind = Constant { value; _ }; _ }) -> (
        match Query.demand database Resolve.resolved key with
        | Some resolved -> expression database ~visiting:(path :: visiting) resolved value
        | None -> None)
    | _ -> None

let value_of =
  Query.query ~name:"constant_value" ~phase:Phases.interfaces ~saved:true ~show:Path.show
    (fun database path -> evaluate database ~visiting:[] path)

let is_usize database path =
  match Summary.definition database path with
  | Some (key, { kind = Constant { type_ = { kind = Path_type written; _ }; _ }; _ }) -> (
      match Query.demand database Resolve.resolved key with
      | Some resolved ->
          resolved.names.(written.path.last.id)
          = Some (Definition (Type, Intrinsic.builtin_path USize))
      | None -> false)
  | _ -> false
