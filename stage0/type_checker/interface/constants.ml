let rec evaluate_expression lookups ~visiting resolved (value : Syntax.expression) : Z.t option =
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
  | Name _ | Member _ -> (
      match (Resolve.find_head resolved value, value.kind) with
      | Some { target = Definition (Constant, path); _ }, _ -> evaluate_path lookups ~visiting path
      | Some _, _ -> None
      | None, Member (owner, member) -> (
          match Resolve.find_head resolved owner with
          | Some { target = Definition (Type, owner); _ } ->
              evaluate_path lookups ~visiting (Member_constant { owner; name = member.text })
          | _ -> None)
      | None, _ -> None)
  | _ -> None

and evaluate_path (lookups : Lookups.t) ~visiting path =
  if List.exists (Path.equal path) visiting then None
  else
    match Resolve.Names.find_definition lookups.names path with
    | Some (key, { kind = Constant { value; _ }; _ }) ->
        evaluate_expression lookups ~visiting:(path :: visiting) (lookups.read_resolved Body key)
          value
    | _ -> None

let evaluate_constant lookups path = evaluate_path lookups ~visiting:[] path

let is_uint64 (lookups : Lookups.t) path =
  match Resolve.Names.find_definition lookups.names path with
  | Some (key, { kind = Constant { type_ = { kind = Path_type written; _ }; _ }; _ }) ->
      (lookups.read_resolved Interface key).names.(written.path.last.id)
      = Some (Definition (Type, Well_known.make_builtin_type_path UInt64))
  | _ -> false

let evaluate_count (lookups : Lookups.t) path : (Z.t, Catalog.Typing.count_error) result =
  if not (is_uint64 lookups path) then Error Not_uint64
  else
    match lookups.find_constant_value path with
    | Some value -> Ok value
    | None -> Error Uncomputable
