type outcome =
  | Folded of Z.t
  | Not_folded
  | Fails of Integer_arithmetic.failure * Syntax.expression
  | Depends_on_failure

let read_declared_type (lookups : Lookups.t) key (written : Syntax.type_expression) =
  match written.kind with
  | Path_type written -> (
      match (lookups.read_resolved Interface key).names.(written.path.last.id) with
      | Some (Definition (Type, type_path)) ->
          Some (Types.Named { path = type_path; arguments = [] })
      | _ -> None)
  | _ -> None

let complete (value : Syntax.expression) = function
  | Ok folded -> Folded folded
  | Error failure -> Fails (failure, value)

let rec evaluate_in lookups ~visiting resolved (width : Integer_arithmetic.width)
    (value : Syntax.expression) =
  let recurse = evaluate_in lookups ~visiting resolved in
  let evaluate_pair left right ~right_width apply =
    match (recurse width left, recurse right_width right) with
    | Folded left, Folded right -> apply left right
    | ((Fails _ | Depends_on_failure) as failed), _ | _, ((Fails _ | Depends_on_failure) as failed)
      ->
        failed
    | (Folded _ | Not_folded), (Folded _ | Not_folded) -> Not_folded
  in
  let with_fixed apply = match width with Fixed fixed -> apply fixed | Unbounded -> Not_folded in
  match value.kind with
  | Integer literal -> Folded literal
  | Parenthesized inner -> recurse width inner
  | Prefix (Negate, inner) -> (
      match recurse width inner with
      | Folded folded -> complete value (Integer_arithmetic.negate width folded)
      | outcome -> outcome)
  | Prefix (Complement, inner) ->
      with_fixed (fun fixed ->
          match recurse width inner with
          | Folded folded -> Folded (Integer_arithmetic.complement fixed folded)
          | outcome -> outcome)
  | Binary { operator = Operation (Arithmetic arithmetic); left; right; _ } ->
      let apply =
        match arithmetic with
        | Add -> Integer_arithmetic.add
        | Subtract -> Integer_arithmetic.subtract
        | Multiply -> Integer_arithmetic.multiply
        | Divide -> Integer_arithmetic.divide
        | Remainder -> Integer_arithmetic.remainder
      in
      evaluate_pair left right ~right_width:width (fun left right ->
          complete value (apply width left right))
  | Binary { operator = Operation (Bitwise bitwise); left; right; _ } ->
      with_fixed (fun _ ->
          let apply =
            match bitwise with Bit_and -> Z.logand | Bit_or -> Z.logor | Bit_xor -> Z.logxor
          in
          evaluate_pair left right ~right_width:width (fun left right -> Folded (apply left right)))
  | Binary { operator = Operation (Shift shift); left; right; _ } ->
      with_fixed (fun fixed ->
          let apply =
            match shift with
            | Shift_left -> Integer_arithmetic.shift_left
            | Shift_right -> Integer_arithmetic.shift_right
          in
          evaluate_pair left right ~right_width:Unbounded (fun left amount ->
              complete value (apply fixed left ~amount)))
  | Name path -> (
      match (resolved : Resolve.resolved).names.(path.last.id) with
      | Some (Definition (Constant, path)) -> evaluate_path lookups ~visiting path
      | _ -> Not_folded)
  | Member ({ kind = Name owner; _ }, member) -> (
      match resolved.names.(owner.last.id) with
      | Some (Definition (Type, owner)) ->
          evaluate_path lookups ~visiting (Member_constant { owner; name = member.text })
      | _ -> Not_folded)
  | _ -> Not_folded

and evaluate_path (lookups : Lookups.t) ~visiting path =
  if List.exists (Path.equal path) visiting then Depends_on_failure
  else
    match Resolve.Names.find_definition lookups.names path with
    | Some (key, { kind = Constant { type_; value; _ }; _ }) -> (
        match Option.bind (read_declared_type lookups key type_) Integer_arithmetic.find_width with
        | None -> Not_folded
        | Some width -> (
            match
              evaluate_in lookups ~visiting:(path :: visiting) (lookups.read_resolved Body key)
                width value
            with
            | Fails _ -> Depends_on_failure
            | outcome -> outcome))
    | _ -> Not_folded

let evaluate_expression lookups resolved type_ value =
  match Integer_arithmetic.find_width type_ with
  | Some width -> evaluate_in lookups ~visiting:[] resolved width value
  | None -> Not_folded

let evaluate_constant lookups path = evaluate_path lookups ~visiting:[] path

let is_uint64 (lookups : Lookups.t) path =
  match Resolve.Names.find_definition lookups.names path with
  | Some (key, { kind = Constant { type_; _ }; _ }) ->
      Option.exists (Types.is_builtin UInt64) (read_declared_type lookups key type_)
  | _ -> false

let evaluate_count (lookups : Lookups.t) path ~written =
  if not (is_uint64 lookups path) then
    Error (Printf.sprintf "`%s` in a type argument must be a constant of type `UInt64`." written)
  else
    match lookups.find_folded_integer path with
    | Some value -> Ok value
    | None ->
        Error
          (Printf.sprintf
             "The value of `%s` cannot be computed when the code is compiled: a constant used in a \
              type is made of literals, arithmetic, and other such constants."
             written)
