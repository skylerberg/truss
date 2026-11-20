let find_target (resolved : Resolve.resolved) (name : Syntax.name) = resolved.names.(name.id)

let is_member_constant (tables : Tables.t) (value : Syntax.expression) =
  match tables.resolutions.(value.id) with
  | Some (Global { path = Member_constant _; _ }) -> true
  | _ -> false

let rec is_place resolved tables (value : Syntax.expression) =
  match value.kind with
  | Name path -> (
      match find_target resolved path.last with
      | Some (Local _ | Law_parameter _ | Field _ | Definition (Constant, _)) -> true
      | _ -> false)
  | Self_value -> true
  | Member (base, _) -> is_place resolved tables base || is_member_constant tables value
  | Bracket (base, _) -> (
      match resolved.brackets.(value.id) with
      | Some Index -> is_place resolved tables base
      | Some Method_bracket -> (
          match base.kind with Member _ -> is_place resolved tables base | _ -> false)
      | _ -> false)
  | Parenthesized inner -> is_place resolved tables inner
  | _ -> false

let rec find_keyword_operation resolved tables (value : Syntax.expression) =
  match value.kind with
  | Call ({ kind = Member (base, _); _ }, _)
  | Call ({ kind = Bracket ({ kind = Member (base, _); _ }, _); _ }, _)
  | With (base, _) ->
      if is_place resolved tables base then Some (value.id, base)
      else find_keyword_operation resolved tables base
  | Member (base, _) | Bracket (base, _) | Try base -> find_keyword_operation resolved tables base
  | _ -> None

let rec find_lent_mode resolved (tables : Tables.t) (value : Syntax.expression) :
    Language.Mode.t option =
  match value.kind with
  | Call _ -> tables.lend_modes.(value.id)
  | Member (base, _) | Parenthesized base -> find_lent_mode resolved tables base
  | Bracket (base, _) when resolved.Resolve.brackets.(value.id) <> Some Type_arguments ->
      find_lent_mode resolved tables base
  | Mode (_, inner) when Option.is_some (find_keyword_operation resolved tables inner) ->
      find_lent_mode resolved tables inner
  | _ -> None

let rec is_slice (value : Syntax.expression) =
  match value.kind with
  | Bracket (_, [ Item { kind = Range _; _ } ]) -> true
  | Parenthesized inner | Mode (_, inner) -> is_slice inner
  | _ -> false

let rec is_plain_string_literal (value : Syntax.expression) =
  match value.kind with
  | String { tag = None; rest = []; _ } -> true
  | Parenthesized inner -> is_plain_string_literal inner
  | _ -> false

let is_borrowed resolved tables (value : Syntax.expression) =
  (is_place resolved tables value || is_plain_string_literal value
  || Option.is_some (find_lent_mode resolved tables value))
  && not (is_slice value)

let classify_scrutinee_mode resolved tables (scrutinee : Syntax.expression) : Language.Mode.t =
  match scrutinee.kind with
  | Mode (Own, inner) when Option.is_none (find_keyword_operation resolved tables inner) -> Own
  | Mode (Mut, inner)
    when Option.is_none (find_keyword_operation resolved tables inner) && not (is_slice inner) ->
      Mut
  | _ -> if is_borrowed resolved tables scrutinee then Read else Own
