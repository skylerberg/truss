module Lookups = Lookups

type context = {
  interface : Interface.Lookups.t;
  module_ : Path.module_;
  resolved : Resolve.resolved;
  tables : Infer.tables;
  mutable diagnostics : Catalog.diagnostic list;
}

let report context diagnostic =
  context.diagnostics <- Catalog.Usage diagnostic :: context.diagnostics

type site = { is_var : bool; is_refutable_position : bool }
type binding = { name : Syntax.name; removal : Catalog.Usage.removal; site : site }

let collect_bindings (definition : Syntax.definition) =
  let bindings = ref [] and assigned = ref [] in
  let bind ~site (name : Syntax.name) removal = bindings := { name; removal; site } :: !bindings in
  let rec visit_pattern ~site (written : Syntax.pattern) =
    match written.kind with
    | Binding name -> bind ~site name Wildcard
    | Variant { fields = Some fields; _ } | Record fields -> visit_pattern_fields ~site fields
    | Tuple patterns | Alternatives patterns -> List.iter (visit_pattern ~site) patterns
    | _ -> ()
  and visit_pattern_fields ~site (fields : Syntax.pattern_field list) =
    let has_rest = List.exists (fun (field : Syntax.pattern_field) -> field.kind = Rest) fields in
    let has_several_fields =
      List.length (List.filter (fun (field : Syntax.pattern_field) -> field.kind <> Rest) fields)
      > 1
    in
    let rec bind_fields = function
      | [] -> ()
      | (field : Syntax.pattern_field) :: following ->
          (match (field.kind, following) with
          | Field { kind = Binding name; _ }, next :: _ when has_rest ->
              bind ~site name (Field_deletion { field = Written field.id; next = Written next.id })
          | Field { kind = Binding name; _ }, _ when has_rest || has_several_fields ->
              bind ~site name Field_wildcard
          | (Named_field (_, inner) | Field inner), _ -> visit_pattern ~site inner
          | Rest, _ -> ());
          bind_fields following
    in
    bind_fields fields
  in
  let refutable = { is_var = false; is_refutable_position = true }
  and irrefutable = { is_var = false; is_refutable_position = false } in
  let rec visit_expression (value : Syntax.expression) =
    (match value.kind with
    | Is { pattern = written; _ } -> visit_pattern ~site:refutable written
    | Lambda { parameters; _ } ->
        List.iter
          (fun (parameter : Syntax.lambda_parameter) ->
            visit_pattern ~site:irrefutable parameter.pattern)
          parameters
    | Match { arms; _ } ->
        List.iter
          (fun (arm : Syntax.arm) -> List.iter (visit_pattern ~site:refutable) arm.patterns)
          arms
    | Quantified { binder = Binder_in (written, _); _ } -> visit_pattern ~site:irrefutable written
    | _ -> ());
    Syntax_walk.visit_expression_parts ~on_expression:visit_expression ~on_statement:visit_statement
      value
  and visit_statement (written : Syntax.statement) =
    (match written.kind with
    | Let { pattern = written_pattern; is_var; else_; _ } ->
        visit_pattern ~site:{ is_var; is_refutable_position = Option.is_some else_ } written_pattern
    | For { pattern = written_pattern; _ } -> visit_pattern ~site:irrefutable written_pattern
    | Assignment { target = { kind = Name last; _ }; operator = Assign; _ } ->
        assigned := last.id :: !assigned
    | _ -> ());
    Syntax_walk.visit_statement_parts ~on_expression:visit_expression ~on_statement:visit_statement
      written
  in
  Syntax_walk.visit_definition ~on_statement:visit_statement visit_expression definition;
  (List.rev !bindings, !assigned)

let find_shadowed_constant context (occurrences : binding list) =
  let may_be_constant (occurrence : binding) =
    occurrence.site.is_refutable_position
    && match occurrence.removal with Wildcard -> true | Field_wildcard | Field_deletion _ -> false
  in
  match occurrences with
  | first :: _ when List.for_all may_be_constant occurrences ->
      Option.bind context.tables.local_types.(first.name.id) (fun type_ ->
          Interface.Definition.find_shadowed_constant context.interface context.module_
            ~name:first.name.text ~type_)
  | _ -> None

let check_unused context (definition : Syntax.definition) =
  let targets = context.resolved.names in
  let bindings, assigned = collect_bindings definition in
  let is_binding = Array.make (Array.length targets) false in
  List.iter (fun (binding : binding) -> is_binding.(binding.name.id) <- true) bindings;
  let is_var = Array.make (Array.length targets) false in
  List.iter
    (fun (binding : binding) -> if binding.site.is_var then is_var.(binding.name.id) <- true)
    bindings;
  let is_assigned = Array.make (Array.length targets) false
  and is_written = Array.make (Array.length targets) false in
  List.iter
    (fun id ->
      match targets.(id) with
      | Some (Resolve.Local binding) when is_var.(binding) ->
          is_assigned.(id) <- true;
          is_written.(binding) <- true
      | _ -> ())
    assigned;
  let is_used = Array.make (Array.length targets) false in
  Array.iteri
    (fun index target ->
      match target with
      | Some (Resolve.Local id) when not (is_binding.(index) || is_assigned.(index)) ->
          is_used.(id) <- true
      | _ -> ())
    targets;
  let rec read_first_alternative id =
    match targets.(id) with
    | Some (Resolve.Local first) when is_binding.(id) -> read_first_alternative first
    | _ -> id
  in
  let later_alternatives = Hashtbl.create 8 in
  List.iter
    (fun (binding : binding) ->
      let first = read_first_alternative binding.name.id in
      if first <> binding.name.id then Hashtbl.add later_alternatives first binding)
    bindings;
  List.iter
    (fun (binding : binding) ->
      let name = binding.name in
      if targets.(name.id) = Some Binding && not is_used.(name.id) then
        if is_written.(name.id) then
          report context (Unread_variable { binding = Written name.id; name = name.text })
        else
          let alternatives = List.rev (Hashtbl.find_all later_alternatives name.id) in
          let occurrence (binding : binding) : Catalog.Usage.occurrence =
            { binding = Written binding.name.id; removal = binding.removal }
          in
          report context
            (Unused_variable
               {
                 name = name.text;
                 binding = occurrence binding;
                 alternatives = List.map occurrence alternatives;
                 constant = find_shadowed_constant context (binding :: alternatives);
               }))
    bindings

let check_block context (written : Syntax.block) =
  let rec check_statements = function
    | first :: (next :: _ as rest) ->
        if Infer.statement_diverges context.tables first then begin
          let last = List.nth rest (List.length rest - 1) in
          report context (Unreachable_code { first = Written next.id; last = Written last.id })
        end
        else check_statements rest
    | _ -> ()
  in
  check_statements written.statements

let check_unreachable context (definition : Syntax.definition) =
  let rec visit_expression (value : Syntax.expression) =
    (match value.kind with
    | Block block | Lambda { body = block; _ } | Provide { body = block; _ } ->
        check_block context block
    | If { then_; else_; _ } -> (
        check_block context then_;
        match else_ with Some (Else block) -> check_block context block | _ -> ())
    | _ -> ());
    Syntax_walk.visit_expression_parts ~on_expression:visit_expression ~on_statement:visit_statement
      value
  and visit_statement (written : Syntax.statement) =
    (match written.kind with
    | For { body; _ } | While { body; _ } | Proof body -> check_block context body
    | Parallel _ | Concurrent _ -> ()
    | Let { else_ = Some block; _ } -> check_block context block
    | _ -> ());
    Syntax_walk.visit_statement_parts ~on_expression:visit_expression ~on_statement:visit_statement
      written
  in
  let bodies =
    match definition.kind with
    | Function { body; _ } | Test { body; _ } | Theorem { body; _ } | Law_proof { body; _ } ->
        [ body ]
    | Trait { members; _ } ->
        List.filter_map
          (fun (line : Syntax.trait_member Syntax.node) ->
            match line.kind with Law law -> Some law.body | _ -> None)
          members
    | _ -> []
  in
  List.iter (check_block context) bodies;
  Syntax_walk.visit_definition ~on_statement:visit_statement visit_expression definition

type place =
  | Self_place
  | Local_place of Syntax.id
  | Constant_place of Path.t
  | Field_place of place * string
  | Index_place of place * index_key

and index_key = Literal_key of Z.t | Place_key of place

let find_named_place context (value : Syntax.expression) (name : Syntax.name) =
  match (context.tables.resolutions.(value.id), context.resolved.names.(name.id)) with
  | Some (Local_value id), _ -> Some (Local_place id)
  | _, Some (Definition (Constant, constant)) -> Some (Constant_place constant)
  | _ -> None

let rec find_place context (value : Syntax.expression) =
  match value.kind with
  | Parenthesized inner -> find_place context inner
  | Self_value -> Some Self_place
  | Name name -> find_named_place context value name
  | Member (_, name) when Option.is_some context.resolved.names.(name.id) ->
      find_named_place context value name
  | Member (base, _) -> (
      match context.tables.resolutions.(value.id) with
      | Some (Field_access { field; _ }) ->
          Option.map (fun place -> Field_place (place, field)) (find_place context base)
      | _ -> None)
  | Bracket (base, [ Item key ]) when context.resolved.brackets.(value.id) = Some Index -> (
      match (find_place context base, find_index_key context key) with
      | Some place, Some index -> Some (Index_place (place, index))
      | _ -> None)
  | _ -> None

and find_index_key context (key : Syntax.expression) =
  match key.kind with
  | Integer value -> Some (Literal_key value)
  | _ -> Option.map (fun place -> Place_key place) (find_place context key)

let rec is_same_place left right =
  match (left, right) with
  | Self_place, Self_place -> true
  | Local_place left, Local_place right -> left = right
  | Constant_place left, Constant_place right -> Path.equal left right
  | Field_place (left_base, left_field), Field_place (right_base, right_field) ->
      left_field = right_field && is_same_place left_base right_base
  | Index_place (left_base, left_key), Index_place (right_base, right_key) ->
      is_same_place left_base right_base && is_same_index_key left_key right_key
  | _ -> false

and is_same_index_key left right =
  match (left, right) with
  | Literal_key left, Literal_key right -> Z.equal left right
  | Place_key left, Place_key right -> is_same_place left right
  | _ -> false

let check_comparison context (value : Syntax.expression) comparison (left : Syntax.expression) right
    =
  match (find_place context left, find_place context right) with
  | Some left_place, Some right_place when is_same_place left_place right_place ->
      let is_float =
        match context.tables.types.(left.id) with
        | Some type_ -> Types.is_float_type type_
        | None -> false
      in
      report context
        (Self_comparison
           {
             comparison = Written value.id;
             operand = Written left.id;
             operator = comparison;
             is_float;
           })
  | _ -> ()

let check_self_comparisons context (definition : Syntax.definition) =
  let rec visit_expression (value : Syntax.expression) =
    (match value.kind with
    | Binary { operator = Comparison comparison; left; right; _ } ->
        check_comparison context value comparison left right
    | _ -> ());
    Syntax_walk.visit_expression_parts ~on_expression:visit_expression ~on_statement:visit_statement
      value
  and visit_statement (written : Syntax.statement) =
    match written.kind with
    | For { iterable; body; _ } ->
        visit_expression iterable;
        visit_block body
    | While { condition; body; _ } ->
        visit_expression condition;
        visit_block body
    | Proof _ -> ()
    | _ ->
        Syntax_walk.visit_statement_parts ~on_expression:visit_expression
          ~on_statement:visit_statement written
  and visit_block (block : Syntax.block) = List.iter visit_statement block.statements in
  match definition.kind with Function { body; _ } | Test { body; _ } -> visit_block body | _ -> ()

let check (lookups : Lookups.t) key =
  let definition = lookups.interface.names.read_definition key in
  let context =
    {
      interface = lookups.interface;
      module_ = key.module_;
      resolved = lookups.read_resolved key;
      tables = lookups.read_tables key;
      diagnostics = [];
    }
  in
  check_unused context definition;
  check_unreachable context definition;
  check_self_comparisons context definition;
  Option.to_list (Unused_run_forever.find lookups key definition) @ List.rev context.diagnostics
