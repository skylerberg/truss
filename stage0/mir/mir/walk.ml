let list_choice_blocks = function
  | Tree.Cases cases ->
      List.concat_map
        (fun (case : Tree.case) -> (case.tests :: Option.to_list case.guard) @ [ case.value ])
        cases
  | Conditional { condition; then_; else_; _ } -> [ condition; then_; else_ ]
  | Connective { left; right; _ } -> [ left; right ]

let list_nested_blocks (statement : Tree.statement) : Tree.block list =
  match statement.kind with
  | Basic (Assign { value = Specification (Quantified { matches; body; _ }); _ }) ->
      [ matches; body ]
  | Assert_by_bit_vector { code; _ } -> [ code ]
  | Choose { choice; _ } -> list_choice_blocks choice
  | While { condition; body; failed; _ } ->
      [ condition; body; { statements = failed; value = None } ]
  | For { elements; bindings; body; _ } ->
      Option.to_list (Option.map (fun (elements : Tree.elements) -> elements.count) elements)
      @ [ bindings; body ]
  | Fork { branches; _ } -> branches
  | Provide { body; _ } -> [ body ]
  | Resume { exits; _ } -> List.map (fun (exit : Tree.early_exit) -> exit.resumed) exits
  | Basic
      ( Assign
          {
            value =
              ( Operand _ | Operation _ | Compare _ | Not _ | Construct _ | Array _ | Is_variant _
              | Convert _ | To_any _ | Copy _ | Function_value _ | Lambda _ | Value_parameter _
              | Specification
                  (Result | Entry _ | Yielded | Identical _ | Applied _ | Method_cost _ | Map _) );
            _;
          }
      | Call _ | Lend _ | Template _ | Live _ | Dead _ | Assert _ | Echo _ | Loan_start _
      | Loan_end _ | Ghost_assert _ | Path_note _ | Proof _ )
  | Yield _
  | Jump (Return _ | Break | Continue | Cancel _ | Unreachable | Written_unreachable | Todo) ->
      []

let rec visit_block visit (block : Tree.block) =
  List.iter
    (fun (statement : Tree.statement) ->
      visit statement;
      (match statement.kind with
      | Basic (Ghost_assert { condition; _ }) -> visit_formula visit condition
      | Basic (Proof code) -> visit_code visit code
      | While { loop; _ } | For { loop; _ } -> visit_loop visit loop
      | Basic
          ( Assign _ | Call _ | Lend _ | Template _ | Live _ | Dead _ | Assert _ | Echo _
          | Loan_start _ | Loan_end _ | Path_note _ )
      | Choose _ | Assert_by_bit_vector _ | Fork _ | Provide _ | Resume _ | Yield _ | Jump _ ->
          ());
      List.iter (visit_block visit) (list_nested_blocks statement))
    block.statements

and visit_formula visit (formula : Tree.formula) =
  visit_block visit formula.value;
  Array.iter (visit_body visit) formula.lambdas

and visit_loop visit (loop : Tree.loop) =
  List.iter
    (function
      | Tree.Invariant clause -> visit_formula visit clause
      | Decreases measures -> List.iter (visit_formula visit) measures
      | Cost { bound = Order_of amount | At_most amount | Exactly amount; _ } ->
          visit_formula visit amount)
    loop.clauses

and visit_body visit (body : Tree.body) = visit_block visit body.code

and visit_code visit (code : Tree.t) =
  visit_body visit code.body;
  Array.iter (visit_body visit) code.lambdas

let iter_code = visit_code
let iter_formula = visit_formula

let find_callee (statement : Tree.statement) : Tree.callee option =
  match statement.kind with
  | Basic (Call { call; _ } | Lend { call; _ } | Template { call; _ }) -> Some call.callee
  | For { iteration = Pull { next; _ }; _ } -> Some next
  | Basic
      ( Assign _ | Live _ | Dead _ | Assert _ | Echo _ | Loan_start _ | Loan_end _ | Ghost_assert _
      | Path_note _ | Proof _ )
  | For { iteration = Range _; _ }
  | Choose _ | Assert_by_bit_vector _ | While _ | Fork _ | Provide _ | Resume _ | Yield _ | Jump _
    ->
      None

let is_in_sequence (place : Tree.place) =
  List.exists
    (fun (projection : Tree.projection) ->
      match projection with Element _ | Range _ -> true | Field _ | Variant_field _ -> false)
    place.projections

let extract_operand_type : Tree.operand -> Types.ty = function
  | Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } | Immediate { type_; _ } -> type_
