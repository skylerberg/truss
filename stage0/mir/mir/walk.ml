let list_choice_blocks = function
  | Tree.Cases cases ->
      List.concat_map
        (fun (case : Tree.case) -> (case.tests :: Option.to_list case.guard) @ [ case.value ])
        cases
  | Conditional { then_; else_; _ } -> [ then_; else_ ]
  | Connective { right; _ } -> [ right ]

let list_nested_blocks_of_kind (kind : Tree.statement_kind) : Tree.block list =
  match kind with
  | Basic (Assign { value = Specification (Quantified { matches; body; _ }); _ }) ->
      [ matches; body ]
  | Assert_by_bit_vector { code; _ } -> [ code ]
  | Choose { choice; _ } -> list_choice_blocks choice
  | While { condition; body; failed; _ } ->
      [ condition; body; { statements = failed; value = None } ]
  | For { lent; body; _ } ->
      Option.to_list (Option.map (fun (lent : Tree.lent_element) -> lent.count) lent) @ [ body ]
  | Fork { branches; _ } -> branches
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
      | Call _ | Lend _ | Slice _ | Template _ | Live _ | Dead _ | Assert _ | Echo _ | Provide _
      | Provide_end | Loan_start _ | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ )
  | Yield _
  | Jump (Return _ | Break | Continue | Cancel _ | Unreachable | Written_unreachable | Todo) ->
      []

let list_nested_blocks (statement : Tree.statement) = list_nested_blocks_of_kind statement.kind

let visit_operand_places visit = function
  | Tree.Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> visit place
  | Constant _ -> ()

let visit_target_places visit : Tree.operand Core.target -> unit = function
  | Indirect function_value -> visit_operand_places visit function_value
  | _ -> ()

let visit_call_places visit (call : Tree.call) =
  visit_target_places visit call.callee.target;
  List.iter
    (function Tree.Passed { value; _ } -> visit_operand_places visit value | Default -> ())
    call.arguments

let visit_iteration_places visit = function
  | Tree.Range { start; stop; _ } ->
      visit_operand_places visit start;
      visit_operand_places visit stop
  | Pull { cursor; next } ->
      visit cursor;
      visit_target_places visit next.target

let rec visit_yielded_places visit = function
  | Tree.Part part -> visit_operand_places visit part
  | Built { fields; _ } ->
      List.iter (fun (_, field) -> Option.iter (visit_yielded_places visit) field) fields

let visit_rvalue_places visit rvalue =
  let visit_operand = visit_operand_places visit in
  let visit_specification = function
    | Tree.Result | Yielded -> ()
    | Entry local -> visit { root = Local local; projections = [] }
    | Identical (first, second) ->
        visit_operand first;
        visit_operand second
    | Applied { arguments; _ } -> List.iter visit_operand arguments
    | Method_cost { method_; _ } -> visit_target_places visit method_
    | Map entries ->
        List.iter
          (fun (key, value) ->
            visit_operand key;
            visit_operand value)
          entries
    | Quantified { range; _ } -> (
        match range with
        | Over_type _ -> ()
        | Over_range { start; stop; _ } ->
            visit_operand start;
            visit_operand stop)
  in
  match rvalue with
  | Tree.Operand value | Not value | Convert { value; _ } | To_any { value; _ } | Copy value ->
      visit_operand value
  | Operation { operands; _ } | Array operands -> List.iter visit_operand operands
  | Compare { left; right; _ } ->
      visit_operand left;
      visit_operand right
  | Construct { fields; _ } -> List.iter (fun (_, field) -> Option.iter visit_operand field) fields
  | Is_variant { place; _ } -> visit place
  | Lambda { captures; _ } ->
      List.iter (fun (capture : Tree.capture) -> visit capture.place) captures
  | Function_value _ | Value_parameter _ -> ()
  | Specification value -> visit_specification value

let rec iter_places_read visit (block : Tree.block) =
  List.iter
    (fun (statement : Tree.statement) -> visit_statement_places visit statement.kind)
    block.statements;
  Option.iter (visit_operand_places visit) block.value

and visit_statement_places visit (kind : Tree.statement_kind) =
  (match kind with
  | Basic (Assign { value; _ }) -> visit_rvalue_places visit value
  | Basic (Call { call; _ } | Lend { call; _ } | Template { call; _ }) ->
      visit_call_places visit call
  | Basic (Slice { base; call; _ }) ->
      visit base;
      visit_call_places visit call
  | Basic (Assert value | Echo value | Loan_start { borrowed = value; _ })
  | Assert_by_bit_vector { condition = value; _ }
  | Choose { choice = Conditional { condition = value; _ } | Connective { left = value; _ }; _ } ->
      visit_operand_places visit value
  | Basic (Provide { provided; _ }) ->
      List.iter
        (fun (provided : Tree.provided) -> visit_operand_places visit provided.value)
        provided
  | For { iteration; _ } -> visit_iteration_places visit iteration
  | Yield { part; _ } -> visit_yielded_places visit part
  | Jump (Return returned) -> Option.iter (visit_operand_places visit) returned
  | Jump (Cancel { returned; _ }) ->
      Option.iter (fun (value, _) -> visit_operand_places visit value) returned
  | Jump (Break | Continue | Unreachable | Written_unreachable | Todo)
  | Basic (Live _ | Dead _ | Provide_end | Loan_end _ | Ghost_assert _ | Matched _ | Proof _)
  | Choose { choice = Cases _; _ }
  | While _ | Fork _ | Resume _ ->
      ());
  List.iter (iter_places_read visit) (list_nested_blocks_of_kind kind)

let rec visit_block visit (block : Tree.block) =
  List.iter
    (fun (statement : Tree.statement) ->
      visit statement;
      (match statement.kind with
      | Basic (Ghost_assert { condition; _ }) -> visit_formula visit condition
      | Basic (Proof code) -> visit_code visit code
      | While { loop; _ } | For { loop; _ } -> visit_loop visit loop
      | Basic
          ( Assign _ | Call _ | Lend _ | Slice _ | Template _ | Live _ | Dead _ | Assert _ | Echo _
          | Provide _ | Provide_end | Loan_start _ | Loan_end _ | Matched _ )
      | Choose _ | Assert_by_bit_vector _ | Fork _ | Resume _ | Yield _ | Jump _ ->
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
  | Basic (Call { call; _ } | Lend { call; _ } | Slice { call; _ } | Template { call; _ }) ->
      Some call.callee
  | For { iteration = Pull { next; _ }; _ } -> Some next
  | Basic
      ( Assign _ | Live _ | Dead _ | Assert _ | Echo _ | Provide _ | Provide_end | Loan_start _
      | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ )
  | For { iteration = Range _; _ }
  | Choose _ | Assert_by_bit_vector _ | While _ | Fork _ | Resume _ | Yield _ | Jump _ ->
      None

let extract_operand_type : Tree.operand -> Types.ty = function
  | Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } | Constant { type_; _ } -> type_
