open Tree

let choice_blocks = function
  | Cases cases ->
      List.concat_map
        (fun (case : case) -> (case.tests :: Option.to_list case.guard) @ [ case.value ])
        cases
  | Conditional { then_; else_; _ } -> [ then_; else_ ]
  | Connective { right; _ } -> [ right ]

let nested_blocks_of (kind : statement_kind) : block list =
  match kind with
  | Basic (Assign { value = Specification (Quantified { matches; body; _ }); _ }) ->
      [ matches; body ]
  | Assert_by_bit_vector { code; _ } -> [ code ]
  | Choose { choice; _ } -> choice_blocks choice
  | While { condition; body; failed; _ } ->
      [ condition; body; { statements = failed; value = None } ]
  | For { lent; body; _ } ->
      Option.to_list (Option.map (fun (lent : lent_element) -> lent.count) lent) @ [ body ]
  | Fork { branches; _ } -> branches
  | Resume { exits; _ } -> List.map (fun (exit : early_exit) -> exit.resumed) exits
  | Basic _ | Yield _ | Jump _ -> []

let nested_blocks (statement : statement) = nested_blocks_of statement.kind

let operand_place visit = function
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> visit place
  | Constant _ -> ()

let callee_places visit : callee -> unit = function
  | Indirect callee -> operand_place visit callee
  | _ -> ()

let call_places visit (call : call) =
  callee_places visit call.callee;
  List.iter
    (function Passed { value; _ } -> operand_place visit value | Default -> ())
    call.arguments

let iteration_places visit = function
  | Range { start; stop; _ } ->
      operand_place visit start;
      operand_place visit stop
  | Pull { cursor; next } ->
      visit cursor;
      callee_places visit next

let rec yielded_places visit = function
  | Part part -> operand_place visit part
  | Built { fields; _ } ->
      List.iter (fun (_, field) -> Option.iter (yielded_places visit) field) fields

let rvalue_places visit rvalue =
  let operand = operand_place visit in
  let specification = function
    | Result | Yielded -> ()
    | Entry local -> visit { root = Local local; projections = [] }
    | Identical (first, second) ->
        operand first;
        operand second
    | Applied { arguments; _ } -> List.iter operand arguments
    | Method_time method_ -> callee_places visit method_
    | Map entries ->
        List.iter
          (fun (key, value) ->
            operand key;
            operand value)
          entries
    | Quantified { range; _ } -> (
        match range with
        | Over_type _ -> ()
        | Over_range { start; stop; _ } ->
            operand start;
            operand stop
        | Over_collection collection -> operand collection)
  in
  match rvalue with
  | Operand value | Not value | Convert { value; _ } | To_any { value; _ } | Copy value ->
      operand value
  | Operation { operands; _ } | Array operands -> List.iter operand operands
  | Compare { left; right; _ } ->
      operand left;
      operand right
  | Construct { fields; _ } -> List.iter (fun (_, field) -> Option.iter operand field) fields
  | Is_variant { place; _ } -> visit place
  | Lambda { captures; _ } -> List.iter (fun (capture : capture) -> visit capture.place) captures
  | Function_value _ | Value_parameter _ -> ()
  | Specification value -> specification value

let rec iter_places_read visit (block : block) =
  List.iter (fun (statement : statement) -> statement_places visit statement.kind) block.statements;
  Option.iter (operand_place visit) block.value

and statement_places visit (kind : statement_kind) =
  (match kind with
  | Basic (Assign { value; _ }) -> rvalue_places visit value
  | Basic (Call { call; _ } | Lend { call; _ } | Template { call; _ }) -> call_places visit call
  | Basic (Slice { base; call; _ }) ->
      visit base;
      call_places visit call
  | Basic (Assert value | Echo value | Loan_start { borrowed = value; _ })
  | Assert_by_bit_vector { condition = value; _ }
  | Choose { choice = Conditional { condition = value; _ } | Connective { left = value; _ }; _ } ->
      operand_place visit value
  | Basic (Provide { provided; _ }) ->
      List.iter (fun (provided : provided) -> operand_place visit provided.value) provided
  | For { iteration; _ } -> iteration_places visit iteration
  | Yield { part; _ } -> yielded_places visit part
  | Jump (Return returned) -> Option.iter (operand_place visit) returned
  | Jump (Cancel { returned; _ }) ->
      Option.iter (fun (value, _) -> operand_place visit value) returned
  | Jump (Break | Continue | Unreachable | Written_unreachable | Todo)
  | Basic (Live _ | Dead _ | Provide_end | Loan_end _ | Ghost_assert _ | Matched _ | Proof _)
  | Choose { choice = Cases _; _ }
  | While _ | Fork _ | Resume _ ->
      ());
  List.iter (iter_places_read visit) (nested_blocks_of kind)

let rec visit_block visit locals (block : block) =
  List.iter
    (fun (statement : statement) ->
      visit locals statement;
      (match statement.kind with
      | Basic (Ghost_assert { condition; _ }) -> visit_formula visit condition
      | Basic (Proof code) -> visit_code visit code
      | While { loop; _ } | For { loop; _ } -> visit_loop visit loop
      | _ -> ());
      List.iter (visit_block visit locals) (nested_blocks statement))
    block.statements

and visit_formula visit (formula : formula) =
  visit_block visit formula.locals formula.value;
  Array.iter (visit_body visit) formula.lambdas

and visit_loop visit (loop : loop) =
  List.iter
    (function
      | Invariant clause -> visit_formula visit clause
      | Decreases measures -> List.iter (visit_formula visit) measures
      | Cost { bound = Finite; _ } -> ()
      | Cost { bound = Order_of amount | At_most amount | Exactly amount; _ } ->
          visit_formula visit amount)
    loop.clauses

and visit_body visit (body : body) = visit_block visit body.locals body.code

and visit_code visit (code : t) =
  visit_body visit code.body;
  Array.iter (visit_body visit) code.lambdas

let iter_code visit code = visit_code (fun _ statement -> visit statement) code
let iter_formula visit formula = visit_formula (fun _ statement -> visit statement) formula
let iter_code_with_locals = visit_code
let iter_formula_with_locals = visit_formula

let operand_type : operand -> Types.ty = function
  | Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } | Constant { type_; _ } -> type_
