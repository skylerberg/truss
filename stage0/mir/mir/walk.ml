open Tree

let nested_blocks (statement : statement) : block list =
  match statement.kind with
  | Assign { value = Specification (Quantified { matches; body; _ }); _ } -> [ matches; body ]
  | Assign { value = Cases cases; _ } ->
      List.concat_map
        (fun (case : case) -> (case.tests :: Option.to_list case.guard) @ [ case.value ])
        cases
  | Assign { value = Conditional { then_; else_; _ }; _ } -> [ then_; else_ ]
  | Assign { value = Connective { right; _ }; _ } -> [ right ]
  | Assert { bit_vector = Some { code; _ }; _ } -> [ code ]
  | While { condition; body; failed; _ } ->
      [ condition; body; { statements = failed; value = None } ]
  | For { lent; body; _ } ->
      Option.to_list (Option.map (fun (lent : lent_element) -> lent.count) lent) @ [ body ]
  | Fork { branches; _ } -> branches
  | Resume { exits; _ } -> List.map (fun (exit : early_exit) -> exit.resumed) exits
  | Assign _ | Call _ | Lend _ | Slice _ | Template _ | Live _ | Dead _ | Assert _ | Echo _
  | Provide _ | Provide_end | Loan_start _ | Loan_end _ | Ghost_assert _ | Matched _ | Proof _
  | Yield _ | Jump _ ->
      []

let rec iter_places_read visit (block : block) =
  let operand = function
    | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> visit place
    | Constant _ -> ()
  in
  let callee : callee -> unit = function Indirect callee -> operand callee | _ -> () in
  let call (call : call) =
    callee call.callee;
    List.iter (function Passed { value; _ } -> operand value | Default -> ()) call.arguments
  in
  let specification = function
    | Result | Yielded -> ()
    | Entry local -> visit { root = Local local; projections = [] }
    | Identical (first, second) ->
        operand first;
        operand second
    | Applied { arguments; _ } -> List.iter operand arguments
    | Method_time method_ -> callee method_
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
  let rvalue = function
    | Cases _ -> ()
    | Conditional { condition; _ } -> operand condition
    | Connective { left; _ } -> operand left
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
  in
  let rec yielded = function
    | Part part -> operand part
    | Built { fields; _ } -> List.iter (fun (_, field) -> Option.iter yielded field) fields
  in
  List.iter
    (fun (statement : statement) ->
      (match statement.kind with
      | Assign { value; _ } -> rvalue value
      | Call { call = called; _ } | Lend { call = called; _ } | Template { call = called; _ } ->
          call called
      | Slice { base; call = called; _ } ->
          visit base;
          call called
      | Assert { condition = value; _ } | Echo value | Loan_start { borrowed = value; _ } ->
          operand value
      | Provide { provided; _ } ->
          List.iter (fun (provided : provided) -> operand provided.value) provided
      | For { iteration = Range { start; stop; _ }; _ } ->
          operand start;
          operand stop
      | For { iteration = Pull { cursor; next }; _ } ->
          visit cursor;
          callee next
      | Yield { part; _ } -> yielded part
      | Jump (Return returned) -> Option.iter operand returned
      | Jump (Cancel { returned; _ }) -> Option.iter (fun (value, _) -> operand value) returned
      | Jump (Break | Continue | Unreachable | Written_unreachable | Todo)
      | Live _ | Dead _ | Provide_end | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ | While _
      | Fork _ | Resume _ ->
          ());
      List.iter (iter_places_read visit) (nested_blocks statement))
    block.statements;
  Option.iter operand block.value

let rec visit_block visit (block : block) =
  List.iter
    (fun (statement : statement) ->
      visit statement;
      (match statement.kind with
      | Ghost_assert { condition; _ } -> visit_formula visit condition
      | Proof code -> visit_code visit code
      | While { loop; _ } | For { loop; _ } -> visit_loop visit loop
      | _ -> ());
      List.iter (visit_block visit) (nested_blocks statement))
    block.statements

and visit_formula visit (formula : formula) =
  visit_block visit formula.value;
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

and visit_body visit (body : body) = visit_block visit body.code

and visit_code visit (code : t) =
  visit_body visit code.body;
  Array.iter (visit_body visit) code.lambdas

let iter_code visit code = visit_code visit code
let iter_formula visit formula = visit_formula visit formula

let operand_type : operand -> Types.ty = function
  | Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } | Constant { type_; _ } -> type_
