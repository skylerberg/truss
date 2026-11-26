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
              | Convert _ | Copy _ | Function_value _ | Lambda _ | Value_parameter _
              | Parameter_default _
              | Specification
                  (Result | Entry _ | Yielded | Identical _ | Applied _ | Method_cost _ | Map _) );
            _;
          }
      | Call _ | Lend _ | Live _ | Dead _ | Assert _ | Echo _ | Loan_start _ | Loan_end _
      | Ghost_assert _ | Proof _ | Evaluated_assert _ )
  | Yield _
  | Jump (Return _ | Break | Continue | Cancel _ | Unreachable | Written_unreachable | Todo) ->
      []

let rec visit_place visit origin (place : Tree.place) =
  visit origin place;
  List.iter
    (fun (projection : Tree.projection) ->
      match projection with
      | Element { index; _ } -> visit_operand visit index
      | Range { start; stop; _ } ->
          visit_operand visit start;
          Option.iter (visit_operand visit) stop
      | Field _ | Variant_field _ -> ())
    place.projections

and visit_operand visit : Tree.operand -> unit = function
  | Use { place; origin; _ } | Borrow { place; origin; _ } | Take { place; origin; _ } ->
      visit_place visit origin place
  | Immediate _ -> ()

let visit_target visit : Tree.operand Core.target -> unit = function
  | Indirect function_value -> visit_operand visit function_value
  | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> ()

let visit_call visit (call : Tree.call) =
  visit_target visit call.callee.target;
  List.iter (fun (argument : Tree.argument) -> visit_operand visit argument.value) call.arguments

let rec visit_yielded visit : Tree.yielded -> unit = function
  | Part part -> visit_operand visit part
  | Built { fields; _ } ->
      List.iter (fun (_, field) -> Option.iter (visit_yielded visit) field) fields

let visit_rvalue visit origin (rvalue : Tree.rvalue) =
  let visit_operand = visit_operand visit in
  match rvalue with
  | Operand value | Not value | Convert { value; _ } | Copy value -> visit_operand value
  | Operation { operands; _ } | Array operands -> List.iter visit_operand operands
  | Compare { left; right; _ } | Specification (Identical (left, right)) ->
      visit_operand left;
      visit_operand right
  | Construct { fields; _ } -> List.iter (fun (_, field) -> Option.iter visit_operand field) fields
  | Is_variant { place; _ } -> visit_place visit origin place
  | Lambda { captures; _ } ->
      List.iter (fun (capture : Tree.capture) -> visit_place visit origin capture.place) captures
  | Specification (Applied { arguments; _ }) -> List.iter visit_operand arguments
  | Specification (Method_cost { method_; _ }) -> visit_target visit method_
  | Specification (Map entries) ->
      List.iter
        (fun (key, value) ->
          visit_operand key;
          visit_operand value)
        entries
  | Specification (Quantified { range = Over_range { start; stop; _ }; _ }) ->
      visit_operand start;
      visit_operand stop
  | Function_value _ | Value_parameter _ | Parameter_default _
  | Specification (Result | Entry _ | Yielded | Quantified { range = Over_type _; _ }) ->
      ()

let visit_statement_places visit (statement : Tree.statement) =
  let visit_operand = visit_operand visit and visit_place = visit_place visit statement.origin in
  match statement.kind with
  | Basic (Assign { target; value }) ->
      visit_place target;
      visit_rvalue visit statement.origin value
  | Basic (Call { destination; call }) ->
      Option.iter visit_place destination;
      visit_call visit call
  | Basic (Lend { call; _ }) -> visit_call visit call
  | Basic (Assert value | Echo value | Loan_start { borrowed = value; _ })
  | Assert_by_bit_vector { condition = value; _ } ->
      visit_operand value
  | Choose { target; _ } -> visit_place target
  | Provide { target; provided; _ } ->
      visit_place target;
      List.iter (fun (provided : Tree.provided) -> visit_operand provided.value) provided
  | For { iteration; elements; _ } ->
      (match iteration with
      | Range { start; stop; _ } ->
          visit_operand start;
          visit_operand stop
      | Pull { cursor; next; _ } ->
          visit_place cursor;
          visit_target visit next.target);
      Option.iter
        (fun (elements : Tree.elements) ->
          visit_place elements.collection;
          match elements.element with
          | Sequence_element { place; _ } -> visit_place place
          | Lent_by_call _ -> ())
        elements
  | Yield { part; _ } -> visit_yielded visit part
  | Jump (Return returned) -> Option.iter visit_operand returned
  | Jump (Cancel { returned; _ }) -> Option.iter (fun (value, _) -> visit_operand value) returned
  | Jump (Break | Continue | Unreachable | Written_unreachable | Todo)
  | Basic (Live _ | Dead _ | Loan_end _ | Ghost_assert _ | Proof _ | Evaluated_assert _)
  | While _ | Fork _ | Resume _ ->
      ()

let rec visit_block ~on_locals ~on_value visit (block : Tree.block) =
  List.iter
    (fun (statement : Tree.statement) ->
      visit statement;
      (match statement.kind with
      | Basic (Ghost_assert { condition; _ }) -> visit_formula ~on_locals ~on_value visit condition
      | Basic (Proof code | Evaluated_assert code) -> visit_code ~on_locals ~on_value visit code
      | While { loop; _ } | For { loop; _ } -> visit_loop ~on_locals ~on_value visit loop
      | Basic
          ( Assign _ | Call _ | Lend _ | Live _ | Dead _ | Assert _ | Echo _ | Loan_start _
          | Loan_end _ )
      | Choose _ | Assert_by_bit_vector _ | Fork _ | Provide _ | Resume _ | Yield _ | Jump _ ->
          ());
      List.iter (visit_block ~on_locals ~on_value visit) (list_nested_blocks statement))
    block.statements;
  Option.iter on_value block.value

and visit_formula ~on_locals ~on_value visit (formula : Tree.formula) =
  on_locals formula.locals;
  visit_block ~on_locals ~on_value visit formula.value;
  Array.iter (visit_body ~on_locals ~on_value visit) formula.lambdas

and visit_loop ~on_locals ~on_value visit (loop : Tree.loop) =
  List.iter
    (function
      | Tree.Invariant clause -> visit_formula ~on_locals ~on_value visit clause
      | Decreases measures -> List.iter (visit_formula ~on_locals ~on_value visit) measures
      | Cost { bound = Order_of amount | At_most amount | Exactly amount; _ } ->
          visit_formula ~on_locals ~on_value visit amount)
    loop.clauses

and visit_body ~on_locals ~on_value visit (body : Tree.body) =
  on_locals body.locals;
  visit_block ~on_locals ~on_value visit body.code

and visit_code ~on_locals ~on_value visit (code : Tree.t) =
  visit_body ~on_locals ~on_value visit code.body;
  Array.iter (visit_body ~on_locals ~on_value visit) code.lambdas

let iter_code visit code = visit_code ~on_locals:ignore ~on_value:ignore visit code
let iter_formula visit formula = visit_formula ~on_locals:ignore ~on_value:ignore visit formula

let iter_places visit code =
  visit_code ~on_locals:ignore ~on_value:(visit_operand visit) (visit_statement_places visit) code

let iter_formula_places visit formula =
  visit_formula ~on_locals:ignore ~on_value:(visit_operand visit) (visit_statement_places visit)
    formula

let iter_locals visit code = visit_code ~on_locals:(Array.iter visit) ~on_value:ignore ignore code

let iter_formula_locals visit formula =
  visit_formula ~on_locals:(Array.iter visit) ~on_value:ignore ignore formula

let list_evaluated_asserts (code : Tree.t) =
  let evaluated = ref [] in
  iter_code
    (fun statement ->
      match statement.kind with
      | Basic (Evaluated_assert asserted) ->
          evaluated := (Core_walk.locate_origin statement.origin, asserted) :: !evaluated
      | _ -> ())
    code;
  List.rev !evaluated

let rec list_leading_fields : Tree.projection list -> string list = function
  | Field field :: projections -> field :: list_leading_fields projections
  | (Variant_field _ | Element _ | Range _) :: _ | [] -> []

let append_fields (place : Tree.place) fields =
  { place with projections = place.projections @ List.map (fun field -> Tree.Field field) fields }

let list_mut_provided_places (provided : Tree.provided list) =
  List.filter_map
    (fun (implementation : Tree.provided) ->
      match (implementation.mode, implementation.value) with
      | Language.Mode.Mut, Borrow { place; _ } -> Some place
      | Mut, (Use _ | Take _ | Immediate _) | (Read | Own), _ -> None)
    provided

type changed = { origin : Core.origin; place : Tree.place; is_elements : bool }

let classify_changed_part (changed : changed) =
  let fields = list_leading_fields changed.place.projections in
  ( fields,
    match List.drop (List.length fields) changed.place.projections with
    | [] -> changed.is_elements
    | (Element _ | Range _) :: _ -> true
    | (Field _ | Variant_field _) :: _ -> false )

let list_changed_places ~list_modified (blocks : Tree.block list) =
  let changed = ref [] in
  let note origin place = changed := { origin; place; is_elements = false } :: !changed in
  let note_passed origin callee position place =
    match list_modified callee position with
    | Some modified ->
        List.iter
          (fun (part : Types.modified) ->
            changed :=
              {
                origin;
                place = append_fields place part.field_path;
                is_elements = part.is_elements;
              }
              :: !changed)
          modified
    | None -> note origin place
  in
  let note_arguments origin (call : Tree.call) =
    List.iteri
      (fun position (argument : Tree.argument) ->
        match argument with
        | { mode = Language.Mode.Mut; value = Borrow { place; _ } | Use { place; _ }; _ } ->
            note_passed origin call.callee position place
        | { mode = Mut; value = Take _ | Immediate _; _ } | { mode = Read | Own; _ } -> ())
      call.arguments
  in
  let rec note_lent origin : Tree.yielded -> unit = function
    | Part (Borrow { place; _ }) -> note origin place
    | Part _ -> ()
    | Built { fields; _ } ->
        List.iter (fun (_, field) -> Option.iter (note_lent origin) field) fields
  in
  let note_local origin local = note origin { Tree.root = Local local; projections = [] } in
  let rec visit (block : Tree.block) =
    List.iter
      (fun (statement : Tree.statement) ->
        let origin = statement.origin in
        (match statement.kind with
        | Basic (Assign { target; value = Operand (Borrow { place; mode = Language.Mode.Mut; _ }) })
          ->
            note origin target;
            note origin place
        | Basic (Assign { target; _ }) | Choose { target; _ } -> note origin target
        | Basic (Call { destination; call }) ->
            Option.iter (note origin) destination;
            note_arguments origin call
        | Basic (Lend { call; _ }) -> note_arguments origin call
        | Provide { target; provided; _ } ->
            note origin target;
            List.iter (note origin) (list_mut_provided_places provided)
        | For { iteration = Pull { cursor; next; _ }; _ } -> note_passed origin next 0 cursor
        | Yield { mode = Language.Mode.Mut; part } -> note_lent origin part
        | Jump (Cancel { winner; returned; _ }) ->
            note_local origin winner;
            Option.iter (fun (_, local) -> note_local origin local) returned
        | Basic
            ( Live _ | Dead _ | Assert _ | Echo _ | Loan_start _ | Loan_end _ | Ghost_assert _
            | Proof _ | Evaluated_assert _ )
        | Assert_by_bit_vector _ | While _ | Fork _ | Resume _
        | For { iteration = Range _; _ }
        | Yield { mode = Read | Own; _ }
        | Jump (Return _ | Break | Continue | Unreachable | Written_unreachable | Todo) ->
            ());
        List.iter visit (list_nested_blocks statement))
      block.statements
  in
  List.iter visit blocks;
  List.rev !changed

let find_callee (statement : Tree.statement) : Tree.callee option =
  match statement.kind with
  | Basic (Call { call; _ } | Lend { call; _ }) -> Some call.callee
  | For { iteration = Pull { next; _ }; _ } -> Some next
  | Basic
      ( Assign _ | Live _ | Dead _ | Assert _ | Echo _ | Loan_start _ | Loan_end _ | Ghost_assert _
      | Proof _ | Evaluated_assert _ )
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
