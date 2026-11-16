type group =
  | Arithmetic
  | Shift
  | Bitwise of Syntax.bitwise
  | Range_group
  | Comparison
  | And_group
  | Or_group
  | Implies_group
  | Lowest

let classify_binary : Syntax.binary -> group = function
  | Operation (Arithmetic _) -> Arithmetic
  | Operation (Shift _) -> Shift
  | Operation (Bitwise bitwise) -> Bitwise bitwise
  | Comparison _ -> Comparison
  | Connective And -> And_group
  | Connective Or -> Or_group
  | Connective Implies -> Implies_group

let group (value : Syntax.expression) =
  match value.kind with
  | Binary { operator; _ } -> Some (classify_binary operator)
  | Is _ -> Some Comparison
  | Range _ -> Some Range_group
  | Quantified _ | Echo _ | Return _ -> Some Lowest
  | _ -> None

let find_operands (value : Syntax.expression) =
  match value.kind with
  | Binary { left; right; _ } -> Some (left.id, right.id)
  | Is { value; pattern; _ } -> Some (value.id, pattern.id)
  | Range { start = Some start; stop = Some stop; _ } -> Some (start.id, stop.id)
  | _ -> None

let extract_operator_id (value : Syntax.expression) =
  match value.kind with
  | Binary { operator_id; _ } | Is { operator_id; _ } | Range { operator_id; _ } -> operator_id
  | _ -> value.id

let rank_operator language (operator : Syntax.binary) =
  match (language, operator) with
  | `Truss, operator -> Parse_expression.rank_binary operator
  | _, Connective _ -> 0
  | `C, Operation (Arithmetic (Multiply | Divide | Remainder)) -> 10
  | `C, Operation (Arithmetic (Add | Subtract)) -> 9
  | `C, Operation (Shift _) -> 8
  | `C, Comparison (Less | Less_equal | Greater | Greater_equal) -> 7
  | `C, Comparison (Equal | Not_equal) -> 6
  | `C, Operation (Bitwise Bit_and) -> 5
  | `C, Operation (Bitwise Bit_xor) -> 4
  | `C, Operation (Bitwise Bit_or) -> 3
  | `Go, Operation (Arithmetic (Multiply | Divide | Remainder) | Shift _ | Bitwise Bit_and) -> 10
  | `Go, Operation (Arithmetic (Add | Subtract) | Bitwise (Bit_or | Bit_xor)) -> 9
  | `Go, Comparison _ -> 4
  | `Swift, Operation (Shift _) -> 11
  | `Swift, Operation (Arithmetic (Multiply | Divide | Remainder) | Bitwise Bit_and) -> 10
  | `Swift, Operation (Arithmetic (Add | Subtract) | Bitwise (Bit_or | Bit_xor)) -> 9
  | `Swift, Comparison _ -> 4

let applies_first language ~first ~second =
  rank_operator language first >= rank_operator language second

type grouping = Left_first | Right_first

let report cursor id message fixes =
  Cursor.report cursor Needs_parentheses (Cursor.read_file_span cursor id) message
    ~fixes:(List.map (fun (title, edits) -> Diagnostic.fix title edits) fixes)

let fix cursor ~fallback whole edits =
  let insertions =
    List.map (fun (edit : Source.span Diagnostic.edit) -> (edit.span.start, edit.replacement)) edits
  in
  match Cursor.spell cursor ~insertions (Cursor.read_file_span cursor whole) with
  | Some fixed -> (Printf.sprintf "Write `%s`" fixed, edits)
  | None -> (fallback, edits)

let make_parentheses cursor first last =
  [
    Diagnostic.insert (Source.zero_width (Cursor.read_file_span cursor first).start) "(";
    Diagnostic.insert (Source.zero_width (Cursor.read_file_span cursor last).stop) ")";
  ]

let is_name_or_literal (value : Syntax.expression) =
  match value.kind with
  | Name _ | Integer _ | Float _ | String _ | True | False -> true
  | _ -> false

type problem = Lowest_operand | Chained of string | Mixed of string | Mixed_bitwise

let find_problem parent child ~right (operand : Syntax.expression) =
  let bitwise = function Shift | Bitwise _ -> true | _ -> false in
  match (parent, child) with
  | (And_group | Or_group | Implies_group), Lowest
    when right && match operand.kind with Quantified _ -> true | _ -> false ->
      None
  | _, Lowest -> Some Lowest_operand
  | Arithmetic, Arithmetic | Shift, Shift | And_group, And_group | Or_group, Or_group -> None
  | Bitwise left_item, Bitwise right_item when left_item = right_item -> None
  | (Range_group | Comparison | And_group | Or_group | Implies_group), Arithmetic -> None
  | (Comparison | And_group | Or_group | Implies_group), Range_group -> None
  | (And_group | Or_group | Implies_group), Comparison -> None
  | Implies_group, (And_group | Or_group) -> None
  | Range_group, Range_group -> Some (Chained "Ranges do not chain.")
  | Comparison, Comparison -> Some (Chained "Comparisons do not chain.")
  | Implies_group, Implies_group -> Some (Chained "`==>` does not chain.")
  | And_group, Or_group | Or_group, And_group ->
      Some (Mixed "`&&` and `||` cannot be mixed without parentheses.")
  | _ when bitwise parent || bitwise child -> Some Mixed_bitwise
  | _ -> Some (Mixed "These operators need parentheses to say which applies first.")

let wrap_edits cursor ?context (whole : Syntax.expression) last edits =
  match (context, last) with
  | Some (outer, whole_is_right), Some last
    when find_problem outer last ~right:whole_is_right whole <> None ->
      edits @ make_parentheses cursor whole.id whole.id
  | _ -> edits

let make_grouping_fix cursor ?context ~(whole : Syntax.expression) ~(operand : Syntax.expression)
    (first_operator, second_operator, third_operator) ~parsed grouping =
  let edits =
    match grouping with
    | Left_first -> make_parentheses cursor first_operator second_operator
    | Right_first -> make_parentheses cursor second_operator third_operator
  in
  let last = if grouping = parsed then group whole else group operand in
  let fallback =
    match grouping with
    | Left_first -> "Group the first two operands"
    | Right_first -> "Group the last two operands"
  in
  fix cursor ~fallback whole.id (wrap_edits cursor ?context whole last edits)

let rec find_first_operand (value : Syntax.expression) =
  match value.kind with
  | Binary { left; _ } when Option.equal ( = ) (group left) (group value) -> find_first_operand left
  | Binary { left; _ } -> Some left
  | Is { value; _ } -> Some value
  | Range { start = Some start; stop = Some _; _ } -> Some start
  | _ -> None

let find_last_operand (value : Syntax.expression) =
  match value.kind with
  | Binary { right; _ } -> Some right
  | Range { start = Some _; stop = Some stop; _ } -> Some stop
  | _ -> None

let report_problem cursor ?context (whole : Syntax.expression) (operand : Syntax.expression) ~right
    problem =
  let pieces =
    match (find_operands whole, find_operands operand) with
    | Some (_, third_operator), Some (first_operator, second_operator) when not right ->
        Some (first_operator, second_operator, third_operator)
    | Some (first_operator, _), Some (_, third_operator) when right ->
        Option.map
          (fun second_operator -> (first_operator, second_operator, third_operator))
          (Option.map (fun (first : Syntax.expression) -> first.id) (find_first_operand operand))
    | _ -> None
  in
  let parsed = if right then Right_first else Left_first in
  let other = if right then Left_first else Right_first in
  let fix_for pieces = make_grouping_fix cursor ?context ~whole ~operand pieces ~parsed in
  let regroups_cleanly grouping =
    grouping = parsed
    ||
    match
      (group whole, if right then find_first_operand operand else find_last_operand operand)
    with
    | Some outer, Some (middle : Syntax.expression) -> (
        match group middle with
        | Some inner -> find_problem outer inner ~right middle = None
        | None -> true)
    | _ -> true
  in
  let groupings =
    List.filter regroups_cleanly
      (match operand.kind with Is _ when not right -> [ parsed ] | _ -> [ parsed; other ])
  in
  let both () =
    match pieces with Some pieces -> List.map (fix_for pieces) groupings | None -> []
  in
  match problem with
  | Lowest_operand ->
      report cursor operand.id
        "This takes everything after it, so as an operand it must be in parentheses, except that \
         `forall` and `exists` may be the last operand of `&&`, `||`, or `==>`."
        [
          fix cursor ~fallback:"Add parentheses" operand.id
            (make_parentheses cursor operand.id operand.id);
        ]
  | Mixed message -> report cursor (extract_operator_id whole) message (both ())
  | Mixed_bitwise ->
      let fixes =
        match (whole.kind, operand.kind, pieces) with
        | Binary { operator = outer; _ }, Binary { operator = inner; _ }, Some pieces ->
            let first, second = if right then (outer, inner) else (inner, outer) in
            let groupings =
              List.map
                (fun language ->
                  if applies_first language ~first ~second then Left_first else Right_first)
                [ `Truss; `C; `Go; `Swift ]
            in
            let ordered =
              List.filter regroups_cleanly
                (if List.mem other groupings then [ parsed; other ] else [ parsed ])
            in
            List.map (fix_for pieces) ordered
        | _ -> both ()
      in
      report cursor (extract_operator_id whole)
        "Shifts and bitwise operators combine only with themselves; add parentheses." fixes
  | Chained message ->
      let fixes =
        match (whole.kind, operand.kind) with
        | Binary { operator = Connective Implies; _ }, _ -> List.rev (both ())
        | Binary _, Binary { right = middle; _ } when (not right) && is_name_or_literal middle -> (
            let middle_span = Cursor.read_file_span cursor middle.id in
            match Cursor.spell cursor middle_span with
            | Some middle_spelling ->
                [
                  fix cursor ~fallback:"Join the comparisons with `&&`" whole.id
                    (wrap_edits cursor ?context whole (Some And_group)
                       [
                         Diagnostic.insert
                           (Source.zero_width middle_span.stop)
                           (" && " ^ middle_spelling);
                       ]);
                ]
            | None -> [])
        | _ -> []
      in
      report cursor (extract_operator_id whole) message fixes

let rec check_expression_with_context ?context cursor (value : Syntax.expression) =
  let operand parent ~right (operand : Syntax.expression) =
    check_expression_with_context ~context:(parent, right) cursor operand;
    match Option.bind (group operand) (fun child -> find_problem parent child ~right operand) with
    | Some problem -> report_problem cursor ?context value operand ~right problem
    | None -> ()
  in
  match value.kind with
  | Binary { operator; left; right; _ } ->
      let group = classify_binary operator in
      operand group ~right:false left;
      operand group ~right:true right
  | Is { value = left; operator_id; _ } ->
      (match left.kind with
      | Prefix (Not, _) ->
          let whole = Cursor.read_file_span cursor value.id in
          report cursor operator_id
            "`!` and `is` have no relative precedence. Add parentheses to say whether the test or \
             the value is negated."
            [
              fix cursor ~fallback:"Negate the test" value.id
                [
                  Diagnostic.insert (Source.zero_width (whole.start + 1)) "(";
                  Diagnostic.insert (Source.zero_width whole.stop) ")";
                ];
              fix cursor ~fallback:"Negate the value" value.id
                (make_parentheses cursor left.id left.id);
            ]
      | _ -> ());
      operand Comparison ~right:false left
  | Range { start; stop; _ } ->
      Option.iter (operand Range_group ~right:false) start;
      Option.iter (operand Range_group ~right:true) stop
  | Prefix (_, inner) -> (
      check_expression_with_context cursor inner;
      match group inner with
      | Some Lowest -> report_problem cursor value inner ~right:true Lowest_operand
      | _ -> ())
  | _ -> Syntax_walk.visit_children (fun inner -> check_expression_with_context cursor inner) value

let check_expression cursor value = check_expression_with_context cursor value

let check_definition cursor definition =
  Syntax_walk.visit_definition (check_expression cursor) definition
