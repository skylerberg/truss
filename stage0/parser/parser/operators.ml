open Syntax

type group =
  | Arithmetic
  | Shift
  | Bitwise of binary
  | Range_group
  | Comparison
  | And_group
  | Or_group
  | Implies_group
  | Lowest

let binary_group = function
  | Multiply | Divide | Remainder | Add | Subtract -> Arithmetic
  | Shift_left | Shift_right -> Shift
  | (Bit_and | Bit_xor | Bit_or) as operator -> Bitwise operator
  | Equal | Not_equal | Less | Less_equal | Greater | Greater_equal -> Comparison
  | And -> And_group
  | Or -> Or_group
  | Implies -> Implies_group

let group (value : expression) =
  match value.kind with
  | Binary { operator; _ } -> Some (binary_group operator)
  | Is _ -> Some Comparison
  | Range _ -> Some Range_group
  | Quantified _ | Echo _ | Return _ -> Some Lowest
  | _ -> None

let operands (value : expression) =
  match value.kind with
  | Binary { left; right; _ } -> Some (left.span, right.span)
  | Is { value; pattern; _ } -> Some (value.span, pattern.span)
  | Range { start = Some start; stop = Some stop; _ } -> Some (start.span, stop.span)
  | _ -> None

let operator_span (value : expression) =
  match value.kind with
  | Binary { operator_span; _ } | Is { operator_span; _ } | Range { operator_span; _ } ->
      operator_span
  | _ -> value.span

let level language operator =
  match (language, operator) with
  | `Truss, operator -> Parse_expression.binary_level operator
  | _, (And | Or | Implies) -> 0
  | `C, (Multiply | Divide | Remainder) -> 10
  | `C, (Add | Subtract) -> 9
  | `C, (Shift_left | Shift_right) -> 8
  | `C, (Less | Less_equal | Greater | Greater_equal) -> 7
  | `C, (Equal | Not_equal) -> 6
  | `C, Bit_and -> 5
  | `C, Bit_xor -> 4
  | `C, Bit_or -> 3
  | `Go, (Multiply | Divide | Remainder | Shift_left | Shift_right | Bit_and) -> 10
  | `Go, (Add | Subtract | Bit_or | Bit_xor) -> 9
  | `Go, (Equal | Not_equal | Less | Less_equal | Greater | Greater_equal) -> 4
  | `Swift, (Shift_left | Shift_right) -> 11
  | `Swift, (Multiply | Divide | Remainder | Bit_and) -> 10
  | `Swift, (Add | Subtract | Bit_or | Bit_xor) -> 9
  | `Swift, (Equal | Not_equal | Less | Less_equal | Greater | Greater_equal) -> 4

let applies_first language ~first ~second = level language first >= level language second

type grouping = Left_first | Right_first

let report cursor (span : Source.Definition_span.t) message fixes =
  Cursor.report cursor Needs_parentheses (Cursor.absolute cursor span) message
    ~fixes:(List.map (fun (title, edits) -> Diagnostic.fix title edits) fixes)

let fix cursor ~fallback (whole : Source.Definition_span.t) edits =
  let insertions =
    List.map (fun (edit : Source.span Diagnostic.edit) -> (edit.span.start, edit.replacement)) edits
  in
  match Cursor.spelling cursor ~insertions (Cursor.absolute cursor whole) with
  | Some fixed -> (Printf.sprintf "Write `%s`" fixed, edits)
  | None -> (fallback, edits)

let parentheses cursor (first : Source.Definition_span.t) (last : Source.Definition_span.t) =
  [
    Diagnostic.insert (Source.zero_width (Cursor.absolute cursor first).start) "(";
    Diagnostic.insert (Source.zero_width (Cursor.absolute cursor last).stop) ")";
  ]

let is_name_or_literal (value : expression) =
  match value.kind with
  | Name _ | Integer _ | Float _ | String _ | True | False -> true
  | _ -> false

type problem = Lowest_operand | Chained of string | Mixed of string | Mixed_bitwise

let problem parent child ~right (operand : expression) =
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

let grouping_fix cursor ?context ~(whole : expression) ~(operand : expression)
    (first_operator, second_operator, third_operator) ~parsed grouping =
  let edits =
    match grouping with
    | Left_first -> parentheses cursor first_operator second_operator
    | Right_first -> parentheses cursor second_operator third_operator
  in
  let last = if grouping = parsed then group whole else group operand in
  let wrap =
    match (context, last) with
    | Some (outer, right), Some last -> problem outer last ~right whole <> None
    | _ -> false
  in
  let fallback =
    match grouping with
    | Left_first -> "Group the first two operands"
    | Right_first -> "Group the last two operands"
  in
  fix cursor ~fallback whole.span
    (if wrap then edits @ parentheses cursor whole.span whole.span else edits)

let report_problem cursor ?context (whole : expression) (operand : expression) ~right problem =
  let rec first_of_chain (value : expression) =
    match value.kind with
    | Binary { left; _ } when Option.equal ( = ) (group left) (group value) -> first_of_chain left
    | _ -> Option.map fst (operands value)
  in
  let pieces =
    match (operands whole, operands operand) with
    | Some (_, third_operator), Some (first_operator, second_operator) when not right ->
        Some (first_operator, second_operator, third_operator)
    | Some (first_operator, _), Some (_, third_operator) when right ->
        Option.map
          (fun second_operator -> (first_operator, second_operator, third_operator))
          (first_of_chain operand)
    | _ -> None
  in
  let parsed = if right then Right_first else Left_first in
  let other = if right then Left_first else Right_first in
  let fix_for pieces = grouping_fix cursor ?context ~whole ~operand pieces ~parsed in
  let groupings =
    match operand.kind with Is _ when not right -> [ parsed ] | _ -> [ parsed; other ]
  in
  let both () =
    match pieces with Some pieces -> List.map (fix_for pieces) groupings | None -> []
  in
  match problem with
  | Lowest_operand ->
      report cursor operand.span
        "This takes everything after it, so as an operand it must be in parentheses, except that \
         `forall` and `exists` may be the last operand of `&&`, `||`, or `==>`."
        [
          fix cursor ~fallback:"Add parentheses" operand.span
            (parentheses cursor operand.span operand.span);
        ]
  | Mixed message -> report cursor (operator_span whole) message (both ())
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
            let ordered = if List.mem other groupings then [ parsed; other ] else [ parsed ] in
            List.map (fix_for pieces) ordered
        | _ -> both ()
      in
      report cursor (operator_span whole)
        "Shifts and bitwise operators combine only with themselves; add parentheses." fixes
  | Chained message ->
      let fixes =
        match (whole.kind, operand.kind) with
        | Binary { operator = Implies; _ }, _ -> List.rev (both ())
        | Binary _, Binary { right = middle; _ } when (not right) && is_name_or_literal middle -> (
            let middle_span = Cursor.absolute cursor middle.span in
            match Cursor.spelling cursor middle_span with
            | Some middle_spelling ->
                [
                  fix cursor ~fallback:"Join the comparisons with `&&`" whole.span
                    [
                      Diagnostic.insert
                        (Source.zero_width middle_span.stop)
                        (" && " ^ middle_spelling);
                    ];
                ]
            | None -> [])
        | _ -> []
      in
      report cursor (operator_span whole) message fixes

let rec expression ?context cursor (value : expression) =
  let operand parent ~right (operand : expression) =
    expression ~context:(parent, right) cursor operand;
    match Option.bind (group operand) (fun child -> problem parent child ~right operand) with
    | Some problem -> report_problem cursor ?context value operand ~right problem
    | None -> ()
  in
  match value.kind with
  | Binary { operator; left; right; _ } ->
      let group = binary_group operator in
      operand group ~right:false left;
      operand group ~right:true right
  | Is { value = left; operator_span; _ } ->
      (match left.kind with
      | Prefix (Not, _) ->
          let whole = Cursor.absolute cursor value.span in
          report cursor operator_span
            "`!` and `is` have no relative precedence. Add parentheses to say whether the test or \
             the value is negated."
            [
              fix cursor ~fallback:"Negate the test" value.span
                [
                  Diagnostic.insert (Source.zero_width (whole.start + 1)) "(";
                  Diagnostic.insert (Source.zero_width whole.stop) ")";
                ];
              fix cursor ~fallback:"Negate the value" value.span
                (parentheses cursor left.span left.span);
            ]
      | _ -> ());
      operand Comparison ~right:false left
  | Range { start; stop; _ } ->
      Option.iter (operand Range_group ~right:false) start;
      Option.iter (operand Range_group ~right:true) stop
  | Prefix (_, inner) -> (
      expression cursor inner;
      match group inner with
      | Some Lowest -> report_problem cursor value inner ~right:true Lowest_operand
      | _ -> ())
  | _ -> Syntax_walk.children (fun inner -> expression cursor inner) value

let definition cursor definition =
  Syntax_walk.definition (fun value -> expression cursor value) definition
