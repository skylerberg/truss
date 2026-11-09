(* The combinations of operators that Truss's partial order of precedence
   leaves out. See PARSER.md, "Precedence and combinations that need
   parentheses".

   The parser builds every expression with a total order. This walk then
   checks each operation against its operands, and reports a combination
   that needs parentheses with the whole expression quoted in its fixes.
   When the readings of other languages disagree, each is a separate fix,
   the parser's own reading first, so an agent picks the one it meant
   instead of trusting a table it may misremember. Every fix inserts only
   parentheses, except the one for a chained comparison. *)

open Syntax

type group =
  | Arithmetic
  | Shift
  | Bitwise of binary  (** [&], [^], and [|] each combine only with themselves. *)
  | Range_group
  | Comparison
  | And_group
  | Or_group
  | Implies_group
  | Lowest  (** [echo], [return], [forall], and [exists] take everything after them. *)

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

(* The two operands of an operation, as spans: the pattern of an [is] is its
   right operand. A range without both ends has none. *)
let operands (value : expression) =
  match value.kind with
  | Binary { left; right; _ } -> Some (left.span, right.span)
  | Is { value; pattern; _ } -> Some (value.span, pattern.span)
  | Range { start = Some start; stop = Some stop; _ } -> Some (start.span, stop.span)
  | _ -> None

(* Where an operation's operator is, which is where an error about it
   points. *)
let operator_span (value : expression) =
  match value.kind with
  | Binary { operator_span; _ } | Is { operator_span; _ } | Range { operator_span; _ } ->
      operator_span
  | _ -> value.span

(* How tightly Rust, C, Go, and Swift bind the operators Truss shares with
   them; higher binds tighter. Truss's total order is Rust's. *)
let level language operator =
  match (language, operator) with
  | _, (And | Or | Implies) -> 0
  | `Rust, (Multiply | Divide | Remainder) -> 10
  | `Rust, (Add | Subtract) -> 9
  | `Rust, (Shift_left | Shift_right) -> 8
  | `Rust, Bit_and -> 7
  | `Rust, Bit_xor -> 6
  | `Rust, Bit_or -> 5
  | `Rust, (Equal | Not_equal | Less | Less_equal | Greater | Greater_equal) -> 4
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

(* In [x first y second z], whether a language applies [first] first, giving
   [(x first y) second z]. Equal levels associate to the left. *)
let applies_first language ~first ~second = level language first >= level language second

type reading = Left_first | Right_first

let report cursor (span : span) message fixes =
  Cursor.report cursor Needs_parentheses (Cursor.absolute cursor span) message
    ~fixes:(List.map (fun (title, edits) -> Diagnostic.fix title edits) fixes)

(* A fix, titled with the whole expression as it reads after the fix. *)
let fix cursor (whole : span) edits =
  let whole_source = Cursor.absolute cursor whole in
  let shifted =
    List.map
      (fun (edit : Diagnostic.edit) ->
        {
          edit with
          span =
            Source.span (edit.span.start - whole_source.start) (edit.span.stop - whole_source.start);
        })
      edits
  in
  ( Printf.sprintf "Write `%s`"
      (Diagnostic.apply_fix (Cursor.text cursor whole_source) (Diagnostic.fix "" shifted)),
    edits )

let parentheses cursor (first : span) (last : span) =
  [
    Diagnostic.insert (Cursor.absolute cursor first).start "(";
    Diagnostic.insert (Cursor.absolute cursor last).stop ")";
  ]

let is_name_or_literal (value : expression) =
  match value.kind with
  | Name _ | Integer _ | Float _ | String _ | True | False -> true
  | _ -> false

(* What is wrong with an operand of a group, if anything. *)
type problem = Lowest_operand | Chained of string | Mixed of string | Mixed_bitwise

let problem parent child ~right (operand : expression) =
  let bitwise = function Shift | Bitwise _ -> true | _ -> false in
  match (parent, child) with
  | (And_group | Or_group | Implies_group), Lowest
    when right && match operand.kind with Quantified _ -> true | _ -> false ->
      None
  | _, Lowest -> Some Lowest_operand
  | Arithmetic, Arithmetic | Shift, Shift | And_group, And_group | Or_group, Or_group -> None
  | Bitwise a, Bitwise b when a = b -> None
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

(* The fix that gives [x _ y _ z] one reading. A reading that changes which
   operator applies last, such as [a & (b == c)] for [a & b == c], may give
   an operator that the one around the whole expression, its [context],
   cannot take as an operand, and then the fix puts the whole in
   parentheses too. *)
let reading_fix cursor ?context ~(whole : expression) ~(operand : expression) (x, y, z) ~parsed
    reading =
  let edits =
    match reading with
    | Left_first -> parentheses cursor x y
    | Right_first -> parentheses cursor y z
  in
  let last = if reading = parsed then group whole else group operand in
  let wrap =
    match (context, last) with
    | Some (outer, right), Some last -> problem outer last ~right whole <> None
    | _ -> false
  in
  fix cursor whole.span (if wrap then edits @ parentheses cursor whole.span whole.span else edits)

(* Reports the combination of [whole] with its operand [operand]. [context]
   is the operator around [whole], if any, and whether [whole] is its right
   operand. *)
let report_problem cursor ?context (whole : expression) (operand : expression) ~right problem =
  (* [x _ y _ z], where [y] is the operand right next to [whole]'s operator.
     On the right, that is the first operand of the chain [operand] starts,
     [b] in [a & b + c + d]; on the left, a chain associates to the left, so
     it is [operand]'s right operand. *)
  let rec first_of_chain (value : expression) =
    match value.kind with
    | Binary { left; _ } when Option.equal ( = ) (group left) (group value) -> first_of_chain left
    | _ -> Option.map fst (operands value)
  in
  let pieces =
    match (operands whole, operands operand) with
    | Some (_, z), Some (x, y) when not right -> Some (x, y, z)
    | Some (x, _), Some (_, z) when right ->
        Option.map (fun y -> (x, y, z)) (first_of_chain operand)
    | _ -> None
  in
  (* The parser's reading, and the other one. *)
  let parsed = if right then Right_first else Left_first in
  let other = if right then Left_first else Right_first in
  let reading_of pieces = reading_fix cursor ?context ~whole ~operand pieces ~parsed in
  (* In [x is P & z], the other reading would put [& z] inside the pattern,
     which has no grouping parentheses. *)
  let other_possible = match operand.kind with Is _ -> right | _ -> true in
  let both () =
    match pieces with
    | Some pieces when other_possible -> List.map (reading_of pieces) [ parsed; other ]
    | Some pieces -> [ reading_of pieces parsed ]
    | None -> []
  in
  match problem with
  | Lowest_operand ->
      report cursor operand.span
        "This takes everything after it, so as an operand it must be in parentheses, except that \
         `forall` and `exists` may be the last operand of `&&`, `||`, or `==>`."
        [ fix cursor operand.span (parentheses cursor operand.span operand.span) ]
  | Mixed message -> report cursor (operator_span whole) message (both ())
  | Mixed_bitwise ->
      let fixes =
        match (whole.kind, operand.kind, pieces) with
        | Binary { operator = outer; _ }, Binary { operator = inner; _ }, Some pieces ->
            let first, second = if right then (outer, inner) else (inner, outer) in
            let readings =
              List.map
                (fun language ->
                  if applies_first language ~first ~second then Left_first else Right_first)
                [ `Rust; `C; `Go; `Swift ]
            in
            (* Rust's reading is the parser's. *)
            let ordered = if List.mem other readings then [ parsed; other ] else [ parsed ] in
            List.map (reading_of pieces) ordered
        | _ -> both ()
      in
      report cursor (operator_span whole)
        "Shifts and bitwise operators combine only with themselves; add parentheses." fixes
  | Chained message ->
      let fixes =
        match (whole.kind, operand.kind) with
        | Binary { operator = Implies; _ }, _ ->
            (* Dafny's reading of [a ==> b ==> c] first: [a ==> (b ==> c)]. *)
            List.rev (both ())
        | Binary _, Binary { right = middle; _ } when (not right) && is_name_or_literal middle ->
            (* Python's reading of [a < b < c]: [a < b && b < c]. *)
            let middle_text = Cursor.text cursor (Cursor.absolute cursor middle.span) in
            [
              fix cursor whole.span
                [
                  Diagnostic.insert (Cursor.absolute cursor middle.span).stop (" && " ^ middle_text);
                ];
            ]
        | _ -> []
      in
      report cursor (operator_span whole) message fixes

(* Checks an expression and everything in it, reporting each operation that
   cannot combine with one of its operands. *)
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
  | Is { value = left; _ } -> operand Comparison ~right:false left
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
