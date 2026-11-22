module Code = struct
  type lexer =
    | Invalid_utf8
    | Carriage_return
    | Forbidden_character
    | Comment
    | Semicolon
    | Unexpected_character
    | Strict_equality
    | Character_literal
    | String_prefix
    | String_delimiter
    | Attribute
    | Foreign_operator
    | Path_separator
    | Confusable_character
    | Lifetime
    | Number_hexadecimal_float
    | Name_case
    | Name_not_ascii
    | Number_suffix
    | Number_uppercase_prefix
    | Number_uppercase_exponent
    | Number_missing_digits
    | Number_invalid_digit
    | Number_followed_by_name
    | Number_underscore
    | Number_digit_separator
    | Number_leading_zero
    | Unterminated_string
    | Invalid_escape
    | Line_break_in_interpolation
    | Empty_interpolation
    | Interpolation_too_deep
    | Raw_string_quotes
    | Raw_string_closing_not_alone
    | Raw_string_indentation
    | Unclosed_bracket
    | Unmatched_closing_bracket

  type parser =
    | Unexpected_token
    | Needs_parentheses
    | Reserved_word
    | Use_after_definition
    | Statement_at_top_level
    | Missing_body
    | Open_range
    | Interpolation_not_allowed
    | Float_pattern
    | Let_else_brace
    | Nesting_too_deep
    | Misplaced_opaque
    | Misplaced_tuple
    | Misplaced_visibility
    | Misplaced_self
    | Lends_own
    | Repeated_clause
    | Cost_word
    | Loop_cost_bound
    | Function_type_cost_bound
    | Function_type_names
    | Misplaced_callback_contract
    | Misplaced_condition
    | Misplaced_function_type
    | Misplaced_associated_type
    | Misplaced_constraint
    | Misplaced_potential
    | Increment
    | Double_negation
    | Match_arm_comma
    | Conditional_operator
    | Let_mut
    | Address_of
    | Closure_bars
    | Brace_record
    | Turbofish
    | Trailing_lambda
    | As_conversion
    | Elif
    | Angle_brackets
    | Qualified_variant
    | Macro_call
    | Tuple
    | Power_operator
    | Short_declaration
    | Pipe_operator
    | Lambda_annotation
    | Impl_parameters
    | Null_coalescing
    | Specification_only
    | Misplaced_assert
    | Misplaced_proof
    | Misplaced_loop_exit
    | Exits_parallel
    | Echo_in_specification
    | Reserved_specification_name

  type resolve =
    | Unknown_name
    | Unknown_module
    | Not_visible
    | Ambiguous_module
    | Duplicate_import
    | Unused_import
    | Intrinsic_import
    | Shadowed_name
    | Duplicate_definition
    | Not_a_place
    | Not_generic
    | Not_a_constant
    | Alternative_bindings
    | Not_a_generic_parameter
    | Unconstrained_capability_parameter
    | Null

  type types =
    | Character_scalar_count
    | Misplaced_self_type
    | Mismatch
    | Not_bit_vector
    | Cannot_infer
    | Missing_label
    | Unknown_label
    | Out_of_order
    | Positional_after_labeled
    | Missing_argument
    | Too_many_arguments
    | Repeated_argument
    | Missing_mode
    | Redundant_mode
    | Wrong_mode
    | Unknown_member
    | Ambiguous_method
    | Private_field
    | Member_not_visible
    | Not_callable
    | Not_a_value
    | No_impl
    | Mismatched_integers
    | String_addition
    | Literal_out_of_range
    | Integer_for_float
    | Negated_unsigned
    | Unused_value
    | Unbounded_time
    | Upper_bound_in_exact_bound
    | Cost_of_other_resource
    | Not_assignable
    | Wrong_try
    | Lambda_needs_type
    | Not_a_record
    | Not_a_tuple_type
    | Unknown_variant
    | Specification_only
    | Not_in_specification
    | Decided_in_specification
    | Not_structural
    | Wrong_receiver
    | Not_indexable
    | Implements_built_in
    | Not_derivable
    | Not_a_type
    | Not_a_trait
    | Not_a_capability
    | Arity
    | Argument_kind
    | Wrong_value_parameter_type
    | Unsatisfied_bound
    | Private_in_public
    | Method_outside_package
    | Default_not_constant
    | Not_constant
    | Constant_overflow
    | Constant_not_data
    | Main_signature
    | No_real_implementation
    | Duplicate_field
    | Cannot_derive
    | Derives_inferred
    | Redeclared_method
    | Restated_method_body
    | Restated_method_clause
    | Decided_condition
    | Misplaced_value_condition
    | Trait_cycle
    | Recursion_limit
    | Missing_member
    | Extra_member
    | Signature_mismatch
    | Missing_required_impl
    | Implements_built_in_capability
    | Impl_uses
    | Mut_self_for_slice
    | Unknown_associated_type
    | Unknown_associated_capability
    | Associated_type_not_fixed

  type patterns = Not_covered | Unreachable_arm | Unreachable_alternative | Refutable

  type usage =
    | Unused_variable
    | Unused_function
    | Unused_constant
    | Unused_run_forever
    | Unreachable_code
    | Self_comparison

  type ownership =
    | Views_temporary
    | Use_after_move
    | Not_owned
    | Not_reinitialized
    | Conflicting_loan
    | Mutated_while_viewed
    | View_escapes
    | Self_referential
    | View_crosses_capability
    | Needs_owned
    | Data_race
    | Lent_part_escapes
    | Lends_other_parameter
    | Lent_mut_in_variant
    | Needs_lent_mut
    | Task_outlives_view

  type capabilities =
    | Not_available
    | Lambda_uses
    | Not_granted
    | Provide_mode
    | Not_an_implementation
    | Callback_may_deadlock
    | Monitor_needs_tasks

  type prover =
    | Overflow
    | Division
    | Shift
    | Out_of_range
    | Out_of_bounds
    | Requires
    | Ensures
    | Invariant
    | Termination
    | Constant_cycle
    | Panic
    | Assertion
    | Law
    | Cost
    | Disjoint
    | Unreachable
    | Unsupported

  type package =
    | Impl_location
    | Sealed_trait_impl
    | Overlapping_impls
    | Method_name_clash
    | Needs_indirect
    | Not_strictly_positive
    | Growing_type
    | Instantiation_cycle
    | Duplicate_test

  type t =
    | Lexer of lexer
    | Parser of parser
    | Resolve of resolve
    | Types of types
    | Patterns of patterns
    | Usage of usage
    | Ownership of ownership
    | Capabilities of capabilities
    | Package of package
    | Prover of prover
    | Too_many_diagnostics

  let name_lexer_code code =
    match code with
    | Invalid_utf8 -> "invalid_utf8"
    | Carriage_return -> "carriage_return"
    | Forbidden_character -> "forbidden_character"
    | Comment -> "comment"
    | Semicolon -> "semicolon"
    | Unexpected_character -> "unexpected_character"
    | Strict_equality -> "strict_equality"
    | Character_literal -> "character_literal"
    | String_prefix -> "string_prefix"
    | String_delimiter -> "string_delimiter"
    | Attribute -> "attribute"
    | Foreign_operator -> "foreign_operator"
    | Path_separator -> "path_separator"
    | Confusable_character -> "confusable_character"
    | Lifetime -> "lifetime"
    | Number_hexadecimal_float -> "number_hexadecimal_float"
    | Name_case -> "name_case"
    | Name_not_ascii -> "name_not_ascii"
    | Number_suffix -> "number_suffix"
    | Number_uppercase_prefix -> "number_uppercase_prefix"
    | Number_uppercase_exponent -> "number_uppercase_exponent"
    | Number_missing_digits -> "number_missing_digits"
    | Number_invalid_digit -> "number_invalid_digit"
    | Number_followed_by_name -> "number_followed_by_name"
    | Number_underscore -> "number_underscore"
    | Number_digit_separator -> "number_digit_separator"
    | Number_leading_zero -> "number_leading_zero"
    | Unterminated_string -> "unterminated_string"
    | Invalid_escape -> "invalid_escape"
    | Line_break_in_interpolation -> "line_break_in_interpolation"
    | Empty_interpolation -> "empty_interpolation"
    | Interpolation_too_deep -> "interpolation_too_deep"
    | Raw_string_quotes -> "raw_string_quotes"
    | Raw_string_closing_not_alone -> "raw_string_closing_not_alone"
    | Raw_string_indentation -> "raw_string_indentation"
    | Unclosed_bracket -> "unclosed_bracket"
    | Unmatched_closing_bracket -> "unmatched_closing_bracket"

  let name_parser_code code =
    match code with
    | Unexpected_token -> "unexpected_token"
    | Needs_parentheses -> "needs_parentheses"
    | Reserved_word -> "reserved_word"
    | Use_after_definition -> "use_after_definition"
    | Statement_at_top_level -> "statement_at_top_level"
    | Missing_body -> "missing_body"
    | Open_range -> "open_range"
    | Interpolation_not_allowed -> "interpolation_not_allowed"
    | Float_pattern -> "float_pattern"
    | Let_else_brace -> "let_else_brace"
    | Nesting_too_deep -> "nesting_too_deep"
    | Misplaced_opaque -> "misplaced_opaque"
    | Misplaced_tuple -> "misplaced_tuple"
    | Misplaced_visibility -> "misplaced_visibility"
    | Misplaced_self -> "misplaced_self"
    | Lends_own -> "lends_own"
    | Repeated_clause -> "repeated_clause"
    | Cost_word -> "cost_word"
    | Loop_cost_bound -> "loop_cost_bound"
    | Function_type_cost_bound -> "function_type_cost_bound"
    | Function_type_names -> "function_type_names"
    | Misplaced_callback_contract -> "misplaced_callback_contract"
    | Misplaced_condition -> "misplaced_condition"
    | Misplaced_function_type -> "misplaced_function_type"
    | Misplaced_associated_type -> "misplaced_associated_type"
    | Misplaced_constraint -> "misplaced_constraint"
    | Misplaced_potential -> "misplaced_potential"
    | Increment -> "increment"
    | Double_negation -> "double_negation"
    | Match_arm_comma -> "match_arm_comma"
    | Conditional_operator -> "conditional_operator"
    | Let_mut -> "let_mut"
    | Address_of -> "address_of"
    | Closure_bars -> "closure_bars"
    | Brace_record -> "brace_record"
    | Turbofish -> "turbofish"
    | Trailing_lambda -> "trailing_lambda"
    | As_conversion -> "as_conversion"
    | Elif -> "elif"
    | Angle_brackets -> "angle_brackets"
    | Qualified_variant -> "qualified_variant"
    | Macro_call -> "macro_call"
    | Tuple -> "tuple"
    | Power_operator -> "power_operator"
    | Short_declaration -> "short_declaration"
    | Pipe_operator -> "pipe_operator"
    | Lambda_annotation -> "lambda_annotation"
    | Impl_parameters -> "impl_parameters"
    | Null_coalescing -> "null_coalescing"
    | Specification_only -> "specification_only"
    | Misplaced_assert -> "misplaced_assert"
    | Misplaced_proof -> "misplaced_proof"
    | Misplaced_loop_exit -> "misplaced_loop_exit"
    | Exits_parallel -> "exits_parallel"
    | Echo_in_specification -> "echo_in_specification"
    | Reserved_specification_name -> "reserved_specification_name"

  let resolve_name code =
    match code with
    | Unknown_name -> "unknown_name"
    | Unknown_module -> "unknown_module"
    | Not_visible -> "not_visible"
    | Ambiguous_module -> "ambiguous_module"
    | Duplicate_import -> "duplicate_import"
    | Unused_import -> "unused_import"
    | Intrinsic_import -> "intrinsic_import"
    | Shadowed_name -> "shadowed_name"
    | Duplicate_definition -> "duplicate_definition"
    | Not_a_place -> "not_a_place"
    | Not_generic -> "not_generic"
    | Not_a_constant -> "not_a_constant"
    | Alternative_bindings -> "alternative_bindings"
    | Not_a_generic_parameter -> "not_a_generic_parameter"
    | Unconstrained_capability_parameter -> "unconstrained_capability_parameter"
    | Null -> "null"

  let name_types_code code =
    match code with
    | Character_scalar_count -> "character_scalar_count"
    | Misplaced_self_type -> "misplaced_self_type"
    | Mismatch -> "mismatch"
    | Not_bit_vector -> "not_bit_vector"
    | Cannot_infer -> "cannot_infer"
    | Missing_label -> "missing_label"
    | Unknown_label -> "unknown_label"
    | Out_of_order -> "out_of_order"
    | Positional_after_labeled -> "positional_after_labeled"
    | Missing_argument -> "missing_argument"
    | Too_many_arguments -> "too_many_arguments"
    | Repeated_argument -> "repeated_argument"
    | Missing_mode -> "missing_mode"
    | Redundant_mode -> "redundant_mode"
    | Wrong_mode -> "wrong_mode"
    | Unknown_member -> "unknown_member"
    | Ambiguous_method -> "ambiguous_method"
    | Private_field -> "private_field"
    | Member_not_visible -> "member_not_visible"
    | Not_callable -> "not_callable"
    | Not_a_value -> "not_a_value"
    | No_impl -> "no_impl"
    | Mismatched_integers -> "mismatched_integers"
    | String_addition -> "string_addition"
    | Literal_out_of_range -> "literal_out_of_range"
    | Integer_for_float -> "integer_for_float"
    | Negated_unsigned -> "negated_unsigned"
    | Unused_value -> "unused_value"
    | Unbounded_time -> "unbounded_time"
    | Upper_bound_in_exact_bound -> "upper_bound_in_exact_bound"
    | Cost_of_other_resource -> "cost_of_other_resource"
    | Not_assignable -> "not_assignable"
    | Wrong_try -> "wrong_try"
    | Lambda_needs_type -> "lambda_needs_type"
    | Not_a_record -> "not_a_record"
    | Not_a_tuple_type -> "not_a_tuple_type"
    | Unknown_variant -> "unknown_variant"
    | Not_structural -> "not_structural"
    | Specification_only -> "specification_only"
    | Not_in_specification -> "not_in_specification"
    | Decided_in_specification -> "decided_in_specification"
    | Wrong_receiver -> "wrong_receiver"
    | Not_indexable -> "not_indexable"
    | Implements_built_in -> "implements_built_in"
    | Not_derivable -> "not_derivable"
    | Not_a_type -> "not_a_type"
    | Not_a_trait -> "not_a_trait"
    | Not_a_capability -> "not_a_capability"
    | Arity -> "arity"
    | Argument_kind -> "argument_kind"
    | Wrong_value_parameter_type -> "wrong_value_parameter_type"
    | Unsatisfied_bound -> "unsatisfied_bound"
    | Private_in_public -> "private_in_public"
    | Method_outside_package -> "method_outside_package"
    | Default_not_constant -> "default_not_constant"
    | Not_constant -> "not_constant"
    | Constant_overflow -> "constant_overflow"
    | Constant_not_data -> "constant_not_data"
    | Main_signature -> "main_signature"
    | No_real_implementation -> "no_real_implementation"
    | Duplicate_field -> "duplicate_field"
    | Cannot_derive -> "cannot_derive"
    | Derives_inferred -> "derives_inferred"
    | Redeclared_method -> "redeclared_method"
    | Restated_method_body -> "restated_method_body"
    | Restated_method_clause -> "restated_method_clause"
    | Decided_condition -> "decided_condition"
    | Misplaced_value_condition -> "misplaced_value_condition"
    | Trait_cycle -> "trait_cycle"
    | Recursion_limit -> "recursion_limit"
    | Missing_member -> "missing_member"
    | Extra_member -> "extra_member"
    | Signature_mismatch -> "signature_mismatch"
    | Missing_required_impl -> "missing_required_impl"
    | Implements_built_in_capability -> "implements_built_in_capability"
    | Impl_uses -> "impl_uses"
    | Mut_self_for_slice -> "mut_self_for_slice"
    | Unknown_associated_type -> "unknown_associated_type"
    | Unknown_associated_capability -> "unknown_associated_capability"
    | Associated_type_not_fixed -> "associated_type_not_fixed"

  let name_patterns_code code =
    match code with
    | Not_covered -> "not_covered"
    | Unreachable_arm -> "unreachable_arm"
    | Unreachable_alternative -> "unreachable_alternative"
    | Refutable -> "refutable"

  let name_usage_code code =
    match code with
    | Unused_variable -> "unused_variable"
    | Unused_function -> "unused_function"
    | Unused_constant -> "unused_constant"
    | Unused_run_forever -> "unused_run_forever"
    | Unreachable_code -> "unreachable_code"
    | Self_comparison -> "self_comparison"

  let name_ownership_code code =
    match code with
    | Views_temporary -> "views_temporary"
    | Use_after_move -> "use_after_move"
    | Not_owned -> "not_owned"
    | Not_reinitialized -> "not_reinitialized"
    | Conflicting_loan -> "conflicting_loan"
    | Mutated_while_viewed -> "mutated_while_viewed"
    | View_escapes -> "view_escapes"
    | Self_referential -> "self_referential"
    | View_crosses_capability -> "view_crosses_capability"
    | Needs_owned -> "needs_owned"
    | Data_race -> "data_race"
    | Lent_part_escapes -> "lent_part_escapes"
    | Lends_other_parameter -> "lends_other_parameter"
    | Lent_mut_in_variant -> "lent_mut_in_variant"
    | Needs_lent_mut -> "needs_lent_mut"
    | Task_outlives_view -> "task_outlives_view"

  let name_capabilities_code code =
    match code with
    | Not_available -> "not_available"
    | Lambda_uses -> "lambda_uses"
    | Not_granted -> "not_granted"
    | Provide_mode -> "provide_mode"
    | Not_an_implementation -> "not_an_implementation"
    | Callback_may_deadlock -> "callback_may_deadlock"
    | Monitor_needs_tasks -> "monitor_needs_tasks"

  let name_package_code code =
    match code with
    | Impl_location -> "impl_location"
    | Sealed_trait_impl -> "sealed_trait_impl"
    | Overlapping_impls -> "overlapping_impls"
    | Method_name_clash -> "method_name_clash"
    | Needs_indirect -> "needs_indirect"
    | Not_strictly_positive -> "not_strictly_positive"
    | Growing_type -> "growing_type"
    | Instantiation_cycle -> "instantiation_cycle"
    | Duplicate_test -> "duplicate_test"

  let name_prover_code code =
    match code with
    | Overflow -> "overflow"
    | Division -> "division"
    | Shift -> "shift"
    | Out_of_range -> "out_of_range"
    | Out_of_bounds -> "out_of_bounds"
    | Requires -> "requires"
    | Ensures -> "ensures"
    | Invariant -> "invariant"
    | Termination -> "termination"
    | Constant_cycle -> "constant_cycle"
    | Panic -> "panic"
    | Assertion -> "assertion"
    | Law -> "law"
    | Cost -> "cost"
    | Disjoint -> "disjoint"
    | Unreachable -> "unreachable"
    | Unsupported -> "unsupported"

  let name = function
    | Lexer code -> "lexer." ^ name_lexer_code code
    | Parser code -> "parser." ^ name_parser_code code
    | Resolve code -> "resolve." ^ resolve_name code
    | Types code -> "types." ^ name_types_code code
    | Patterns code -> "patterns." ^ name_patterns_code code
    | Usage code -> "usage." ^ name_usage_code code
    | Ownership code -> "ownership." ^ name_ownership_code code
    | Capabilities code -> "capabilities." ^ name_capabilities_code code
    | Package code -> "package." ^ name_package_code code
    | Prover code -> "prover." ^ name_prover_code code
    | Too_many_diagnostics -> "too_many_diagnostics"
end

type 'span edit = { span : 'span; replacement : string }
type 'span fix = { title : string; edits : 'span edit list }
type severity = Error | Warning

type 'span diagnostic = {
  code : Code.t;
  severity : severity;
  message : string;
  span : 'span;
  notes : ('span * string) list;
  fixes : 'span fix list;
}

type t = Source.span diagnostic
type in_definition = Source.Definition_span.t diagnostic

let make ?(severity : severity = Error) ?(notes = []) ?(fixes = []) ~code span message =
  { code; severity; message; span; notes; fixes }

let is_error (diagnostic : _ diagnostic) = diagnostic.severity = Error
let show_severity : severity -> string = function Error -> "error" | Warning -> "warning"

type reported = Reported

let make_reported (_ : _ diagnostic) = Reported
let reported_elsewhere = Reported
let fix title edits = { title; edits }
let replace span replacement = { span; replacement }
let insert at replacement = { span = at; replacement }
let delete span = { span; replacement = "" }

let find_closest text candidates =
  let limit = max 1 (String.length text / 3) in
  let enumerate_candidates select =
    List.iter
      (fun candidate -> if candidate <> text then select candidate)
      (List.sort_uniq compare candidates)
  in
  match String.spellcheck ~max_dist:(fun _ -> limit) enumerate_candidates text with
  | closest :: _ -> Some closest
  | [] -> None

let list_spelling_fixes span ~written candidates =
  match find_closest written candidates with
  | Some candidate -> [ fix (Printf.sprintf "Write `%s`." candidate) [ replace span candidate ] ]
  | None -> []

let show_count count singular plural =
  Printf.sprintf "%d %s" count (if count = 1 then singular else plural)

let map_spans convert (diagnostic : _ diagnostic) : _ diagnostic =
  {
    diagnostic with
    span = convert diagnostic.span;
    notes = List.map (fun (span, note) -> (convert span, note)) diagnostic.notes;
    fixes =
      List.map
        (fun fix ->
          {
            fix with
            edits =
              List.map
                (fun (edit : _ edit) ->
                  { span = convert edit.span; replacement = edit.replacement })
                fix.edits;
          })
        diagnostic.fixes;
  }

let apply_edits text (edits : Source.span edit list) =
  let edits =
    List.stable_sort
      (fun (left : Source.span edit) (right : Source.span edit) ->
        compare left.span.start right.span.start)
      edits
  in
  let buffer = Buffer.create (String.length text) in
  let position =
    List.fold_left
      (fun position (edit : Source.span edit) ->
        if edit.span.start < position then invalid_arg "Diagnostic.apply_edits: overlapping edits";
        Buffer.add_substring buffer text position (edit.span.start - position);
        Buffer.add_string buffer edit.replacement;
        edit.span.stop)
      0 edits
  in
  Buffer.add_substring buffer text position (String.length text - position);
  Buffer.contents buffer

module Starts = Map.Make (Int)

type accepted = { stop : int; has_insertion : bool }

let list_machine_applicable (diagnostics : t list) =
  let accepted = ref Starts.empty in
  let overlaps (edit : Source.span edit) =
    let start = edit.span.start and stop = edit.span.stop in
    let is_insertion = start = stop in
    (match Starts.find_last_opt (fun other -> other <= start) !accepted with
      | Some (other_start, other) ->
          start < other.stop || (other_start = start && (is_insertion || other.has_insertion))
      | None -> false)
    ||
    match Starts.find_first_opt (fun other -> other > start) !accepted with
    | Some (other_start, _) -> other_start < stop
    | None -> false
  in
  let accept (edit : Source.span edit) =
    let start = edit.span.start and stop = edit.span.stop in
    accepted :=
      Starts.update start
        (fun previous ->
          let is_insertion = start = stop in
          Some
            (match previous with
            | Some other ->
                { stop = max stop other.stop; has_insertion = is_insertion || other.has_insertion }
            | None -> { stop; has_insertion = is_insertion }))
        !accepted
  in
  List.filter
    (fun (diagnostic : t) ->
      match diagnostic.fixes with
      | [ fix ] ->
          let clear = not (List.exists overlaps fix.edits) in
          if clear then List.iter accept fix.edits;
          clear
      | _ -> false)
    diagnostics

let limit = 200

module Collector = struct
  type diagnostic = t
  type nonrec t = diagnostic Dynarray.t

  let create () = Dynarray.create ()
  let add collector diagnostic = Dynarray.add_last collector diagnostic

  let to_list collector =
    List.stable_sort
      (fun (left : diagnostic) (right : diagnostic) -> compare left.span.start right.span.start)
      (Dynarray.to_list collector)
end

let select_shown diagnostics =
  let rec take count last = function
    | [] -> []
    | rest when count = limit ->
        [
          make
            ~severity:(if List.exists is_error rest then (Error : severity) else Warning)
            ~code:Too_many_diagnostics (Source.make_zero_width last)
            (Printf.sprintf "%d more diagnostics are not shown." (List.length rest));
        ]
    | (first : t) :: rest -> first :: take (count + 1) first.span.stop rest
  in
  take 0 0 diagnostics

let show_location source offset =
  let line, column = Source.compute_position source offset in
  Printf.sprintf "%s:%d:%d" (Source.path source) line column

let iter_utf8 text ~on_valid ~on_invalid =
  let rec loop index =
    if index < String.length text then begin
      let decoded = String.get_utf_8_uchar text index in
      if not (Uchar.utf_decode_is_valid decoded) then begin
        on_invalid text.[index];
        loop (index + 1)
      end
      else begin
        let length = Uchar.utf_decode_length decoded in
        on_valid (String.sub text index length);
        loop (index + length)
      end
    end
  in
  loop 0

let quote text =
  let buffer = Buffer.create (String.length text + 2) in
  Buffer.add_char buffer '"';
  iter_utf8 text
    ~on_valid:(fun character ->
      match character with
      | "\"" -> Buffer.add_string buffer "\\\""
      | "\\" -> Buffer.add_string buffer "\\\\"
      | "\n" -> Buffer.add_string buffer "\\n"
      | "\t" -> Buffer.add_string buffer "\\t"
      | scalar
        when String.length scalar = 1 && (Char.code scalar.[0] < 0x20 || Char.code scalar.[0] = 0x7F)
        ->
          Printf.bprintf buffer "\\x%02X" (Char.code scalar.[0])
      | scalar -> Buffer.add_string buffer scalar)
    ~on_invalid:(fun byte -> Printf.bprintf buffer "\\x%02X" (Char.code byte));
  Buffer.add_char buffer '"';
  Buffer.contents buffer

type style = Bold | Margin | Severity of severity

let paint ~is_colored style text =
  if not is_colored then text
  else
    let start =
      match style with
      | Bold -> "\027[1m"
      | Margin -> "\027[1;34m"
      | Severity Error -> "\027[1;31m"
      | Severity Warning -> "\027[1;33m"
    in
    start ^ text ^ "\027[0m"

let paint_severity ~is_colored severity text = paint ~is_colored (Severity severity) text

let render ~is_colored source (diagnostic : t) =
  let paint = paint ~is_colored in
  let buffer = Buffer.create 256 in
  let text = Source.text source in
  let margin = paint Margin "  |" in
  Printf.bprintf buffer "%s %s%s\n"
    (paint Bold (show_location source diagnostic.span.start ^ ":"))
    (paint (Severity diagnostic.severity)
       (Printf.sprintf "%s[%s]" (show_severity diagnostic.severity) (Code.name diagnostic.code)))
    (paint Bold (": " ^ diagnostic.message));
  let start = diagnostic.span.start in
  let line_start = Source.compute_line_start source start in
  let line_end = Source.compute_line_end source start in
  let line = String.sub text line_start (line_end - line_start) in
  let _, start_column = Source.compute_position source start in
  let _, stop_column = Source.compute_position source (min diagnostic.span.stop line_end) in
  let is_printable =
    String.for_all (fun character -> character = '\t' || Char.code character >= 0x20) line
    &&
    let valid = ref true in
    iter_utf8 line ~on_valid:ignore ~on_invalid:(fun _ -> valid := false);
    !valid
  in
  if is_printable && String.length line <= 200 then begin
    Printf.bprintf buffer "%s %s\n" margin line;
    let leading = Buffer.create 16 in
    for index = line_start to start - 1 do
      match text.[index] with
      | '\t' -> Buffer.add_char leading '\t'
      | character when Char.code character land 0xC0 = 0x80 -> ()
      | _ -> Buffer.add_char leading ' '
    done;
    Printf.bprintf buffer "%s %s%s\n" margin (Buffer.contents leading)
      (paint (Severity diagnostic.severity) (String.make (max 1 (stop_column - start_column)) '^'))
  end;
  List.iter
    (fun ((span : Source.span), note) ->
      Printf.bprintf buffer "  %s %s: %s\n" (paint Bold "note:") (show_location source span.start)
        note)
    diagnostic.notes;
  List.iter
    (fun fix ->
      Printf.bprintf buffer "  %s %s\n" (paint Bold "fix:") fix.title;
      List.iter
        (fun (edit : Source.span edit) ->
          let original = String.sub text edit.span.start (edit.span.stop - edit.span.start) in
          Printf.bprintf buffer "    %s at %s\n"
            (if edit.span.start = edit.span.stop then "insert " ^ quote edit.replacement
             else if edit.replacement = "" then "delete " ^ quote original
             else Printf.sprintf "replace %s with %s" (quote original) (quote edit.replacement))
            (show_location source edit.span.start))
        fix.edits)
    diagnostic.fixes;
  Buffer.add_char buffer '\n';
  Buffer.contents buffer

let encode_json_string value =
  let buffer = Buffer.create (String.length value + 2) in
  Buffer.add_char buffer '"';
  iter_utf8 value
    ~on_valid:(fun character ->
      match character with
      | "\"" -> Buffer.add_string buffer "\\\""
      | "\\" -> Buffer.add_string buffer "\\\\"
      | "\n" -> Buffer.add_string buffer "\\n"
      | "\r" -> Buffer.add_string buffer "\\r"
      | "\t" -> Buffer.add_string buffer "\\t"
      | scalar
        when String.length scalar = 1 && (Char.code scalar.[0] < 0x20 || Char.code scalar.[0] = 0x7F)
        ->
          Printf.bprintf buffer "\\u%04x" (Char.code scalar.[0])
      | scalar -> Buffer.add_string buffer scalar)
    ~on_invalid:(fun _ -> Buffer.add_string buffer "\xEF\xBF\xBD");
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let encode_json_span source (span : Source.span) =
  let line, column = Source.compute_position source span.start in
  let end_line, end_column = Source.compute_position source span.stop in
  Printf.sprintf {|{"start":%d,"stop":%d,"line":%d,"column":%d,"end_line":%d,"end_column":%d}|}
    span.start span.stop line column end_line end_column

let to_json_object source diagnostic =
  let path = encode_json_string (Source.path source) in
  let notes =
    List.map
      (fun (span, message) ->
        Printf.sprintf {|{"span":%s,"message":%s}|} (encode_json_span source span)
          (encode_json_string message))
      diagnostic.notes
  in
  let fixes =
    List.map
      (fun fix ->
        let edits =
          List.map
            (fun (edit : Source.span edit) ->
              Printf.sprintf {|{"start":%d,"stop":%d,"replacement":%s}|} edit.span.start
                edit.span.stop
                (encode_json_string edit.replacement))
            fix.edits
        in
        Printf.sprintf {|{"title":%s,"edits":[%s]}|} (encode_json_string fix.title)
          (String.concat "," edits))
      diagnostic.fixes
  in
  Printf.sprintf
    {|{"path":%s,"code":%s,"severity":%s,"message":%s,"span":%s,"notes":[%s],"fixes":[%s]}|} path
    (encode_json_string (Code.name diagnostic.code))
    (encode_json_string (show_severity diagnostic.severity))
    (encode_json_string diagnostic.message)
    (encode_json_span source diagnostic.span)
    (String.concat "," notes) (String.concat "," fixes)

module For_testing = struct
  let limit = limit
end
