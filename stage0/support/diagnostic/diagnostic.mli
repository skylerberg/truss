module Code : sig
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
    | Amortized_bound
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
    | Not_iterable
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
    | Condition_not_constant
    | Main_signature
    | No_real_implementation
    | Duplicate_field
    | Cannot_derive
    | Derives_inferred
    | Redeclared_method
    | Restated_method_body
    | Restated_method_clause
    | Restated_method_default
    | Overridden_method_default
    | Default_without_body
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
    | Read_only_owning_parameter
    | Unknown_associated_type
    | Unknown_associated_capability

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
    | Evaluation
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

  val name : t -> string
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

val make :
  ?severity:severity ->
  ?notes:('span * string) list ->
  ?fixes:'span fix list ->
  code:Code.t ->
  'span ->
  string ->
  'span diagnostic

val is_error : _ diagnostic -> bool
val fix : string -> 'span edit list -> 'span fix
val replace : 'span -> string -> 'span edit
val insert : 'span -> string -> 'span edit
val delete : 'span -> 'span edit
val list_spelling_fixes : 'span -> written:string -> string list -> 'span fix list
val show_count : int -> string -> string -> string

type reported

val make_reported : _ diagnostic -> reported
val reported_elsewhere : reported
val map_spans : ('a -> 'b) -> 'a diagnostic -> 'b diagnostic
val apply_edits : string -> Source.span edit list -> string
val list_machine_applicable : t list -> t list

module Collector : sig
  type diagnostic := t
  type t

  val create : unit -> t
  val add : t -> diagnostic -> unit
  val to_list : t -> diagnostic list
end

val select_shown : t list -> t list
val paint_severity : is_colored:bool -> severity -> string -> string
val render : is_colored:bool -> Source.t -> t -> string
val to_json_object : Source.t -> t -> string
val encode_json_string : string -> string
val quote : string -> string

module For_testing : sig
  val limit : int
end
