type expected =
  | Token_punctuation of Token.punctuation
  | Token_keyword of Token.keyword
  | Open_paren_after_calls
  | Open_paren_in_function_type
  | Open_paren_in_lambda
  | Open_paren_after_with
  | Type_body_start
  | Parameters_start
  | Function_type_clauses_end
  | Calls_target_end
  | Uses_separator
  | Modifies_separator
  | Self_capability_set
  | Type_arguments_end
  | Capability_member
  | Trait_member
  | Impl_member
  | Potential_word
  | Function_type_clause of Token.keyword
  | Body_start
  | Cost_bound
  | Resource
  | Clause
  | Constant
  | Definition
  | Field_name
  | Parenthesized_function_type
  | Generic_parameter
  | Line_break_after_definition
  | Line_break_after_module_path
  | Line_break_after_statement
  | Line_break_after_method
  | Line_break_or_brace
  | Range_bound
  | Method_name_after_dot
  | Method_name
  | Module_name
  | Name_after_dot
  | Name
  | Number_after_minus
  | Parameter_name
  | Pattern
  | Plain_test_name
  | Test_name
  | Tagged_string
  | Type_name
  | Type
  | Self_associated_capability_set
  | Associated_capability_set
  | Self_associated_type
  | Associated_type
  | Expression
  | Index_or_type_arguments
  | Range_end
  | Capability_parameter_name
  | Constant_name_after_dot
  | Constant_name
  | Law_name
  | Variant_name
  | Associated_capability_set_name
  | Associated_type_name
  | Capability_name
  | Theorem_name
  | Trait_name
  | Defined_type_name
  | Interpolation_end

type cost_word = Potential_cost_word | Resource_word | Bound_word
type loop_exit = Break_exit | Continue_exit
type conversion = Integer_conversion | Library_conversion

type macro =
  | Print_macro
  | Format_macro
  | Vector_macro
  | Assertion_macro
  | Debug_macro
  | Panic_macro
  | Other_macro

type visibility_owner = Test_owner | Law_proof_owner | Impl_owner
type range_part = Range_start | Range_stop
type chain = Range_chain | Comparison_chain | Implication_chain

type problem =
  | Unexpected of { expected : expected; found : Token.kind }
  | Reserved_word of { word : string }
  | Nesting_too_deep of { limit : int }
  | Chain_too_long of { limit : int }
  | Misspelled_cost_word of { category : cost_word; words : string list; found : string }
  | Whole_type_quantifier of { quantifier : string }
  | Implies_in_code
  | Echo_in_specification
  | Try_in_parallel
  | Return_in_parallel
  | Loop_exit_outside_loop of loop_exit
  | Loop_exit_across_lambda of loop_exit
  | Break_in_parallel_for
  | Loop_exit_from_parallel_branch of loop_exit
  | Misplaced_callback_requires
  | Misplaced_callback_ensures
  | Misplaced_proof
  | Misplaced_assert
  | Parameter_named_result
  | Lending_parameter_named_final
  | Associated_type_argument of { written : string; is_law_proof : bool }
  | Function_type_argument of { is_law_proof : bool }
  | Constraint_on_trait of {
      written : string;
      name : string;
      chosen : string option;
      is_law_proof : bool;
    }
  | Function_named_old
  | Function_named_identical
  | Increment of { sign : string; written : string }
  | Double_negation
  | Match_arm_comma
  | Conditional_operator
  | Let_mut
  | Address_of of { is_mut : bool }
  | Closure_bars
  | Brace_record
  | Turbofish
  | Angle_brackets
  | Qualified_variant of { variant : string }
  | Macro_call of { name : string; macro : macro }
  | Keyword_macro
  | Tuple
  | Tuple_field
  | Power_operator
  | Short_declaration
  | Pipe_operator
  | Lambda_annotation
  | Impl_parameters
  | Null_coalescing of { written : string }
  | Trailing_lambda of { parameter : string }
  | As_conversion of { target : string; conversion : conversion }
  | As_float_conversion of { method_ : string }
  | As_unknown_conversion
  | Elif
  | Loop_keyword
  | Constant_keyword of { word : string }
  | Misplaced_visibility of visibility_owner
  | Self_outside_method
  | Self_not_first
  | Self_in_capability
  | Lends_own
  | Repeated_uses
  | Repeated_decreases
  | Repeated_modifies
  | Repeated_loop_decreases
  | Missing_body
  | One_field_tuple
  | Interpolated_test_name
  | Misplaced_opaque
  | Misplaced_tuple_word of { written : string }
  | Statement_at_top_level
  | Empty_type_arguments
  | Function_type_condition
  | Function_type_cost_bound
  | Function_type_needs_names
  | Function_type_extra_names
  | Parenthesized_type
  | Empty_generic_parameters
  | Value_condition_in_when
  | Misplaced_potential
  | Inclusive_range_without_end
  | Open_range_outside_brackets of range_part
  | Open_range_comma
  | Open_range_with_items
  | Update_label
  | Mixed_collection
  | Tuple_pattern_annotation
  | Let_else_brace
  | Amortized_loop_cost
  | Interpolated_pattern
  | Float_pattern
  | Rest_not_last
  | Use_after_definition
  | Lowest_operand
  | Chained of chain
  | Mixed_and_or
  | Unordered_operators
  | Mixed_bitwise
  | Negation_and_is

type action =
  | Write of string
  | Write_conversion of string
  | Write_method of string
  | Remove_it
  | Remove_own
  | Add_todo_body
  | Remove_word of string
  | Remove_comma
  | Next_arm_on_line
  | Write_if
  | Remove_ampersand
  | Write_lambda
  | Use_parentheses
  | Use_square_brackets
  | Remove_qualifier
  | Write_list
  | Remove_macro_call
  | Declare_with_let
  | Write_call
  | Remove_annotation
  | Remove_parameters
  | Call_unwrap_or
  | Pass_lambda
  | Move_use_up
  | Parenthesize_expression
  | Add_parentheses
  | Group_first_two
  | Group_last_two
  | Join_comparisons
  | Negate_test
  | Negate_value

type fix = { action : action; edits : Source.span Diagnostic.edit list }
type t = { at : Source.span; problem : problem; fixes : fix list }
