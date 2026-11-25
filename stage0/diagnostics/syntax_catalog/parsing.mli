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
type angle_bracket = Opening_angle | Closing_angle | Double_closing_angle
type float_type = Float32 | Float64
type insertion = Open_parenthesis | Close_parenthesis | Repeated_operand of Source.span

type regrouping_kind =
  | Group_first_two
  | Group_last_two
  | Add_parentheses
  | Join_comparisons
  | Negate_test
  | Negate_value

type regrouping = {
  expression : Source.span;
  insertions : (int * insertion) list;
  kind : regrouping_kind;
}

type pipe = { value : Source.span; callee : Source.span }
type trailing_call = { callee_gap : Source.span; closing : Source.span; uses : Source.span list }

type problem =
  | Unexpected of { expected : expected; found : Token.kind }
  | Reserved_word of { word : string }
  | Nesting_too_deep of { limit : int }
  | Chain_too_long of { limit : int }
  | Misspelled_cost_word of {
      category : cost_word;
      words : string list;
      found : string;
      correction : string option;
    }
  | Echo_in_specification
  | Try_in_parallel
  | Return_in_parallel
  | Loop_exit_outside_loop of loop_exit
  | Loop_exit_across_lambda of loop_exit
  | Break_in_parallel_for
  | Loop_exit_from_parallel_branch of loop_exit
  | Misplaced_callback_requires
  | Misplaced_callback_ensures
  | Misplaced_callback_panic_condition
  | Misplaced_callback_cost
  | Misplaced_proof
  | Misplaced_assert
  | Parameter_named_result
  | Lending_parameter_named_final
  | Associated_type_argument of { argument : Source.span; is_law_proof : bool }
  | Function_type_argument of { is_law_proof : bool }
  | Constraint_on_trait of {
      constraint_ : Source.span;
      name : string;
      chosen : Source.span;
      is_law_proof : bool;
    }
  | Function_named_old
  | Function_named_identical
  | Increment of { is_increment : bool; target : Source.span }
  | Double_negation of { operand : Source.span }
  | Match_arm_comma of { next_arm : Source.span option }
  | Conditional_operator of { condition : Source.span; then_ : Source.span; else_ : Source.span }
  | Let_mut of { let_mut : Source.span }
  | Address_of of { is_mut : bool; removed : Source.span; needs_space : bool }
  | Closure_bars of {
      closing : Source.span;
      body : Source.span;
      has_parameters : bool;
      is_block : bool;
      is_before_else : bool;
    }
  | Brace_record of { opening : Source.span; closing : Source.span }
  | Turbofish of { opening : Source.span; closing : Source.span }
  | Angle_brackets of (Source.span * angle_bracket) list
  | Qualified_variant of { variant : string }
  | Macro_call of { name : string; macro : macro; list_call : Source.span option }
  | Keyword_macro of { call : Source.span option }
  | Tuple
  | Tuple_field
  | Power_operator
  | Short_declaration of { name : Source.span option }
  | Pipe_operator of { call : pipe option }
  | Lambda_annotation
  | Impl_parameters of { parameters : Source.span option }
  | Null_coalescing of {
      written : string;
      value : Source.span;
      default : Source.span;
      needs_parentheses : bool;
    }
  | Trailing_lambda of { receiver : string option; call : trailing_call option }
  | As_conversion of { value : Source.span; target : Source.span; conversion : conversion }
  | As_float_conversion of {
      value : Source.span;
      target : Source.span;
      float_type : float_type;
      is_simple : bool;
    }
  | As_unknown_conversion
  | Elif of { replaced : Source.span }
  | Loop_keyword
  | Constant_keyword of { word : string }
  | Misplaced_visibility of { owner : visibility_owner; removed : Source.span }
  | Self_outside_method
  | Self_not_first
  | Self_in_capability
  | Lends_own of { removed : Source.span }
  | Repeated_uses
  | Repeated_decreases
  | Repeated_modifies
  | Repeated_loop_decreases
  | Missing_body of { can_add_todo : bool }
  | One_field_tuple of { removed : Source.span }
  | Interpolated_test_name
  | Misplaced_opaque of { removed : Source.span }
  | Misplaced_tuple_word of { written : string; is_misspelled : bool; removed : Source.span }
  | Statement_at_top_level
  | Empty_type_arguments
  | Function_type_condition
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
  | Let_else_brace of { value : Source.span }
  | Amortized_loop_cost
  | Interpolated_pattern
  | Float_pattern
  | Rest_not_last
  | Use_after_definition of { moved : Source.span; destination : Source.span }
  | Lowest_operand of regrouping list
  | Chained of { chain : chain; regroupings : regrouping list }
  | Mixed_and_or of regrouping list
  | Unordered_operators of regrouping list
  | Mixed_bitwise of regrouping list
  | Negation_and_is of regrouping list

type t = { at : Source.span; problem : problem; has_lexer_errors : bool }
