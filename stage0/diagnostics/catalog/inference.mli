type shown = Some_integer | Some_float | Exactly of Types.ty
type decision_site = Use | Statement_end | Actual_head | Method_call
type mutation = Assignment | Passed_mut
type side = Left | Right

type decision = {
  name : Core.origin;
  decided : Types.ty;
  site : decision_site;
  decided_at : Core.origin;
  declares : bool;
}

type view_copy = Append_copy of Core.origin | Wrap_copy of Core.origin
type widening = { side : side; operand : Core.origin; target : Types.ty }
type impl_need = { needing : Types.ty; condition : Types.trait_reference }

type unmet_bound =
  | Does_not_hold
  | Does_not_hold_for_view
  | Associated_differs of { name : string; found : Types.ty }

type mismatch =
  | Expected of { expected : shown; actual : shown; copy : view_copy option }
  | Loop_element of { element : shown; annotated : shown }
  | Lambda_parameter_type of { passed : shown; annotated : shown }
  | Mismatched_integers of { left : Types.ty; right : Types.ty; widening : widening option }
  | Unsatisfied_bound of {
      of_type : Types.ty option;
      subject : Types.ty;
      bound : Types.trait_reference;
      unmet : unmet_bound;
      impl_need : impl_need option;
    }

type integer_subject = Potential | Decreases_measure | Cost_bound | Log_argument | Power_argument
type range_owner = Range_of_loop | Range_of_quantifier

type formula_construct =
  | Unreachable_expression
  | Break_expression
  | Continue_expression
  | Return_expression
  | Try_expression
  | Var_binding
  | For_statement
  | While_statement
  | Concurrent_block
  | Parallel_block

type owner = Variant_name of string | Type_named of Types.ty
type counted_callee = Fields_of of owner | Method_besides_self | Plain_function

type bare_owner =
  | Pattern_owner of { owner : owner; is_tuple_type : bool }
  | Construction_owner of owner

type method_owner =
  | Type_owner of { type_ : Types.ty; list : Types.ty option }
  | Named_owner of string
  | Path_owner of Path.t

type cost_callee =
  | Function_parameter of string
  | Bound_method of { self_type : Types.ty; method_ : string }
  | Unknown_callee

type cost_operand = { cost_function : Language.Metric.t; callee : cost_callee }

type not_callee =
  | Operand_is_neither
  | Local_of_type of { name : string; type_ : Types.ty }
  | Name_is_neither of string

type not_data = Function_type | Handle | Shared_state
type empty_literal = Empty_list | Empty_map
type integer_operator = Bitwise | Shift | Complement
type joined_piece = Fragment of Core.origin | Interpolated of Core.origin
type specification_call = Theorem_call | Mentions of Types.ty | Specification_function_call
type specification_subject = Binding_subject of Core.origin | Value_subject

type undetermined =
  | Binding_type
  | Generic_argument of { parameter : string; is_type : bool; declared_on : Path.t }
  | List_element
  | Map_entries
  | Lambda_parameter

type t =
  | Mismatch of { at : Core.origin; mismatch : mismatch; decision : decision option }
  | Integer_for_float of { at : Core.origin; wanted : shown; literals : (Core.origin * Z.t) list }
  | Decided_in_specification of { at : Core.origin; local : Core.origin option }
  | Operator_output of {
      at : Core.origin;
      found : Types.ty;
      wanted : Types.ty;
      impl_need : impl_need option;
    }
  | Operator_not_implemented of {
      at : Core.origin;
      subject : Types.ty;
      trait : Types.trait_reference;
      impl_need : impl_need option;
    }
  | Not_implemented of {
      at : Core.origin;
      subject : Types.ty;
      trait : Types.trait_reference;
      is_iteration : bool;
      impl_need : impl_need option;
    }
  | Body_ends_without_value of { body : Core.origin; output : Types.ty }
  | Last_statement_without_value of { statement : Core.origin; output : Types.ty }
  | Not_bit_vector of { at : Core.origin; type_ : Types.ty }
  | Unchecked_invariant of { at : Core.origin }
  | Argument_count of { at : Core.origin; callee : counted_callee; expected : int; given : int }
  | Label_in_indirect_call of { label : Core.origin; value : Core.origin }
  | Not_callable of { at : Core.origin; callee : shown }
  | Missing_parameter of { at : Core.origin; parameter : string }
  | Unknown_variant of {
      at : Core.origin;
      type_ : Types.ty;
      variant : string;
      candidates : string list;
    }
  | Variant_without_fields of { at : Core.origin; variant : string }
  | Not_a_record_construction of { at : Core.origin; type_ : Types.ty }
  | Opaque_construction of { at : Core.origin; type_ : Types.ty }
  | Mut_base_of_with of { at : Core.origin }
  | Unknown_label of {
      label : Core.origin;
      written : string;
      owner : owner option;
      candidates : string list;
    }
  | Positional_after_labeled of { argument : Core.origin; label : string option }
  | Tuple_argument_out_of_order of {
      argument : Core.origin;
      owner : owner;
      filled : string;
      field : string;
    }
  | Bare_value of {
      argument : Core.origin;
      owner : bare_owner;
      fields : string list;
      label : string option;
    }
  | Repeated_argument of { at : Core.origin; name : string; is_pattern : bool }
  | Not_an_integer of { at : Core.origin; subject : integer_subject; excluded : shown }
  | No_method of { at : Core.origin; owner : method_owner; name : string; candidates : string list }
  | Counted_not_a_capability of { at : Core.origin; written : string }
  | Counted_not_a_function of { at : Core.origin; name : string; type_ : Types.ty }
  | Counted_neither of { at : Core.origin; name : string }
  | Cost_of_other_metric of {
      at : Core.origin;
      operand : cost_operand;
      cost_function_name : Core.origin;
      bounded : Language.Metric.t;
    }
  | Cost_of_calls of { at : Core.origin; operand : cost_operand }
  | Upper_bound_in_exact_bound of { at : Core.origin; operand : cost_operand }
  | Unbounded_time of { clause : Core.origin; condition : Types.condition; has_condition : bool }
  | Clause_never_holds of { at : Core.origin }
  | Constant_out_of_range of {
      at : Core.origin;
      constant : Z.t;
      type_ : Types.ty;
      low : Z.t;
      high : Z.t;
    }
  | Division_by_zero of { at : Core.origin }
  | Default_not_constant of { at : Core.origin }
  | Not_constant of { at : Core.origin }
  | Condition_not_constant of { at : Core.origin }
  | Condition_names_parameter of { at : Core.origin }
  | Constant_not_data of { at : Core.origin; part : not_data }
  | Hidden_in_public_clause of { at : Core.origin; name : string; hidden : Path.t }
  | Float_too_large of { at : Core.origin; target : shown }
  | Runs_in_formula of { at : Core.origin; construct : formula_construct }
  | Self_outside_method of { at : Core.origin }
  | Self_type_as_value of { at : Core.origin }
  | Quantifier_over_type_in_code of { at : Core.origin }
  | Static_method_as_value of { at : Core.origin; name : string }
  | Method_with_type_arguments_as_value of { at : Core.origin }
  | String_indexed of { at : Core.origin }
  | Not_sliceable of { at : Core.origin; base : shown }
  | Not_indexable of { at : Core.origin; base : shown }
  | Several_indexes of { at : Core.origin }
  | Parameter_with_arguments of { at : Core.origin; name : string }
  | Type_arity of { at : Core.origin; type_path : Path.t; expected : int; given : int }
  | Associated_in_type_arguments of { at : Core.origin }
  | Not_a_type_argument of { at : Core.origin }
  | Hidden_member of { at : Core.origin; hidden : Path.t; visibility : Language.Visibility.t }
  | No_receiver_overload of { at : Core.origin; name : string }
  | Old_arity of { at : Core.origin; given : int }
  | Final_misused of { at : Core.origin }
  | Identical_arity of { at : Core.origin; given : int }
  | Not_a_function_or_type of { at : Core.origin; name : string }
  | Callback_ensures_in_code of { at : Core.origin; name : string }
  | Callback_ensures_label of { at : Core.origin; name : string }
  | Callback_ensures_arity of {
      at : Core.origin;
      name : string;
      inputs : Language.Mode.t list;
      has_result : bool;
      given : int;
    }
  | Ensures_of_non_parameter of { at : Core.origin; name : string }
  | Ensures_without_function of { at : Core.origin; base : shown }
  | Cost_operand_not_callee of {
      at : Core.origin;
      metric : Language.Metric.t;
      operand : not_callee;
    }
  | No_bound_method of { at : Core.origin; type_ : Types.ty; name : string }
  | Ambiguous_cost_method of {
      at : Core.origin;
      type_ : Types.ty;
      name : string;
      metric : Language.Metric.t;
    }
  | New_on_literal_type of {
      at : Core.origin;
      type_ : Types.ty;
      literal : empty_literal;
      call : Core.origin option;
    }
  | Ambiguous_static_method of {
      at : Core.origin;
      type_ : Types.ty;
      name : string;
      traits : Types.trait_reference list;
    }
  | Trait_arity of { at : Core.origin; trait : Types.trait_reference; expected : int; given : int }
  | Receiver_missing_in_full_call of { at : Core.origin }
  | Wrong_receiver_overload of {
      at : Core.origin;
      name : string;
      wanted : Path.receiver;
      overloads : Path.receiver list;
    }
  | Missing_receiver_mode of { receiver : Core.origin; name : string }
  | Ambiguous_method_call of {
      at : Core.origin;
      call : Core.origin;
      type_ : Types.ty;
      name : string;
      receiver : Core.origin;
      arguments : Core.origin Description.range list;
      traits : (Types.trait_reference * Language.Mode.t) list;
    }
  | Index_not_mutable of { at : Core.origin; by : mutation; self_type : Types.ty; assigns : bool }
  | View_written of { at : Core.origin; by : mutation; view : Core.origin }
  | Mutation_in_formula of { at : Core.origin; by : mutation }
  | Captured_mutation of { at : Core.origin; by : mutation; name : string }
  | Read_only_mutation of { at : Core.origin; by : mutation; name : string }
  | Lent_read_only_assigned of { at : Core.origin }
  | Mode_on_assignment_target of {
      at : Core.origin;
      inner : Core.origin;
      keyword : Language.Mode.t;
    }
  | Not_assignable_place of { at : Core.origin }
  | Mode_on_read_argument of { at : Core.origin; inner : Core.origin; parameter : string }
  | Missing_mut_argument of { at : Core.origin; parameter : string }
  | Lent_read_only_argument of { at : Core.origin; parameter : string }
  | Temporary_passed_mut of { at : Core.origin; parameter : string }
  | Redundant_own of { at : Core.origin; inner : Core.origin; type_ : Types.ty }
  | Mut_for_own of { at : Core.origin; parameter : string }
  | Lambda_parameter_mode of {
      at : Core.origin;
      type_expression : Core.origin;
      passed : Language.Mode.t;
      annotated : Language.Mode.t;
    }
  | Type_parameter_as_value of { at : Core.origin; name : string }
  | Theorem_as_value of { at : Core.origin; name : string }
  | Type_as_value of { at : Core.origin; name : string }
  | Trait_as_value of { at : Core.origin; name : string }
  | Specification_function_as_value of { at : Core.origin; name : string }
  | Variant_with_fields_as_function of { at : Core.origin; variant : string; fields : string list }
  | No_variants of { at : Core.origin; type_ : Types.ty }
  | Unknown_field of { at : Core.origin; base : shown; name : string; candidates : string list }
  | Opaque_field_read of { at : Core.origin; type_ : Types.ty }
  | Method_as_field of { at : Core.origin; name : string }
  | Lending_function_value of { at : Core.origin }
  | View_passed_mut of { at : Core.origin }
  | View_receiver of { at : Core.origin; name : string; receivers : Path.receiver list }
  | No_member of { at : Core.origin; type_ : Types.ty; name : string; list : string option }
  | Type_argument_count of { at : Core.origin; expected : int; given : int }
  | Type_for_value_argument of { at : Core.origin }
  | Value_for_type_argument of { at : Core.origin }
  | Specification_call_in_code of { at : Core.origin; name : string; call : specification_call }
  | Not_an_integer_operand of { at : Core.origin; operator : integer_operator; excluded : shown }
  | Shift_amount_not_unsigned of { at : Core.origin; excluded : shown }
  | Try_error_mismatch of { at : Core.origin; output_error : Types.ty; error : Types.ty }
  | Try_misused of { at : Core.origin }
  | Implies_in_code of { at : Core.origin }
  | String_addition of { at : Core.origin; join : (joined_piece * joined_piece) option }
  | Alternative_type_mismatch of {
      at : Core.origin;
      name : string;
      first : Types.ty;
      here : Types.ty;
    }
  | Range_pattern_type of { at : Core.origin; excluded : shown }
  | Variant_pattern_without_fields of { at : Core.origin; variant : string }
  | Parenthesized_tuple_pattern of {
      at : Core.origin;
      patterns : Core.origin Description.range;
      type_ : Types.ty;
    }
  | Not_a_record_pattern of { at : Core.origin; type_ : shown }
  | Not_a_tuple_type_pattern of { at : Core.origin; type_ : shown }
  | Tuple_pattern_arity of { at : Core.origin; type_ : Types.ty; fields : string list; given : int }
  | Tuple_pattern_for_record of {
      at : Core.origin;
      type_ : Types.ty;
      fields : string list;
      form : (string option * Core.origin) list option;
    }
  | Opaque_pattern of { at : Core.origin; type_ : Types.ty }
  | Tuple_pattern_out_of_order of {
      at : Core.origin;
      type_ : Types.ty;
      name : string;
      bound_field : string;
      reorder : string list option;
    }
  | Unmatched_fields of { at : Core.origin; missing : string list }
  | Not_structural of { at : Core.origin; type_ : Types.ty; constant : string }
  | Not_a_constant of { at : Core.origin }
  | Literal_does_not_fit of {
      at : Core.origin;
      number : Z.t;
      excluded : shown;
      low : Z.t;
      high : Z.t;
    }
  | Negated_unsigned of { at : Core.origin; excluded : shown; is_unsigned : bool }
  | Literal_fits_no_integer of { at : Core.origin; number : Z.t }
  | Character_literal of { at : Core.origin; tag : Language.Builtin_type.t }
  | Integer_pattern_type of { at : Core.origin; excluded : shown }
  | String_pattern_type of { at : Core.origin; type_ : Types.ty }
  | Capability_mismatch of {
      at : Core.origin;
      left : Types.capability_set;
      right : Types.capability_set;
    }
  | Undetermined of { at : Core.origin; undetermined : undetermined }
  | Types_undetermined of { at : Core.origin }
  | Trait_arguments_undetermined of { at : Core.origin; trait : Path.t }
  | Range_not_integer of { at : Core.origin; owner : range_owner; element : Types.ty }
  | Unused_value of { at : Core.origin; type_ : Types.ty }
  | Let_else_falls_through of { at : Core.origin }
  | Not_iterable_loop of { at : Core.origin; mode : Language.Mode.t; is_view : bool; type_ : shown }
  | Cursor_not_cursor of { at : Core.origin; type_ : Types.ty; cursor : Types.ty }
  | Not_displayable of { at : Core.origin; type_ : Types.ty }
  | Interpolation_not_convertible of {
      at : Core.origin;
      interpolated_type : Types.ty;
      interpolation_type : Types.ty;
      tag_type : Types.ty;
    }
  | Not_a_tag of { at : Core.origin; tag_type : Types.ty }
  | Tag_not_a_type of { at : Core.origin }
  | Array_length of { at : Core.origin; given : int; count : Z.t }
  | Lambda_arity of { at : Core.origin; given : int; function_type : Types.ty; expected : int }
  | Arm_pattern_count of { at : Core.origin; given : int; expected : int }
  | Not_iterable_quantifier of { at : Core.origin; type_ : shown }
  | Specification_only_type of {
      at : Core.origin;
      subject : specification_subject;
      type_ : Types.ty;
      specification_type : Types.ty;
    }
