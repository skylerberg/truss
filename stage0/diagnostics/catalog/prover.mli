type quoted = { key : Path.key; origin : Core.origin }
type location = Node of Core.origin | Whole_definition
type call = { at : location; callee : Path.t option }
type counting = Upper_bound | Exact
type moment = On_entry | After_iteration | Where_left

type value =
  | Named of string
  | Quoted of quoted
  | Temporary
  | Self_value
  | Compiler_local
  | Lent_part

type changed_part = { root : value; fields : string list }

type invariant_moment =
  | When_lend_ends
  | When_passed of call
  | Lambda_result
  | Lambda_mut_parameter
  | Returned_value
  | Mut_parameter_at_return of string
  | Self_at_return
  | Built_here
  | At_scope_end of value
  | Element_changed
  | Part_lent

type requirement =
  | Room_written
  | Elements_mutated
  | Elements_read
  | Ends_with_zero
  | Elements_at_both_indexes
  | Length_within_storage
  | Element_to_pop
  | Element_at_index
  | Index_within_length
  | Range_within_view
  | Count_of_array

type recursion_impl = Derives | Inherits

type supplied_recursion =
  | Named_function of Path.t
  | Bound_through_call of { call : call; owner : Path.t }
  | Bound_through_name of { path : Path.t; owner : Path.t }
  | Provided of Path.t

type dependency_kind = Reads | Calls | Uses
type omitted = Omitted_field of string | Omitted_argument of string
type dependency = { kind : dependency_kind; path : Path.t; omitted : omitted option }

type unbounded =
  | Unstated_costs of {
      metric : Language.Metric.t;
      callees : Path.t list;
      editable : Path.t list;
      counts_units : bool;
    }
  | Changing_cost of { is_amortized : bool; call : quoted; values : changed_part list }
  | Unbounded_iteration

type promiser = Trait_promiser | Capability_promiser

type promise =
  | Own_promise of { counting : counting; clause : quoted }
  | Inherited_promise of { counting : counting; promiser : promiser; clause : quoted }
  | Restated_promise of {
      counting : counting;
      for_type : Types.ty;
      name : string;
      clause : quoted;
      trait : Types.trait_reference;
      declared : Types.trait_reference;
    }

type callback_reason = Used_as_unpromising_value | Passed_for_unpromising_parameter

type unpromised =
  | Nothing_promises
  | Type_may_not_promise of string
  | Type_promises_nothing of string
  | Ensures_may_not_promise of Path.t

type obligation =
  | Assertion_may_fail of { clause : quoted }
  | Bit_vector_assertion_may_fail of { clause : quoted }
  | Desugared_assertion_may_fail of { call : call }
  | Recursion_not_on_part of { call : call; compared : string list }
  | Recursion_may_not_end of { call : call; is_self_call : bool }
  | Uncompared_recursion of { call : call }
  | Measure_may_not_decrease of { call : call; measures : quoted list }
  | Recursion_through_impl of { call : call; impl : recursion_impl }
  | Recursion_through_supply of supplied_recursion
  | Constant_cycle of { cyclic : Path.t; dependency : dependency }
  | Precondition_may_fail of { clause : quoted; call : call }
  | Precondition_may_panic of { clause : quoted; call : call }
  | Panics_where_ruled_out of { call : call; condition : quoted list }
  | Upper_bound_in_exact_cost of { metric : Language.Metric.t; call : call }
  | Out_of_bounds of { at : quoted }
  | Intrinsic_requirement of { at : quoted; requirement : requirement }
  | Invariant_may_fail of { type_ : Types.ty; moment : invariant_moment }
  | Preserved_invariant of { type_ : Types.ty; value : value }
  | Derived_default_invariant
  | Loop_invariant of { clause : quoted; moment : moment }
  | Lambda_promise of { promise : quoted }
  | Lambda_cost of { counting : counting; type_ : Types.ty }
  | Lambda_call_above_bound of { metric : Language.Metric.t }
  | Callback_precondition of { clause : quoted; call : call; name : string }
  | Parameter_contract of { path : Path.t; clause : quoted }
  | Loop_cost_clause of { clause : quoted; moment : moment }
  | Iteration_above_inferred_bound
  | Unbounded_iteration_cost of unbounded
  | Visited_out_of_order
  | Loop_measure_may_not_decrease
  | Element_count_changes
  | Out_of_range of { at : quoted; type_ : Types.ty }
  | Divisor_may_be_zero of { at : quoted }
  | Division_overflow of { at : quoted; type_ : Types.ty }
  | Overflow of { at : quoted; type_ : Types.ty }
  | Shift_amount of { amount : quoted; is_operand : bool; bits : int }
  | Float_conversion of { at : quoted; target : Types.ty }
  | Not_a_scalar_value of { at : quoted }
  | Unreachable_reached
  | Lent_part_ensures of { clause : quoted }
  | Cost_promise of promise
  | Impl_precondition of { clause : quoted }
  | Impl_panic_condition of { clause : quoted }
  | Ensures_at_method_end of { clause : quoted }
  | Ensures_at_return of { clause : quoted }
  | Promiser_ensures of { promiser : promiser; clause : quoted }
  | Law_may_fail of { trait : Types.trait_reference; law : string; for_type : Types.ty }
  | Restated_contract of {
      for_type : Types.ty;
      name : string;
      clause : quoted;
      trait : Types.trait_reference;
      declared : Types.trait_reference;
    }
  | Negative_potential of { type_ : Types.ty }
  | May_alias of { first : quoted; second : quoted }
  | Callback_requirement of { name : string; reason : callback_reason; clause : quoted }
  | Callback_promise of { promise : quoted; unpromised : unpromised }
  | Duplicate_key of { key : quoted option }
  | Value_contract of { path : Path.t; type_ : Types.ty; clause : quoted }

type construct =
  | Potential_of_elements
  | Metric_of_non_trait_method of Language.Metric.t
  | Calls_target
  | Unsolved_size
  | Elements_of of Types.ty
  | Sequence_elements
  | Function_value_costs
  | Intrinsic_at_parameter of { operation : string; parameter : Types.ty }
  | Negation_of of Types.ty
  | Shift_of of Types.ty
  | Slice_of of Types.ty
  | Unreadable_parameter_type
  | Unreadable_cursor of Types.ty
  | Field of string
  | Alternatives_binding_mut
  | Hidden_field_of of Types.ty
  | Fields_of of Types.ty
  | Constant_assignment
  | Float_literal_without_type
  | Lent_part_outside_lending_method
  | Hidden_variant_of of Types.ty
  | Nonreturning_specification_call
  | Compiler_restated_method of { trait : Types.trait_reference; declared_by : Path.t }
  | Literal_of of Types.ty
  | Unreadable_function_value
  | String_pattern_on of Types.ty
  | Specification_function

type failed_run = Constant_run of { path : Path.t; report : string } | Assertion_run of string

type path_note =
  | Arm_taken of Core.origin list
  | Condition_holds of { condition : Core.origin; holds : bool }
  | Else_runs of Core.origin
  | Returns_early of Core.origin

type unknown = Out_of_steps | Incomplete of string

type failure =
  | Refuted
  | Counterexample of {
      values : (string * string) list;
      path : path_note list;
      failed_runs : failed_run list;
    }
  | Undecided of { unknown : unknown; has_untriggered_fact : bool; failed_runs : failed_run list }

type required =
  | Code of string
  | Substituted_clause of {
      clause : quoted;
      replacements : (Core.origin * string) list;
      type_names : (string * string) list;
    }

type panic_place =
  | After_uses of Core.origin
  | Before_clause of Core.origin
  | Before_body of Core.origin

type fix =
  | Add_requires of {
      body : Core.origin;
      required : required list;
      premise : string option;
      condition : Types.condition;
    }
  | Add_panic of panic_place

type citation = Cited_here | Cited_at of { path : string; line : int }
type instance = (string * Language.Builtin_type.t) list

type t =
  | Proves of { location : location; instance : instance; obligation : obligation }
  | Unproven of {
      location : location;
      instance : instance;
      obligation : obligation;
      failure : failure;
      fixes : fix list;
      cited : quoted option;
    }
  | Unreadable of { location : location; construct : construct; foreign : string option }
  | Unevaluated of { path : Path.t; report : string }
