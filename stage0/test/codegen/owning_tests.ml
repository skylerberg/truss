let () =
  Codegen_support.passes
    "a value moved in one iteration and given one in the next is not dropped twice"
    Fixtures.Owning.value_moved_and_reassigned_in_a_loop;
  Codegen_support.passes "an assignment to an element drops the element it replaces"
    Fixtures.Owning.element_replaced_test;
  Codegen_support.passes "an early return inside an interpolation drops the text built so far"
    Fixtures.Owning.question_mark_inside_an_interpolation;
  Codegen_support.passes "an argument moved before a later argument returns early is dropped"
    Fixtures.Owning.pair_with_an_early_returning_argument;
  Codegen_support.passes "an early return while an any value is being made leaves no block"
    Fixtures.Owning.question_mark_while_making_an_any_value;
  Codegen_support.passes
    "an any value drops its value's owned parts, also when it is made in a loop"
    Fixtures.Owning.named_any_values_made_in_a_loop;
  Codegen_support.passes "a copy of an any value owns a box of its own"
    Fixtures.Owning.copy_of_an_any_value;
  Codegen_support.passes "a copy of a list of any values owns their boxes"
    Fixtures.Owning.copy_of_a_list_of_any_values;
  Codegen_support.passes "an any value of a zero-size type and its copy drop"
    Fixtures.Owning.any_of_a_zero_size_type_copied;
  Codegen_support.passes
    "a loop over a cursor that is left without taking its value drops the value"
    Fixtures.Owning.words_cursor_loop_left_early;
  Codegen_support.passes "a loop that uses up a list takes its elements in order"
    Fixtures.Owning.join_of_an_own_list;
  Codegen_support.passes
    "a loop that uses up a list and is left early drops the elements it did not reach"
    Fixtures.Owning.own_list_loop_left_early;
  Codegen_support.passes "a loop that uses up an array takes its elements in order"
    Fixtures.Owning.join_of_an_own_array;
  Codegen_support.passes
    "a loop that uses up an array and is left early drops the elements it did not reach"
    Fixtures.Owning.own_array_loop_left_early;
  Codegen_support.passes "an array moved into a list keeps its elements in order"
    Fixtures.Owning.array_to_list_test;
  Codegen_support.passes "continue keeps a list a loop is over, when the list is a call's result"
    Fixtures.Owning.loop_with_continue_over_a_made_list;
  Codegen_support.passes "an own parameter left to its default is dropped once"
    Fixtures.Owning.total_with_an_own_list_default;
  Codegen_support.passes "a lambda that ignores an own parameter drops it"
    Fixtures.Owning.lambda_ignoring_an_own_parameter;
  Codegen_support.passes "a copy of a list with room and no elements has a buffer of its own"
    Fixtures.Owning.copy_of_an_empty_list_with_capacity;
  Codegen_support.passes "a copy of a list of values of no size is dropped once"
    Fixtures.Owning.copy_of_a_list_of_quiet_values;
  Codegen_support.passes "a compound assignment evaluates its target once"
    Fixtures.Owning.compound_assignment_with_a_counted_index;
  Codegen_support.passes "an assignment evaluates its value, then its target's index keys"
    Fixtures.Owning.digit_ordered_assignment;
  Codegen_support.passes "a compound assignment to an element frees the replaced value once"
    Fixtures.Owning.bag_element_added_to;
  Codegen_support.passes "a compound assignment's operand runs before the operator takes the target"
    Fixtures.Owning.bag_element_added_to_by_a_mutating_operand;
  Codegen_support.passes "a result assigned over its own argument reads the argument as it was"
    Fixtures.Owning.quad_swapped_over_itself
