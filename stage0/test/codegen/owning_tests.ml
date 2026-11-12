(* Truss source compiled and run: every value is dropped exactly once, on
   every way out of the code that owns it. A test passes only if it frees
   each block it allocates, which the runner checks. *)

open Codegen_support

let () =
  passes "an assignment to an element drops the element it replaces"
    Fixtures.Owning.assignment_to_an_element_drops_the_element_it;
  passes "an early return inside an interpolation drops the text built so far"
    Fixtures.Owning.early_return_inside_an_interpolation_drops_the;
  passes "an argument moved before a later argument returns early is dropped"
    Fixtures.Owning.argument_moved_before_a_later_argument_returns;
  passes "an early return while an any value is being made leaves no block"
    Fixtures.Owning.early_return_while_an_any_value_is_being_made;
  passes "an any value drops what its value owns, also when it is made in a loop"
    Fixtures.Owning.any_value_drops_what_its_value_owns_also_when_it;
  passes "a pulled loop left without taking its value drops the value"
    Fixtures.Owning.pulled_loop_left_without_taking_its_value_drops;
  passes "a loop that uses up a list takes its elements in order"
    Fixtures.Owning.loop_that_uses_up_a_list_takes_its_elements_in;
  passes "a loop that uses up a list and is left early drops the elements it did not reach"
    Fixtures.Owning.loop_that_uses_up_a_list_and_is_left_early_drops;
  passes "a loop that uses up an array takes its elements in order"
    Fixtures.Owning.loop_that_uses_up_an_array_takes_its_elements_in;
  passes "a loop that uses up an array and is left early drops the elements it did not reach"
    Fixtures.Owning.loop_that_uses_up_an_array_and_is_left_early_drops;
  passes "an array given up as a list keeps its elements in order"
    Fixtures.Owning.array_given_up_as_a_list_keeps_its_elements_in;
  passes "continue keeps a list a loop is over, when the list is a call's result"
    Fixtures.Owning.continue_keeps_a_list_a_loop_is_over_when_the_list;
  passes "a loop over a yielding function that takes nothing"
    Fixtures.Owning.loop_over_a_yielding_function_that_takes_nothing;
  passes "an own parameter left to its default is dropped once"
    Fixtures.Owning.own_parameter_left_to_its_default_is_dropped_once;
  passes "a lambda that ignores an own parameter drops it"
    Fixtures.Owning.lambda_that_ignores_an_own_parameter_drops_it;
  passes "a copy of a list with room and no elements has a buffer of its own"
    Fixtures.Owning.copy_of_a_list_with_room_and_no_elements_has_a;
  passes "a copy of a list of values of no size is dropped once"
    Fixtures.Owning.copy_of_a_list_of_values_of_no_size_is_dropped;
  passes "a compound assignment evaluates its target once"
    Fixtures.Owning.compound_assignment_evaluates_its_target_once;
  passes "an assignment evaluates its value, then its target's index keys"
    Fixtures.Owning.assignment_evaluates_its_value_then_its_targets;
  passes "a compound assignment to an element frees the replaced value once"
    Fixtures.Owning.compound_assignment_to_an_element_frees_the;
  passes "a compound assignment's operand runs before the operator takes the target"
    Fixtures.Owning.compound_assignments_operand_runs_before_the;
  passes "a result assigned over its own argument reads the argument as it was"
    Fixtures.Owning.result_assigned_over_its_own_argument_reads_the
