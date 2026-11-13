(* The standard library's contracts, read from another package. Each test
   is a small program a user might write, proven against the library as it
   stands, so a contract that only the library's own package can read
   fails here. *)

open Harness

let solver = Lazy.force Support.solver

let check database module_ =
  match Checks.diagnostics database module_ with
  | [] -> Prover.diagnostics ~record:(Support.record database) database solver module_
  | errors -> errors

let proven text = Support.no_diagnostics ~check [ ("app::main", text) ]

let () =
  test "a map that was inserted into holds the key" (fun () ->
      proven Fixtures.Library_use.map_that_was_inserted_into_holds_the_key);
  test "a password is hashed with the default cost and with a cost that meets its limits" (fun () ->
      proven Fixtures.Library_use.password_is_hashed_with_the_default_cost_and_with);
  test "a map literal has its keys and its length" (fun () ->
      proven Fixtures.Library_use.map_literal_has_its_keys_and_its_length);
  test "a key that a map contains can be indexed" (fun () ->
      proven Fixtures.Library_use.key_that_a_map_contains_can_be_indexed);
  test "replace leaves the key in the map" (fun () ->
      proven Fixtures.Library_use.replace_leaves_the_key_in_the_map);
  test "take and clear leave a map without the key" (fun () ->
      proven Fixtures.Library_use.take_and_clear_leave_a_map_without_the_key);
  test "maps and sets are compared" (fun () ->
      proven Fixtures.Library_use.maps_and_sets_are_compared);
  test "a set holds inserted elements and not removed ones" (fun () ->
      proven Fixtures.Library_use.set_holds_inserted_elements_and_not_removed_ones);
  test "a set literal contains its listed elements and nothing else" (fun () ->
      proven Fixtures.Library_use.set_literal_contains_its_listed_elements_and)

let () =
  test "a display that ends is proven, and a function with a time clause calls it" (fun () ->
      proven Fixtures.Library_use.display_that_ends_is_proven_and_a_function_with_a);
  test "a display that may not end is rejected" (fun () ->
      Support.one_diagnostic ~check Fixtures.Library_use.display_that_may_not_end_is_rejected
        "prover.termination")

let () =
  test "two strings with the same text are equal" (fun () ->
      proven Fixtures.Library_use.two_strings_with_the_same_text_are_equal)
