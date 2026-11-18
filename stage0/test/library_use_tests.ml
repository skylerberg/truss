let check packages file =
  let database = Support.make_database packages in
  match Support.list_diagnostics database file with
  | [] -> Support.list_proof_diagnostics database file
  | errors -> errors

let expect_proven text = Support.expect_no_diagnostics ~check [ ("app::main", text) ]

let () =
  Harness.test "a map that was inserted into holds the key" (fun () ->
      expect_proven Fixtures.Library_use.maps_built_by_insert);
  Harness.test "a password is hashed with the default cost and with a cost that meets its limits"
    (fun () -> expect_proven Fixtures.Library_use.password_hashes_with_default_and_given_costs);
  Harness.test "a map literal has its keys and its length" (fun () ->
      expect_proven Fixtures.Library_use.map_literal_with_two_entries);
  Harness.test "a key that a map contains can be indexed" (fun () ->
      expect_proven Fixtures.Library_use.map_indexed_after_contains);
  Harness.test "replace leaves the key in the map" (fun () ->
      expect_proven Fixtures.Library_use.map_replace);
  Harness.test "take and clear leave a map without the key" (fun () ->
      expect_proven Fixtures.Library_use.map_take_and_clear);
  Harness.test "maps and sets are compared" (fun () ->
      expect_proven Fixtures.Library_use.map_and_set_comparisons);
  Harness.test "a set holds inserted elements and not removed ones" (fun () ->
      expect_proven Fixtures.Library_use.set_insert_and_remove);
  Harness.test "a set literal contains its listed elements and nothing else" (fun () ->
      expect_proven Fixtures.Library_use.set_literal_with_two_elements);
  Harness.test "comparisons, hashes, and lookups state how much they allocate" (fun () ->
      expect_proven Fixtures.Library_use.comparisons_and_lookups_without_allocations);
  Harness.test "a comparison of a list or a string with its view allocates nothing and proves"
    (fun () -> expect_proven Fixtures.Library_use.comparisons_of_owners_and_views);
  Harness.test "a lookup with a view of its key allocates nothing and finds the key's elements"
    (fun () -> expect_proven Fixtures.Library_use.lookups_by_views_of_keys)

let () =
  Harness.test "a display that ends is proven, and a function with a time clause calls it"
    (fun () -> expect_proven Fixtures.Library_use.point_display_called_by_a_timed_function);
  Harness.test "a display that may not end is rejected" (fun () ->
      Support.expect_one_diagnostic ~check Fixtures.Library_use.display_with_an_endless_loop
        "capabilities.may_not_terminate")

let () =
  Harness.test "two strings with the same text are equal" (fun () ->
      expect_proven Fixtures.Library_use.two_equal_string_literals)
