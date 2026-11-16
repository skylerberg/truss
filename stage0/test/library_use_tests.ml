let check packages file =
  let database = Support.database packages in
  match Support.diagnostics database file with
  | [] -> Support.proof_diagnostics database file
  | errors -> errors

let proven text = Support.no_diagnostics ~check [ ("app::main", text) ]

let () =
  Harness.test "a map that was inserted into holds the key" (fun () ->
      proven Fixtures.Library_use.maps_built_by_insert);
  Harness.test "a password is hashed with the default cost and with a cost that meets its limits"
    (fun () -> proven Fixtures.Library_use.password_hashes_with_default_and_given_costs);
  Harness.test "a map literal has its keys and its length" (fun () ->
      proven Fixtures.Library_use.map_literal_with_two_entries);
  Harness.test "a key that a map contains can be indexed" (fun () ->
      proven Fixtures.Library_use.map_indexed_after_contains);
  Harness.test "replace leaves the key in the map" (fun () ->
      proven Fixtures.Library_use.map_replace);
  Harness.test "take and clear leave a map without the key" (fun () ->
      proven Fixtures.Library_use.map_take_and_clear);
  Harness.test "maps and sets are compared" (fun () ->
      proven Fixtures.Library_use.map_and_set_comparisons);
  Harness.test "a set holds inserted elements and not removed ones" (fun () ->
      proven Fixtures.Library_use.set_insert_and_remove);
  Harness.test "a set literal contains its listed elements and nothing else" (fun () ->
      proven Fixtures.Library_use.set_literal_with_two_elements)

let () =
  Harness.test "a display that ends is proven, and a function with a time clause calls it"
    (fun () -> proven Fixtures.Library_use.point_display_called_by_a_timed_function);
  Harness.test "a display that may not end is rejected" (fun () ->
      Support.one_diagnostic ~check Fixtures.Library_use.display_with_an_endless_loop
        "prover.termination")

let () =
  Harness.test "two strings with the same text are equal" (fun () ->
      proven Fixtures.Library_use.two_equal_string_literals)
