(* The tests of exhaustiveness and reachability. *)

open Harness
open Support

let check = Checks.For_testing.through Patterns
let one_diagnostic = one_diagnostic ~check
let fine text = no_diagnostics ~check [ ("app::main", text) ]
let priority = Fixtures.Patterns.priority

let message text =
  let database = setup [ ("app::main", text) ] in
  match check database (file_of "app::main") with
  | [ diagnostic ] -> diagnostic.message
  | actual -> failwith (Printf.sprintf "%d diagnostics" (List.length actual))

let () =
  test "a missing case is named" (fun () ->
      let text = priority ^ Fixtures.Patterns.missing_case_is_named in
      let actual = message text in
      let expected = "`Some(Urgent(_))` is not covered" in
      if not (Substring.contains actual expected) then fail "message %S" actual);
  test "a missing case's fix adds an arm with todo" (fun () ->
      one_diagnostic Fixtures.Patterns.missing_cases_fix_adds_an_arm_with_todo
        "patterns.not_covered"
        ~fixed:Fixtures.Patterns.missing_cases_fix_adds_an_arm_with_todo_fixed);
  test "an arm earlier arms cover is an error with a fix that deletes it" (fun () ->
      one_diagnostic Fixtures.Patterns.arm_earlier_arms_cover_is_an_error_with_a_fix_that
        "patterns.unreachable_arm"
        ~fixed:Fixtures.Patterns.arm_earlier_arms_cover_is_an_error_with_a_fix_that_fixed);
  test "an alternative the alternatives before it cover is an error" (fun () ->
      one_diagnostic Fixtures.Patterns.alternative_the_alternatives_before_it_cover_is_an
        "patterns.unreachable_alternative");
  test "an arm with a guard does not cover its pattern" (fun () ->
      one_diagnostic Fixtures.Patterns.arm_with_a_guard_does_not_cover_its_pattern
        "patterns.not_covered");
  test "integer ranges that cover the type are exhaustive" (fun () ->
      fine Fixtures.Patterns.integer_ranges_that_cover_the_type_are_exhaustive);
  test "integer ranges that leave a gap name it" (fun () ->
      let actual = message Fixtures.Patterns.integer_ranges_that_leave_a_gap_name_it in
      if not (Substring.contains actual "`100`") then fail "message %S" actual);
  test "a match on a string needs a pattern that matches everything" (fun () ->
      one_diagnostic Fixtures.Patterns.match_on_a_string_needs_a_pattern_that_matches
        "patterns.not_covered");
  test "a match over several values is checked as one" (fun () ->
      fine Fixtures.Patterns.match_over_several_values_is_checked_as_one);
  test "a match over several values misses a combination" (fun () ->
      one_diagnostic Fixtures.Patterns.match_over_several_values_misses_a_combination
        "patterns.not_covered");
  test "a pattern that can fail cannot be a let's" (fun () ->
      one_diagnostic Fixtures.Patterns.pattern_that_can_fail_cannot_be_a_lets "patterns.refutable");
  test "a record pattern cannot fail" (fun () -> fine Fixtures.Patterns.record_pattern_cannot_fail);
  test "a constant in a pattern is its value" (fun () ->
      fine Fixtures.Patterns.constant_in_a_pattern_is_its_value)

(* Constants in patterns *)

let () =
  let codes_of text =
    let database = setup [ ("app::main", text) ] in
    (match parse_errors database (file_of "app::main") with
    | [] -> ()
    | errors -> fail "the test input does not parse: %s" (String.concat " " errors));
    codes (check database (file_of "app::main"))
  in
  let expect text expected =
    match codes_of text with
    | actual when actual = expected -> ()
    | actual -> fail "found [%s]" (String.concat "; " actual)
  in
  test "a qualified constant covers only its value" (fun () ->
      expect Fixtures.Patterns.qualified_constant_covers_only_its_value [ "patterns.not_covered" ]);
  test "a range with a constant end covers only up to it" (fun () ->
      expect Fixtures.Patterns.range_with_a_constant_end_covers_only_up_to_it
        [ "patterns.unreachable_alternative" ]);
  test "a range with a constant end is not a wildcard" (fun () ->
      expect Fixtures.Patterns.range_with_a_constant_end_is_not_a_wildcard
        [ "patterns.not_covered" ]);
  test "a Bool constant covers its value" (fun () ->
      expect Fixtures.Patterns.bool_constant_covers_its_value []);
  test "a variant constant covers its variant" (fun () ->
      expect Fixtures.Patterns.variant_constant_covers_its_variant []);
  test "a constant whose value is not evaluated at compile time covers only itself" (fun () ->
      expect Fixtures.Patterns.constant_whose_value_is_not_evaluated_at_compile [])

(* Errors reported once *)

let () =
  let codes_of text = codes (check (setup [ ("app::main", text) ]) (file_of "app::main")) in
  test "a generic parameter that is a value covers nothing else" (fun () ->
      one_diagnostic Fixtures.Patterns.generic_parameter_that_is_a_value_covers_nothing
        "patterns.not_covered");
  test "a record constant covers the record it is" (fun () ->
      one_diagnostic Fixtures.Patterns.record_constant_covers_the_record_it_is
        "patterns.unreachable_arm");
  test "a match on a type that failed to parse reports nothing more" (fun () ->
      match codes_of Fixtures.Patterns.match_on_a_type_that_failed_to_parse_reports with
      | actual when List.mem "patterns.not_covered" actual ->
          fail "found [%s]" (String.concat "; " actual)
      | _ -> ());
  test "code that builds a type that failed to parse reports nothing more" (fun () ->
      (* The definition that builds the value has no error of its own. It
         must still have no core form, or building one stops the compiler. *)
      List.iter
        (fun argument ->
          match
            codes_of
              ("type Entry = {\n\
               \  name: String\n\
                }\n\n\
                fn built(name: String) -> Entry {\n\
               \  Entry(name: " ^ argument ^ ")\n}\n")
          with
          | [] -> ()
          | actual -> fail "found [%s]" (String.concat "; " actual))
        [ "own name"; "\"${name}\"" ]);
  test "a sub-pattern that failed to type makes no arm unreachable" (fun () ->
      match codes_of Fixtures.Patterns.sub_pattern_that_failed_to_type_makes_no_arm with
      | actual when List.exists (fun code -> String.starts_with ~prefix:"patterns." code) actual ->
          fail "found [%s]" (String.concat "; " actual)
      | _ -> ())

(* Alternatives *)

let () =
  test "an alternative that an earlier arm covers is unreachable, even the first" (fun () ->
      one_diagnostic Fixtures.Patterns.alternative_that_an_earlier_arm_covers_is
        "patterns.unreachable_alternative"
        ~fixed:Fixtures.Patterns.alternative_that_an_earlier_arm_covers_is_fixed);
  test "a nested alternative that the one before covers is unreachable" (fun () ->
      one_diagnostic Fixtures.Patterns.nested_alternative_that_the_one_before_covers_is
        "patterns.unreachable_alternative")

let () =
  test "character literals and ranges cover their values" (fun () ->
      one_diagnostic Fixtures.Patterns.character_literals_and_ranges_cover_their_values
        "patterns.unreachable_arm")
