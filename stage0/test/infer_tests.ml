let check packages =
  Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ]
    (Support.make_database packages)

let make_standard_packages files : Project.package list =
  [
    {
      name = Path.standard_package;
      dependencies = [];
      files = List.map (fun (name, text) -> (Support.parse_file name, text)) files;
    };
  ]

let check_as_standard_library packages =
  Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ]
    (Support.extend_standard_library packages)

let expect_one_diagnostic = Support.expect_one_diagnostic ~check
let expect_no_diagnostics = Support.expect_no_diagnostics ~check
let expect_fine text = expect_no_diagnostics [ ("app.main", text) ]

let locate_expression text written occurrence =
  let packages = Support.setup [ ("app.main", text) ] in
  let file = Support.parse_file "app.main" in
  let offset = Support.locate_occurrence ~sub:written ~occurrence text in
  let actual =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = declaration.key in
        match
          ( (Support.make_names packages).read_definition key,
            (Support.make_source packages).read_spans key,
            (Support.make_source packages).read_place key,
            Database.read_checked_body (Support.make_database packages) key )
        with
        | definition, spans, { base; _ }, Some result ->
            let best = ref None in
            let measure (value : Syntax.expression) =
              let span : Source.Definition_span.t = spans.(value.id) in
              span.stop - span.start
            in
            let is_exact value = measure value = String.length written in
            let rec visit (value : Syntax.expression) =
              (if base + spans.(value.id).start = offset then
                 match !best with
                 | Some (other : Syntax.expression)
                   when is_exact other || ((not (is_exact value)) && measure other <= measure value)
                   ->
                     ()
                 | _ -> best := Some value);
              Syntax_walk.visit_children visit value
            in
            Syntax_walk.visit_definition visit definition;
            Option.map (fun value -> (value, result)) !best
        | _ -> None)
      ((Support.make_names packages).list_declarations_in file)
  in
  match actual with
  | Some actual -> actual
  | None -> failwith (Printf.sprintf "no expression at %S" written)

let has_integer text value =
  List.exists
    (fun (node : Core.expression) ->
      match node.kind with Integer actual -> Z.equal actual (Z.of_int value) | _ -> false)
    (Support.collect_first_core_nodes text).expressions

let list_core_at text written occurrence =
  let value, (result : Infer.checked) = locate_expression text written occurrence in
  let form = result.form in
  let nodes = ref [] in
  Core_walk.walk_definition
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) ->
          if Core_walk.locate_origin node.origin = value.id then nodes := node :: !nodes);
    }
    form.definition;
  List.rev !nodes

let locate_core_call text written occurrence =
  match
    List.find_map
      (fun (node : Core.expression) ->
        match node.kind with Call call -> Some (call, node.type_) | _ -> None)
      (list_core_at text written occurrence)
  with
  | Some call -> call
  | None -> failwith (Printf.sprintf "%S is not a call" written)

let is_whole_range : Core.argument -> bool = function
  | {
      value = Value { kind = Use (Range { stop = None; _ }); _ } | Place (Range { stop = None; _ });
      _;
    } ->
      true
  | _ -> false

let expect_type text written ?(occurrence = 1) expected =
  let value, (result : Infer.checked) = locate_expression text written occurrence in
  match result.tables.types.(value.id) with
  | Some type_ ->
      if Types.show type_ <> expected then
        Harness.fail "`%s` has type %s, not %s" written (Types.show type_) expected
  | None -> Harness.fail "`%s` has no type" written

let expect_fix_titles text expected =
  let packages = Support.setup [ ("app.main", text) ] in
  let titles =
    List.concat_map
      (fun (diagnostic : Diagnostic.t) ->
        List.map (fun (fix : Source.span Diagnostic.fix) -> fix.title) diagnostic.fixes)
      (Support.run_check ~check packages "app.main")
  in
  if titles <> expected then
    Harness.fail "expected the fixes [%s], got [%s]"
      (String.concat "; " (List.map (Printf.sprintf "%S") expected))
      (String.concat "; " (List.map (Printf.sprintf "%S") titles))

let () =
  Harness.test "a part with a syntax error is not checked, and the other definitions are" (fun () ->
      let packages =
        Support.setup
          [
            ( "app.main",
              "fn double(x: Int64) -> Int64 {\n\
              \  x\n\
               }\n\n\
               fn piped(name: String) -> Int64 {\n\
              \  name |> double\n\
               }\n\n\
               fn compared(flag: Bool) -> Bool {\n\
              \  flag === 1\n\
               }\n\n\
               fn wrong() -> Int64 {\n\
              \  \"one\"\n\
               }\n" );
          ]
      in
      let file = Support.parse_file "app.main" in
      let database = Support.make_database packages in
      if List.length (Database.For_testing.list_diagnostics [ Parse ] database file) <> 2 then
        Harness.fail "expected two syntax errors";
      match
        Support.list_codes
          (Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ] database file)
      with
      | [ "types.mismatch" ] -> ()
      | reported -> Harness.fail "reported [%s]" (String.concat "; " reported));
  Harness.test "a literal takes the type of the other operand" (fun () ->
      expect_type Fixtures.Prover.addition_that_can_overflow "1" "UInt8");
  Harness.test "a literal nothing decides is an Int64" (fun () ->
      expect_type Fixtures.Infer.var_of_a_literal "0" "Int64");
  Harness.test "a literal takes the expected type" (fun () ->
      expect_type Fixtures.Infer.uint8_let_of_a_literal "3" "UInt8");
  Harness.test "a literal multiplied by a type that is not an integer is an Int64" (fun () ->
      expect_fine Fixtures.Infer.literal_times_a_duration);
  Harness.test "an expression of literals waits for the same decision" (fun () ->
      expect_type Fixtures.Infer.uint16_plus_a_product_of_literals "60" "UInt16");
  Harness.test "a literal that does not fit its type is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.uint8_let_of_300 "types.literal_out_of_range");
  Harness.test "a literal of a type an integer trait bounds is an integer of that type" (fun () ->
      expect_fine Fixtures.Infer.signed_integer_compared_with_minus_one);
  Harness.test "a literal of a type an integer trait bounds must fit every type that implements it"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.signed_integer_compared_with_200
        "types.literal_out_of_range";
      expect_one_diagnostic Fixtures.Infer.fixed_width_integer_compared_with_128
        "types.literal_out_of_range");
  Harness.test "a literal of a type UnsignedInteger bounds cannot be negated" (fun () ->
      expect_one_diagnostic Fixtures.Infer.unsigned_integer_compared_with_minus_one
        "types.negated_unsigned");
  Harness.test "a negated literal is checked after the negation" (fun () ->
      expect_fine Fixtures.Infer.int8_let_of_minus_128);
  Harness.test
    "an integer literal where a float is expected is an error that says to write it as a float, \
     with no fix" (fun () ->
      let text = Fixtures.Infer.integer_literal_as_a_float in
      expect_one_diagnostic text "types.integer_for_float"
        ~says:
          "An integer literal is never a float, and `Float64` is expected here. Write `1` as `1.0`.";
      expect_fix_titles text []);
  Harness.test "a literal shift amount is a UInt64" (fun () ->
      expect_type Fixtures.Infer.shift_by_a_literal "3" ~occurrence:3 "UInt64");
  Harness.test "a loop variable's literal type is decided by the loop's body" (fun () ->
      expect_type Fixtures.Infer.range_loop_index_bound_to_a_uint8 "0" "UInt8");
  Harness.test "a local's literal type is decided by a later statement" (fun () ->
      let text = Fixtures.Infer.literal_decided_by_a_later_comparison in
      expect_type text "10" "UInt8";
      expect_type text "2" "UInt8";
      expect_type text "0.5" "Float32";
      expect_fine text);
  Harness.test "the literal type a local leaves undecided ends with the local's scope" (fun () ->
      let text = Fixtures.Infer.range_loop_bound_to_a_uint8 in
      expect_type text "0" "UInt8";
      expect_type text "5" "UInt64");
  Harness.test "a specification converts a local whose literal type is undecided to Integer"
    (fun () ->
      let text = Fixtures.Infer.requires_of_an_undecided_local in
      expect_type text "0" "UInt8";
      expect_fine text);
  Harness.test "a pattern of a local's undecided literal type is checked once it is decided"
    (fun () ->
      let text = Fixtures.Infer.match_on_an_undecided_literal in
      expect_type text "3" "UInt8";
      expect_fine text);
  Harness.test "a local in a block is decided after the block" (fun () ->
      expect_type Fixtures.Infer.literal_decided_after_its_block "5" "UInt16");
  Harness.test "a local whose literal does not fit the type a later statement decides is an error"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.local_of_300_bound_to_a_uint8
        "types.literal_out_of_range");
  Harness.test "a loop's annotation decides the literals of its range" (fun () ->
      let text = Fixtures.Infer.range_loop_annotated_uint8 in
      expect_type text "10" "UInt8";
      expect_fine text);
  Harness.test "a loop's annotation is the type of a destructured element" (fun () ->
      expect_fine Fixtures.Infer.loop_annotating_a_destructured_element);
  Harness.test "a loop's annotation must be its element type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.loop_over_uint16s_annotated_uint8 "types.mismatch"
        ~says:"Each element of this loop is `UInt16`, not `UInt8`.");
  Harness.test
    "a loop variable's method of a sealed trait that covers its literal types leaves its type to \
     the loop's body" (fun () ->
      let text = Fixtures.Infer.range_loop_wrapping_added_then_bound_to_a_uint8 in
      expect_fine text;
      expect_type text "index" ~occurrence:2 "UInt8");
  Harness.test
    "a loop variable given its default type by a method call is an error that says to declare the \
     variable with a type, with no fix" (fun () ->
      let text = Fixtures.Infer.range_loop_absolute_difference_then_bound_to_a_uint8 in
      expect_one_diagnostic text "types.mismatch"
        ~says:
          "`index` took its default type, `Int64`, at an earlier method call. Declare `index` with \
           a type.";
      expect_fix_titles text []);
  Harness.test "a local used as two types is one error, at the second use" (fun () ->
      expect_one_diagnostic Fixtures.Infer.local_bound_to_two_types "types.mismatch"
        ~says:"An earlier statement decided that the type of `base` is `UInt8`.");
  Harness.test
    "a local's method of a sealed trait that covers its literal types leaves its type to a later \
     statement" (fun () ->
      let text = Fixtures.Infer.local_wrapping_added_then_bound_to_a_uint8 in
      expect_fine text;
      expect_type text "base" ~occurrence:2 "UInt8")

let () =
  Harness.test "a literal local used as a shift amount defaults to UInt64" (fun () ->
      let text = Fixtures.Infer.local_shifted_by in
      expect_fine text;
      expect_type text "amount" ~occurrence:2 "UInt64");
  Harness.test "a literal local used as a shift amount is decided by a later statement" (fun () ->
      let text = Fixtures.Infer.local_shifted_by_then_bound_to_a_uint8 in
      expect_fine text;
      expect_type text "amount" ~occurrence:2 "UInt8");
  Harness.test "a literal too large for Int64 defaults to UInt64" (fun () ->
      let text = Fixtures.Infer.local_of_a_literal_beyond_int64 in
      expect_fine text;
      expect_type text "large" ~occurrence:2 "UInt64");
  Harness.test "a literal in a specification that nothing decides is an Integer" (fun () ->
      let text = Fixtures.Infer.requires_of_two_literals in
      expect_fine text;
      expect_type text "2" "Integer")

let () =
  Harness.test
    "a negated local of literals decided unsigned is reported as a negated unsigned value"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.negation_of_a_literal_local_decided_unsigned
        "types.negated_unsigned";
      expect_one_diagnostic Fixtures.Infer.uint8_let_of_a_negated_literal_local
        "types.negated_unsigned");
  Harness.test "a negated local of literals used as a shift amount is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.local_shifted_by_then_negated "types.negated_unsigned");
  Harness.test "a local of literals must fit its type before it is negated" (fun () ->
      expect_one_diagnostic Fixtures.Infer.int8_let_of_a_negated_local_of_128
        "types.literal_out_of_range")

let () =
  Harness.test
    "a local of literals of a type an integer trait bounds must fit every type that implements it"
    (fun () ->
      expect_fine Fixtures.Infer.unsigned_integer_compared_with_a_local_of_200;
      expect_one_diagnostic Fixtures.Infer.unsigned_integer_compared_with_a_local_of_256
        "types.literal_out_of_range";
      expect_one_diagnostic Fixtures.Infer.fixed_width_integer_compared_with_a_local_of_200
        "types.literal_out_of_range");
  Harness.test "a negated local of literals compared with a SignedInteger parameter takes its type"
    (fun () -> expect_fine Fixtures.Infer.signed_integer_compared_with_a_negated_local);
  Harness.test "a literal operand of an associated type of a parameter takes that type" (fun () ->
      expect_fine Fixtures.Infer.literal_plus_an_associated_type_of_a_parameter);
  Harness.test "a shift amount of a parameter that may be signed is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.shift_by_a_fixed_width_integer_parameter "types.mismatch"
        ~says:"A shift amount is an unsigned integer, not `Value`.";
      expect_one_diagnostic Fixtures.Infer.shift_by_a_signed_integer_parameter "types.mismatch"
        ~says:"A shift amount is an unsigned integer, not `Value`.");
  Harness.test "a negated parameter that may be unsigned is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.negation_of_a_fixed_width_integer_parameter
        "types.negated_unsigned" ~says:"may be unsigned");
  Harness.test
    "a negated local of literals compared with a parameter that may be unsigned is an error"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.fixed_width_integer_compared_with_a_negated_local
        "types.negated_unsigned");
  Harness.test "a negative literal compared with a parameter that may be unsigned is an error"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.fixed_width_integer_compared_with_minus_five
        "types.negated_unsigned");
  Harness.test "an integer pattern excludes the types its value does not fit from the scrutinee"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.local_matched_against_256_then_compared_with_a_uint8
        "types.literal_out_of_range");
  Harness.test
    "a loop over a range of literals in a local takes their type from an operand in the body"
    (fun () ->
      let text = Fixtures.Infer.loop_over_a_literal_range_local_summed_into_a_uint8 in
      expect_fine text;
      expect_type text "range" ~occurrence:2 "Range[UInt8]")

let () =
  Harness.test "a literal operand that does not fit the other operand's type is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.uint8_plus_300 "types.literal_out_of_range");
  Harness.test
    "a local of a float literal too large for the Float32 it is compared with is an error"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.float32_compared_with_a_local_too_large_for_it
        "types.literal_out_of_range")

let () =
  Harness.test "deriving Deserialize rejects an invariant whose literal does not fit the field"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.deserialize_of_a_level_with_an_invariant_beyond_its_type
        "types.cannot_derive");
  Harness.test
    "a literal in a specification's arithmetic that does not fit the other operand is an Integer"
    (fun () ->
      let text = Fixtures.Infer.requires_adds_a_large_literal_to_a_uint8 in
      expect_fine text;
      expect_type text "300" "Integer")

let () =
  Harness.test "a specification does not decide the type of a local in code" (fun () ->
      expect_one_diagnostic Fixtures.Infer.invariant_mentions_a_code_local "types.mismatch"
        ~says:"Expected `Bool`, found an integer.");
  Harness.test "a specification does not change the type of a local that code computes with"
    (fun () ->
      let text = Fixtures.Infer.invariant_compares_a_code_local_then_counted_zeros in
      expect_fine text;
      expect_type text "limit" ~occurrence:3 "Int64");
  Harness.test "a proof assertion does not join two locals in code" (fun () ->
      expect_one_diagnostic Fixtures.Infer.proof_compares_two_code_locals "types.mismatch"
        ~says:"Expected `Bool`, found an integer.");
  Harness.test "a decreases clause does not decide the type of a local in code" (fun () ->
      expect_one_diagnostic Fixtures.Infer.decreases_subtracts_from_a_code_local "types.mismatch"
        ~says:"Expected `Bool`, found an integer.");
  Harness.test "a literal in a loop invariant does not decide the type of a local in code"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.invariant_compares_a_code_local_with_a_literal
        "types.mismatch" ~says:"Expected `Bool`, found an integer.");
  Harness.test "a call in an invariant does not decide the type of its argument in code" (fun () ->
      expect_one_diagnostic Fixtures.Infer.invariant_passes_a_code_local_to_a_call "types.mismatch"
        ~says:"Expected `Bool`, found an integer.");
  Harness.test "a generic call in an invariant does not join two locals in code" (fun () ->
      expect_one_diagnostic Fixtures.Infer.invariant_passes_two_code_locals_to_a_generic_call
        "types.mismatch" ~says:"Expected `Bool`, found an integer.");
  Harness.test "a quantifier's range does not join two locals in code" (fun () ->
      expect_one_diagnostic Fixtures.Infer.invariant_quantifies_over_a_range_of_code_locals
        "types.mismatch" ~says:"Expected `Bool`, found an integer.");
  Harness.test "a comparison of two float locals in an invariant is an error, since it joins them"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.invariant_compares_two_float_locals
        "types.decided_in_specification");
  Harness.test "a float literal in an invariant leaves the float local it is compared with to code"
    (fun () ->
      let text = Fixtures.Infer.invariant_compares_a_float_local_with_a_literal in
      expect_fine text;
      expect_type text "ratio" ~occurrence:3 "Float32");
  Harness.test
    "a comparison of records in an invariant is an error when it would decide a literal type \
     argument" (fun () ->
      expect_one_diagnostic Fixtures.Infer.invariant_compares_a_structure_of_code_literals
        "types.decided_in_specification");
  Harness.test "arithmetic in a specification may mix integer types" (fun () ->
      expect_fine Fixtures.Infer.requires_adds_a_uint8_and_an_int64);
  Harness.test "a lambda's body does not decide the type of the lambda's parameter" (fun () ->
      expect_one_diagnostic Fixtures.Infer.lambda_body_compares_its_parameter "types.cannot_infer"
        ~at:("scaled", 1)
        ~says:
          "The type of `scaled` cannot be inferred from where this lambda is used. Declare \
           `scaled` with a type.");
  Harness.test "a method call in an invariant cannot give a float local in code its default type"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.invariant_calls_an_inherent_method_of_a_float_local
        "types.decided_in_specification"
        ~says:"A specification cannot decide the type of `ratio`. Declare `ratio` with a type.");
  Harness.test "a float local's method of FloatingPoint in an invariant leaves its type to code"
    (fun () ->
      let text = Fixtures.Infer.invariant_calls_a_method_of_a_float_local in
      expect_fine text;
      expect_type text "ratio" ~occurrence:2 "Float32");
  Harness.test "an integer pattern in an invariant matches a local in code as an Integer" (fun () ->
      let text = Fixtures.Infer.invariant_matches_a_code_local in
      expect_fine text;
      expect_type text "limit" ~occurrence:3 "UInt8")

let () =
  Harness.test "a sealed integer bound decides a literal's default" (fun () ->
      let text = Fixtures.Infer.literal_passed_to_an_unsigned_integer_parameter in
      expect_fine text;
      expect_type text "count" ~occurrence:2 "UInt64");
  Harness.test "a literal's default ignores the impls of a trait that is not sealed" (fun () ->
      expect_one_diagnostic
        Fixtures.Infer.literal_passed_to_a_parameter_bounded_by_a_trait_of_uint64
        "types.unsatisfied_bound" ~says:"needs `Int64: Tagged`");
  Harness.test
    "associated types under different trait arguments are not equated argument by argument"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.associated_types_under_different_trait_arguments
        "types.mismatch"
        ~says:
          "The `Output` of `Value` under `Add[Int64]` may differ from the `Output` of `Value` \
           under `Add[UInt64]`.");
  Harness.test "a literal operand takes the argument of the parameter's one bound" (fun () ->
      let text = Fixtures.Infer.literal_operand_of_a_parameter_with_one_add_bound in
      expect_fine text;
      expect_type text "1" "UInt8");
  Harness.test
    "a literal for a bound's trait argument waits for the impl that the other argument selects"
    (fun () -> expect_fine Fixtures.Infer.literal_for_a_trait_argument_of_a_bound);
  Harness.test "a literal multiplying a record takes its default type, whose impl takes the record"
    (fun () ->
      let text = Fixtures.Infer.literal_times_a_span in
      expect_fine text;
      expect_type text "2 * span" "Span");
  Harness.test
    "an operator's impl for a generic type unifies a literal type argument with the other operand's"
    (fun () ->
      let text = Fixtures.Infer.sum_of_vectors_of_a_literal_and_a_uint8 in
      expect_fine text;
      expect_type text "other" ~occurrence:2 "Vector[UInt8]";
      expect_type text "sum" ~occurrence:2 "Vector[UInt8]");
  Harness.test "an operator's impl for a generic type unifies the operand's unknown type argument"
    (fun () ->
      let text = Fixtures.Infer.sum_of_vectors_of_an_unknown_and_an_int64 in
      expect_fine text;
      expect_type text "make() + right" "Vector[Int64]");
  Harness.test
    "a literal multiplying a record in a specification is an Integer, which no impl takes"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.requires_multiplies_a_span_by_a_literal "types.no_impl"
        ~says:"`Span` does not implement `Multiply[Integer]`");
  Harness.test
    "an operand that an earlier local of literals does not fit is reported at its literal"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.sum_of_a_uint8_and_an_earlier_local_beyond_it
        "types.literal_out_of_range" ~says:"`300` does not fit in `UInt8`";
      expect_one_diagnostic Fixtures.Infer.sum_of_a_uint64_and_an_earlier_negative_local
        "types.negated_unsigned" ~says:"`UInt64` is unsigned");
  Harness.test
    "an operator that fails on a local's default type is one error, which a later use of the local \
     does not repeat" (fun () ->
      expect_one_diagnostic
        Fixtures.Infer.sum_of_an_earlier_local_beyond_a_uint8_then_bound_to_a_uint64
        "types.literal_out_of_range" ~at:("300", 1));
  Harness.test "a bound whose trait argument is a hole is checked against the subject's impls"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.bound_whose_trait_argument_is_a_hole
        "types.unsatisfied_bound" ~says:"needs `Bool: Multiply[_]`");
  Harness.test
    "a narrowing by an impl's condition reports the condition when a later use excludes it"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.vector_times_an_integer_whose_impl_narrows_its_element
        "types.unsatisfied_bound" ~says:"needs `Int8: UnsignedInteger`");
  Harness.test "a bound on an associated type of an unknown waits for the unknown" (fun () ->
      expect_one_diagnostic Fixtures.Infer.bound_on_an_item_of_an_unknown_source
        "types.cannot_infer");
  Harness.test "a bound selects the impl whose header matches the subject's arguments" (fun () ->
      expect_fine Fixtures.Infer.bound_on_a_type_with_overlapping_impls);
  Harness.test
    "a goal of a loop invariant keeps the specification's rule when a later statement lets it \
     select an impl" (fun () ->
      expect_one_diagnostic
        Fixtures.Infer.invariant_adds_vectors_whose_argument_a_later_statement_decides
        "types.decided_in_specification" ~says:"A specification cannot decide the type of `first`.");
  Harness.test "a proof in a lambda's body does not decide the length of the lambda's parameter"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.proof_in_a_lambda_compares_the_length_of_its_parameter
        "types.decided_in_specification" ~says:"A specification cannot decide the type of `bytes`.");
  Harness.test "a method that two traits declare is the one whose impl's conditions hold" (fun () ->
      let text = Fixtures.Infer.method_declared_by_two_traits_with_conditional_impls in
      expect_fine text;
      match locate_core_call text "box.describe()" 1 with
      | ( {
            callee =
              {
                target =
                  Trait_method
                    {
                      evidence =
                        Impl { impl = Impl { trait = { path = Top { name; _ }; _ }; _ }; _ };
                      _;
                    };
                _;
              };
            _;
          },
          _ ) ->
          if name <> "First" then Harness.fail "`box.describe()` calls the `describe` of `%s`" name
      | _ -> Harness.fail "`box.describe()` records no impl")

let () =
  Harness.test "a member of an operator's result gives a literal operand its default type"
    (fun () ->
      let text = Fixtures.Infer.field_of_a_product_of_a_literal_local in
      expect_fine text;
      expect_type text "(span * count).ticks" "Int64";
      expect_type text "count" ~occurrence:2 "Int64");
  Harness.test "a member of a chain of operator results gives each literal operand its default type"
    (fun () ->
      let text = Fixtures.Infer.field_of_a_product_of_two_literal_locals in
      expect_fine text;
      expect_type text "first" ~occurrence:2 "Int64";
      expect_type text "second" ~occurrence:2 "Int64");
  Harness.test
    "a literal local given its default type by a member read is one error, with a note, that says \
     to declare the local with a type, with no fix" (fun () ->
      let text = Fixtures.Infer.field_of_a_product_then_literal_local_bound_to_a_uint8 in
      expect_one_diagnostic text "types.mismatch"
        ~says:
          "Expected `UInt8`, found `Int64`. `count` took its default type, `Int64`, where the type \
           of an earlier value was needed. Declare `count` with a type."
        ~notes:
          [
            ( "The type of this value is needed here, so `count` takes its default type `Int64`.",
              ("(span * count)", 1) );
          ];
      expect_fix_titles text []);
  Harness.test "literal arguments whose parameter type is a type parameter wait for a later use"
    (fun () ->
      let text = Fixtures.Infer.literals_passed_to_generic_parameters_then_bound_to_a_uint8 in
      expect_fine text;
      expect_type text "3" "UInt8";
      expect_type text "4" "UInt8");
  Harness.test "a generic call's result converts to the parameter's view" (fun () ->
      expect_fine Fixtures.Infer.generic_result_passed_as_a_view)

let () =
  Harness.test
    "a later statement does not change the structured type of an earlier local, and the mismatch \
     with its default offers no conversion" (fun () ->
      let text = Fixtures.Infer.later_statement_keeps_an_earlier_structured_type in
      expect_one_diagnostic text "types.mismatched_integers" ~at:("small == count", 1);
      expect_fix_titles text []);
  Harness.test "a local of literals for a bound's trait argument takes its default at the statement"
    (fun () ->
      let text = Fixtures.Infer.local_of_literals_for_a_trait_argument_of_a_bound in
      expect_fine text;
      expect_type text "count" ~occurrence:2 "Int64");
  Harness.test "a literal that reaches an enclosing statement's type is decided there" (fun () ->
      let text = Fixtures.Infer.literal_returned_early_from_a_lambda in
      expect_fine text;
      expect_type text "3" "UInt8");
  Harness.test
    "a local of an integer literal compared with a float is an error that says to write the \
     literal as a float, with no fix" (fun () ->
      let text = Fixtures.Infer.float_compared_with_an_integer_local in
      expect_one_diagnostic text "types.integer_for_float" ~says:"Write `3` as `3.0`.";
      expect_fix_titles text []);
  Harness.test
    "an integer literal added to a float literal is an error that says to write it as a float, \
     with no fix" (fun () ->
      let text = Fixtures.Infer.integer_literal_plus_a_float_literal in
      expect_one_diagnostic text "types.integer_for_float" ~says:"Write `3` as `3.0`.";
      expect_fix_titles text []);
  Harness.test
    "a sum of integer literals compared with a float is an error that says to write each literal \
     as a float" (fun () ->
      expect_one_diagnostic Fixtures.Infer.float_compared_with_a_sum_of_integer_literals
        "types.integer_for_float" ~says:"Write `3` as `3.0` and `1` as `1.0`.");
  Harness.test "a local of literals multiplied by a record takes the type of the impl's operand"
    (fun () ->
      let text = Fixtures.Infer.duration_times_a_literal_local in
      expect_fine text;
      expect_type text "count" ~occurrence:2 "Int64");
  Harness.test "a scrutinee's literal type is decided by the statement that holds the match"
    (fun () ->
      let text = Fixtures.Infer.match_on_a_literal_decided_by_an_arm in
      expect_fine text;
      expect_type text "3" "UInt8");
  Harness.test "a local of literals in a lambda's body is decided by a use after the lambda"
    (fun () -> expect_fine Fixtures.Infer.literal_locals_decided_in_and_after_a_lambda);
  Harness.test "an integer literal where a Bool is expected is a mismatch" (fun () ->
      expect_one_diagnostic Fixtures.Infer.bool_let_of_a_literal "types.mismatch"
        ~says:"Expected `Bool`, found an integer.");
  Harness.test "two joined locals of literals must both fit the type a later use decides" (fun () ->
      expect_one_diagnostic Fixtures.Infer.literal_locals_joined_then_compared_with_a_uint8
        "types.literal_out_of_range" ~at:("300", 1))

let () =
  Harness.test "a literal local that a goal of an earlier statement gives takes the goal's output"
    (fun () ->
      let text = Fixtures.Infer.literal_local_given_by_a_goal_of_an_earlier_statement in
      expect_fine text;
      expect_type text "magnitude" ~occurrence:3 "UInt64");
  Harness.test
    "a literal local given its default type by a member read and then expected as a float is an \
     error that says to write the literal as a float" (fun () ->
      let text = Fixtures.Infer.field_of_a_product_then_literal_local_bound_to_a_float64 in
      expect_one_diagnostic text "types.integer_for_float" ~says:"Write `2` as `2.0`.";
      expect_fix_titles text []);
  Harness.test
    "a local given its default type by a method call and expected as a type that is no number is \
     not told to declare a type" (fun () ->
      let text = Fixtures.Infer.local_absolute_difference_then_bound_to_a_bool in
      Harness.expect_strings
        ~expected:
          [
            "Expected `Bool`, found `Int64`. `count` took its default type, `Int64`, at an earlier \
             method call.";
          ]
        (List.map
           (fun (diagnostic : Diagnostic.t) -> diagnostic.message)
           (check (Support.setup [ ("app.main", text) ]) (Support.parse_file "app.main")));
      expect_fix_titles text []);
  Harness.test
    "a hexadecimal integer literal compared with a float is an error that spells it as a decimal \
     float" (fun () ->
      let text = Fixtures.Infer.float_compared_with_a_hexadecimal_local in
      expect_one_diagnostic text "types.integer_for_float" ~says:"Write `0x10` as `16.0`.";
      expect_fix_titles text []);
  Harness.test "a default inside a type argument is explained at the mismatch" (fun () ->
      expect_one_diagnostic Fixtures.Infer.vector_of_a_literal_added_then_bound_to_a_vector_of_uint8
        "types.mismatch" ~says:"`1` took its default type, `Int64`, at an earlier statement."
        ~notes:
          [
            ( "This statement needs the type of `1`, so `1` takes its default type `Int64` here.",
              ("let sum", 1) );
          ]);
  Harness.test "a goal whose output cannot be inferred reports no later failure" (fun () ->
      match
        Support.list_codes
          (check
             (Support.setup
                [ ("app.main", Fixtures.Infer.invariant_multiplies_a_span_by_a_float_local) ])
             (Support.parse_file "app.main"))
      with
      | [ "types.cannot_infer"; "types.unknown_member" ] -> ()
      | reported -> Harness.fail "reported [%s]" (String.concat "; " reported))

let () =
  Harness.test
    "a bound that a literal local's default type fails is one error that says to declare the local \
     with a type, with no fix" (fun () ->
      let text = Fixtures.Infer.literal_local_passed_to_a_parameter_bounded_by_add_of_uint8 in
      expect_one_diagnostic text "types.unsatisfied_bound"
        ~says:
          "This needs `Int64: Add[UInt8]`, which does not hold. `first` took its default type, \
           `Int64`, where the type of an earlier value was needed. Declare `first` with a type.";
      expect_fix_titles text []);
  Harness.test
    "a bound that a literal local's default type fails and several of its types meet is one error \
     that says to declare the local with a type" (fun () ->
      expect_one_diagnostic
        Fixtures.Infer.literal_local_passed_to_a_parameter_bounded_by_a_trait_of_uint8_and_uint16
        "types.unsatisfied_bound"
        ~says:
          "This needs `Int64: Small`, which does not hold. `first` took its default type, `Int64`, \
           where the type of an earlier value was needed. Declare `first` with a type.");
  Harness.test
    "a literal for an associated type of another argument waits for that argument, in either order"
    (fun () -> expect_fine Fixtures.Infer.literal_for_an_associated_type_of_another_argument);
  Harness.test "an associated type of a literal argument waits for the literal's type" (fun () ->
      let text = Fixtures.Infer.literal_passed_to_a_function_returning_an_associated_type in
      expect_fine text;
      expect_type text "doubled(3)" "UInt8";
      expect_type text "doubled(3)" ~occurrence:2 "Int64");
  Harness.test "an associated type of a call's argument converts to the parameter's view" (fun () ->
      expect_fine Fixtures.Infer.view_of_an_associated_type_argument);
  Harness.test
    "a field read from a value of a generic type leaves a literal type argument undecided"
    (fun () ->
      let text = Fixtures.Infer.field_of_a_structure_of_a_literal_type in
      expect_fine text;
      expect_type text "first" ~occurrence:2 "Int8");
  Harness.test "an associated type of an earlier statement's literal is decided with the literal"
    (fun () ->
      let text = Fixtures.Infer.associated_type_of_an_earlier_literal in
      expect_fine text;
      expect_type text "sum" ~occurrence:2 "Int64");
  Harness.test "an associated type of a literal argument waits for the literal when it is compared"
    (fun () ->
      expect_fine
        Fixtures.Infer.literal_passed_to_a_function_returning_an_associated_type_of_its_bound);
  Harness.test "a method of an associated type of an earlier statement's literal is found"
    (fun () -> expect_fine Fixtures.Infer.method_of_an_associated_type_of_an_earlier_literal);
  Harness.test "an associated type of a literal that a use needs takes the literal's default"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.associated_type_of_a_literal_mismatched_with_its_use
        "types.mismatch" ~says:"Expected `UInt8`, found `Int64`.");
  Harness.test
    "an associated type of a sealed bound on a literal argument is the default type's when compared"
    (fun () ->
      let float = Fixtures.Infer.bits_of_a_float_literal_compared_with_a_literal in
      expect_fine float;
      expect_type float "bits_of(1.5)" "UInt64";
      let integer = Fixtures.Infer.unsigned_of_an_integer_literal_compared_with_a_literal in
      expect_fine integer;
      expect_type integer "unsigned_of(3)" "UInt64");
  Harness.test
    "a literal for an associated type of a literal local's argument leaves the local to a later \
     statement" (fun () ->
      let text = Fixtures.Infer.literal_for_an_associated_type_of_a_literal_local_argument in
      expect_fine text;
      expect_type text "5" "UInt8";
      expect_type text "first" ~occurrence:2 "UInt8")

let () =
  Harness.test "a local's type is the same whichever statement decides it first" (fun () ->
      expect_fine Fixtures.Infer.local_saturating_added_then_compared_with_a_length;
      expect_fine Fixtures.Infer.local_compared_with_a_length_then_saturating_added);
  Harness.test "the argument of a local's method of a sealed trait decides the local's type"
    (fun () ->
      let text = Fixtures.Infer.local_whose_trait_method_takes_a_length in
      expect_fine text;
      expect_type text "limit" ~occurrence:2 "UInt64");
  Harness.test "a local's method of a sealed trait is called on the type a later statement decides"
    (fun () ->
      let text = Fixtures.Infer.local_counted_zeros_then_bound_to_a_uint8 in
      expect_fine text;
      expect_type text "mask" ~occurrence:2 "UInt8");
  Harness.test
    "a trait that is not sealed and declares a sealed trait's method does not change a local's \
     lookup" (fun () ->
      let text = Fixtures.Infer.local_counted_zeros_beside_another_trait_of_the_method in
      expect_fine text;
      expect_type text "mask" ~occurrence:2 "UInt8");
  Harness.test "a local's method of SignedInteger narrows the local to the signed integers"
    (fun () ->
      let text = Fixtures.Infer.local_absolute_then_bound_to_an_int8 in
      expect_fine text;
      expect_type text "level" ~occurrence:2 "Int8");
  Harness.test
    "a local's method of a trait that only SignedInteger requires narrows the local to the signed \
     integers" (fun () ->
      let text = Fixtures.Infer.local_negated_then_bound_to_an_int8 in
      expect_fine text;
      expect_type text "level" ~occurrence:2 "Int8");
  Harness.test
    "a later statement that excludes the types of a local's method of a sealed trait is one error, \
     at the call" (fun () ->
      expect_one_diagnostic Fixtures.Infer.local_absolute_then_bound_to_a_uint8 "types.no_impl"
        ~at:("level.absolute()", 1) ~says:"`UInt8` does not implement `SignedInteger`.");
  Harness.test "a local's method of UnsignedInteger narrows the local's default to UInt64"
    (fun () ->
      let text = Fixtures.Infer.integer_square_root_of_a_literal_local in
      expect_fine text;
      expect_type text "count" ~occurrence:2 "UInt64");
  Harness.test "a float local's method of FloatingPoint leaves its type to a later statement"
    (fun () ->
      let text = Fixtures.Infer.float_literal_method_then_bound_to_a_float32 in
      expect_fine text;
      expect_type text "ratio" ~occurrence:2 "Float32");
  Harness.test "a literal's method that two sealed traits declare gives it its default type"
    (fun () ->
      let text = Fixtures.Infer.literal_absolute_difference in
      expect_fine text;
      expect_type text "first" ~occurrence:2 "Int64");
  Harness.test
    "a local's method that two sealed traits declare gives the local its default type at the call, \
     and the error says to declare the local with a type" (fun () ->
      let text = Fixtures.Infer.local_absolute_difference_then_bound_to_a_uint8 in
      expect_one_diagnostic text "types.mismatch"
        ~says:
          "`first` took its default type, `Int64`, at an earlier method call. Declare `first` with \
           a type.";
      expect_fix_titles text []);
  Harness.test
    "a local's method of a trait that is not sealed gives the local its default type at the call, \
     and the error says to declare the local with a type" (fun () ->
      let text = Fixtures.Infer.local_halved_then_bound_to_a_uint64 in
      expect_one_diagnostic text "types.mismatch"
        ~says:
          "`value` took its default type, `Int64`, at an earlier method call. Declare `value` with \
           a type.";
      expect_fix_titles text []);
  Harness.test
    "a local's method that only UInt8 declares gives the local its default type at the call"
    (fun () ->
      Support.expect_one_diagnostic ~setup:make_standard_packages ~file:"standard.probe"
        ~check:check_as_standard_library Fixtures.Infer.local_calling_a_method_of_uint8_alone
        "types.unknown_member" ~says:"`Int64` has no method `twice`.");
  Harness.test
    "a literal's method that two traits declare, neither sealed, is looked up on its default type"
    (fun () ->
      let text = Fixtures.Infer.literal_method_that_two_unsealed_traits_declare in
      expect_fine text;
      expect_type text "limit.twice()" "Int64");
  Harness.test
    "a trait's method written in full on a literal local leaves the local's type to a later \
     statement" (fun () ->
      expect_fine Fixtures.Infer.trait_method_written_in_full_then_bound_to_a_uint64);
  Harness.test
    "a local's method of a trait that is not sealed checks its arguments against the default \
     type's impl" (fun () -> expect_fine Fixtures.Infer.unsealed_trait_methods_of_literal_locals);
  Harness.test
    "a local that an earlier use decides calls the decided type's method of a trait that is not \
     sealed" (fun () ->
      expect_fine Fixtures.Infer.literal_local_compared_before_its_unsealed_method);
  Harness.test
    "a statement whose types depend on a literal local gives the local its default type, and the \
     error says to declare the local with a type" (fun () ->
      let text = Fixtures.Infer.local_converted_to_bytes_then_bound_to_a_uint32 in
      expect_one_diagnostic text "types.mismatch"
        ~says:
          "`value` took its default type, `Int64`, at an earlier statement. Declare `value` with a \
           type.";
      expect_fix_titles text []);
  Harness.test "the result of a literal local's method passes to a read-only list parameter"
    (fun () -> expect_fine Fixtures.Infer.bytes_of_a_literal_local_passed_as_a_range);
  Harness.test
    "a literal local whose method gives an associated type takes its default type at that statement"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.local_unsigned_absolute_then_compared_with_a_uint8
        "types.mismatched_integers"
        ~fixed:("small == magnitude", "UInt64.from_integer(small) == magnitude"));
  Harness.test
    "a literal local joined with an associated type of another literal local takes the type the \
     other's default gives" (fun () ->
      let text = Fixtures.Infer.literal_local_joined_with_an_associated_type_of_another in
      expect_fine text;
      expect_type text "magnitude" ~occurrence:2 "UInt64";
      expect_type text "chosen" ~occurrence:2 "UInt64")

let () =
  Harness.test "comparing integer types that differ is an error with a fix that converts" (fun () ->
      expect_one_diagnostic Fixtures.Infer.comparison_of_uint64_and_uint32
        "types.mismatched_integers"
        ~fixed:("length == count", "length == UInt64.from_integer(count)"));
  Harness.test "a comparison views a list, an array, or a string that meets its view" (fun () ->
      expect_fine Fixtures.Infer.comparisons_of_owners_and_views);
  Harness.test "a comparison of a list with a range of another element type is a mismatch"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.comparison_of_a_list_and_a_range_of_another_element
        "types.mismatch");
  Harness.test
    "a read-only parameter whose type is a type parameter or an associated type takes a view of \
     the list or the string it stands for" (fun () ->
      expect_fine Fixtures.Infer.views_passed_as_owners_to_generic_parameters);
  Harness.test "a view is not passed to an `own` parameter of its viewed type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.view_passed_as_an_own_key "types.mismatch"
        ~fixed:("mut counts.insert(word, value: 1)", "mut counts.insert(word.copy(), value: 1)"));
  Harness.test "a list is not passed as an array" (fun () ->
      expect_one_diagnostic Fixtures.Infer.range_passed_as_an_array_key "types.mismatch");
  Harness.test "a list of bytes is not passed as a string" (fun () ->
      expect_one_diagnostic Fixtures.Infer.byte_list_passed_as_a_string_key "types.mismatch");
  Harness.test "a map literal passed to a read-only map owns its keys" (fun () ->
      expect_fine Fixtures.Infer.map_literal_passed_to_a_read_only_map);
  Harness.test "a view where its viewed type is owned is a mismatch with a fix to `copy()`"
    (fun () ->
      expect_one_diagnostic "fn f(name: view String) -> List[String] {\n  [name]\n}\n"
        "types.mismatch" ~at:("name]", 1) ~fixed:("[name]", "[name.copy()]"));
  Harness.test "`copy()` of a view makes an owned value" (fun () ->
      expect_fine "fn f(items: view List[Int64]) -> List[Int64] {\n  items.copy()\n}\n");
  Harness.test
    "a view passed `own` where its owning type is expected is copied, and the redundant `own` \
     removed" (fun () ->
      let text =
        "fn keep(name: own String) {}\n\nfn f(name: view String) {\n  keep(own name)\n}\n"
      in
      let diagnostics =
        Support.run_check ~check (Support.setup [ ("app.main", text) ]) "app.main"
      in
      if Support.list_codes diagnostics <> [ "types.mismatch"; "types.redundant_mode" ] then
        Harness.fail "found [%s]" (String.concat "; " (Support.list_codes diagnostics));
      let fixed =
        Diagnostic.apply_edits text
          (List.concat_map
             (fun (diagnostic : Diagnostic.t) ->
               List.concat_map
                 (fun (fix : Source.span Diagnostic.fix) -> fix.edits)
                 diagnostic.fixes)
             diagnostics)
      in
      if
        fixed
        <> "fn keep(name: own String) {}\n\nfn f(name: view String) {\n  keep(name.copy())\n}\n"
      then Harness.fail "fixed to %S" fixed);
  Harness.test "a view of elements that do not copy, where a list is owned, has no fix" (fun () ->
      let text =
        "public opaque type Token(code: Int64)\n\n\
         fn f(tokens: view List[Token]) -> List[Token] {\n\
        \  tokens\n\
         }\n"
      in
      expect_one_diagnostic text "types.mismatch";
      expect_fix_titles text []);
  Harness.test "a view of another element type than the list's has no fix" (fun () ->
      let text = "fn f(items: view List[Int64]) -> List[String] {\n  items\n}\n" in
      expect_one_diagnostic text "types.mismatch";
      expect_fix_titles text []);
  Harness.test "+ on strings is an error with a fix to interpolation" (fun () ->
      expect_one_diagnostic Fixtures.Infer.string_plus_a_string "types.string_addition"
        ~fixed:("name + \"!\"", "\"${name}!\""));
  Harness.test "an operator chooses the impl by both operands" (fun () ->
      let text = Fixtures.Infer.additions_of_meters_and_integers in
      match locate_core_call text "length + extra" 1 with
      | ( {
            callee = { target = Trait_method { evidence = Impl { impl; _ }; name = "add"; _ }; _ };
            _;
          },
          _ ) -> (
          match impl with
          | Impl { trait = { arguments = [ Named { path = Top { name = "Int64"; _ }; _ } ]; _ }; _ }
            ->
              ()
          | _ -> Harness.fail "the impl chosen is %s" (Path.show impl))
      | _ -> Harness.fail "no impl recorded");
  Harness.test "an ordering on Self in a trait's law is its compare" (fun () ->
      let text = Fixtures.Infer.law_ordering_self_values in
      List.iter
        (fun written ->
          match locate_core_call text written 1 with
          | ( { callee = { target = Trait_method { name = "compare"; evidence = Bound; _ }; _ }; _ },
              result ) ->
              if Types.show result <> "Ordering" then
                Harness.fail "`%s` calls a `compare` that gives `%s`" written (Types.show result)
          | _ -> Harness.fail "`%s` is another call" written)
        [ "first < second"; "second < third"; "first < third" ]);
  Harness.test "an operand can be the result of an operator's method" (fun () ->
      expect_fine Fixtures.Infer.sum_with_a_multiply_call);
  Harness.test "a type without the operator's trait is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.sum_of_points "types.no_impl")

let () =
  Harness.test "a call to a function whose signature fails a check reports nothing" (fun () ->
      expect_one_diagnostic Fixtures.Infer.call_of_a_public_function_taking_a_private_type
        "types.private_in_public");
  Harness.test "a call to a function whose parameter type is unknown reports nothing" (fun () ->
      expect_one_diagnostic Fixtures.Infer.call_of_a_function_with_a_misspelled_parameter_type
        "resolve.unknown_name")

let () =
  let functions = "fn copy_file(source: Int64, destination: Int64) {}\n\n" in
  let passes_local name : Core.argument -> bool = function
    | { value = Place (Local { local = Declared { name = passed; _ }; _ }); _ } -> passed = name
    | _ -> false
  in
  Harness.test "arguments without labels are passed by position" (fun () ->
      expect_fine (functions ^ Fixtures.Infer.copy_file_with_positional_arguments));
  Harness.test "a variable named like another parameter is passed by position" (fun () ->
      let text = functions ^ Fixtures.Infer.copy_file_with_swapped_arguments in
      match locate_core_call text "copy_file(destination, source)" 1 with
      | { arguments = [ first; second ]; _ }, _
        when passes_local "destination" first && passes_local "source" second ->
          ()
      | _ -> Harness.fail "the arguments are not passed by position");
  Harness.test "labeled arguments come in any order and are evaluated in the order written"
    (fun () ->
      let text = functions ^ Fixtures.Infer.copy_file_with_labels_in_reverse in
      match locate_core_call text "copy_file(destination: backup, source: original)" 1 with
      | { arguments = [ first; second ]; evaluation_order = [ 1; 0 ]; _ }, _
        when passes_local "original" first && passes_local "backup" second ->
          ()
      | { evaluation_order; _ }, _ ->
          Harness.fail "the call evaluates [%s]"
            (String.concat ", " (List.map string_of_int evaluation_order)));
  Harness.test
    "a positional argument after labels at their own positions is an error with a fix that labels \
     it" (fun () ->
      expect_one_diagnostic
        (functions ^ Fixtures.Infer.copy_file_with_a_positional_argument_after_a_label)
        "types.positional_after_labeled"
        ~fixed:
          ("copy_file(source: original, backup)", "copy_file(source: original, destination: backup)"));
  Harness.test
    "a positional argument gets no fix after a label away from its position, or when it is named \
     like another parameter" (fun () ->
      List.iter
        (fun text ->
          let packages = Support.setup [ ("app.main", text) ] in
          match check packages (Support.parse_file "app.main") with
          | [ ({ fixes = []; _ } as diagnostic) ]
            when Diagnostic.Code.name diagnostic.code = "types.positional_after_labeled" ->
              ()
          | reported ->
              Harness.fail "reported [%s]" (String.concat "; " (Support.list_codes reported)))
        [
          functions ^ Fixtures.Infer.copy_file_with_a_destination_label_and_a_positional_source;
          Fixtures.Infer.place_with_a_variable_named_like_a_later_parameter;
        ]);
  Harness.test "a missing argument is an error" (fun () ->
      expect_one_diagnostic
        (functions ^ Fixtures.Infer.copy_file_with_one_argument)
        "types.missing_argument");
  Harness.test "a call with more arguments than parameters is one error" (fun () ->
      expect_one_diagnostic
        (functions ^ Fixtures.Infer.copy_file_with_three_arguments)
        "types.too_many_arguments" ~says:"This function takes 2 arguments, and 3 are given.");
  Harness.test "a method called through its type counts its arguments besides `self`" (fun () ->
      expect_one_diagnostic Fixtures.Infer.counter_read_through_its_type_with_an_extra_argument
        "types.too_many_arguments"
        ~says:"This method takes 0 arguments besides `self`, and 1 is given.");
  Harness.test "a method called through its type takes its receiver first, without a label"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.point_shifted_through_its_type_with_a_label_first
        "types.missing_argument" ~says:"its receiver as its first argument, without a label";
      expect_one_diagnostic Fixtures.Infer.compare_written_in_full_with_a_label_first
        "types.missing_argument" ~says:"its receiver as its first argument, without a label");
  Harness.test "the first argument of a record with several fields needs a label too" (fun () ->
      expect_one_diagnostic Fixtures.Infer.point_with_an_unlabeled_first_argument
        "types.missing_label" ~says:"`Point` has 2 fields"
        ~fixed:("Point(0, y: 1)", "Point(x: 0, y: 1)"));
  Harness.test "a variant with one field given two arguments is one error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.circle_built_with_two_arguments
        "types.too_many_arguments" ~says:"`Circle` has 1 field, and 2 arguments are given.");
  Harness.test "an argument without a parameter is still checked" (fun () ->
      let packages =
        Support.setup [ ("app.main", Fixtures.Infer.apply_twice_with_a_string_sum_after_a_label) ]
      in
      match Support.list_codes (check packages (Support.parse_file "app.main")) with
      | [ "types.positional_after_labeled"; "types.string_addition" ] -> ()
      | reported -> Harness.fail "reported [%s]" (String.concat "; " reported));
  Harness.test "a call with an argument without a parameter has the error type" (fun () ->
      expect_one_diagnostic
        Fixtures.Infer.distance_with_a_positional_argument_after_a_label_returned_as_a_string
        "types.positional_after_labeled"
        ~fixed:("distance(from: start, finish)", "distance(from: start, to: finish)")
        ~left_after_fix:[ "types.mismatch" ]);
  Harness.test "a repeated argument has no parameter, so no other parameter is missing" (fun () ->
      expect_one_diagnostic
        (functions ^ Fixtures.Infer.copy_file_with_a_repeated_source)
        "types.repeated_argument");
  Harness.test "a lambda passed as an extra argument is one error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.apply_twice_with_an_extra_lambda
        "types.too_many_arguments");
  Harness.test "an empty list after a label, with no parameter to type it, is one error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.sum_of_with_an_empty_list_after_a_label
        "types.positional_after_labeled"
        ~fixed:("sum_of(first: items, [])", "sum_of(first: items, second: [])"));
  Harness.test "a constant built by a rejected call is one error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.wrapper_constant_with_an_extra_argument
        "types.too_many_arguments");
  Harness.test "an opaque type built outside its package has the error type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.crc32_built_outside_its_package_returned_as_a_string
        "types.private_field");
  Harness.test "an argument for a parameter with a default can be omitted" (fun () ->
      let text = Fixtures.Infer.connect_without_its_port in
      match locate_core_call text "connect(1)" 1 with
      | ( {
            arguments =
              [
                _;
                {
                  mode = Read;
                  value =
                    Value
                      {
                        kind =
                          Parameter_default
                            { definition = Top { name = "connect"; _ }; position = 1; _ };
                        _;
                      };
                };
              ];
            _;
          },
          _ ) ->
          ()
      | _ -> Harness.fail "the omitted argument is not the default that `connect` declares");
  Harness.test "an `Array` passed where a `List` is expected is passed as its whole range"
    (fun () ->
      let text = Fixtures.Infer.sum_of_an_array_passed_as_a_list in
      match locate_core_call text "total(values)" 1 with
      | { arguments = [ argument ]; _ }, _ when is_whole_range argument -> ()
      | _ -> Harness.fail "the argument is not the whole range of the array");
  Harness.test "an `Array` receiver finds a method of `List` and is passed as its whole range"
    (fun () ->
      let text = Fixtures.Infer.contains_of_an_array in
      match locate_core_call text "values.contains(1)" 1 with
      | { arguments = [ receiver; _ ]; _ }, _ when is_whole_range receiver -> ()
      | _ -> Harness.fail "the receiver is not the whole range of the array");
  Harness.test "an `Array` receiver passed `mut` to a method of `List` is passed as its whole range"
    (fun () ->
      let text = Fixtures.Infer.sort_of_a_mut_array in
      match locate_core_call text "values.sort()" 1 with
      | ( {
            arguments =
              [ { mode = Mut; value = Value { kind = Use (Range _); _ } | Place (Range _) } ];
            _;
          },
          _ ) ->
          ()
      | _ -> Harness.fail "the receiver is not the whole range of the array");
  Harness.test
    "a type argument of a `List` method is counted after the list's parameters, not the array's"
    (fun () -> expect_fine Fixtures.Infer.zip_of_an_array_with_a_type_argument);
  Harness.test
    "a call of a method that takes `mut self` needs the mode keyword, with a fix that adds it"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.sort_of_a_list_without_mut "types.missing_mode"
        ~fixed:("items.sort()", "mut items.sort()"));
  Harness.test
    "the receiver's mode chooses between a `String`'s read-only overload and its `own` overload"
    (fun () ->
      let text = Fixtures.Infer.to_bytes_of_a_string_read_and_owned in
      let find_owner occurrence =
        match locate_core_call text "name.to_bytes()" occurrence with
        | { callee = { target = Function { path = Method { owner; receiver; _ }; _ }; _ }; _ }, _ ->
            (Well_known.of_path owner, receiver)
        | _ -> failwith "the callee is not a method"
      in
      if find_owner 1 <> (Some String, Instance Read) then
        Harness.fail "a read-only receiver does not call the read-only overload";
      if find_owner 2 <> (Some String, Instance Own) then
        Harness.fail "an `own` receiver does not call the `String`'s own overload");
  Harness.test "a method of a view takes no `mut` receiver" (fun () ->
      expect_one_diagnostic Fixtures.Infer.push_onto_a_view "types.wrong_receiver");
  Harness.test "an unknown method of a `String` is reported" (fun () ->
      expect_one_diagnostic Fixtures.Infer.unknown_method_of_a_string "types.unknown_member"
        ~says:"`String` has no method `width`.");
  Harness.test "an unknown label is an error with a fix to the closest" (fun () ->
      expect_one_diagnostic
        (functions ^ Fixtures.Infer.misspelled_label)
        "types.unknown_label" ~fixed:("destinaton", "destination"));
  Harness.test "a record is built with labels in any order" (fun () ->
      expect_fine Fixtures.Infer.point_built_with_labels_reversed);
  Harness.test "a record with one field takes a bare value" (fun () ->
      expect_fine Fixtures.Infer.user_id_of_a_bare_value);
  Harness.test "a generic function's type arguments are solved from its arguments" (fun () ->
      expect_type Fixtures.Infer.wrap_of_an_integer "wrap(5)" "Option[Int64]")

let () =
  Harness.test "a mut parameter needs mut at the call, with a fix that adds it" (fun () ->
      expect_one_diagnostic Fixtures.Infer.bump_without_mut "types.missing_mode"
        ~fixed:("bump(count)", "bump(mut count)"));
  Harness.test "own on a place that copies implicitly is redundant" (fun () ->
      expect_one_diagnostic Fixtures.Infer.own_before_an_integer "types.redundant_mode"
        ~fixed:("own count", "count"));
  Harness.test "own on a place of the error type is not reported again as redundant" (fun () ->
      expect_one_diagnostic Fixtures.Infer.own_before_a_local_bound_to_a_misspelled_field
        "types.unknown_member" ~fixed:("itemz", "items"));
  Harness.test "own on a place of an option of the error type is not reported again as redundant"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.own_before_an_option_of_a_misspelled_field
        "types.unknown_member" ~fixed:("itemz", "items"));
  Harness.test "own on a place of a hole's type is not redundant" (fun () ->
      expect_fine Fixtures.Infer.own_before_a_local_bound_to_todo);
  Harness.test "a redundant own is reported once a later element of the statement solves the type"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.own_before_a_lambda_parameter_solved_later_as_an_integer
        "types.redundant_mode" ~fixed:("own value", "value"));
  Harness.test "a mut receiver chooses the method's mut overload" (fun () ->
      expect_fine Fixtures.Infer.mut_push_onto_a_var_list);
  Harness.test
    "a place calling a method that takes mut self needs the mode keyword, with a fix that adds it"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.push_without_mut "types.missing_mode"
        ~fixed:("items.push(1)", "mut items.push(1)"))

let () =
  let shapes = Fixtures.Infer.others_shape_with_private_members in
  let others = [ ("app.shapes", shapes) ] in
  List.iter
    (fun (use, fixture) ->
      Harness.test (Printf.sprintf "another module's private %s is not visible" use) (fun () ->
          expect_one_diagnostic ~others fixture "types.member_not_visible"
            ~says:"private to its module"))
    [
      ("method, called with a dot,", Fixtures.Infer.call_of_another_modules_private_method);
      ("method, called in full,", Fixtures.Infer.call_in_full_of_another_modules_private_method);
      ("static method", Fixtures.Infer.call_of_another_modules_private_static_method);
      ("member constant", Fixtures.Infer.read_of_another_modules_private_member_constant);
      ("method, used as a value,", Fixtures.Infer.another_modules_private_method_as_a_value);
      ( "member constant, in a pattern,",
        Fixtures.Infer.pattern_of_another_modules_private_member_constant );
    ];
  Harness.test
    "an internal method, an internal trait's method, and a public method of another module are \
     visible" (fun () ->
      expect_no_diagnostics
        [
          ("app.main", Fixtures.Infer.calls_of_another_modules_internal_and_public_methods);
          ("app.shapes", shapes);
        ]);
  Harness.test "an internal method of another package is not visible" (fun () ->
      expect_one_diagnostic
        ~setup:(Support.setup ~dependencies:[ ("app", "tools") ])
        ~others:[ ("tools.shapes", shapes) ]
        Fixtures.Infer.call_of_another_packages_internal_method "types.member_not_visible"
        ~says:"internal to its package");
  List.iter
    (fun (call, fixture, method_) ->
      Harness.test
        (Printf.sprintf "%s of another module's private trait names the method as not visible" call)
        (fun () ->
          expect_one_diagnostic ~others fixture "types.member_not_visible"
            ~says:(Printf.sprintf "`app.shapes.Measured.%s` is private to its module" method_)))
    [
      ( "a call with a dot of a method",
        Fixtures.Infer.call_of_a_method_of_another_modules_private_trait,
        "measure" );
      ( "a call in full of a method",
        Fixtures.Infer.call_in_full_of_a_method_of_another_modules_private_trait,
        "measure" );
      ( "a call of a static method",
        Fixtures.Infer.call_of_a_static_method_of_another_modules_private_trait,
        "sample" );
    ];
  Harness.test
    "a call with a dot of a method of another package's internal trait names the method as not \
     visible" (fun () ->
      expect_one_diagnostic
        ~setup:(Support.setup ~dependencies:[ ("app", "tools") ])
        ~others:[ ("tools.shapes", shapes) ]
        Fixtures.Infer.call_of_a_method_of_another_packages_internal_trait
        "types.member_not_visible"
        ~says:"`tools.shapes.Sided.side_count` is internal to its package");
  Harness.test
    "a call with a dot does not name a private trait that the receiver's type does not implement"
    (fun () ->
      expect_one_diagnostic ~others
        Fixtures.Infer
        .call_of_a_method_of_another_modules_private_trait_that_the_type_does_not_implement
        "types.unknown_member" ~says:"`Shape` has no method `weigh`.");
  Harness.test
    "a call reaches a visible trait's method where another module's private trait declares a \
     method of the same name" (fun () ->
      expect_no_diagnostics
        [
          ( "app.main",
            Fixtures.Infer
            .call_of_a_visible_trait_method_named_like_another_modules_private_trait_method );
          ("app.shapes", shapes);
        ]);
  Harness.test "reading another module's private method as a field does not reveal the method"
    (fun () ->
      expect_one_diagnostic ~others Fixtures.Infer.field_read_of_another_modules_private_method
        "types.unknown_member" ~says:"has no field `secret`");
  Harness.test
    "a call with a dot reaches a trait's method where the type's own method of its name is hidden"
    (fun () ->
      let packages =
        Support.setup
          ~dependencies:[ ("app", "tools") ]
          [
            ( "app.main",
              Fixtures.Infer.call_of_a_trait_method_named_like_another_packages_internal_method );
            ("tools.kits", Fixtures.Infer.kit_with_an_internal_part);
          ]
      in
      let list_callees module_ definition_name =
        let file = Support.parse_file module_ in
        (match check packages file with
        | [] -> ()
        | reported ->
            Harness.fail "%s: %s" module_ (String.concat "; " (Support.list_codes reported)));
        List.concat_map
          (fun (declaration : Resolve.Names.declaration) ->
            match declaration.key.path with
            | (Top { name; _ } | Method { name; _ }) when name = definition_name ->
                List.filter_map
                  (fun (node : Core.expression) ->
                    match node.kind with Call { callee; _ } -> Some callee.target | _ -> None)
                  (Support.collect_core_nodes packages declaration.key).expressions
            | _ -> [])
          (Support.list_declarations packages file.module_)
      in
      (match list_callees "app.main" "f" with
      | [ Trait_method { name = "part"; _ } ] -> ()
      | _ -> Harness.fail "the call in `app` does not reach `Parted.part`");
      match list_callees "tools.kits" "measure" with
      | [ Function { path = Method { name = "part"; receiver = Instance Read; _ }; _ } ] -> ()
      | _ -> Harness.fail "the call in `tools` does not reach `Kit.part`")

let () =
  Harness.test "a statement's value must be used, with a fix that discards it" (fun () ->
      expect_one_diagnostic Fixtures.Infer.unused_length "types.unused_value"
        ~fixed:("items.length()", "let _ = items.length()"));
  Harness.test "the default of a parameter of a view type can be an owned value" (fun () ->
      expect_fine Fixtures.Ownership.view_parameters_with_owned_defaults);
  Harness.test "`time` of a method that no bound of the type parameter declares is an error"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.cost_naming_time_of_an_undeclared_method
        "types.unknown_member");
  Harness.test "the base of a record update cannot be passed `mut`" (fun () ->
      expect_one_diagnostic Fixtures.Infer.record_update_of_a_base_passed_mut "types.wrong_mode"
        ~says:"so the base is passed `own`, not `mut`");
  Harness.test "a let cannot be assigned" (fun () ->
      expect_one_diagnostic Fixtures.Infer.assignment_to_a_let "types.not_assignable");
  Harness.test "a call cannot be assigned" (fun () ->
      expect_one_diagnostic Fixtures.Infer.assignment_to_a_call "types.not_assignable"
        ~says:"Only a place, such as a variable, a field, or an element, can be assigned.");
  Harness.test "a mode keyword before a call that is assigned is reported once, as not a place"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.mut_before_an_assigned_call "resolve.not_a_place"
        ~fixed:("mut five", "five") ~left_after_fix:[ "types.not_assignable" ]);
  List.iter
    (fun (written, text, fixed, says) ->
      Harness.test
        ("a mode keyword before an assigned place is redundant, with a fix that deletes it: "
       ^ written) (fun () -> expect_one_diagnostic text "types.redundant_mode" ~fixed ~says))
    [
      ( "an element",
        Fixtures.Infer.mut_before_an_assigned_element,
        ("mut waits", "waits"),
        "An assignment writes its target, so `waits[1]` takes no `mut`." );
      ( "a variable",
        Fixtures.Infer.mut_before_an_assigned_variable,
        ("mut count", "count"),
        "An assignment writes its target, so `count` takes no `mut`." );
      ( "a variable after `own`",
        Fixtures.Infer.own_before_an_assigned_variable,
        ("own count", "count"),
        "An assignment writes its target, so `count` takes no `own`." );
      ( "a field of `self`",
        Fixtures.Infer.mut_before_an_assigned_field,
        ("mut self.count = 0", "self.count = 0"),
        "An assignment writes its target, so `self.count` takes no `mut`." );
      ( "the target of a compound assignment",
        Fixtures.Infer.mut_before_a_compound_assignment,
        ("mut total", "total"),
        "An assignment writes its target, so `total` takes no `mut`." );
      ( "an entry of a map",
        Fixtures.Infer.mut_before_an_assigned_map_entry,
        ("mut group_of", "group_of"),
        "An assignment writes its target, so `group_of[own key]` takes no `mut`." );
    ];
  List.iter
    (fun (written, text, code) ->
      Harness.test ("nothing is written through a view: " ^ written) (fun () ->
          expect_one_diagnostic text code ~says:"a view"))
    [
      ( "a `mut self` method of a view held in a `var`",
        Fixtures.Infer.view_variable_copied_into,
        "types.wrong_receiver" );
      ( "a view of a read-only parameter passed `mut`",
        Fixtures.Infer.view_of_a_read_only_parameter_bumped,
        "types.wrong_mode" );
      ( "a view of a constant passed `mut`",
        Fixtures.Infer.view_of_a_constant_list_bumped,
        "types.wrong_mode" );
      ( "an assigned element of a view of a `let`",
        Fixtures.Infer.view_of_a_let_list_assigned,
        "types.not_assignable" );
      ("a view held in a field", Fixtures.Infer.window_rest_bumped, "types.wrong_mode");
      ( "the variable of a `mut` loop over a list of views",
        Fixtures.Infer.element_of_a_view_in_a_list_assigned,
        "types.not_assignable" );
      ( "a range of a view",
        Fixtures.Infer.range_of_a_view_of_a_read_only_list_sorted,
        "types.wrong_mode" );
      ( "a range of a range of a view",
        Fixtures.Infer.range_of_a_range_of_a_view_of_a_read_only_list_sorted,
        "types.wrong_mode" );
      ( "an assigned element of a range of a view",
        Fixtures.Infer.element_of_a_range_of_a_view_of_a_read_only_list_assigned,
        "types.not_assignable" );
      ( "an element of a range of a view passed `mut`",
        Fixtures.Infer.element_of_a_range_of_a_view_of_a_read_only_list_passed_mut,
        "types.wrong_mode" );
      ( "an assigned element of an element of a view",
        Fixtures.Infer.element_of_an_element_of_a_view_of_a_read_only_list_assigned,
        "types.not_assignable" );
      ( "an element of an element of a view passed `mut`",
        Fixtures.Infer.element_of_an_element_of_a_view_of_a_read_only_list_passed_mut,
        "types.wrong_mode" );
      ( "a range of an element of a view",
        Fixtures.Infer.range_of_an_element_of_a_view_of_a_read_only_list_sorted,
        "types.wrong_mode" );
      ( "a `mut` loop over a view",
        Fixtures.Infer.loop_variable_over_a_view_of_a_read_only_list_passed_mut,
        "types.not_iterable" );
      ( "a `mut` loop over a range of a view",
        Fixtures.Infer.loop_variable_over_a_range_of_a_view_of_a_read_only_list_passed_mut,
        "types.wrong_mode" );
      ( "a `match` on an element of a view",
        Fixtures.Infer.match_binding_of_an_element_of_a_view_of_a_read_only_list_passed_mut,
        "types.wrong_mode" );
    ];
  Harness.test "a `mut` list parameter and a range of a mutable place can be written through"
    (fun () -> expect_fine Fixtures.Infer.lists_written_through_parameters_and_ranges);
  Harness.test "a view implements a trait whose inherited methods take `Self` by `own`" (fun () ->
      expect_fine Fixtures.Infer.views_in_ordered_positions);
  Harness.test "a view satisfies no bound whose impl writes a method that takes `self` by `own`"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.view_given_to_a_bound_whose_impl_owns_self
        "types.unsatisfied_bound");
  Harness.test
    "a view satisfies no bound whose supertrait's impl writes a method that takes `self` by `mut`"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.view_given_to_a_bound_whose_supertrait_mutates_self
        "types.unsatisfied_bound");
  Harness.test "a view is no receiver of an inherited method whose supertrait's impl mutates `self`"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.view_receiver_of_a_method_whose_supertrait_mutates_self
        "types.wrong_receiver");
  Harness.test "a view satisfies no bound whose trait has a `mut self` method" (fun () ->
      expect_one_diagnostic Fixtures.Infer.view_written_through_a_copy_in_generic_code
        "types.unsatisfied_bound" ~says:"a view implements a trait only where");
  List.iter
    (fun (construct, text) ->
      Harness.test (construct ^ " cannot be passed `mut`") (fun () ->
          expect_one_diagnostic text "types.wrong_mode"))
    [
      ("a read-only parameter", Fixtures.Infer.push_onto_a_read_only_parameter);
      ("an `own` parameter", Fixtures.Infer.push_onto_an_own_parameter);
      ("a `let`", Fixtures.Infer.push_onto_a_let_list);
      ("a field of a `let`", Fixtures.Infer.push_onto_a_field_of_a_let);
      ( "an element of a read-only parameter",
        Fixtures.Infer.push_onto_an_element_of_a_read_only_parameter );
      ("a constant", Fixtures.Infer.constant_list_pushed_to);
      ("a read-only argument", Fixtures.Infer.read_only_list_passed_mut);
      ( "the collection of a `for` loop that is a read-only parameter",
        Fixtures.Infer.mut_loop_over_a_read_only_list );
      ( "`self` in a method that takes `self` read-only",
        Fixtures.Infer.push_onto_a_field_of_read_only_self );
      ("`self` inside a lambda", Fixtures.Infer.lambda_pushing_onto_self);
      ("a local that a lambda captures", Fixtures.Infer.lambda_pushing_onto_a_captured_list);
    ];
  Harness.test
    "a `var`, a `mut` parameter, `mut self`, and a `mut` loop variable can be passed `mut`"
    (fun () -> expect_fine Fixtures.Infer.mut_arguments_of_every_kind);
  Harness.test "the variable of a loop over elements lent `mut` can be passed `mut`" (fun () ->
      expect_fine Fixtures.Infer.mut_loop_over_rows);
  Harness.test "a var can be assigned" (fun () -> expect_fine Fixtures.Infer.assignment_to_a_var);
  Harness.test "an empty list bound to a `var` without a type asks for the `var`'s type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.empty_list_without_a_type "types.cannot_infer"
        ~at:("names", 1)
        ~says:
          "The type of `names` cannot be inferred from this statement alone. Declare `names` with \
           a type.");
  Harness.test "a loop over an empty list asks for its binding's type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.loop_over_an_empty_list "types.cannot_infer"
        ~at:("value", 1) ~says:"The type of `value` cannot be inferred from this statement alone.");
  Harness.test "a comparison of empty lists names the first list" (fun () ->
      expect_one_diagnostic Fixtures.Infer.comparison_of_empty_lists "types.cannot_infer"
        ~at:("[]", 1)
        ~says:
          "Nothing here determines the element type of `[]`. Bind the list with a typed `let`, \
           such as `let names: List[String] = []`.");
  Harness.test "a method of an empty list names the list, not the method's type parameter"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.length_of_an_empty_list "types.cannot_infer"
        ~at:("[]", 1) ~says:"Nothing here determines the element type of `[]`.");
  Harness.test "a method of an empty map names the map" (fun () ->
      expect_one_diagnostic Fixtures.Infer.length_of_an_empty_map "types.cannot_infer" ~at:("[:]", 1)
        ~says:
          "Nothing here determines the key and value types of `[:]`. Bind the map with a typed \
           `let`, such as `let ages: Map[String, UInt8] = [:]`.");
  Harness.test "a function value whose type argument nothing decides is reported at its name"
    (fun () ->
      expect_one_diagnostic ~at:("make", 3)
        Fixtures.Infer.let_of_a_function_value_with_an_unused_type_parameter "types.cannot_infer"
        ~says:
          "Nothing here determines `Unused`, a type parameter of `make`. Give `make` its type \
           arguments in brackets.");
  Harness.test "an empty list takes its elements' type from the annotation" (fun () ->
      expect_fine Fixtures.Infer.empty_list_of_strings);
  Harness.test "a body's value must have the result type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.body_returning_bool_as_int64 "types.mismatch");
  Harness.test "a body may end with a let whose value never finishes" (fun () ->
      expect_fine Fixtures.Infer.let_of_a_returning_if_at_the_end);
  Harness.test "an arm of type Never does not contribute to the type of the match" (fun () ->
      expect_fine Fixtures.Infer.match_with_a_returning_arm);
  Harness.test "? needs the function's error type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.question_mark_on_a_result_of_another_error
        "types.wrong_try");
  Harness.test "? on a matching Result gives its value" (fun () ->
      expect_type Fixtures.Infer.question_mark_on_a_result_of_the_same_error "parse()?" "Int64");
  Harness.test "if without else has type Unit" (fun () ->
      expect_type Fixtures.Infer.let_of_an_if_without_else "if ready { }" "Unit")

let () =
  Harness.test "an unknown field is an error with a fix to the closest" (fun () ->
      expect_one_diagnostic Fixtures.Infer.misspelled_field "types.unknown_member"
        ~fixed:("point.z", "point.x"));
  Harness.test "a method from a trait needs no import" (fun () ->
      expect_fine Fixtures.Infer.copy_of_a_list);
  Harness.test "a law's proof names the law's parameters, which have the proof's type for Self"
    (fun () -> expect_fine Fixtures.Infer.law_proof_reading_its_parameters);
  Harness.test "a law's proof for a generic impl is checked under its own generic parameters"
    (fun () -> expect_fine Fixtures.Infer.law_proof_for_a_generic_box);
  Harness.test "a law's proof names no parameter of another law" (fun () ->
      expect_one_diagnostic Fixtures.Infer.law_proof_naming_another_laws_parameter
        "resolve.unknown_name");
  Harness.test "a law's proof cannot assign to a parameter of the law" (fun () ->
      expect_one_diagnostic Fixtures.Infer.law_proof_assigning_a_parameter
        "types.not_in_specification");
  Harness.test "a variant with one field is a function" (fun () ->
      expect_fine Fixtures.Infer.circle_as_a_function);
  Harness.test "a variant with several fields is not a function, because fields have no order"
    (fun () -> expect_one_diagnostic Fixtures.Infer.rectangle_as_a_function "types.not_a_value");
  Harness.test "a lending method is not a function value, because a function type cannot lend"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.lending_method_as_a_value "types.not_a_value"
        ~says:"a function value cannot lend");
  Harness.test "a variant is looked up under its type" (fun () ->
      expect_fine Fixtures.Infer.shape_variants_built);
  Harness.test "a constant under a type is read by name" (fun () ->
      expect_type Fixtures.Infer.uint8_maximum "UInt8.maximum" "UInt8");
  Harness.test "a trait method through a type chooses the impl by the argument" (fun () ->
      expect_fine Fixtures.Infer.big_integer_from_an_int64)

let () =
  Harness.test "an unknown variant in a pattern is fixed to the closest variant with as many fields"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.misspelled_variant_arm "types.unknown_variant"
        ~fixed:("Sone", "Some"));
  Harness.test "a bare name in a record pattern binds the field it names" (fun () ->
      expect_fine Fixtures.Infer.let_binding_both_fields_of_a_pair);
  Harness.test "a bare name that names no field of a record with several is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.record_pattern_with_a_name_of_no_field
        "types.missing_label"
        ~fixed:("let (a, second) = pair", "let (first: a, second) = pair"))

let () =
  Harness.test "a tuple pattern binds the fields of a tuple type by position" (fun () ->
      let text = Fixtures.Infer.tuple_patterns_bind_fields_by_position in
      expect_fine text;
      expect_type text "name" ~occurrence:2 "String";
      expect_type text "count" ~occurrence:4 "Int64";
      expect_type text "index" ~occurrence:2 "UInt64";
      expect_type text "byte" ~occurrence:4 "UInt8");
  Harness.test "a tuple pattern names the fields in their order" (fun () ->
      expect_one_diagnostic Fixtures.Infer.tuple_pattern_names_fields_out_of_order
        "types.out_of_order" ~says:"`value` here would bind the field `key`"
        ~fixed:("value, key", "key, value"));
  Harness.test "a tuple pattern has one pattern for each field" (fun () ->
      expect_one_diagnostic Fixtures.Infer.tuple_pattern_with_a_pattern_too_many "types.arity");
  Harness.test "a tuple pattern matches only a tuple type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.tuple_pattern_on_a_record "types.not_a_tuple_type"
        ~fixed:("let x, y = point", "let (x, y) = point"));
  Harness.test "parentheses match the fields of a tuple type by name" (fun () ->
      expect_fine Fixtures.Infer.record_pattern_on_a_tuple_type_by_name;
      expect_one_diagnostic Fixtures.Infer.record_pattern_on_map_entries_with_a_wildcard
        "types.missing_label"
        ~says:"a list of patterns without parentheses matches its fields by position"
        ~fixed:("(_, group)", "_, group"));
  Harness.test "a bare pattern that names no field is labeled with the one field left open"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.record_pattern_on_map_entries_in_a_lambda
        "types.missing_label"
        ~fixed:
          ( "counts.count_where(fn((key, count)) { count > key.length() })",
            "counts.count_where(fn((key, value: count)) { count > key.length() })" );
      expect_one_diagnostic Fixtures.Infer.variant_pattern_with_a_wildcard_for_a_field
        "types.missing_label" ~says:"`Link` has 2 fields: `value`, `rest`."
        ~fixed:("Link(_, rest) => rest is Link(..)", "Link(value: _, rest) => rest is Link(..)"))

let () =
  let report text = check (Support.setup [ ("app.main", text) ]) (Support.parse_file "app.main") in
  let expect_codes code ~count diagnostics =
    let codes = Support.list_codes diagnostics in
    if codes <> List.init count (fun _ -> code) then
      Harness.fail "expected %d %s, got [%s]" count code (String.concat "; " codes)
  in
  let expect_every_fix text code ~count ~fixed =
    let diagnostics = report text in
    expect_codes code ~count diagnostics;
    match
      List.concat_map
        (fun (diagnostic : Diagnostic.t) ->
          match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
        diagnostics
    with
    | edits when List.length edits <> count -> Harness.fail "not every diagnostic has one fix"
    | edits -> (
        let after = Diagnostic.apply_edits text edits in
        if after <> Support.apply_edit text fixed then Harness.fail "fixed to %S" after
        else
          match report after with
          | [] -> ()
          | left ->
              Harness.fail "after the fixes: [%s]" (String.concat "; " (Support.list_codes left)))
  in
  let expect_no_fix text code ~count =
    let diagnostics = report text in
    expect_codes code ~count diagnostics;
    if List.exists (fun (diagnostic : Diagnostic.t) -> diagnostic.fixes <> []) diagnostics then
      Harness.fail "offered a fix"
  in
  Harness.test "a complete positional list is labeled in the declared order of the fields"
    (fun () ->
      expect_every_fix Fixtures.Infer.color_built_with_three_positional_arguments
        "types.missing_label" ~count:3
        ~fixed:("Color(1, 2, 3)", "Color(red: 1, green: 2, blue: 3)");
      expect_every_fix Fixtures.Infer.link_matched_with_two_names_of_no_field "types.missing_label"
        ~count:2
        ~fixed:("Link(head, tail)", "Link(value: head, rest: tail)"));
  Harness.test "a partial positional list gets no fix, since which field each means is not known"
    (fun () ->
      expect_no_fix Fixtures.Infer.color_built_with_two_positional_arguments_and_a_label
        "types.missing_label" ~count:2;
      expect_no_fix Fixtures.Infer.triple_matched_with_two_names_of_no_field_and_a_rest
        "types.missing_label" ~count:2);
  Harness.test "a label in a pattern that names no field is an unknown label" (fun () ->
      expect_one_diagnostic Fixtures.Infer.link_matched_with_a_misspelled_label
        "types.unknown_label" ~says:"`Link` has no field `valu`."
        ~fixed:("Link(valu: head, ..) => head", "Link(value: head, ..) => head"));
  Harness.test "a field matched twice in a pattern is a repeated argument" (fun () ->
      expect_one_diagnostic Fixtures.Infer.link_matched_with_a_field_twice "types.repeated_argument"
        ~says:"`value` is matched more than once.");
  Harness.test "a tuple pattern on a record is fixed to its labeled form" (fun () ->
      expect_one_diagnostic Fixtures.Infer.tuple_pattern_of_other_names_on_a_record
        "types.not_a_tuple_type" ~says:"as in `(start: low, stop: high)`"
        ~fixed:("low, high", "(start: low, stop: high)"));
  Harness.test "a tuple type is built by position, then by label" (fun () ->
      expect_fine Fixtures.Infer.span_built_by_position_and_by_label);
  Harness.test
    "a variable named like another field of a tuple type is an error, with a fix that labels it"
    (fun () ->
      expect_every_fix Fixtures.Infer.span_built_with_its_fields_swapped "types.out_of_order"
        ~count:2
        ~fixed:("Span(end, start)", "Span(end: end, start: start)"));
  Harness.test "a tuple type takes no positional argument after a label" (fun () ->
      expect_one_diagnostic Fixtures.Infer.span_built_with_a_positional_argument_after_a_label
        "types.positional_after_labeled")

let () =
  Harness.test "a lambda parameter that nothing gives a type asks for an annotation" (fun () ->
      expect_one_diagnostic Fixtures.Infer.lambda_bound_without_a_type "types.cannot_infer"
        ~at:("text", 1) ~says:"Declare `text` with a type.";
      expect_one_diagnostic Fixtures.Infer.lambda_passed_as_a_type_argument "types.cannot_infer"
        ~at:("x", 1) ~says:"Declare `x` with a type.");
  Harness.test "an annotation decides a lambda parameter's type that the callee leaves open"
    (fun () ->
      expect_fine Fixtures.Infer.annotated_lambda_parameter_of_a_generic_callee;
      expect_fine Fixtures.Infer.annotated_lambda_passed_as_a_type_argument);
  Harness.test "a lambda that nothing passes as a function type is typed by its annotations"
    (fun () ->
      expect_type Fixtures.Infer.annotated_lambda_bound_without_a_type
        "fn(value: Int64) { value.saturating_add(amount) }" "fn(Int64) -> Int64";
      expect_type Fixtures.Infer.annotated_mut_lambda_bound_without_a_type
        "fn(count: mut Int64) { count = count.saturating_add(1) }" "fn(mut Int64)");
  Harness.test "an annotation of another type than the function type's is a mismatch" (fun () ->
      expect_one_diagnostic Fixtures.Infer.lambda_parameter_annotated_with_another_type
        "types.mismatch" ~at:("UInt8", 1)
        ~says:"This lambda's function type gives this parameter `Int64`, not `UInt8`.");
  Harness.test "an annotation of another mode than the function type's is a wrong mode" (fun () ->
      expect_one_diagnostic Fixtures.Infer.lambda_parameter_annotated_without_mut "types.wrong_mode"
        ~says:"This lambda's function type passes this parameter `mut`, not read-only."
        ~fixed:("score: Int64", "score: mut Int64");
      expect_one_diagnostic Fixtures.Infer.lambda_parameter_annotated_mut_where_passed_read_only
        "types.wrong_mode"
        ~says:"This lambda's function type passes this parameter read-only, not `mut`."
        ~fixed:("item: mut Int64", "item: Int64"));
  Harness.test "a lambda takes its parameter types from the function type it is passed as"
    (fun () -> expect_type Fixtures.Infer.lambda_incrementing_items "item + 1" "Int64");
  Harness.test "concurrent code needs `Tasks`, in a block and in a loop" (fun () ->
      expect_one_diagnostic Fixtures.Infer.concurrent_block_without_tasks
        "capabilities.not_available";
      expect_one_diagnostic Fixtures.Infer.concurrent_loop_without_tasks
        "capabilities.not_available");
  Harness.test "a branch of a concurrent block uses the capabilities around the block" (fun () ->
      expect_fine Fixtures.Infer.concurrent_branch_calling_tick);
  (let sessions = Fixtures.Infer.sessions in
   Harness.test
     "a capability implemented by a monitor has no method with a callback that uses a capability"
     (fun () ->
       expect_one_diagnostic
         (sessions ^ Fixtures.Infer.monitor_table_with_a_callback)
         "capabilities.callback_may_deadlock");
   Harness.test
     "a capability implemented by a monitor may take a callback that uses only `Panic` and \
      `RunForever`, since no `provide` implements either" (fun () ->
       expect_fine Fixtures.Infer.monitor_table_with_callbacks_that_use_only_built_in_capabilities);
   Harness.test "an implementation is not a monitor if the body of its `provide` cannot use `Tasks`"
     (fun () -> expect_fine (sessions ^ Fixtures.Infer.table_provided_without_tasks));
   let tally = Fixtures.Infer.tally in
   Harness.test "a monitor needs `Tasks` at its `provide`, not only in a nested one" (fun () ->
       expect_one_diagnostic
         (tally ^ Fixtures.Infer.tally_provided_without_tasks)
         "capabilities.monitor_needs_tasks");
   Harness.test
     "a monitor can lock through `Tasks` of its `provide`, an enclosing one, or a capability \
      parameter" (fun () ->
       expect_fine (tally ^ Fixtures.Infer.monitors_provided_with_and_without_tasks)));
  Harness.test "an assignment through an index of a map takes the key as an owned value" (fun () ->
      expect_fine Fixtures.Infer.map_assignments_with_owned_keys;
      expect_one_diagnostic Fixtures.Infer.map_assignment_to_a_read_only_map "types.not_assignable");
  Harness.test "`final(result)` is a lending method's part as the caller left it" (fun () ->
      expect_fine Fixtures.Infer.lending_part_ensuring_final_of_result;
      expect_one_diagnostic ~says:"`final(result)`"
        Fixtures.Infer.lending_part_ensuring_final_of_a_field "types.not_callable");
  Harness.test "`final` and `visited` are names only where they have a meaning" (fun () ->
      expect_one_diagnostic Fixtures.Infer.ensures_naming_final_outside_a_lend
        "resolve.unknown_name";
      expect_one_diagnostic Fixtures.Infer.while_invariant_naming_visited "resolve.unknown_name");
  (let readings = Fixtures.Infer.readings in
   let assign = Fixtures.Infer.readings_assign in
   Harness.test "an element of a type that implements `Index` alone is read" (fun () ->
       expect_fine (readings ^ Fixtures.Infer.elements_of_readings_read));
   Harness.test "an element of a type that implements `Index` alone is not assigned" (fun () ->
       expect_one_diagnostic ~says:"and not `IndexMut`"
         (readings ^ Fixtures.Infer.assignment_through_an_index_of_readings)
         "types.not_assignable");
   Harness.test "an element of a type that implements `Index` alone is not passed `mut`" (fun () ->
       expect_one_diagnostic ~says:"and not `IndexMut`"
         (readings ^ Fixtures.Infer.element_of_readings_passed_mut)
         "types.wrong_mode");
   Harness.test "an assignment through an index calls `assign` without `IndexMut`" (fun () ->
       expect_fine (readings ^ assign ^ Fixtures.Infer.assignment_through_an_index_of_readings));
   Harness.test "a compound assignment through an index needs `IndexMut`" (fun () ->
       expect_one_diagnostic ~says:"Assign the whole element with `=`."
         (readings ^ assign ^ Fixtures.Infer.compound_assignment_through_an_index_of_readings)
         "types.not_assignable"));
  (let tagged = Fixtures.Infer.tagged in
   let cell = tagged ^ Fixtures.Infer.cell in
   Harness.test "an assignment through an index checks the conditions of the `IndexAssign` impl"
     (fun () ->
       let assign = cell ^ Fixtures.Infer.cell_assign_for_tagged_items in
       expect_one_diagnostic ~says:"Its impl needs `Int64: Tagged`."
         (assign ^ Fixtures.Infer.assignment_through_an_index_of_a_cell_of_a_literal)
         "types.no_impl";
       expect_fine (assign ^ Fixtures.Infer.assignment_through_an_index_of_a_cell_of_a_uint8));
   Harness.test "an element passed `mut` needs `IndexMut` for the element's final type" (fun () ->
       let index_mut = cell ^ Fixtures.Infer.cell_mut_for_tagged_items in
       expect_one_diagnostic ~says:"and not `IndexMut`"
         (index_mut ^ Fixtures.Infer.element_of_a_cell_of_a_literal_passed_mut)
         "types.wrong_mode";
       expect_fine (index_mut ^ Fixtures.Infer.element_of_a_cell_of_a_uint8_passed_mut));
   Harness.test "a loop over a cursor is measured by `FiniteCursor` of the cursor's final type"
     (fun () ->
       let countdown = tagged ^ Fixtures.Infer.countdown_finite_for_tagged_items in
       expect_one_diagnostic ~says:"implement `FiniteCursor` for `Countdown[Int64]`"
         (countdown ^ Fixtures.Infer.loop_over_a_countdown_of_a_literal)
         "capabilities.not_available";
       expect_fine (countdown ^ Fixtures.Infer.loop_over_a_countdown_of_a_uint8)));
  (let keep = Fixtures.Infer.keep in
   Harness.test "a type that holds no view is Storable" (fun () ->
       expect_fine (keep ^ Fixtures.Infer.values_without_views_kept));
   Harness.test "a trait that requires Storable cannot be implemented for a view type" (fun () ->
       expect_one_diagnostic
         (keep ^ Fixtures.Infer.job_impl_for_labeled)
         "types.missing_required_impl");
   List.iter
     (fun (name, body) ->
       Harness.test name (fun () -> expect_one_diagnostic (keep ^ body) "types.unsatisfied_bound"))
     [
       ("a view is not Storable", Fixtures.Infer.view_kept);
       ("a record that holds a view is not Storable", Fixtures.Infer.labeled_view_kept);
       ("a generic type is not Storable where its argument is not", Fixtures.Infer.boxed_view_kept);
       ("a function type is not Storable", Fixtures.Infer.function_kept);
       ( "a type parameter is Storable only when it is bounded",
         Fixtures.Infer.unbounded_element_kept );
     ];
   Harness.test "no impl of Storable can be written" (fun () ->
       expect_one_diagnostic (keep ^ "impl Storable for Labeled {}\n") "types.implements_built_in"));
  Harness.test "the body of a concurrent block gets its types" (fun () ->
      expect_type Fixtures.Infer.concurrent_block_calling_g "2" "UInt16");
  Harness.test "a lambda's captures are the outer locals it reads" (fun () ->
      let text = Fixtures.Infer.lambda_adding_a_captured_step in
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match node.kind with Lambda { captures; _ } -> Some captures | _ -> None)
          (Support.collect_first_core_nodes text).expressions
      with
      | [ [ _ ] ] -> ()
      | [ actual ] -> Harness.fail "%d captures" (List.length actual)
      | actual -> Harness.fail "%d lambdas" (List.length actual))

let () =
  Harness.test "an interpolated value must implement Display" (fun () ->
      expect_one_diagnostic Fixtures.Infer.interpolation_of_a_point "types.no_impl");
  Harness.test "an array literal must have its type's length" (fun () ->
      expect_one_diagnostic Fixtures.Infer.array_literal_of_the_wrong_length "types.mismatch");
  Harness.test "a list literal is a set where a set is expected" (fun () ->
      expect_fine Fixtures.Infer.list_literal_as_a_set);
  Harness.test "a list literal is a deque where a deque is expected" (fun () ->
      expect_fine Fixtures.Infer.list_literal_as_a_deque);
  Harness.test "a map literal is a sorted map where a sorted map is expected" (fun () ->
      expect_fine Fixtures.Infer.map_literal_as_a_sorted_map);
  Harness.test "a loop over a type with its own `count` and `element` and no `Iterable` is an error"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.loop_over_a_type_with_its_own_count_and_element
        "types.not_iterable"
        ~says:"A `for` loop cannot go over `Pair`: it implements neither `Iterable` nor `Cursor`."
        ~at:("pair {", 1));
  Harness.test
    "a quantifier over a type with its own `count` and `element` and no `Iterable` is an error"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.quantifier_over_a_type_with_its_own_count_and_element
        "types.not_iterable"
        ~says:"A quantifier cannot go over `Pair`: it does not implement `Iterable`."
        ~at:("pair =>", 1));
  Harness.test "an `own` loop over a type with its own `cursor` and no `IntoCursor` is an error"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.own_loop_over_a_type_with_its_own_cursor
        "types.not_iterable"
        ~says:"A `for` loop cannot consume `Deck`: it implements neither `IntoCursor` nor `Cursor`."
        ~at:("deck {", 1));
  Harness.test
    "loops over type parameters read, mutate, and consume through `Iterable`, `IterableMut`, and \
     `IntoCursor`" (fun () -> expect_fine Fixtures.Infer.loops_over_type_parameters_by_their_traits);
  Harness.test "a bound fixes the associated types that the traits it requires declare" (fun () ->
      expect_fine Fixtures.Infer.bounds_fixing_associated_types_of_required_traits);
  Harness.test
    "an `own` loop over an `IntoCursor` impl whose `Cursor` is no cursor reports only the impl"
    (fun () ->
      match
        Support.list_codes
          (check
             (Support.setup
                [
                  ( "app.main",
                    Fixtures.Infer.own_loop_over_an_into_cursor_whose_cursor_is_not_a_cursor );
                ])
             (Support.parse_file "app.main"))
      with
      | [ "types.unsatisfied_bound" ] -> ()
      | reported -> Harness.fail "reported [%s]" (String.concat "; " reported));
  Harness.test "a list literal is a type that implements FromElements" (fun () ->
      expect_fine Fixtures.Infer.list_literal_as_a_type_with_from_elements;
      expect_type Fixtures.Infer.list_literal_as_a_type_with_from_elements "[1, 2, 3]"
        "Stack[Int64]");
  Harness.test "a map literal is a type that implements FromEntries" (fun () ->
      expect_fine Fixtures.Infer.map_literal_as_a_type_with_from_entries);
  Harness.test "a list literal is a type parameter that FromElements bounds" (fun () ->
      expect_fine Fixtures.Infer.list_literal_as_a_bounded_type_parameter);
  Harness.test "a literal's elements take the element type of the expected collection" (fun () ->
      expect_type Fixtures.Infer.list_literal_of_set_literals "[1, 2]" "Set[Int64]");
  Harness.test "a list literal needs the conditions of the collection's impl" (fun () ->
      expect_one_diagnostic Fixtures.Infer.list_literal_as_a_type_whose_impl_needs_more
        "types.no_impl"
        ~says:"`Ranked[Point]` does not implement `FromElements`. Its impl needs `Point: Ordered`.");
  Harness.test "a list literal is not a type that implements no literal trait" (fun () ->
      expect_one_diagnostic Fixtures.Infer.list_literal_as_a_heap "types.mismatch");
  Harness.test "new on a type that takes a list literal names the literal" (fun () ->
      expect_one_diagnostic Fixtures.Infer.new_on_a_list "types.unknown_member"
        ~says:"The literal `[]` is an empty `List[_]`." ~fixed:("List.new()", "[]"));
  Harness.test "new on a type that takes a map literal names the literal" (fun () ->
      expect_one_diagnostic Fixtures.Infer.new_on_a_sorted_map "types.unknown_member"
        ~says:"The literal `[:]` is an empty"
        ~fixed:("collections.SortedMap.new()", "[:]"));
  Harness.test "new where nothing expects the collection names the literal and offers no fix"
    (fun () ->
      let text = Fixtures.Infer.new_on_a_list_with_type_arguments in
      expect_one_diagnostic text "types.unknown_member"
        ~says:"The literal `[]` is an empty `List[String]`.";
      List.iter
        (fun (diagnostic : Diagnostic.t) ->
          if diagnostic.fixes <> [] then
            Harness.fail "`[]` alone would not say which collection it is, and a fix is offered")
        (check (Support.setup [ ("app.main", text) ]) (Support.parse_file "app.main")))

let () =
  Harness.test "deriving Deserialize needs every invariant clause to run" (fun () ->
      expect_one_diagnostic Fixtures.Infer.deserialize_of_digits_with_an_invariant_over_a_type
        "types.cannot_derive");
  Harness.test "deriving Deserialize needs an invariant that names no `identical`" (fun () ->
      expect_one_diagnostic Fixtures.Infer.deserialize_of_rivals_with_an_invariant_naming_identical
        "types.cannot_derive");
  Harness.test "deriving Deserialize accepts an invariant that runs" (fun () ->
      expect_fine Fixtures.Infer.deserialize_of_bounds_with_an_invariant);
  Harness.test "deriving Deserialize accepts an invariant that quantifies over a range" (fun () ->
      expect_fine Fixtures.Infer.deserialize_of_scores_with_an_invariant_over_a_range);
  Harness.test "integer arithmetic in a specification is exact" (fun () ->
      expect_type Fixtures.Infer.ensures_of_a_sum "a + b" "Integer");
  Harness.test "comparisons in a specification may mix integer types" (fun () ->
      expect_fine Fixtures.Infer.requires_comparing_uint32_and_uint64);
  Harness.test "a lambda in a specification may give a built-in integer for an Integer" (fun () ->
      expect_fine Fixtures.Infer.requires_summing_lengths_with_a_lambda)

let () =
  Harness.test "a for loop over a range of integers is a counted loop" (fun () ->
      let text = Fixtures.Infer.range_loop_to_a_count in
      if
        not
          (List.exists
             (fun (node : Core.statement) ->
               match node.kind with For { iteration = Integer_range _; _ } -> true | _ -> false)
             (Support.collect_first_core_nodes text).statements)
      then Harness.fail "no counted loop");
  Harness.test "a for loop over a list visits its positions" (fun () ->
      expect_fine Fixtures.Infer.loop_summing_a_list)

let () =
  Harness.test "checking twice gives the same result" (fun () ->
      let text = Fixtures.Infer.loop_summing_a_list in
      let find_type_check_result () =
        let packages = Support.setup [ ("app.main", text) ] in
        let key =
          (List.hd (Support.list_declarations packages (Support.parse_module "app.main"))).key
        in
        Database.read_checked_body (Support.make_database packages) key
      in
      if find_type_check_result () <> find_type_check_result () then Harness.fail "different")

let point = "type Point(x: Int64)\n\n"

let () =
  Harness.test "a call's type arguments must meet their bounds" (fun () ->
      expect_one_diagnostic
        (point ^ Fixtures.Infer.need_of_an_unordered_point)
        "types.unsatisfied_bound");
  Harness.test "a type written in a body must meet its bounds" (fun () ->
      let packages = Support.setup [ ("app.main", point ^ Fixtures.Infer.set_of_points) ] in
      match Support.list_codes (check packages (Support.parse_file "app.main")) with
      | [ "types.unsatisfied_bound"; "types.unsatisfied_bound" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test
    "storage_lengthen rejects an element type with a drop, which would free memory that nothing \
     wrote" (fun () ->
      Support.expect_one_diagnostic ~setup:make_standard_packages ~file:"standard.probe"
        ~check:check_as_standard_library Fixtures.Infer.storage_lengthen_of_storages
        "types.unsatisfied_bound");
  Harness.test "a type written in a body that is not a type is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.let_of_type_display "types.not_a_type");
  Harness.test "an operator's result must be the type expected of it" (fun () ->
      expect_one_diagnostic Fixtures.Infer.product_of_a_span "types.mismatch");
  Harness.test "an array length nothing decides is an error at its call" (fun () ->
      expect_one_diagnostic Fixtures.Infer.zeros_without_a_length "types.cannot_infer"
        ~at:("zeros()", 1)
        ~says:
          "Nothing here determines `count`, a value parameter of `zeros`. Give `zeros` its \
           arguments in brackets.");
  Harness.test "a qualified constant in a pattern must have the matched type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.exit_code_constant_arm_on_an_integer "types.mismatch");
  Harness.test "the alternatives of a pattern bind each name with one type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.or_pattern_binding_value_of_two_types "types.mismatch");
  Harness.test "a pattern must match every field or write .." (fun () ->
      expect_one_diagnostic Fixtures.Infer.record_pattern_missing_a_field "types.missing_argument");
  (let make_comparison_source depth =
     "type Box[Value](value: Value)\n  derives Equal\n\nfn same(value: "
     ^ String.concat "" (List.init depth (fun _ -> "Box["))
     ^ "Int64" ^ String.make depth ']' ^ ") -> Bool {\n  value == value\n}\n"
   in
   Harness.test "a type nested 40 deep implements a trait through 40 nested impls" (fun () ->
       expect_fine (make_comparison_source 40));
   Harness.test "a type nested 70 deep reaches the recursion limit of the impls that it needs"
     (fun () ->
       expect_one_diagnostic (make_comparison_source 70) "types.recursion_limit"
         ~says:"needs more than 64 nested impls"));
  Harness.test "an opaque type cannot be matched outside its package" (fun () ->
      expect_one_diagnostic Fixtures.Infer.record_pattern_on_a_list "types.private_field");
  Harness.test "a bitwise compound assignment works on integers only" (fun () ->
      expect_one_diagnostic Fixtures.Infer.bitwise_assignment_to_a_string "types.no_impl");
  Harness.test "a method written in full takes its receiver's mode" (fun () ->
      expect_one_diagnostic Fixtures.Infer.push_written_in_full "types.wrong_receiver");
  Harness.test
    "a for loop reads through `Iterable`'s `element` and mutates through `IterableMut`'s overload"
    (fun () -> expect_fine Fixtures.Infer.loop_over_a_bag_with_an_element_overload);
  Harness.test "a call picks an overload among a type's own and its family of traits'" (fun () ->
      expect_fine Fixtures.Infer.overloads_of_label_across_traits);
  Harness.test "two traits that give one overload of a name are ambiguous at the call" (fun () ->
      expect_one_diagnostic Fixtures.Infer.traits_giving_one_label "types.ambiguous_method"
        ~alternatives:[ ("counter.label()", "Second.label(counter)") ]
        ~fixed:("counter.label()", "First.label(counter)"));
  Harness.test "two unrelated traits that share a name are ambiguous however each takes self"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.unrelated_traits_sharing_label "types.ambiguous_method"
        ~fixed:("Counter(count: 3).label()", "First.label(Counter(count: 3))")
        ~alternatives:[ ("Counter(count: 3).label()", "Second.label(Counter(count: 3))") ]);
  Harness.test "two bounds that give one overload of a name are ambiguous through the type"
    (fun () -> expect_one_diagnostic Fixtures.Infer.bounds_giving_one_make "types.ambiguous_method");
  Harness.test "two unrelated bounds that share a name are ambiguous however each takes self"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.unrelated_bounds_sharing_label "types.ambiguous_method"
        ~fixed:("value.label()", "First.label(value)"));
  Harness.test "a bound's method is picked from its family by how the call takes self" (fun () ->
      expect_fine Fixtures.Infer.bound_with_overloads_by_receiver);
  Harness.test "a trait's method written in full takes a temporary or a `Plain` place as `own self`"
    (fun () -> expect_fine Fixtures.Infer.consumed_written_in_full_on_a_temporary_and_a_plain_place);
  Harness.test "a trait's method written in full has no overload for a mode it lacks" (fun () ->
      expect_one_diagnostic Fixtures.Infer.label_written_in_full_with_mut_self
        "types.wrong_receiver");
  Harness.test "an associated type of an argument is normalized" (fun () ->
      expect_fine Fixtures.Infer.has_key_of_a_list);
  Harness.test "a literal receiver's method of a sealed trait takes the type its use decides"
    (fun () ->
      let text = Fixtures.Infer.wrapping_add_on_a_literal in
      expect_fine text;
      expect_type text "5.wrapping_add(3)" "UInt8");
  Harness.test "a for loop over characters counts" (fun () ->
      expect_fine Fixtures.Infer.range_loop_over_characters);
  Harness.test "an operation on a hole is a hole" (fun () ->
      expect_fine Fixtures.Infer.addition_to_a_todo);
  Harness.test "a mistake is not reported again as a type that cannot be inferred" (fun () ->
      expect_one_diagnostic Fixtures.Infer.map_of_an_undefined_name "resolve.unknown_name");
  Harness.test "a Float32 literal too large is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.float32_literal_too_large "types.literal_out_of_range");
  Harness.test "a Float32 literal is rounded once, from its decimal" (fun () ->
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match node.kind with Float rounded -> Some rounded | _ -> None)
          (Support.collect_first_core_nodes Fixtures.Infer.float32_literal_needing_rounding)
            .expressions
      with
      | [ rounded ] ->
          if rounded <> Float.of_string "0x1.000002p+0" then Harness.fail "rounded to %h" rounded
      | _ -> Harness.fail "no value");
  Harness.test "a range pattern has the values of its two bounds" (fun () ->
      match
        List.filter_map
          (fun (node : Core.pattern) ->
            match node.kind with
            | Range { start = Integer_bound low; stop = Integer_bound high; _ } ->
                Some (Z.to_int low, Z.to_int high)
            | _ -> None)
          (Support.collect_first_core_nodes Fixtures.Infer.integer_range_arm).patterns
      with
      | [ (1, 5) ] -> ()
      | _ -> Harness.fail "the range pattern does not have the bounds 1 and 5");
  Harness.test
    "a `let` and a `match` arm copy a `Plain` value that they bind, and a loop variable, a lambda \
     parameter, and a binding of another type do not" (fun () ->
      let modes =
        List.filter_map
          (fun (node : Core.pattern) ->
            match node.kind with
            | Bind { local = Declared { name; _ }; mode; _ } -> Some (name, mode)
            | _ -> None)
          (Support.collect_first_core_nodes Fixtures.Infer.bindings_of_plain_and_other_values)
            .patterns
      in
      List.iter
        (fun (name, (expected : Language.Mode.t)) ->
          match List.assoc_opt name modes with
          | Some mode when mode = expected -> ()
          | Some _ -> Harness.fail "`%s` is bound in another mode" name
          | None -> Harness.fail "`%s` is not bound" name)
        [
          ("copied", Own);
          ("matched", Own);
          ("viewed", Read);
          ("each", Read);
          ("given", Read);
          ("count", Own);
        ]);
  Harness.test
    "a compound assignment copies a `Plain` operand that its operator reads, and views an operand \
     of another type" (fun () ->
      let packages = Support.setup [ ("app.main", Fixtures.Infer.compound_assignment_operands) ] in
      let assigning =
        List.find
          (fun (declaration : Resolve.Names.declaration) ->
            Path.equal declaration.key.path (Support.make_top_path "app.main" "f"))
          (Support.list_declarations packages (Support.parse_module "app.main"))
      in
      match
        List.filter_map
          (fun (node : Core.statement) ->
            match node.kind with Compound_assign { operand; _ } -> Some operand | _ -> None)
          (Support.collect_core_nodes packages assigning.key).statements
      with
      | [ Value _; Place _ ] -> ()
      | _ -> Harness.fail "the operands are not a copy of `count` and a view of `title`");
  Harness.test "a range pattern on a type that is not an integer or Character is an error"
    (fun () -> expect_one_diagnostic Fixtures.Infer.bool_range_arm "types.mismatch");
  Harness.test "an integer range on a type that is not ordered is one error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.integer_range_arm_on_a_bool "types.mismatch");
  Harness.test "a range pattern whose bounds infer its type as Bool is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.bool_range_let_else_of_an_undecided_value
        "types.mismatch" ~says:"not `Bool`");
  Harness.test "a range pattern on Character is fine" (fun () ->
      expect_fine Fixtures.Infer.character_range_arm);
  Harness.test "a Character literal is a tagged string holding its scalar value" (fun () ->
      expect_type Fixtures.Infer.accented_character_literal "Character\"é\"" "Character";
      if not (has_integer Fixtures.Infer.accented_character_literal 0xE9) then
        Harness.fail "no value");
  Harness.test
    "a tagged template rejects an interpolated value that its interpolation type has no `From` \
     impl for" (fun () ->
      expect_one_diagnostic Fixtures.Infer.shout_of_a_number "types.no_impl"
        ~says:"`Int64` cannot become a `String`, the interpolation type of `Shout`.");
  Harness.test "a UInt8 literal holds its ASCII character's value" (fun () ->
      if not (has_integer Fixtures.Infer.uint8_newline_literal 10) then Harness.fail "no value");
  Harness.test "a Character literal of two scalar values is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.character_literal_of_two_letters
        "types.character_scalar_count");
  Harness.test "a UInt8 literal of a character that is not ASCII is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.uint8_accented_literal "types.character_scalar_count");
  Harness.test "a negated literal of an unsigned type is one error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.uint8_let_of_minus_one "types.negated_unsigned");
  Harness.test "a constant of type UInt64 is a type argument in an expression" (fun () ->
      expect_fine Fixtures.Infer.width_given_a_uint64_constant);
  Harness.test "a constant of another type is not a type argument in an expression" (fun () ->
      expect_one_diagnostic Fixtures.Infer.width_given_an_int64_constant "types.arity"
        ~says:"`size` in a type argument must be a constant of type `UInt64`.");
  Harness.test "a constant whose value is not computed is one error as a type argument" (fun () ->
      expect_one_diagnostic Fixtures.Infer.width_given_an_unevaluated_constant "types.arity"
        ~says:"The value of `size` cannot be computed");
  Harness.test "explicit type arguments give exactly the function's own" (fun () ->
      expect_one_diagnostic Fixtures.Infer.pick_with_one_type_argument "types.arity");
  Harness.test
    "a written type argument gives the type parameter of a function that has a capability parameter"
    (fun () ->
      let text = Fixtures.Infer.make_with_a_type_argument_and_a_capability_parameter in
      expect_fine text;
      expect_type text "make[String](ignore)" "Option[String]");
  Harness.test "a capability parameter takes no written type argument" (fun () ->
      expect_one_diagnostic Fixtures.Infer.make_with_a_type_argument_for_its_capability_parameter
        "types.arity" ~says:"This takes 1 type argument, and 2 are given.");
  Harness.test "a type given too few arguments is one error, not a mismatch for each field"
    (fun () -> expect_one_diagnostic Fixtures.Infer.pair_built_with_one_type_argument "types.arity");
  Harness.test "an associated type that a supertrait fixes to Self is Self" (fun () ->
      expect_no_diagnostics [ ("app.main", Fixtures.Infer.output_of_a_fixed_width_integer) ]);
  Harness.test "an associated type of a generic supertrait takes the supertrait's arguments"
    (fun () ->
      expect_no_diagnostics [ ("app.main", Fixtures.Infer.output_of_a_generic_supertrait) ]);
  Harness.test "the string + fix keeps escapes" (fun () ->
      expect_one_diagnostic Fixtures.Infer.escaped_string_plus_a_string "types.string_addition"
        ~fixed:("\"a\\\"b\" + name", "\"a\\\"b${name}\""));
  Harness.test "a lambda cannot mutate a captured variable" (fun () ->
      expect_one_diagnostic Fixtures.Infer.lambda_assigning_a_captured_var "types.not_assignable")

let () =
  Harness.test "a function-typed parameter's requires is a Bool over its inputs" (fun () ->
      expect_fine Fixtures.Infer.function_parameter_requiring_its_index_below_a_limit);
  Harness.test "a function-typed parameter's requires must be a Bool" (fun () ->
      expect_one_diagnostic Fixtures.Infer.function_parameter_requiring_an_integer "types.mismatch");
  Harness.test "a trait method without a body has its clauses checked" (fun () ->
      expect_one_diagnostic Fixtures.Infer.trait_method_ensuring_a_sum_with_true "types.no_impl");
  Harness.test "==> in a compiled body" (fun () ->
      expect_one_diagnostic Fixtures.Infer.implication_in_a_body "types.specification_only");
  Harness.test "a quantifier over a type in a compiled body" (fun () ->
      expect_one_diagnostic Fixtures.Infer.quantifier_over_int64_in_a_body
        "types.specification_only");
  Harness.test "a quantifier's range from an Integer to a UInt64 is a range of Integer" (fun () ->
      let text = Fixtures.Infer.range_in_a_specification_from_an_integer_to_a_uint64 in
      expect_fine text;
      expect_type text "middle + 1..items.length()" "Range[Integer]");
  Harness.test "a quantifier's range is of integers or characters, as a `for` loop's is" (fun () ->
      expect_one_diagnostic Fixtures.Infer.quantifier_over_a_float_range "types.not_iterable";
      expect_fine Fixtures.Infer.quantifier_over_a_character_range);
  Harness.test "a local of type Integer in a compiled body" (fun () ->
      expect_one_diagnostic Fixtures.Infer.integer_local_in_a_body "types.specification_only"
        ~says:"`big` has the type `Integer`");
  Harness.test "a local whose type holds Integer in a compiled body" (fun () ->
      expect_one_diagnostic Fixtures.Infer.list_of_integers_in_a_body "types.specification_only"
        ~says:"which holds `Integer`");
  Harness.test "a model in a compiled body" (fun () ->
      expect_one_diagnostic Fixtures.Infer.model_of_a_list_in_a_body "types.specification_only"
        ~says:"`Sequence[Int64]`");
  Harness.test "a range of a model is a Sequence with Integer bounds" (fun () ->
      let text = Fixtures.Infer.range_of_a_model in
      expect_fine text;
      expect_type text "items.model()[1..]" "Sequence[Int64]");
  Harness.test "a field of type Integer" (fun () ->
      expect_one_diagnostic Fixtures.Infer.box_of_an_integer "types.specification_only");
  Harness.test "a variant's field of type Sequence" (fun () ->
      expect_one_diagnostic Fixtures.Infer.variant_holding_a_sequence "types.specification_only");
  Harness.test "a constant of type Integer is read in specifications" (fun () ->
      expect_fine Fixtures.Infer.integer_constant_read_in_requires);
  Harness.test "a constant of type Integer in a compiled body" (fun () ->
      expect_one_diagnostic Fixtures.Infer.integer_constant_read_in_a_body
        "types.specification_only");
  Harness.test "a default of a function for specifications only is a specification" (fun () ->
      expect_fine Fixtures.Infer.specification_function_with_a_default);
  Harness.test "a loop clause of a compiled body reads a Sequence" (fun () ->
      expect_fine Fixtures.Infer.loop_invariant_reading_visited);
  Harness.test "a function for specifications only has a specification for a body" (fun () ->
      expect_fine Fixtures.Infer.specification_function_with_a_quantifier);
  Harness.test "a function for specifications only cannot hold a var" (fun () ->
      expect_one_diagnostic Fixtures.Infer.specification_function_with_a_var
        "types.not_in_specification");
  Harness.test "a theorem is not a value" (fun () ->
      expect_one_diagnostic Fixtures.Infer.theorem_as_a_value "types.not_a_value"
        ~says:"is a theorem, so it is not a value");
  Harness.test "a theorem call in a compiled body" (fun () ->
      expect_one_diagnostic Fixtures.Infer.body_calling_a_theorem "types.specification_only"
        ~says:"is a theorem");
  Harness.test "a theorem is called in a theorem and in a proof block" (fun () ->
      expect_fine Fixtures.Infer.theorem_called_by_a_theorem_and_a_proof_block);
  Harness.test "a call of a function for specifications only in a compiled body is reported once"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.body_calling_a_specification_function
        "types.specification_only" ~says:"`scaled` mentions `Integer`");
  Harness.test "a theorem cannot hold a loop" (fun () ->
      expect_one_diagnostic Fixtures.Infer.theorem_with_a_loop "types.not_in_specification");
  Harness.test "a proof block cannot hold a loop" (fun () ->
      expect_one_diagnostic Fixtures.Infer.proof_block_with_a_loop "types.not_in_specification");
  Harness.test "a proof block cannot assign to a variable of the program" (fun () ->
      expect_one_diagnostic Fixtures.Infer.proof_block_assigning_a_var "types.not_in_specification");
  Harness.test "a proof block cannot return" (fun () ->
      expect_one_diagnostic Fixtures.Infer.proof_block_returning "types.not_in_specification");
  Harness.test "unreachable is not part of a formula" (fun () ->
      expect_one_diagnostic Fixtures.Infer.requires_unreachable "types.not_in_specification");
  Harness.test "a quantifier's body in code cannot return" (fun () ->
      expect_one_diagnostic Fixtures.Infer.quantifier_returning_in_a_body
        "types.not_in_specification");
  Harness.test "a quantifier's body cannot pass an argument mut" (fun () ->
      expect_one_diagnostic Fixtures.Infer.quantifier_calling_grow "types.not_in_specification");
  Harness.test "a contract cannot pass an argument mut" (fun () ->
      expect_one_diagnostic Fixtures.Infer.requires_calling_bump "types.not_in_specification");
  Harness.test "a constant in a pattern needs structural equality" (fun () ->
      expect_one_diagnostic Fixtures.Infer.float_point_constant_arm "types.not_structural");
  Harness.test "a constant of a derived type of integers in a pattern" (fun () ->
      expect_fine Fixtures.Infer.integer_point_constant_arm);
  Harness.test "a loop's cost bound is checked" (fun () ->
      expect_one_diagnostic Fixtures.Infer.loop_cost_naming_a_missing_name "resolve.unknown_name");
  Harness.test "a function's measure of a sum type is a type error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.decreases_naming_a_chain "types.mismatch"
        ~says:"A `decreases` measure is an integer, not `Chain`." ~at:("chain\n", 1));
  Harness.test "a function's measure of a `Bool` is a type error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.decreases_naming_a_bool "types.mismatch"
        ~says:"A `decreases` measure is an integer, not `Bool`." ~at:("flag\n", 1));
  Harness.test "a loop's measure of a `String` is a type error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.loop_decreases_naming_a_string "types.mismatch"
        ~says:"A `decreases` measure is an integer, not `String`." ~at:("text\n", 1));
  Harness.test "a function's cost bound of a sum type is a type error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.cost_bounded_by_a_chain "types.mismatch"
        ~says:"A cost bound is an integer, not `Chain`." ~at:("chain)", 1));
  Harness.test "a loop's cost bound of a list is a type error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.loop_cost_bounded_by_a_list "types.mismatch"
        ~says:"A cost bound is an integer, not `List[Int64]`." ~at:("items)", 1));
  Harness.test "a measure or a cost bound is a fixed-width integer, an `Integer`, or a literal"
    (fun () ->
      let text = Fixtures.Infer.integer_measures_and_bounds in
      expect_fine text;
      expect_type text "1" "Integer");
  List.iter
    (fun (amount, fixture, says) ->
      Harness.test (Printf.sprintf "%s that is not an integer is a type error" amount) (fun () ->
          expect_one_diagnostic fixture "types.mismatch" ~says ~at:("\"steps\"", 1)))
    [
      ( "an argument of log",
        Fixtures.Infer.log_of_a_string,
        "An argument of `log` is an integer, not `String`." );
      ( "an argument of power",
        Fixtures.Infer.power_of_a_string,
        "An argument of `power` is an integer, not `String`." );
      ( "a potential",
        Fixtures.Infer.potential_of_a_string,
        "A `potential` is an integer, not `String`." );
    ];
  Harness.test "the arguments of log and power and a potential of integers check cleanly" (fun () ->
      expect_fine Fixtures.Infer.integer_logs_powers_and_potentials)

let identity = Fixtures.Infer.identity

let () =
  Harness.test "type arguments after a parenthesized name are read as after the name" (fun () ->
      expect_fine (identity ^ Fixtures.Infer.parenthesized_identity_called_with_a_type_argument);
      expect_one_diagnostic
        (identity ^ Fixtures.Infer.parenthesized_identity_of_an_integer_as_a_string)
        "types.mismatch");
  Harness.test "a parenthesized name with type arguments is a value of that function" (fun () ->
      expect_fine (identity ^ Fixtures.Infer.parenthesized_identity_with_a_type_argument));
  Harness.test "a trait's written arguments are the ones its call uses" (fun () ->
      let packages = Support.setup [ ("app.main", Fixtures.Infer.add_of_strings_given_integers) ] in
      if
        not
          (List.mem "types.unsatisfied_bound"
             (Support.list_codes (check packages (Support.parse_file "app.main"))))
      then Harness.fail "the written argument was ignored");
  Harness.test "a literal is the receiver of a trait method written in full" (fun () ->
      expect_fine Fixtures.Infer.add_of_two_literals_written_in_full);
  Harness.test "a generic parameter takes no type arguments" (fun () ->
      expect_one_diagnostic Fixtures.Infer.generic_parameter_given_type_arguments "types.arity");
  Harness.test "a trait's count argument is a value inferred from a call written in full" (fun () ->
      expect_fine Fixtures.Infer.full_call_of_a_trait_with_a_count);
  Harness.test "a bound with a count argument gives an associated type its methods" (fun () ->
      expect_fine Fixtures.Infer.method_of_an_associated_type_bounded_by_a_count);
  Harness.test "the one bound of a trait gives a call written in full the trait's argument"
    (fun () -> expect_fine Fixtures.Infer.full_call_of_a_trait_whose_argument_a_bound_fixes);
  Harness.test "a bound written directly and through a supertrait is one instance of the trait"
    (fun () ->
      expect_fine Fixtures.Infer.full_call_of_a_trait_bound_directly_and_through_a_supertrait);
  Harness.test "an impl does not give a call the trait's argument that its signature omits"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.method_of_a_trait_with_an_argument_its_signature_omits
        ~says:"does not determine the arguments of `Tagged`" "types.cannot_infer");
  Harness.test "an impl does not give a call the trait's count that its signature omits" (fun () ->
      expect_one_diagnostic Fixtures.Infer.method_of_a_trait_with_a_count_its_signature_omits
        ~says:"does not determine the arguments of `Sized`" "types.cannot_infer");
  Harness.test "a method call through two bounds of one trait does not choose the first" (fun () ->
      expect_one_diagnostic Fixtures.Infer.method_of_a_parameter_with_two_bounds_of_one_trait
        ~says:"does not determine the arguments of `Tagged`" "types.cannot_infer");
  Harness.test "a method call's argument chooses among two bounds of one trait" (fun () ->
      expect_fine Fixtures.Infer.method_of_a_parameter_whose_argument_chooses_a_bound);
  Harness.test "a generic parameter given type arguments is an error type, not the parameter"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.method_of_a_parameter_given_type_arguments "types.arity");
  Harness.test "`~` of a string is one error, and its value is not a string" (fun () ->
      expect_one_diagnostic Fixtures.Infer.complement_of_a_string "types.no_impl");
  Harness.test "a negated unsigned value is one error, and its value is not unsigned" (fun () ->
      expect_one_diagnostic Fixtures.Infer.negation_of_an_unsigned_parameter
        "types.negated_unsigned");
  Harness.test "a sum of strings is one error, and its value is not a string" (fun () ->
      expect_one_diagnostic Fixtures.Infer.string_addition_bound_to_a_let "types.string_addition"
        ~fixed:("let count = \"a\" + text", "let count = \"a${text}\"")
        ~left_after_fix:[ "types.mismatch" ]);
  Harness.test "a variant that its type does not have is one error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.unknown_variant_of_an_option "types.unknown_variant");
  Harness.test "a variant constructor of a record is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.variant_constructor_of_a_record "types.unknown_variant");
  Harness.test "a function value given too many arguments is one error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.function_value_called_with_two_arguments
        "types.too_many_arguments");
  Harness.test "a function value given too few arguments is a missing argument" (fun () ->
      expect_one_diagnostic Fixtures.Infer.function_value_called_with_no_arguments
        "types.missing_argument" ~says:"This function takes 1 argument, and 0 are given.");
  Harness.test "a labeled call through a function value has the error type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.function_value_called_with_a_label "types.unknown_label"
        ~fixed:("value: 1", "1") ~left_after_fix:[ "types.mismatch" ]);
  Harness.test "`identical` given one value has the error type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.identical_of_one_value_compared_with_an_integer
        "types.missing_argument");
  Harness.test "a member of a generic parameter that it does not have is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.member_of_an_unbounded_generic "types.unknown_member");
  Harness.test "a type with no fields is not its own value" (fun () ->
      expect_one_diagnostic Fixtures.Infer.marker_without_parentheses "types.not_a_value");
  Harness.test "`self` outside a method is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.self_in_a_function "types.not_a_value");
  Harness.test "`old` without its operand is an error" (fun () ->
      expect_one_diagnostic Fixtures.Infer.ensures_comparing_old_alone "types.not_a_value");
  Harness.test "a type argument that nothing decides is an error at its call" (fun () ->
      expect_one_diagnostic Fixtures.Infer.make_without_a_type_argument "types.cannot_infer"
        ~at:("make()", 1) ~says:"Nothing here determines `Value`, a type parameter of `make`.");
  Harness.test "a trait is not called" (fun () ->
      expect_one_diagnostic Fixtures.Infer.trait_called "types.not_callable");
  Harness.test "a generic function given type arguments, as a value, must meet its bounds"
    (fun () ->
      expect_one_diagnostic
        (point ^ Fixtures.Infer.need_of_a_point_as_a_value)
        "types.unsatisfied_bound");
  Harness.test "the scrutinee of an `is` is inferred before its pattern is checked" (fun () ->
      expect_fine Fixtures.Infer.is_on_a_span_division);
  Harness.test "a `for` over a cursor binds the values of its `next`" (fun () ->
      expect_fine Fixtures.Infer.loop_over_a_cursor);
  Harness.test "`Self` in the body of a method without `self` is the method's type" (fun () ->
      expect_fine Fixtures.Infer.self_type_in_a_static_method);
  Harness.test "a pattern that does not fit its type still gives its bindings a type" (fun () ->
      expect_one_diagnostic Fixtures.Infer.some_pattern_on_an_integer "types.unknown_variant");
  Harness.test "a `todo` that nothing decides keeps the hole type in the tables" (fun () ->
      let value, (result : Infer.checked) = locate_expression Fixtures.Infer.let_of_todo "todo" 1 in
      if result.tables.types.(value.id) <> Some Types.Hole then Harness.fail "not the hole type")

let shape = Fixtures.Infer.shape
let source = Fixtures.Infer.source

let () =
  Harness.test "a value built of a generic type must meet the type's bounds" (fun () ->
      expect_one_diagnostic (shape ^ Fixtures.Infer.holder_of_an_integer) "types.unsatisfied_bound");
  Harness.test "a value built of a generic type that meets its bounds is fine" (fun () ->
      expect_fine (shape ^ Fixtures.Infer.holder_of_a_square));
  Harness.test "a value built inside another must meet its type's bounds" (fun () ->
      expect_one_diagnostic
        (shape ^ Fixtures.Infer.some_of_a_holder_of_an_integer)
        "types.unsatisfied_bound");
  Harness.test "a variant built of a generic type must meet the type's bounds" (fun () ->
      expect_one_diagnostic
        (shape ^ Fixtures.Infer.full_slot_of_a_type_without_shape)
        "types.unsatisfied_bound");
  Harness.test "a generic type named in an expression must meet its bounds" (fun () ->
      expect_one_diagnostic
        (shape ^ Fixtures.Infer.slot_of_a_type_without_shape)
        "types.unsatisfied_bound");
  Harness.test "a statement reports a bound once, however many of its parts need it" (fun () ->
      expect_one_diagnostic
        (shape ^ Fixtures.Infer.area_of_a_holder_of_integers)
        "types.unsatisfied_bound");
  Harness.test "a method used as a value must meet its bounds" (fun () ->
      expect_one_diagnostic
        (shape ^ Fixtures.Infer.fits_of_a_point_as_a_value)
        "types.unsatisfied_bound");
  Harness.test "function types that count the calls of different capabilities are different types"
    (fun () ->
      let make_lists_source counted =
        "fn take(runs: List[(fn() uses Clock, Console cost calls(Console) <= 1)]) {}\n\n\
         fn f(runs: view List[(fn() uses Clock, Console cost calls(" ^ counted
        ^ ") <= 1)]) {\n  take(runs)\n}\n"
      in
      expect_fine (make_lists_source "Console");
      expect_one_diagnostic (make_lists_source "Clock") "types.mismatch";
      expect_one_diagnostic (make_lists_source "Console.print_line") "types.mismatch");
  Harness.test "the target of `calls` in a function type is a capability or one of its methods"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.calls_cost_of_a_type "types.not_a_capability";
      expect_one_diagnostic "fn f(run: (fn() uses Clock cost calls(Clock.later) <= 1)) {}\n"
        "types.unknown_member";
      expect_one_diagnostic "fn f(visit: fn(), run: (fn() cost calls(visit) <= 1)) {}\n"
        "types.not_a_capability");
  Harness.test "`.ensures` names a function parameter's postcondition in a specification" (fun () ->
      expect_fine
        "fn f(visit: fn(Int64) -> Int64, value: Int64) -> Int64\n\
        \  ensures visit.ensures(value, result)\n\
         {\n\
        \  visit(value)\n\
         }\n");
  Harness.test "`.ensures` follows a parameter of function type" (fun () ->
      expect_one_diagnostic "fn f(count: Int64) -> Bool\n  ensures count.ensures(1)\n{\n  todo\n}\n"
        "types.not_callable";
      expect_one_diagnostic
        "fn f(visit: fn(Int64) -> Int64) -> Bool {\n\
        \  let local: fn(Int64) -> Int64 = visit\n\
        \  proof {\n\
        \    assert local.ensures(1, 2)\n\
        \  }\n\
        \  true\n\
         }\n"
        "types.not_callable");
  Harness.test "`.ensures` appears only in specifications" (fun () ->
      expect_one_diagnostic "fn f(visit: fn(Int64) -> Int64) -> Bool {\n  visit.ensures(1, 2)\n}\n"
        "types.specification_only");
  Harness.test "`.ensures` takes each input, a mut input twice, and then the result" (fun () ->
      expect_one_diagnostic
        "fn f(visit: fn(Int64) -> Int64) -> Bool\n  ensures visit.ensures(1)\n{\n  todo\n}\n"
        "types.missing_argument";
      expect_one_diagnostic
        "fn f(visit: fn(mut Int64)) -> Bool\n  ensures visit.ensures(1, 2, 3)\n{\n  todo\n}\n"
        "types.too_many_arguments";
      expect_fine
        "fn f(visit: fn(mut Int64)) -> Bool\n  ensures visit.ensures(1, 2)\n{\n  todo\n}\n";
      expect_one_diagnostic
        "fn f(visit: fn(Int64) -> Bool) -> Bool\n  ensures visit.ensures(1, 2)\n{\n  todo\n}\n"
        "types.mismatch");
  Harness.test "`.ensures` takes its arguments by position" (fun () ->
      expect_one_diagnostic
        "fn f(visit: fn(Int64) -> Int64) -> Bool\n\
        \  ensures visit.ensures(value: 1, 2)\n\
         {\n\
        \  todo\n\
         }\n"
        "types.unknown_label");
  Harness.test "a callback type's ensures names its inputs and its result" (fun () ->
      expect_fine
        "fn f(choose: (fn(count: UInt64) -> UInt64 requires count > 0 ensures result < count)) -> \
         UInt64 {\n\
        \  choose(1)\n\
         }\n";
      expect_one_diagnostic
        "fn f(choose: (fn(count: UInt64) -> Bool ensures result == count)) -> Bool {\n\
        \  choose(1)\n\
         }\n"
        "types.mismatch");
  Harness.test
    "the target of `calls` in a clause is a function parameter, a capability, or a capability's \
     method" (fun () ->
      let make_clause_source counted =
        "type Point(x: Int64)\n\nfn f(count: Int64, visit: fn())\n  uses Clock\n  cost calls("
        ^ counted ^ ") <= 1\n{\n  todo\n}\n"
      in
      expect_fine (make_clause_source "visit");
      expect_fine (make_clause_source "Clock");
      expect_fine (make_clause_source "Clock.now");
      expect_one_diagnostic (make_clause_source "count") "types.not_callable";
      expect_one_diagnostic (make_clause_source "Point") "types.not_a_capability";
      expect_one_diagnostic (make_clause_source "Clock.later") "types.unknown_member");
  Harness.test "an associated type a bound fixes infers a type argument" (fun () ->
      expect_fine (source ^ Fixtures.Infer.first_of_a_source_with_a_fixed_item));
  Harness.test "an associated type a bound fixes must be the one the impl gives" (fun () ->
      expect_one_diagnostic
        (source ^ Fixtures.Infer.text_of_a_source_of_integers)
        "types.unsatisfied_bound")

let point = "type Point(x: Int64, y: Int64)\n\n"

let () =
  Harness.test "a constant is built from literals, operators on numbers, and other constants"
    (fun () -> expect_fine Fixtures.Infer.constants_of_literals_and_operators);
  Harness.test "a constant builds records, variants, and collections of constants" (fun () ->
      expect_fine (point ^ Fixtures.Infer.constants_of_records_variants_and_collections));
  Harness.test
    "a constant calls functions, methods, operators, indexing, quantifiers, and templates"
    (fun () -> expect_fine Fixtures.Infer.constants_calling_functions);
  Harness.test "a constant cannot branch" (fun () ->
      expect_one_diagnostic "let chosen: Int64 = if true { 1 } else { 2 }\n" "types.not_constant"
        ~says:"Move this into a function");
  Harness.test "a constant cannot hold a lambda" (fun () ->
      expect_one_diagnostic Fixtures.Infer.constant_calling_a_function_value "types.not_constant"
        ~at:("fn(value) { value }", 1));
  Harness.test
    "a constant's type cannot be or hold a function type, a handle, or state that tasks share"
    (fun () ->
      let reported =
        List.map
          (fun (diagnostic : Diagnostic.t) ->
            (Diagnostic.Code.name diagnostic.code, diagnostic.message))
          (check
             (Support.setup [ ("app.main", Fixtures.Infer.constants_that_are_not_data) ])
             (Support.parse_file "app.main"))
      in
      let expected =
        List.map
          (fun part ->
            ( "types.constant_not_data",
              "A constant is stored in the compiled program as data, so its type cannot be or hold "
              ^ part ^ "." ))
          [ "a function type"; "a function type"; "a handle"; "state that tasks share" ]
      in
      if reported <> expected then
        Harness.fail "reported [%s]" (String.concat "; " (List.map snd reported)));
  Harness.test "a constant's arithmetic must stay within its type" (fun () ->
      expect_one_diagnostic "let size: UInt64 = 0 - 1\n" "types.constant_overflow");
  Harness.test "each step of a constant's arithmetic must stay within its type" (fun () ->
      expect_one_diagnostic "let small: UInt8 = 200 + 100 - 100\n" "types.constant_overflow");
  Harness.test "a constant's arithmetic through another constant must stay within its type"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.constant_overflowing_through_another
        "types.constant_overflow");
  Harness.test "negating a constant's least value overflows" (fun () ->
      expect_one_diagnostic "let flipped: Int8 = -(-128)\n" "types.constant_overflow");
  Harness.test "a constant cannot divide by zero" (fun () ->
      expect_one_diagnostic "let nothing: Int64 = 5 / 0\n" "types.constant_overflow");
  Harness.test "a default must be a constant expression" (fun () ->
      expect_one_diagnostic Fixtures.Infer.default_calling_a_function "types.default_not_constant");
  Harness.test "a default cannot name a parameter" (fun () ->
      expect_one_diagnostic "fn f(count: Int64, twice: Int64 = count * 2) {}\n"
        "types.default_not_constant");
  Harness.test "a method's default must be a constant expression" (fun () ->
      expect_one_diagnostic
        (point ^ Fixtures.Infer.method_default_calling_a_function)
        "types.default_not_constant");
  Harness.test "a field's default must be a constant expression" (fun () ->
      expect_one_diagnostic Fixtures.Infer.field_default_calling_a_function
        "types.default_not_constant");
  Harness.test "a field's default's arithmetic must stay within its type" (fun () ->
      expect_one_diagnostic "type Settings(retries: UInt8 = 250 + 10)\n" "types.constant_overflow")

let () =
  let make_helper_source visibility =
    Printf.sprintf "%sfn half(value: Int64) -> Int64\n  cost time O(1)\n{\n  value - 1\n}\n\n"
      visibility
  in
  Harness.test "a public contract names only functions that other packages can call" (fun () ->
      let make_sorted_source visibility =
        Printf.sprintf
          "%sfn in_order(items: List[Int64]) -> Bool\n\
          \  cost time O(1)\n\
           {\n\
          \  items.length() < 2\n\
           }\n\n"
          visibility
      in
      let sort visibility clause =
        Printf.sprintf "%sfn sort(items: mut List[Int64])\n  %s\n{\n  todo\n}\n" visibility clause
      in
      expect_one_diagnostic
        (make_sorted_source "internal " ^ sort "public " "requires in_order(items)")
        "types.private_in_public";
      expect_one_diagnostic
        (make_sorted_source "" ^ sort "public " "requires in_order(items)")
        "types.private_in_public";
      expect_fine (make_sorted_source "public " ^ sort "public " "requires in_order(items)");
      expect_fine (make_sorted_source "internal " ^ sort "internal " "requires in_order(items)");
      expect_fine (make_sorted_source "" ^ sort "" "requires in_order(items)"));
  Harness.test "a public ensures may name a private function" (fun () ->
      expect_fine
        ("fn in_order(items: List[Int64]) -> Bool\n  cost time O(1)\n{\n  items.length() < 2\n}\n\n"
       ^ "public fn sort(items: mut List[Int64])\n\
         \  modifies items[..]\n\
         \  ensures in_order(items)\n\
          {\n\
         \  todo\n\
          }\n"));
  Harness.test "a public contract names only constants that other packages can name" (fun () ->
      let make_capped_source visibility =
        Printf.sprintf
          "%slet limit: Int64 = 10\n\n\
           public fn capped(value: Int64) -> Int64\n\
          \  requires value <= limit\n\
           {\n\
          \  todo\n\
           }\n"
          visibility
      in
      expect_one_diagnostic (make_capped_source "internal ") "types.private_in_public";
      expect_fine (make_capped_source "public "));
  Harness.test "a public trait's method names only public functions in its requires" (fun () ->
      let helper = Fixtures.Infer.helper in
      expect_one_diagnostic
        (helper ^ Fixtures.Infer.requires_naming_a_private_function)
        "types.private_in_public";
      expect_fine (helper ^ Fixtures.Infer.ensures_naming_a_private_function);
      let make_implemented_source visibility =
        helper
        ^ Printf.sprintf
            "public trait Sized {\n\
            \  fn size(self) -> Int64\n\
             }\n\n\
             %stype Box(side: Int64)\n\n\
             impl Sized for Box {\n\
            \  fn size(self) -> Int64\n\
            \    ensures small(result)\n\
            \  {\n\
            \    todo\n\
            \  }\n\
             }\n"
            visibility
      in
      expect_fine (make_implemented_source "public ");
      expect_fine (make_implemented_source "internal "));
  Harness.test "an impl whose trait names a private type has clauses no other package reads"
    (fun () ->
      let make_converting_source visibility =
        Fixtures.Infer.helper
        ^ Printf.sprintf
            "public trait Converts[Source] {\n\
            \  fn convert(source: Source) -> Self\n\
             }\n\n\
             %stype Secret(value: Int64)\n\n\
             public type Shown(value: Int64)\n\n\
             impl Converts[Secret] for Shown {\n\
            \  fn convert(source: Secret) -> Shown\n\
            \    cost time O(1)\n\
            \    requires small(source.value)\n\
            \  {\n\
            \    Shown(value: source.value)\n\
            \  }\n\
             }\n"
            visibility
      in
      expect_fine (make_converting_source "");
      expect_one_diagnostic (make_converting_source "public ") "types.private_in_public");
  Harness.test "a function's body can call a function that other packages cannot" (fun () ->
      expect_fine
        (make_helper_source "internal " ^ Fixtures.Infer.public_function_calling_a_private_one))

let () =
  let expect_not_constant ?says text ~at =
    expect_one_diagnostic text "types.condition_not_constant" ?says ~at
  in
  Harness.test "an assertion by evaluation takes calls, constants, quantifiers, and literals"
    (fun () -> expect_fine Fixtures.Infer.assertions_by_evaluation);
  Harness.test "an assertion by evaluation cannot name a local variable" (fun () ->
      expect_not_constant Fixtures.Infer.assertion_by_evaluation_naming_a_local
        ~says:"before any variable has a value" ~at:("chosen", 2));
  Harness.test "an assertion by evaluation cannot mention a type parameter" (fun () ->
      expect_not_constant Fixtures.Infer.assertion_by_evaluation_naming_a_type_parameter
        ~says:"cannot mention a type parameter" ~at:("[]", 1));
  Harness.test "an assertion by evaluation cannot branch" (fun () ->
      expect_not_constant Fixtures.Infer.assertion_by_evaluation_that_branches
        ~says:"Move this into a function"
        ~at:("if true { true } else { false }", 1));
  Harness.test "the condition of an assertion by evaluation is code, in a theorem too" (fun () ->
      expect_one_diagnostic Fixtures.Infer.assertion_by_evaluation_with_an_implication
        "types.specification_only")

let () =
  Harness.test "a bit-vector assertion names only integers and booleans" (fun () ->
      expect_one_diagnostic Fixtures.Infer.bit_vector_assertion_naming_a_list "types.not_bit_vector")

let () =
  let text = Fixtures.Infer.lambda_and_function_value_that_tick_through_a_bound in
  Harness.test
    "a lambda and a function value that tick through a bound have no time clause in their type"
    (fun () ->
      expect_fine text;
      expect_type text "fn(source) { mut source.tick() }" "fn(mut Inner) -> UInt64";
      expect_type text "advance" ~occurrence:2 "fn(mut Inner) -> UInt64");
  Harness.test "the time of a method that no bound of the type declares is an error" (fun () ->
      expect_one_diagnostic
        "trait Ticker {\n\
        \  fn tick(mut self) -> UInt64\n\
         }\n\n\
         fn f[Inner: Ticker](ticker: mut Inner) -> UInt64\n\
        \  cost time O(time(Inner.tock))\n\
         {\n\
        \  mut ticker.tick()\n\
         }\n"
        "types.unknown_member"
        ~says:"`Inner` has no method `tock`: no trait that bounds it declares one.");
  Harness.test "the time of a method with two overloads that mutate or take `self` is ambiguous"
    (fun () ->
      expect_one_diagnostic
        "trait Opened {\n\
        \  fn open(mut self) -> UInt64\n\n\
        \  fn open(own self) -> UInt64\n\
         }\n\n\
         fn f[Door: Opened](door: mut Door) -> UInt64\n\
        \  cost time O(time(Door.open))\n\
         {\n\
        \  mut door.open()\n\
         }\n"
        "types.ambiguous_method" ~says:"`Door` has more than one method `open`")

let () =
  let make_each_source ?(loop_clause = "") clause =
    Printf.sprintf
      "fn each(items: List[Int64], count: UInt64, visit: (fn(Int64) uses generic Granted))\n\
      \  uses generic Granted\n\
      \  %s\n\
       {\n\
      \  for item in items%s {\n\
      \    visit(item)\n\
      \  }\n\
       }\n"
      clause loop_clause
  in
  let expect_rejected ?fixed ?loop_clause clause code ~says =
    expect_one_diagnostic
      ?fixed:(Option.map (fun fixed -> (clause, fixed)) fixed)
      (make_each_source ?loop_clause clause)
      code ~says
  in
  Harness.test "a bound names the allocations of a callee in `O(...)` and in `<=`" (fun () ->
      expect_fine Fixtures.Infer.bounds_naming_the_allocations_of_a_callee);
  Harness.test "an exact bound does not name the allocations of a callback" (fun () ->
      expect_rejected "cost allocations == items.length() * allocations(visit)"
        "types.upper_bound_in_exact_bound"
        ~says:
          "`allocations(visit)` is an upper bound on one call, and a call may spend less, so an \
           exact amount that names it would be false for that call. State this bound with `<=` or \
           `O(...)`.");
  Harness.test "an exact bound does not name the allocated bytes of a callback" (fun () ->
      expect_rejected "cost allocated_bytes == allocated_bytes(visit)"
        "types.upper_bound_in_exact_bound"
        ~says:"`allocated_bytes(visit)` is an upper bound on one call");
  Harness.test "an exact bound does not name the time of a callback" (fun () ->
      expect_rejected "cost time == time(visit)" "types.upper_bound_in_exact_bound"
        ~says:"`time(visit)` is an upper bound on one call");
  Harness.test "a loop's exact bound does not name the allocations of a callback" (fun () ->
      expect_rejected "cost allocations <= items.length() * allocations(visit)"
        ~loop_clause:"\n    cost allocations == visited.length() * allocations(visit)\n "
        "types.upper_bound_in_exact_bound"
        ~says:"`allocations(visit)` is an upper bound on one call");
  Harness.test "an allocation bound does not name the time of a callback" (fun () ->
      expect_rejected "cost allocations <= time(visit)" "types.cost_of_other_resource"
        ~fixed:"cost allocations <= allocations(visit)"
        ~says:
          "`time(visit)` bounds the `time` of one call, not its `allocations`, which this clause \
           bounds. Write `allocations(visit)`.");
  Harness.test "a time bound does not name the allocations of a callback" (fun () ->
      expect_rejected "cost time O(allocations(visit))" "types.cost_of_other_resource"
        ~fixed:"cost time O(time(visit))"
        ~says:"`allocations(visit)` bounds the `allocations` of one call, not its `time`");
  Harness.test "an allocation bound does not name the allocated bytes of a callback" (fun () ->
      expect_rejected "cost allocations <= allocated_bytes(visit)" "types.cost_of_other_resource"
        ~fixed:"cost allocations <= allocations(visit)"
        ~says:"`allocated_bytes(visit)` bounds the `allocated_bytes` of one call");
  Harness.test "a bound on calls does not name the allocations of a callback" (fun () ->
      expect_rejected "cost calls(visit) <= allocations(visit)" "types.cost_of_other_resource"
        ~says:
          "`allocations(visit)` bounds the `allocations` of one call, not the calls it makes, \
           which this clause counts.");
  Harness.test "the allocations of a parameter that is not a function are an error" (fun () ->
      expect_rejected "cost allocations <= allocations(count)" "types.not_callable"
        ~says:
          "`allocations` takes a function parameter, as in `allocations(visit)`, or a method of a \
           bound, as in `allocations(Element.equal)`, and `count` is a `UInt64`.");
  Harness.test "the allocated bytes of a named function are an error" (fun () ->
      expect_rejected "cost allocated_bytes <= allocated_bytes(each)" "types.not_callable"
        ~says:"and `each` is neither.");
  Harness.test "the allocations of an expression are an error" (fun () ->
      expect_rejected "cost allocations <= allocations(count + 1)" "types.not_callable"
        ~says:"and its operand is neither.");
  Harness.test "the allocations of a method of a type that no bound names are an error" (fun () ->
      expect_rejected "cost allocations <= allocations(Int64.equal)" "types.not_callable"
        ~says:"and its operand is neither.");
  Harness.test "the time of a parameter that is not a function is an error" (fun () ->
      expect_rejected "cost time O(time(count))" "types.not_callable"
        ~says:"`time` takes a function parameter, as in `time(visit)`");
  Harness.test "the allocations of a method that no bound of the type declares are an error"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.cost_naming_allocations_of_an_undeclared_method
        "types.unknown_member"
        ~says:"`Element` has no method `compare`: no trait that bounds it declares one.");
  Harness.test "the allocations of a method with two overloads that take `self` are ambiguous"
    (fun () ->
      expect_one_diagnostic Fixtures.Infer.cost_naming_allocations_of_an_overloaded_method
        "types.ambiguous_method" ~says:"so `allocations` cannot tell which one is meant.");
  Harness.test "the time of a method that a bound restates names the one method" (fun () ->
      expect_fine Fixtures.Infer.cost_naming_time_of_a_restated_method)

let () =
  Harness.test "the body of an impl's method whose signature is not its trait's is not checked"
    (fun () ->
      expect_one_diagnostic
        Fixtures.Infer.meters_fed_to_an_impl_bounding_its_item_by_another_trait_argument
        "types.signature_mismatch" ~at:("feed", 2))

let () =
  Harness.test "a negated local of literals waits for the same decision" (fun () ->
      expect_fine Fixtures.Infer.negation_of_a_literal_local;
      expect_type Fixtures.Infer.negation_of_a_literal_local "-count" "Int64";
      expect_fine Fixtures.Infer.negation_of_a_float_literal_local;
      expect_type Fixtures.Infer.negation_of_a_float_literal_local "-ratio" "Float64");
  Harness.test "a product of a float literal local takes the type a later annotation decides"
    (fun () ->
      let text = Fixtures.Infer.float32_let_of_a_product_of_a_literal_local in
      expect_fine text;
      expect_type text "0.5" "Float32";
      expect_type text "2.0" "Float32");
  Harness.test "a negated float literal local takes the type a later annotation decides" (fun () ->
      let text = Fixtures.Infer.float32_let_of_a_negated_literal_local in
      expect_fine text;
      expect_type text "0.5" "Float32");
  Harness.test "a literal under a sealed bound that fixes an associated type takes its default type"
    (fun () ->
      let float_text = Fixtures.Infer.float_literal_passed_where_floating_point_fixes_its_bits in
      expect_fine float_text;
      expect_type float_text "1.5" "Float64";
      let integer_text =
        Fixtures.Infer.integer_literal_passed_where_signed_integer_fixes_its_unsigned
      in
      expect_fine integer_text;
      expect_type integer_text "-5" "Int64");
  Harness.test "a loop over a range of literals in a local lets its body decide them" (fun () ->
      expect_fine Fixtures.Infer.loop_over_a_literal_range_local;
      expect_type Fixtures.Infer.loop_over_a_literal_range_local "range" ~occurrence:2
        "Range[UInt8]");
  Harness.test "a loop over a reversed range of literals" (fun () ->
      expect_fine Fixtures.Infer.loop_over_a_reversed_literal_range)

let () =
  let declare literal = Printf.sprintf "fn f() {\n  let _: Float64 = %s\n}\n" literal in
  Harness.test "a float literal far past every float is out of range, whatever its exponent"
    (fun () ->
      List.iter
        (fun literal -> expect_one_diagnostic (declare literal) "types.literal_out_of_range")
        [
          "1.8e308";
          "1e10000000000";
          "1e999999999999";
          "1e4611686018427387903";
          "1e9999999999999999999";
        ]);
  Harness.test "a float literal far below every float rounds to zero, whatever its exponent"
    (fun () ->
      List.iter
        (fun literal -> expect_no_diagnostics [ ("app.main", declare literal) ])
        [ "2e-324"; "1e-99999999999"; "-1e-9999999999999999999" ])

let () =
  Harness.test "the shorthand of with names its value, whatever the name resolves to" (fun () ->
      expect_one_diagnostic Fixtures.Infer.record_update_shorthand_naming_a_function
        "types.mismatch");
  Harness.test "with names fields as a construction does" (fun () ->
      expect_one_diagnostic Fixtures.Infer.record_update_of_an_unknown_field "types.unknown_label"
        ~fixed:("nme", "name") ~says:"`Config` has no field `nme`.");
  Harness.test "with updates a field once" (fun () ->
      expect_one_diagnostic Fixtures.Infer.record_update_of_a_field_twice "types.repeated_argument";
      expect_one_diagnostic Fixtures.Infer.record_update_of_a_field_and_its_part
        "types.repeated_argument")

let () =
  Harness.test "a clause is checked with its condition's bounds" (fun () ->
      expect_fine Fixtures.Infer.clause_calling_a_method_of_its_condition);
  Harness.test "a clause without a condition has only the definition's bounds" (fun () ->
      match
        Support.list_codes
          (check
             (Support.setup
                [ ("app.main", Fixtures.Infer.clause_calling_a_method_without_its_condition) ])
             (Support.parse_file "app.main"))
      with
      | [] -> Harness.fail "no diagnostics"
      | codes ->
          if List.exists (fun code -> code <> "types.unknown_member") codes then
            Harness.fail "%s" (String.concat ", " codes));
  Harness.test "a condition names a type parameter or Self" (fun () ->
      expect_one_diagnostic Fixtures.Infer.condition_on_a_concrete_type "types.decided_condition"
        ~says:"`Int64` is neither");
  Harness.test "a condition names an associated type through a type parameter" (fun () ->
      expect_one_diagnostic Fixtures.Infer.condition_on_an_associated_type "types.decided_condition"
        ~says:"Give it a type parameter, as in `[Element, Items: Cursor[Element = Element]]`";
      expect_fine Fixtures.Infer.condition_on_a_parameter_bound_to_an_associated_type);
  Harness.test "a clause whose condition never holds is rejected" (fun () ->
      expect_one_diagnostic Fixtures.Infer.clause_whose_condition_never_holds
        "types.decided_condition" ~says:"never holds");
  Harness.test "a bound goal of a clause is decided with the clause's condition" (fun () ->
      expect_fine Fixtures.Infer.clause_whose_bound_goal_needs_its_condition);
  Harness.test "a bound goal of the body is decided without a loop clause's condition" (fun () ->
      expect_one_diagnostic Fixtures.Infer.loop_clause_condition_after_a_pending_bound_goal
        "types.unsatisfied_bound" ~says:"`Item: Convert[Int64]`")
