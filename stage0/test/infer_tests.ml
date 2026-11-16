let check packages =
  Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ] (Support.database packages)

let one_diagnostic = Support.one_diagnostic ~check
let no_diagnostics = Support.no_diagnostics ~check
let fine text = no_diagnostics [ ("app::main", text) ]

let expression_at text written occurrence =
  let packages = Support.setup [ ("app::main", text) ] in
  let file = Support.file_of "app::main" in
  let offset = Support.find_occurrence ~sub:written ~occurrence text in
  let actual =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.make_key declaration in
        match
          ( (Support.names packages key.module_.package).definition key,
            (Support.names packages key.module_.package).spans key,
            (Support.names packages key.module_.package).place key,
            Database.read_checked_body (Support.database packages) key )
        with
        | definition, spans, { base; _ }, Some result ->
            let best = ref None in
            let length (value : Syntax.expression) =
              let span : Source.Definition_span.t = spans.(value.id) in
              span.stop - span.start
            in
            let exact value = length value = String.length written in
            let rec visit (value : Syntax.expression) =
              (if base + spans.(value.id).start = offset then
                 match !best with
                 | Some (other : Syntax.expression)
                   when exact other || ((not (exact value)) && length other <= length value) ->
                     ()
                 | _ -> best := Some value);
              Syntax_walk.visit_children visit value
            in
            Syntax_walk.visit_definition visit definition;
            Option.map (fun value -> (value, result)) !best
        | _ -> None)
      ((Support.names packages file.module_.package).declarations_in file)
  in
  match actual with
  | Some actual -> actual
  | None -> failwith (Printf.sprintf "no expression at %S" written)

let has_integer text value =
  List.exists
    (fun (node : Core.expression) ->
      match node.kind with Integer actual -> Z.equal actual (Z.of_int value) | _ -> false)
    (Support.first_core_nodes text).expressions

let core_at text written occurrence =
  let value, (result : Infer.checked) = expression_at text written occurrence in
  let form = result.form in
  let nodes = ref [] in
  Core_walk.walk_definition
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) -> if node.origin = value.id then nodes := node :: !nodes);
    }
    form.definition;
  List.rev !nodes

let core_call_at text written occurrence =
  match
    List.find_map
      (fun (node : Core.expression) ->
        match node.kind with Call call -> Some (call, node.type_) | _ -> None)
      (core_at text written occurrence)
  with
  | Some call -> call
  | None -> failwith (Printf.sprintf "%S is not a call" written)

let is_view : Core.argument -> bool = function
  | Passed
      {
        value =
          Value
            { kind = Call { callee = Function { path = Method { name = "slice"; _ }; _ }; _ }; _ };
        _;
      } ->
      true
  | _ -> false

let has_type text written ?(occurrence = 1) expected =
  let value, (result : Infer.checked) = expression_at text written occurrence in
  match result.tables.types.(value.id) with
  | Some type_ ->
      if Types.show type_ <> expected then
        Harness.fail "`%s` has type %s, not %s" written (Types.show type_) expected
  | None -> Harness.fail "`%s` has no type" written

let () =
  Harness.test "a part with a syntax error is not checked, and the other definitions are" (fun () ->
      let packages =
        Support.setup
          [
            ( "app::main",
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
      let file = Support.file_of "app::main" in
      if List.length (Support.parse_errors packages file) <> 2 then
        Harness.fail "expected two syntax errors";
      match Support.codes (check packages file) with
      | [ "types.mismatch" ] -> ()
      | reported -> Harness.fail "reported [%s]" (String.concat "; " reported));
  Harness.test "a literal takes the type of the other operand" (fun () ->
      has_type Fixtures.Infer.uint8_plus_a_literal "1" "UInt8");
  Harness.test "a literal nothing decides is an Int64" (fun () ->
      has_type Fixtures.Infer.var_of_a_literal "0" "Int64");
  Harness.test "a literal takes the expected type" (fun () ->
      has_type Fixtures.Infer.uint8_let_of_a_literal "3" "UInt8");
  Harness.test "a literal multiplied by a type that is not an integer is an Int64" (fun () ->
      fine Fixtures.Infer.literal_times_a_duration);
  Harness.test "an expression of literals waits for the same decision" (fun () ->
      has_type Fixtures.Infer.uint16_plus_a_product_of_literals "60" "UInt16");
  Harness.test "a literal that does not fit its type is an error" (fun () ->
      one_diagnostic Fixtures.Infer.uint8_let_of_300 "types.literal_out_of_range");
  Harness.test "a literal of a type an integer trait bounds is an integer of that type" (fun () ->
      fine Fixtures.Infer.signed_integer_compared_with_minus_one);
  Harness.test "a literal of a type an integer trait bounds must fit every type that implements it"
    (fun () ->
      one_diagnostic Fixtures.Infer.signed_integer_compared_with_200 "types.literal_out_of_range";
      one_diagnostic Fixtures.Infer.fixed_width_integer_compared_with_128
        "types.literal_out_of_range");
  Harness.test "a literal of a type UnsignedInteger bounds cannot be negated" (fun () ->
      one_diagnostic Fixtures.Infer.unsigned_integer_compared_with_minus_one
        "types.negated_unsigned");
  Harness.test "a negated literal is checked after the negation" (fun () ->
      fine Fixtures.Infer.int8_let_of_minus_128);
  Harness.test "an integer literal where a float is expected is an error with a fix" (fun () ->
      one_diagnostic Fixtures.Infer.integer_literal_as_a_float "types.integer_for_float"
        ~fixed:Fixtures.Infer.integer_literal_as_a_float_fixed);
  Harness.test "a literal shift amount is a UInt64" (fun () ->
      has_type Fixtures.Infer.shift_by_a_literal "3" ~occurrence:3 "UInt64");
  Harness.test "a loop variable's literal type is decided by the loop's body" (fun () ->
      has_type Fixtures.Infer.range_loop_index_bound_to_a_uint8 "0" "UInt8");
  Harness.test "a local's literal type is decided by a later statement" (fun () ->
      let text = Fixtures.Infer.literal_decided_by_a_later_comparison in
      has_type text "10" "UInt8";
      has_type text "2" "UInt8";
      has_type text "0.5" "Float32";
      fine text);
  Harness.test "the literal type a local leaves undecided ends with the local's scope" (fun () ->
      let text = Fixtures.Infer.range_loop_bound_to_a_uint8 in
      has_type text "0" "UInt8";
      has_type text "5" "UInt64");
  Harness.test "a specification converts a local whose literal type is undecided to Integer"
    (fun () ->
      let text = Fixtures.Infer.requires_of_an_undecided_local in
      has_type text "0" "UInt8";
      fine text);
  Harness.test "a pattern of a local's undecided literal type is checked once it is decided"
    (fun () ->
      let text = Fixtures.Infer.match_on_an_undecided_literal in
      has_type text "3" "UInt8";
      fine text);
  Harness.test "a local in a block is decided after the block" (fun () ->
      has_type Fixtures.Infer.literal_decided_after_its_block "5" "UInt16");
  Harness.test "a local whose literal does not fit the type a later statement decides is an error"
    (fun () ->
      one_diagnostic Fixtures.Infer.local_of_300_bound_to_a_uint8 "types.literal_out_of_range");
  Harness.test "a loop's annotation decides the literals of its range" (fun () ->
      let text = Fixtures.Infer.range_loop_annotated_uint8 in
      has_type text "10" "UInt8";
      fine text);
  Harness.test "a loop's annotation is the type of a destructured element" (fun () ->
      fine Fixtures.Infer.loop_annotating_a_destructured_element);
  Harness.test "a loop's annotation must be its element type" (fun () ->
      one_diagnostic Fixtures.Infer.loop_over_uint16s_annotated_uint8 "types.mismatch"
        ~says:"The elements of this loop are `UInt16`, not `UInt8`.");
  Harness.test
    "a loop variable given its default type by a method call has a fix that annotates the loop"
    (fun () ->
      one_diagnostic Fixtures.Infer.range_loop_wrapping_added_then_bound_to_a_uint8 "types.mismatch"
        ~fixed:Fixtures.Infer.range_loop_wrapping_added_then_bound_to_a_uint8_fixed);
  Harness.test "a local used as two types is one error, at the second use" (fun () ->
      one_diagnostic Fixtures.Infer.local_bound_to_two_types "types.mismatch"
        ~says:"An earlier statement decided that the type of `base` is `UInt8`.");
  Harness.test "a local given its default type by a method call is one error, with a fix" (fun () ->
      one_diagnostic Fixtures.Infer.local_wrapping_added_then_bound_to_a_uint8 "types.mismatch"
        ~says:"`base` took its default type, `Int64`, at an earlier method call."
        ~fixed:Fixtures.Infer.local_wrapping_added_then_bound_to_a_uint8_fixed)

let () =
  Harness.test "comparing integer types that differ is an error with a fix that converts" (fun () ->
      one_diagnostic Fixtures.Infer.comparison_of_uint64_and_uint32 "types.mismatched_integers"
        ~fixed:Fixtures.Infer.comparison_of_uint64_and_uint32_fixed);
  Harness.test "+ on strings is an error with a fix to interpolation" (fun () ->
      one_diagnostic Fixtures.Infer.string_plus_a_string "types.string_addition"
        ~fixed:Fixtures.Infer.string_plus_a_string_fixed);
  Harness.test "an operator chooses the impl by both operands" (fun () ->
      let text = Fixtures.Infer.additions_of_meters_and_integers in
      match core_call_at text "length + extra" 1 with
      | { callee = Trait_method { evidence = Impl { impl; _ }; name = "add"; _ }; _ }, _ -> (
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
          match core_call_at text written 1 with
          | { callee = Trait_method { name = "compare"; evidence = Bound; _ }; _ }, result ->
              if Types.show result <> "Ordering" then
                Harness.fail "`%s` calls a `compare` that gives `%s`" written (Types.show result)
          | _ -> Harness.fail "`%s` is another call" written)
        [ "first < second"; "second < third"; "first < third" ]);
  Harness.test "an operand can be the result of an operator's method" (fun () ->
      fine Fixtures.Infer.sum_with_a_multiply_call);
  Harness.test "a type without the operator's trait is an error" (fun () ->
      one_diagnostic Fixtures.Infer.sum_of_points "types.no_impl")

let () =
  Harness.test "a call to a function whose signature fails a check reports nothing" (fun () ->
      one_diagnostic Fixtures.Infer.call_of_a_public_function_taking_a_private_type
        "types.private_in_public");
  Harness.test "a call to a function whose parameter type is unknown reports nothing" (fun () ->
      one_diagnostic Fixtures.Infer.call_of_a_function_with_a_misspelled_parameter_type
        "resolve.unknown_name")

let () =
  let functions = "fn copy_file(source: Int64, destination: Int64) {}\n\n" in
  Harness.test "an argument after the first needs a label, with a fix that adds it" (fun () ->
      one_diagnostic
        (functions ^ Fixtures.Infer.copy_file_with_an_unlabeled_second_argument)
        "types.missing_label"
        ~fixed:(functions ^ Fixtures.Infer.copy_file_with_a_labeled_destination));
  Harness.test "a variable with the parameter's name needs no label" (fun () ->
      fine (functions ^ Fixtures.Infer.copy_file_with_arguments_named_like_parameters));
  Harness.test "arguments out of order are an error with a fix that reorders them" (fun () ->
      one_diagnostic
        (functions ^ Fixtures.Infer.copy_file_with_swapped_arguments)
        "types.out_of_order"
        ~fixed:(functions ^ Fixtures.Infer.copy_file_with_arguments_named_like_parameters));
  Harness.test "a missing argument is an error" (fun () ->
      one_diagnostic
        (functions ^ Fixtures.Infer.copy_file_with_one_argument)
        "types.missing_argument");
  Harness.test "an argument for a parameter with a default can be omitted" (fun () ->
      let text = Fixtures.Infer.connect_without_its_port in
      match core_call_at text "connect(1)" 1 with
      | { arguments = [ Passed _; Default ]; _ }, _ -> ()
      | _ -> Harness.fail "the omitted default is not recorded");
  Harness.test "a String passed where a StringSlice is expected is viewed" (fun () ->
      let text = Fixtures.Infer.greet_of_a_string in
      match core_call_at text "greet(name)" 1 with
      | { arguments = [ argument ]; _ }, _ when is_view argument -> ()
      | _ -> Harness.fail "no conversion recorded");
  Harness.test "a capability's method views a String argument too" (fun () ->
      let text = Fixtures.Infer.print_line_of_a_string in
      match core_call_at text "Console.print_line(name)" 1 with
      | { arguments = [ argument ]; _ }, _ when is_view argument -> ()
      | _ -> Harness.fail "no conversion recorded");
  Harness.test "a string literal is a StringSlice where one is expected, and a String elsewhere"
    (fun () ->
      let text = Fixtures.Infer.string_literals_kept_and_printed in
      has_type text "\"kept\"" "String";
      has_type text "\"hello\"" "StringSlice";
      match core_call_at text "Console.print_line(\"hello\")" 1 with
      | { arguments = [ argument ]; _ }, _ when not (is_view argument) -> ()
      | _ -> Harness.fail "the literal is converted to a view");
  Harness.test "an unknown label is an error with a fix to the closest" (fun () ->
      one_diagnostic
        (functions ^ Fixtures.Infer.misspelled_label)
        "types.unknown_label"
        ~fixed:(functions ^ Fixtures.Infer.copy_file_with_a_destination_label));
  Harness.test "a record is built with labels in any order" (fun () ->
      fine Fixtures.Infer.point_built_with_labels_reversed);
  Harness.test "a record with one field takes a bare value" (fun () ->
      fine Fixtures.Infer.user_id_of_a_bare_value);
  Harness.test "a generic function's type arguments are solved from its arguments" (fun () ->
      has_type Fixtures.Infer.wrap_of_an_integer "wrap(5)" "Option[Int64]")

let () =
  Harness.test "a mut parameter needs mut at the call, with a fix that adds it" (fun () ->
      one_diagnostic Fixtures.Infer.bump_without_mut "types.missing_mode"
        ~fixed:Fixtures.Infer.bump_without_mut_fixed);
  Harness.test "an own parameter needs own for a place that does not copy implicitly" (fun () ->
      one_diagnostic Fixtures.Infer.own_list_passed_without_own "types.missing_mode"
        ~fixed:Fixtures.Infer.own_list_passed_without_own_fixed);
  Harness.test "own on a place that copies implicitly is redundant" (fun () ->
      one_diagnostic Fixtures.Infer.own_before_an_integer "types.redundant_mode"
        ~fixed:Fixtures.Infer.own_before_an_integer_fixed);
  Harness.test "a mut receiver chooses the method's mut overload" (fun () ->
      fine Fixtures.Infer.mut_push_onto_a_var_list);
  Harness.test
    "a place calling a method that takes mut self needs the mode keyword, with a fix that adds it"
    (fun () ->
      one_diagnostic Fixtures.Infer.push_without_mut "types.missing_mode"
        ~fixed:Fixtures.Infer.push_without_mut_fixed)

let () =
  Harness.test "a statement's value must be used, with a fix that discards it" (fun () ->
      one_diagnostic Fixtures.Infer.unused_length "types.unused_value"
        ~fixed:Fixtures.Infer.unused_length_fixed);
  Harness.test "the default of a parameter of a view type can be an owned value" (fun () ->
      fine Fixtures.Infer.view_parameters_with_owned_defaults);
  Harness.test "`time` of a method that no bound of the type parameter declares is an error"
    (fun () ->
      one_diagnostic Fixtures.Infer.cost_naming_time_of_an_undeclared_method "types.unknown_member");
  Harness.test "a let cannot be assigned" (fun () ->
      one_diagnostic Fixtures.Infer.assignment_to_a_let "types.not_assignable");
  List.iter
    (fun (construct, text) ->
      Harness.test (construct ^ " cannot be passed `mut`") (fun () ->
          one_diagnostic text "types.wrong_mode"))
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
    (fun () -> fine Fixtures.Infer.mut_arguments_of_every_kind);
  Harness.test "the variable of a loop over elements lent `mut` can be passed `mut`" (fun () ->
      fine Fixtures.Infer.mut_loop_over_rows);
  Harness.test "a var can be assigned" (fun () -> fine Fixtures.Infer.assignment_to_a_var);
  Harness.test "an empty list with nothing to decide its elements is an error" (fun () ->
      one_diagnostic Fixtures.Infer.empty_list_without_a_type "types.cannot_infer");
  Harness.test "an empty list takes its elements' type from the annotation" (fun () ->
      fine Fixtures.Infer.empty_list_of_strings);
  Harness.test "a body's value must have the result type" (fun () ->
      one_diagnostic Fixtures.Infer.body_returning_bool_as_int64 "types.mismatch");
  Harness.test "a body may end with a let whose value never finishes" (fun () ->
      fine Fixtures.Infer.let_of_a_returning_if_at_the_end);
  Harness.test "an arm of type Never does not contribute to the type of the match" (fun () ->
      fine Fixtures.Infer.match_with_a_returning_arm);
  Harness.test "? needs the function's error type" (fun () ->
      one_diagnostic Fixtures.Infer.question_mark_on_a_result_of_another_error "types.wrong_try");
  Harness.test "? on a matching Result gives its value" (fun () ->
      has_type Fixtures.Infer.question_mark_on_a_result_of_the_same_error "parse()?" "Int64");
  Harness.test "if without else has type Unit" (fun () ->
      has_type Fixtures.Infer.let_of_an_if_without_else "if ready { }" "Unit")

let () =
  Harness.test "an unknown field is an error with a fix to the closest" (fun () ->
      one_diagnostic Fixtures.Infer.misspelled_field "types.unknown_member");
  Harness.test "a method from a trait needs no import" (fun () ->
      fine Fixtures.Infer.copy_of_a_list);
  Harness.test "a law's proof names the law's parameters, which have the proof's type for Self"
    (fun () -> fine Fixtures.Infer.law_proof_reading_its_parameters);
  Harness.test "a law's proof for a generic impl is checked under its own generic parameters"
    (fun () -> fine Fixtures.Infer.law_proof_for_a_generic_box);
  Harness.test "a law's proof names no parameter of another law" (fun () ->
      one_diagnostic Fixtures.Infer.law_proof_naming_another_laws_parameter "resolve.unknown_name");
  Harness.test "a law's proof cannot assign to a parameter of the law" (fun () ->
      one_diagnostic Fixtures.Infer.law_proof_assigning_a_parameter "types.not_in_specification");
  Harness.test "a variant with one field is a function" (fun () ->
      fine Fixtures.Infer.circle_as_a_function);
  Harness.test "a variant with several fields is not a function, because fields have no order"
    (fun () -> one_diagnostic Fixtures.Infer.rectangle_as_a_function "types.not_a_value");
  Harness.test "a lending method is not a function value, because a function type cannot lend"
    (fun () ->
      one_diagnostic Fixtures.Infer.lending_method_as_a_value "types.not_a_value"
        ~says:"a function value cannot lend");
  Harness.test "a variant is looked up under its type" (fun () ->
      fine Fixtures.Infer.shape_variants_built);
  Harness.test "a constant under a type is read by name" (fun () ->
      has_type Fixtures.Infer.uint8_maximum "UInt8.maximum" "UInt8");
  Harness.test "a trait method through a type chooses the impl by the argument" (fun () ->
      fine Fixtures.Infer.int64_from_an_int32)

let () =
  Harness.test "an unknown variant in a pattern is an error" (fun () ->
      one_diagnostic Fixtures.Infer.misspelled_variant_arm "types.unknown_variant");
  Harness.test "a bare name in a record pattern binds the field it names" (fun () ->
      fine Fixtures.Infer.let_binding_both_fields_of_a_pair);
  Harness.test "a bare name that names no field of a record with several is an error" (fun () ->
      one_diagnostic Fixtures.Infer.record_pattern_with_a_name_of_no_field "types.unknown_member")

let () =
  Harness.test "a lambda with nothing to give its parameter types is an error" (fun () ->
      one_diagnostic Fixtures.Infer.lambda_bound_without_a_type "types.lambda_needs_type");
  Harness.test "a lambda takes its parameter types from the function type it is passed as"
    (fun () -> has_type Fixtures.Infer.lambda_incrementing_items "item + 1" "Int64");
  Harness.test "concurrent code needs `Tasks`, in a block and in a loop" (fun () ->
      one_diagnostic Fixtures.Infer.concurrent_block_without_tasks "capabilities.not_available";
      one_diagnostic Fixtures.Infer.concurrent_loop_without_tasks "capabilities.not_available");
  Harness.test "a branch of a concurrent block uses the capabilities around the block" (fun () ->
      fine Fixtures.Infer.concurrent_branch_calling_tick);
  (let sessions = Fixtures.Infer.sessions in
   Harness.test
     "a capability implemented by a monitor has no method with a callback that uses a capability"
     (fun () ->
       one_diagnostic
         (sessions ^ Fixtures.Infer.monitor_table_with_a_callback)
         "capabilities.callback_may_deadlock");
   Harness.test "an implementation is not a monitor if the body of its `provide` cannot use `Tasks`"
     (fun () -> fine (sessions ^ Fixtures.Infer.table_provided_without_tasks));
   let tally = Fixtures.Infer.tally in
   Harness.test "a monitor needs `Tasks` at its `provide`, not only in a nested one" (fun () ->
       one_diagnostic
         (tally ^ Fixtures.Infer.tally_provided_without_tasks)
         "capabilities.monitor_needs_tasks");
   Harness.test
     "a monitor can lock through `Tasks` of its `provide`, an enclosing one, or a capability \
      parameter" (fun () -> fine (tally ^ Fixtures.Infer.monitors_provided_with_and_without_tasks)));
  Harness.test "an assignment through an index of a map takes the key as an owned value" (fun () ->
      fine Fixtures.Infer.map_assignments_with_owned_keys;
      one_diagnostic Fixtures.Infer.map_assignment_with_a_viewed_key "types.missing_mode";
      one_diagnostic Fixtures.Infer.map_assignment_to_a_read_only_map "types.not_assignable");
  Harness.test "`final(result)` is a lending method's part as the caller left it" (fun () ->
      fine Fixtures.Infer.lending_part_ensuring_final_of_result;
      one_diagnostic ~says:"`final(result)`" Fixtures.Infer.lending_part_ensuring_final_of_a_field
        "types.not_callable");
  Harness.test "`final` and `visited` are names only where they have a meaning" (fun () ->
      one_diagnostic Fixtures.Infer.ensures_naming_final_outside_a_lend "resolve.unknown_name";
      one_diagnostic Fixtures.Infer.while_invariant_naming_visited "resolve.unknown_name");
  (let readings = Fixtures.Infer.readings in
   let assign = Fixtures.Infer.readings_assign in
   Harness.test "an element of a type that implements `Index` alone is read" (fun () ->
       fine (readings ^ Fixtures.Infer.elements_of_readings_read));
   Harness.test "an element of a type that implements `Index` alone is not assigned" (fun () ->
       one_diagnostic ~says:"and not `IndexMut`"
         (readings ^ Fixtures.Infer.assignment_through_an_index_of_readings)
         "types.not_assignable");
   Harness.test "an element of a type that implements `Index` alone is not passed `mut`" (fun () ->
       one_diagnostic ~says:"and not `IndexMut`"
         (readings ^ Fixtures.Infer.element_of_readings_passed_mut)
         "types.wrong_mode");
   Harness.test "an assignment through an index calls `assign` without `IndexMut`" (fun () ->
       fine (readings ^ assign ^ Fixtures.Infer.assignment_through_an_index_of_readings));
   Harness.test "a compound assignment through an index needs `IndexMut`" (fun () ->
       one_diagnostic ~says:"Assign the whole element with `=`."
         (readings ^ assign ^ Fixtures.Infer.compound_assignment_through_an_index_of_readings)
         "types.not_assignable"));
  (let keep = Fixtures.Infer.keep in
   Harness.test "a type that holds no view is Storable" (fun () ->
       fine (keep ^ Fixtures.Infer.values_without_views_kept));
   Harness.test "an any type is Storable when its trait requires Storable" (fun () ->
       fine (keep ^ Fixtures.Infer.any_job_kept));
   Harness.test "a trait that requires Storable cannot be implemented for a view type" (fun () ->
       one_diagnostic (keep ^ Fixtures.Infer.job_impl_for_labeled) "types.missing_required_impl");
   List.iter
     (fun (name, body) ->
       Harness.test name (fun () -> one_diagnostic (keep ^ body) "types.unsatisfied_bound"))
     [
       ("a slice is not Storable", Fixtures.Infer.slice_kept);
       ("a record that holds a slice is not Storable", Fixtures.Infer.labeled_slice_kept);
       ("a generic type is not Storable where its argument is not", Fixtures.Infer.boxed_slice_kept);
       ("a function type is not Storable", Fixtures.Infer.function_kept);
       ( "an any type is not Storable when its trait does not require it",
         Fixtures.Infer.any_task_kept );
       ( "a type parameter is Storable only when it is bounded",
         Fixtures.Infer.unbounded_element_kept );
     ];
   Harness.test "no impl of Storable can be written" (fun () ->
       one_diagnostic (keep ^ "impl Storable for Labeled {}\n") "types.implements_built_in"));
  Harness.test "the body of a concurrent block gets its types" (fun () ->
      has_type Fixtures.Infer.concurrent_block_calling_g "2" "UInt16");
  Harness.test "a lambda's captures are the outer locals it reads" (fun () ->
      let text = Fixtures.Infer.lambda_adding_a_captured_step in
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match node.kind with Lambda { captures; _ } -> Some captures | _ -> None)
          (Support.first_core_nodes text).expressions
      with
      | [ [ _ ] ] -> ()
      | [ actual ] -> Harness.fail "%d captures" (List.length actual)
      | actual -> Harness.fail "%d lambdas" (List.length actual))

let () =
  Harness.test "an interpolated value must implement Display" (fun () ->
      one_diagnostic Fixtures.Infer.interpolation_of_a_point "types.no_impl");
  Harness.test "an array literal must have its type's length" (fun () ->
      one_diagnostic Fixtures.Infer.array_literal_of_the_wrong_length "types.mismatch");
  Harness.test "a list literal is a set where a set is expected" (fun () ->
      fine Fixtures.Infer.list_literal_as_a_set)

let () =
  Harness.test "deriving Deserialize needs every invariant clause to run" (fun () ->
      one_diagnostic Fixtures.Infer.deserialize_of_scores_with_a_quantified_invariant
        "types.cannot_derive");
  Harness.test "deriving Deserialize accepts an invariant that runs" (fun () ->
      fine Fixtures.Infer.deserialize_of_bounds_with_an_invariant);
  Harness.test "integer arithmetic in a specification is exact" (fun () ->
      has_type Fixtures.Infer.ensures_of_a_sum "a + b" "Integer");
  Harness.test "comparisons in a specification may mix integer types" (fun () ->
      fine Fixtures.Infer.requires_comparing_uint32_and_uint64);
  Harness.test "a lambda in a specification may give a built-in integer for an Integer" (fun () ->
      fine Fixtures.Infer.requires_summing_lengths_with_a_lambda)

let () =
  Harness.test "a for loop over a range of integers is a counted loop" (fun () ->
      let text = Fixtures.Infer.range_loop_to_a_count in
      if
        not
          (List.exists
             (fun (node : Core.statement) ->
               match node.kind with For { iteration = Integer_range _; _ } -> true | _ -> false)
             (Support.first_core_nodes text).statements)
      then Harness.fail "no counted loop");
  Harness.test "a for loop over a list visits its positions" (fun () ->
      fine Fixtures.Infer.loop_summing_a_list)

let () =
  Harness.test "checking twice gives the same result" (fun () ->
      let text = Fixtures.Infer.loop_summing_a_list in
      let type_check_result () =
        let packages = Support.setup [ ("app::main", text) ] in
        let key =
          Resolve.Names.make_key
            (List.hd (Support.declarations packages (Support.module_of "app::main")))
        in
        Database.read_checked_body (Support.database packages) key
      in
      if type_check_result () <> type_check_result () then Harness.fail "different")

let () =
  Harness.test "no table of the standard library holds a type inference left unsolved" (fun () ->
      let packages = Support.setup [] in
      List.iter
        (fun ((file : Path.file), _) ->
          List.iter
            (fun (declaration : Resolve.Names.declaration) ->
              match
                Database.read_checked_body (Support.database packages)
                  (Resolve.Names.make_key declaration)
              with
              | Some { tables; _ } ->
                  List.iter
                    (Array.iter (function
                      | Some type_
                        when Types.exists
                               (function Variable _ | Literal _ -> true | _ -> false)
                               type_ ->
                          Harness.fail "%s: an unsolved type" (Path.show declaration.path)
                      | _ -> ()))
                    [ tables.types; tables.local_types ]
              | None -> ())
            ((Support.names packages file.module_.package).declarations_in file))
        Standard_library.files)

let point = "type Point(x: Int64)\n\n"

let () =
  Harness.test "a call's type arguments must meet their bounds" (fun () ->
      one_diagnostic (point ^ Fixtures.Infer.need_of_an_unordered_point) "types.unsatisfied_bound");
  Harness.test "a type written in a body must meet its bounds" (fun () ->
      let packages = Support.setup [ ("app::main", point ^ Fixtures.Infer.set_of_points) ] in
      match Support.codes (check packages (Support.file_of "app::main")) with
      | [ "types.unsatisfied_bound"; "types.unsatisfied_bound" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test
    "storage_lengthen rejects an element type with a drop, which would free memory that nothing \
     wrote" (fun () ->
      let in_standard files : Project.package list =
        [
          {
            name = Path.standard_package;
            dependencies = [];
            files =
              Standard_library.files
              @ List.map (fun (name, text) -> (Support.file_of name, text)) files;
          };
        ]
      in
      Support.one_diagnostic ~setup:in_standard ~file:"standard::probe"
        ~check:(fun packages ->
          Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ]
            (Database.create packages))
        Fixtures.Infer.storage_lengthen_of_storages "types.unsatisfied_bound");
  Harness.test "a type written in a body that is not a type is an error" (fun () ->
      one_diagnostic Fixtures.Infer.let_of_type_display "types.not_a_type");
  Harness.test "an operator's result must be the type expected of it" (fun () ->
      one_diagnostic Fixtures.Infer.product_of_a_span "types.mismatch");
  Harness.test "an array length nothing decides is an error" (fun () ->
      one_diagnostic Fixtures.Infer.zeros_without_a_length "types.cannot_infer");
  Harness.test "a qualified constant in a pattern must have the matched type" (fun () ->
      one_diagnostic Fixtures.Infer.exit_code_constant_arm_on_an_integer "types.mismatch");
  Harness.test "the alternatives of a pattern bind each name with one type" (fun () ->
      one_diagnostic Fixtures.Infer.or_pattern_binding_value_of_two_types "types.mismatch");
  Harness.test "a pattern must match every field or write .." (fun () ->
      one_diagnostic Fixtures.Infer.record_pattern_missing_a_field "types.missing_argument");
  (let comparison depth =
     "type Box[Value](value: Value)\n  derives Equal\n\nfn same(value: "
     ^ String.concat "" (List.init depth (fun _ -> "Box["))
     ^ "Int64" ^ String.make depth ']' ^ ") -> Bool {\n  value == value\n}\n"
   in
   Harness.test "a type nested 40 deep implements a trait through 40 nested impls" (fun () ->
       fine (comparison 40));
   Harness.test "a type nested 70 deep reaches the recursion limit of the impls that it needs"
     (fun () ->
       one_diagnostic (comparison 70) "types.recursion_limit"
         ~says:"needs more than 64 nested impls"));
  Harness.test "an associated type that grows a type reaches the recursion limit" (fun () ->
      one_diagnostic Fixtures.Infer.associated_type_that_grows_its_type "types.recursion_limit"
        ~says:"needs more than 64 nested types");
  Harness.test "an opaque type cannot be matched outside its package" (fun () ->
      one_diagnostic Fixtures.Infer.record_pattern_on_a_list "types.private_field");
  Harness.test "a bitwise compound assignment works on integers only" (fun () ->
      one_diagnostic Fixtures.Infer.bitwise_assignment_to_a_string "types.no_impl");
  Harness.test "a method written in full takes its receiver's mode" (fun () ->
      one_diagnostic Fixtures.Infer.push_written_in_full "types.wrong_receiver");
  Harness.test "a for loop takes the `element` overload from the type or from a trait" (fun () ->
      fine Fixtures.Infer.loop_over_a_bag_with_an_element_overload);
  Harness.test "a call picks an overload among a type's own and its family of traits'" (fun () ->
      fine Fixtures.Infer.overloads_of_label_across_traits);
  Harness.test "two traits that give one overload of a name are ambiguous at the call" (fun () ->
      one_diagnostic Fixtures.Infer.traits_giving_one_label "types.ambiguous_method"
        ~fixed:Fixtures.Infer.traits_giving_one_label_fixed);
  Harness.test "two unrelated traits that share a name are ambiguous however each takes self"
    (fun () ->
      one_diagnostic Fixtures.Infer.unrelated_traits_sharing_label "types.ambiguous_method");
  Harness.test "two bounds that give one overload of a name are ambiguous through the type"
    (fun () -> one_diagnostic Fixtures.Infer.bounds_giving_one_make "types.ambiguous_method");
  Harness.test "two unrelated bounds that share a name are ambiguous however each takes self"
    (fun () ->
      one_diagnostic Fixtures.Infer.unrelated_bounds_sharing_label "types.ambiguous_method");
  Harness.test "a bound's method is picked from its family by how the call takes self" (fun () ->
      fine Fixtures.Infer.bound_with_overloads_by_receiver);
  Harness.test "a trait's method written in full has no overload for a mode it lacks" (fun () ->
      one_diagnostic Fixtures.Infer.label_written_in_full_with_mut_self "types.wrong_receiver");
  Harness.test "an associated type of an argument is normalized" (fun () ->
      fine Fixtures.Infer.has_key_of_a_list);
  Harness.test "a literal receiver has its default type" (fun () ->
      has_type Fixtures.Infer.wrapping_add_on_a_literal "5.wrapping_add(3)" "Int64");
  Harness.test "a for loop over characters counts" (fun () ->
      fine Fixtures.Infer.range_loop_over_characters);
  Harness.test "an operation on a hole is a hole" (fun () -> fine Fixtures.Infer.addition_to_a_todo);
  Harness.test "a mistake is not reported again as a type that cannot be inferred" (fun () ->
      let packages = Support.setup [ ("app::main", Fixtures.Infer.map_of_an_undefined_name) ] in
      if
        List.mem "types.cannot_infer" (Support.codes (check packages (Support.file_of "app::main")))
      then Harness.fail "cascaded");
  Harness.test "a Float32 literal too large is an error" (fun () ->
      one_diagnostic Fixtures.Infer.float32_literal_too_large "types.literal_out_of_range");
  Harness.test "a Float32 literal is rounded once, from its decimal" (fun () ->
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match node.kind with Float rounded -> Some rounded | _ -> None)
          (Support.first_core_nodes Fixtures.Infer.float32_literal_needing_rounding).expressions
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
          (Support.first_core_nodes Fixtures.Infer.integer_range_arm).patterns
      with
      | [ (1, 5) ] -> ()
      | _ -> Harness.fail "the range pattern does not have the bounds 1 and 5");
  Harness.test "a range pattern on a type that is not an integer or Character is an error"
    (fun () -> one_diagnostic Fixtures.Infer.bool_range_arm "types.mismatch");
  Harness.test "an integer range on a type that is not ordered is one error" (fun () ->
      one_diagnostic Fixtures.Infer.integer_range_arm_on_a_bool "types.mismatch");
  Harness.test "a range pattern whose bounds infer its type as Bool is an error" (fun () ->
      one_diagnostic Fixtures.Infer.bool_range_lambda_parameter "types.mismatch" ~says:"not `Bool`");
  Harness.test "a range pattern on Character is fine" (fun () ->
      fine Fixtures.Infer.character_range_arm);
  Harness.test "a Character literal is a tagged string holding its scalar value" (fun () ->
      has_type Fixtures.Infer.accented_character_literal "Character\"é\"" "Character";
      if not (has_integer Fixtures.Infer.accented_character_literal 0xE9) then
        Harness.fail "no value");
  Harness.test "a UInt8 literal holds its ASCII character's value" (fun () ->
      if not (has_integer Fixtures.Infer.uint8_newline_literal 10) then Harness.fail "no value");
  Harness.test "a Character literal of two scalar values is an error" (fun () ->
      one_diagnostic Fixtures.Infer.character_literal_of_two_letters "types.character_scalar_count");
  Harness.test "a UInt8 literal of a character that is not ASCII is an error" (fun () ->
      one_diagnostic Fixtures.Infer.uint8_accented_literal "types.character_scalar_count");
  Harness.test "a negated literal of an unsigned type is one error" (fun () ->
      one_diagnostic Fixtures.Infer.uint8_let_of_minus_one "types.negated_unsigned");
  Harness.test "explicit type arguments give exactly the function's own" (fun () ->
      one_diagnostic Fixtures.Infer.pick_with_one_type_argument "types.arity");
  Harness.test "a type given too few arguments is one error, not a mismatch for each field"
    (fun () -> one_diagnostic Fixtures.Infer.pair_built_with_one_type_argument "types.arity");
  Harness.test "an associated type that a supertrait fixes to Self is Self" (fun () ->
      no_diagnostics [ ("app::main", Fixtures.Infer.output_of_a_fixed_width_integer) ]);
  Harness.test "an associated type of a generic supertrait takes the supertrait's arguments"
    (fun () -> no_diagnostics [ ("app::main", Fixtures.Infer.output_of_a_generic_supertrait) ]);
  Harness.test "a missing label has no fix when which one is meant is not known" (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Infer.call_with_three_unlabeled_arguments) ]
      in
      List.iter
        (fun (diagnostic : Diagnostic.t) ->
          if diagnostic.fixes <> [] then Harness.fail "offered a fix")
        (check packages (Support.file_of "app::main")));
  Harness.test "the string + fix keeps escapes" (fun () ->
      one_diagnostic Fixtures.Infer.escaped_string_plus_a_string "types.string_addition"
        ~fixed:Fixtures.Infer.escaped_string_plus_a_string_fixed);
  Harness.test "a lambda cannot mutate a captured variable" (fun () ->
      one_diagnostic Fixtures.Infer.lambda_assigning_a_captured_var "types.not_assignable")

let () =
  Harness.test "a function-typed parameter's requires is a Bool over its inputs" (fun () ->
      fine Fixtures.Infer.function_parameter_requiring_its_index_below_a_limit);
  Harness.test "a function-typed parameter's requires must be a Bool" (fun () ->
      one_diagnostic Fixtures.Infer.function_parameter_requiring_an_integer "types.mismatch");
  Harness.test "a trait method without a body has its clauses checked" (fun () ->
      one_diagnostic Fixtures.Infer.trait_method_ensuring_a_sum_with_true "types.no_impl");
  Harness.test "==> in a compiled body" (fun () ->
      one_diagnostic Fixtures.Infer.implication_in_a_body "types.specification_only");
  Harness.test "a quantifier over a type in a compiled body" (fun () ->
      one_diagnostic Fixtures.Infer.quantifier_over_int64_in_a_body "types.specification_only");
  Harness.test "a local of type Integer in a compiled body" (fun () ->
      one_diagnostic Fixtures.Infer.integer_local_in_a_body "types.specification_only"
        ~says:"`big` has the type `Integer`");
  Harness.test "a local whose type holds Integer in a compiled body" (fun () ->
      one_diagnostic Fixtures.Infer.list_of_integers_in_a_body "types.specification_only"
        ~says:"which holds `Integer`");
  Harness.test "a model in a compiled body" (fun () ->
      one_diagnostic Fixtures.Infer.model_of_a_list_in_a_body "types.specification_only"
        ~says:"`Sequence[Int64]`");
  Harness.test "a field of type Integer" (fun () ->
      one_diagnostic Fixtures.Infer.box_of_an_integer "types.specification_only");
  Harness.test "a variant's field of type Sequence" (fun () ->
      one_diagnostic Fixtures.Infer.variant_holding_a_sequence "types.specification_only");
  Harness.test "a constant of type Integer is read in specifications" (fun () ->
      fine Fixtures.Infer.integer_constant_read_in_requires);
  Harness.test "a constant of type Integer in a compiled body" (fun () ->
      one_diagnostic Fixtures.Infer.integer_constant_read_in_a_body "types.specification_only");
  Harness.test "a default of a function for specifications only is a specification" (fun () ->
      fine Fixtures.Infer.specification_function_with_a_default);
  Harness.test "a loop clause of a compiled body reads a Sequence" (fun () ->
      fine Fixtures.Infer.loop_invariant_reading_visited);
  Harness.test "a function for specifications only has a specification for a body" (fun () ->
      fine Fixtures.Infer.specification_function_with_a_quantifier);
  Harness.test "a function for specifications only cannot hold a var" (fun () ->
      one_diagnostic Fixtures.Infer.specification_function_with_a_var "types.not_in_specification");
  Harness.test "a theorem is not a value" (fun () ->
      one_diagnostic Fixtures.Infer.theorem_as_a_value "types.not_a_value"
        ~says:"is a theorem, so it is not a value");
  Harness.test "a theorem call in a compiled body" (fun () ->
      one_diagnostic Fixtures.Infer.body_calling_a_theorem "types.specification_only"
        ~says:"is a theorem");
  Harness.test "a theorem is called in a theorem and in a proof block" (fun () ->
      fine Fixtures.Infer.theorem_called_by_a_theorem_and_a_proof_block);
  Harness.test "a call of a function for specifications only in a compiled body is reported once"
    (fun () ->
      one_diagnostic Fixtures.Infer.body_calling_a_specification_function "types.specification_only"
        ~says:"`scaled` mentions `Integer`");
  Harness.test "a theorem cannot hold a loop" (fun () ->
      one_diagnostic Fixtures.Infer.theorem_with_a_loop "types.not_in_specification");
  Harness.test "a proof block cannot hold a loop" (fun () ->
      one_diagnostic Fixtures.Infer.proof_block_with_a_loop "types.not_in_specification");
  Harness.test "a proof block cannot assign to a variable of the program" (fun () ->
      one_diagnostic Fixtures.Infer.proof_block_assigning_a_var "types.not_in_specification");
  Harness.test "a proof block cannot return" (fun () ->
      one_diagnostic Fixtures.Infer.proof_block_returning "types.not_in_specification");
  Harness.test "a quantifier's body in code cannot return" (fun () ->
      one_diagnostic Fixtures.Infer.quantifier_returning_in_a_body "types.not_in_specification");
  Harness.test "a quantifier's body cannot pass an argument mut" (fun () ->
      one_diagnostic Fixtures.Infer.quantifier_calling_grow "types.not_in_specification");
  Harness.test "a contract cannot pass an argument mut" (fun () ->
      one_diagnostic Fixtures.Infer.requires_calling_bump "types.not_in_specification");
  Harness.test "a constant in a pattern needs structural equality" (fun () ->
      one_diagnostic Fixtures.Infer.float_point_constant_arm "types.not_structural");
  Harness.test "a constant of a derived type of integers in a pattern" (fun () ->
      fine Fixtures.Infer.integer_point_constant_arm);
  Harness.test "a loop's cost bound is checked" (fun () ->
      one_diagnostic Fixtures.Infer.loop_cost_naming_a_missing_name "resolve.unknown_name")

let identity = Fixtures.Infer.identity

let () =
  Harness.test "type arguments after a parenthesized name are read as after the name" (fun () ->
      fine (identity ^ Fixtures.Infer.parenthesized_identity_called_with_a_type_argument);
      one_diagnostic
        (identity ^ Fixtures.Infer.parenthesized_identity_of_an_integer_as_a_string)
        "types.mismatch");
  Harness.test "a parenthesized name with type arguments is a value of that function" (fun () ->
      fine (identity ^ Fixtures.Infer.parenthesized_identity_with_a_type_argument));
  Harness.test "a trait's written arguments are the ones its call uses" (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Infer.add_of_strings_given_integers) ]
      in
      if
        not
          (List.mem "types.no_impl" (Support.codes (check packages (Support.file_of "app::main"))))
      then Harness.fail "the written argument was ignored");
  Harness.test "a literal is the receiver of a trait method written in full" (fun () ->
      fine Fixtures.Infer.add_of_two_literals_written_in_full);
  Harness.test "a generic parameter takes no type arguments" (fun () ->
      one_diagnostic Fixtures.Infer.generic_parameter_given_type_arguments "types.arity");
  Harness.test "a trait's count argument is a value inferred from a call written in full" (fun () ->
      fine Fixtures.Infer.full_call_of_a_trait_with_a_count);
  Harness.test "a bound with a count argument gives an associated type its methods" (fun () ->
      fine Fixtures.Infer.method_of_an_associated_type_bounded_by_a_count);
  Harness.test "a generic parameter given type arguments is an error type, not the parameter"
    (fun () ->
      one_diagnostic Fixtures.Infer.method_of_a_parameter_given_type_arguments "types.arity");
  Harness.test "`~` of a string is one error, and its value is not a string" (fun () ->
      one_diagnostic Fixtures.Infer.complement_of_a_string "types.no_impl");
  Harness.test "a negated unsigned value is one error, and its value is not unsigned" (fun () ->
      one_diagnostic Fixtures.Infer.negation_of_an_unsigned_parameter "types.negated_unsigned");
  Harness.test "a sum of strings is one error, and its value is not a string" (fun () ->
      one_diagnostic Fixtures.Infer.string_addition_bound_to_a_let "types.string_addition");
  Harness.test "a variant that its type does not have is one error" (fun () ->
      one_diagnostic Fixtures.Infer.unknown_variant_of_an_option "types.unknown_variant");
  Harness.test "a variant constructor of a record is an error" (fun () ->
      one_diagnostic Fixtures.Infer.variant_constructor_of_a_record "types.unknown_variant");
  Harness.test "a function value given too many arguments is one error" (fun () ->
      one_diagnostic Fixtures.Infer.function_value_called_with_two_arguments
        "types.too_many_arguments");
  Harness.test "a member of a generic parameter that it does not have is an error" (fun () ->
      one_diagnostic Fixtures.Infer.member_of_an_unbounded_generic "types.unknown_member");
  Harness.test "a type with no fields is not its own value" (fun () ->
      one_diagnostic Fixtures.Infer.marker_without_parentheses "types.not_a_value");
  Harness.test "`self` outside a method is an error" (fun () ->
      one_diagnostic Fixtures.Infer.self_in_a_function "types.not_a_value");
  Harness.test "`old` without its operand is an error" (fun () ->
      one_diagnostic Fixtures.Infer.ensures_comparing_old_alone "types.not_a_value");
  Harness.test "a type argument that nothing decides is an error at its call" (fun () ->
      one_diagnostic Fixtures.Infer.make_without_a_type_argument "types.cannot_infer");
  Harness.test "a trait is not called" (fun () ->
      one_diagnostic Fixtures.Infer.trait_called "types.not_callable");
  Harness.test "a generic function given type arguments, as a value, must meet its bounds"
    (fun () ->
      one_diagnostic (point ^ Fixtures.Infer.need_of_a_point_as_a_value) "types.unsatisfied_bound");
  Harness.test "the scrutinee of an `is` is inferred before its pattern is checked" (fun () ->
      fine Fixtures.Infer.is_on_a_span_division);
  Harness.test "a `for` over a cursor binds the values of its `next`" (fun () ->
      fine Fixtures.Infer.loop_over_a_cursor);
  Harness.test "`Self` in the body of a method without `self` is the method's type" (fun () ->
      fine Fixtures.Infer.self_type_in_a_static_method);
  Harness.test "a pattern that does not fit its type still gives its bindings a type" (fun () ->
      one_diagnostic Fixtures.Infer.some_pattern_on_an_integer "types.unknown_variant");
  Harness.test "a `todo` that nothing decides keeps the hole type in the tables" (fun () ->
      has_type Fixtures.Infer.let_of_todo "todo" "an undecided type")

let shape = Fixtures.Infer.shape
let source = Fixtures.Infer.source

let () =
  Harness.test "a value built of a generic type must meet the type's bounds" (fun () ->
      one_diagnostic (shape ^ Fixtures.Infer.holder_of_an_integer) "types.unsatisfied_bound");
  Harness.test "a value built of a generic type that meets its bounds is fine" (fun () ->
      fine (shape ^ Fixtures.Infer.holder_of_a_square));
  Harness.test "a value built inside another must meet its type's bounds" (fun () ->
      one_diagnostic
        (shape ^ Fixtures.Infer.some_of_a_holder_of_an_integer)
        "types.unsatisfied_bound");
  Harness.test "a variant built of a generic type must meet the type's bounds" (fun () ->
      one_diagnostic
        (shape ^ Fixtures.Infer.full_slot_of_a_type_without_shape)
        "types.unsatisfied_bound");
  Harness.test "a generic type named in an expression must meet its bounds" (fun () ->
      one_diagnostic (shape ^ Fixtures.Infer.slot_of_a_type_without_shape) "types.unsatisfied_bound");
  Harness.test "a statement reports a bound once, however many of its parts need it" (fun () ->
      one_diagnostic (shape ^ Fixtures.Infer.area_of_a_holder_of_integers) "types.unsatisfied_bound");
  Harness.test "a method used as a value must meet its bounds" (fun () ->
      one_diagnostic (shape ^ Fixtures.Infer.fits_of_a_point_as_a_value) "types.unsatisfied_bound");
  Harness.test "function types that count the calls of different capabilities are different types"
    (fun () ->
      let lists counted =
        "fn take(runs: List[(fn() uses Clock, Console cost calls(Console) <= 1)]) {}\n\n\
         fn f(runs: List[(fn() uses Clock, Console cost calls(" ^ counted
        ^ ") <= 1)]) {\n  take(runs)\n}\n"
      in
      fine (lists "Console");
      one_diagnostic (lists "Clock") "types.mismatch";
      one_diagnostic (lists "Console.print_line") "types.mismatch");
  Harness.test "the target of `calls` in a function type is a capability or one of its methods"
    (fun () ->
      one_diagnostic Fixtures.Infer.calls_cost_of_a_type "types.not_a_capability";
      one_diagnostic "fn f(run: (fn() uses Clock cost calls(Clock.later) <= 1)) {}\n"
        "types.unknown_member";
      one_diagnostic "fn f(visit: fn(), run: (fn() cost calls(visit) <= 1)) {}\n"
        "types.not_a_capability");
  Harness.test
    "the target of `calls` in a clause is a function parameter, a capability, or a capability's \
     method" (fun () ->
      let clause counted =
        "type Point(x: Int64)\n\n\
         fn f(count: Int64, visit: (fn() cost time finite))\n\
        \  uses Clock\n\
        \  cost calls(" ^ counted ^ ") <= 1\n{\n  todo\n}\n"
      in
      fine (clause "visit");
      fine (clause "Clock");
      fine (clause "Clock.now");
      one_diagnostic (clause "count") "types.not_callable";
      one_diagnostic (clause "Point") "types.not_a_capability";
      one_diagnostic (clause "Clock.later") "types.unknown_member");
  Harness.test "a method with generic parameters is not object-safe" (fun () ->
      one_diagnostic Fixtures.Infer.generic_visit_through_any "types.not_callable");
  Harness.test "a method that takes or returns Self cannot be called through any" (fun () ->
      one_diagnostic Fixtures.Infer.join_through_any "types.not_callable");
  Harness.test "a method whose result holds Self cannot be called through any" (fun () ->
      one_diagnostic Fixtures.Infer.skip_through_any_cursor "types.not_callable");
  Harness.test "a cursor's own step and its counting can be called through any" (fun () ->
      fine Fixtures.Infer.any_cursor_stepped_and_counted);
  Harness.test "a method that names an associated type can be called through any" (fun () ->
      fine (source ^ Fixtures.Infer.any_source_of_numbers));
  Harness.test "`any value` must give the associated types its type fixes" (fun () ->
      one_diagnostic (source ^ Fixtures.Infer.any_source_of_numbers_as_strings) "types.no_impl");
  Harness.test "`any value` that gives the associated types its type fixes is fine" (fun () ->
      fine (source ^ Fixtures.Infer.any_source_of_numbers));
  Harness.test "`any value` of a generic parameter needs a bound that fixes the associated types"
    (fun () ->
      one_diagnostic (source ^ Fixtures.Infer.any_source_of_an_unfixed_input) "types.no_impl");
  Harness.test "`any value` of a generic parameter whose bound fixes the associated types is fine"
    (fun () -> fine (source ^ Fixtures.Infer.any_source_of_a_fixed_input));
  Harness.test "an associated type a bound fixes infers a type argument" (fun () ->
      fine (source ^ Fixtures.Infer.first_of_a_source_with_a_fixed_item));
  Harness.test "an associated type a bound fixes must be the one the impl gives" (fun () ->
      one_diagnostic
        (source ^ Fixtures.Infer.text_of_a_source_of_integers)
        "types.unsatisfied_bound")

let point = "type Point(x: Int64, y: Int64)\n\n"

let () =
  Harness.test "a constant is built from literals, operators on numbers, and other constants"
    (fun () -> fine Fixtures.Infer.constants_of_literals_and_operators);
  Harness.test "a constant builds records, variants, and collections of constants" (fun () ->
      fine (point ^ Fixtures.Infer.constants_of_records_variants_and_collections));
  Harness.test "a constant cannot call a function" (fun () ->
      one_diagnostic Fixtures.Infer.constant_calling_a_function "types.not_constant");
  Harness.test "a constant cannot call a capability" (fun () ->
      one_diagnostic "let started: Instant = Clock.now()\n" "types.not_constant");
  Harness.test "a constant cannot call a method" (fun () ->
      one_diagnostic "let length: UInt64 = \"four\".length()\n" "types.not_constant");
  Harness.test "a constant cannot index a collection" (fun () ->
      one_diagnostic Fixtures.Infer.constant_indexing_a_list "types.not_constant");
  Harness.test "a constant cannot branch" (fun () ->
      one_diagnostic "let chosen: Int64 = if true { 1 } else { 2 }\n" "types.not_constant");
  Harness.test "a constant cannot use an operator that a type defines" (fun () ->
      one_diagnostic Fixtures.Infer.constant_comparing_strings "types.not_constant");
  Harness.test "a constant's arithmetic must stay within its type" (fun () ->
      one_diagnostic "let size: UInt64 = 0 - 1\n" "types.constant_overflow");
  Harness.test "each step of a constant's arithmetic must stay within its type" (fun () ->
      one_diagnostic "let small: UInt8 = 200 + 100 - 100\n" "types.constant_overflow");
  Harness.test "a constant's arithmetic through another constant must stay within its type"
    (fun () ->
      one_diagnostic Fixtures.Infer.constant_overflowing_through_another "types.constant_overflow");
  Harness.test "negating a constant's least value overflows" (fun () ->
      one_diagnostic "let flipped: Int8 = -(-128)\n" "types.constant_overflow");
  Harness.test "a constant cannot divide by zero" (fun () ->
      one_diagnostic "let nothing: Int64 = 5 / 0\n" "types.constant_overflow");
  Harness.test "a default must be a constant expression" (fun () ->
      one_diagnostic Fixtures.Infer.default_calling_a_function "types.default_not_constant");
  Harness.test "a default cannot name a parameter" (fun () ->
      one_diagnostic "fn f(count: Int64, twice: Int64 = count * 2) {}\n"
        "types.default_not_constant");
  Harness.test "a method's default must be a constant expression" (fun () ->
      one_diagnostic
        (point ^ Fixtures.Infer.method_default_calling_a_function)
        "types.default_not_constant");
  Harness.test "a field's default must be a constant expression" (fun () ->
      one_diagnostic Fixtures.Infer.field_default_calling_a_function "types.default_not_constant");
  Harness.test "a field's default's arithmetic must stay within its type" (fun () ->
      one_diagnostic "type Settings(retries: UInt8 = 250 + 10)\n" "types.constant_overflow")

let () =
  let helper visibility =
    Printf.sprintf "%sfn half(value: Int64) -> Int64\n  cost time O(1)\n{\n  value - 1\n}\n\n"
      visibility
  in
  Harness.test "a public contract names only functions that other packages can call" (fun () ->
      let sorted visibility =
        Printf.sprintf
          "%sfn in_order(items: Slice[Int64]) -> Bool\n\
          \  cost time O(1)\n\
           {\n\
          \  items.length() < 2\n\
           }\n\n"
          visibility
      in
      let sort visibility clause =
        Printf.sprintf "%sfn sort(items: mut Slice[Int64])\n  %s\n{\n  todo\n}\n" visibility clause
      in
      one_diagnostic
        (sorted "internal " ^ sort "public " "requires in_order(items)")
        "types.private_in_public";
      one_diagnostic
        (sorted "" ^ sort "public " "requires in_order(items)")
        "types.private_in_public";
      fine (sorted "public " ^ sort "public " "requires in_order(items)");
      fine (sorted "internal " ^ sort "internal " "requires in_order(items)");
      fine (sorted "" ^ sort "" "requires in_order(items)"));
  Harness.test "a public ensures may name a private function" (fun () ->
      fine
        ("fn in_order(items: Slice[Int64]) -> Bool\n\
         \  cost time O(1)\n\
          {\n\
         \  items.length() < 2\n\
          }\n\n"
       ^ "public fn sort(items: mut Slice[Int64])\n  ensures in_order(items)\n{\n  todo\n}\n"));
  Harness.test "a public contract names only constants that other packages can name" (fun () ->
      let capped visibility =
        Printf.sprintf
          "%slet limit: Int64 = 10\n\n\
           public fn capped(value: Int64) -> Int64\n\
          \  requires value <= limit\n\
           {\n\
          \  todo\n\
           }\n"
          visibility
      in
      one_diagnostic (capped "internal ") "types.private_in_public";
      fine (capped "public "));
  Harness.test "a public trait's method names only public functions in its requires" (fun () ->
      let helper = Fixtures.Infer.helper in
      one_diagnostic
        (helper ^ Fixtures.Infer.requires_naming_a_private_function)
        "types.private_in_public";
      fine (helper ^ Fixtures.Infer.ensures_naming_a_private_function);
      let implemented visibility =
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
      fine (implemented "public ");
      fine (implemented "internal "));
  Harness.test "a function's body can call a function that other packages cannot" (fun () ->
      fine (helper "internal " ^ Fixtures.Infer.public_function_calling_a_private_one))

let () =
  Harness.test "a bit-vector assertion names only integers and booleans" (fun () ->
      one_diagnostic Fixtures.Infer.bit_vector_assertion_naming_a_list "types.not_bit_vector")
