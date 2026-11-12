(* The tests of checking bodies. Each gives a small definition and states
   one fact: a diagnostic with its fix, or one fact about the tables or the
   core form. *)

open Harness
open Support

let check = Type_checker.through Infer
let one_diagnostic = one_diagnostic ~check
let no_diagnostics = no_diagnostics ~check
let fine text = no_diagnostics [ ("app::main", text) ]

(* The type check result of the definition that holds the [occurrence]th
   appearance of [written], and the innermost expression that starts there. *)
let expression_at text written occurrence =
  let database = setup [ ("app::main", text) ] in
  let module_ = module_of "app::main" in
  let offset = Option.get (Substring.find ~occurrence text written) in
  let actual =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        match
          ( Query.demand database Resolve.Names.definition key,
            Query.demand database Resolve.Names.base key,
            Query.demand database Infer.type_check_result key )
        with
        | Some definition, Some (_, base), Some result ->
            (* The expression whose span is exactly the text, or else the
               innermost one that starts there. *)
            let best = ref None in
            let exact (value : Syntax.expression) =
              value.span.stop - value.span.start = String.length written
            in
            let rec visit (value : Syntax.expression) =
              (if base + value.span.start = offset then
                 match !best with
                 | Some (other : Syntax.expression)
                   when exact other
                        || (not (exact value))
                           && other.span.stop - other.span.start
                              <= value.span.stop - value.span.start ->
                     ()
                 | _ -> best := Some value);
              Syntax_walk.children visit value
            in
            Syntax_walk.definition visit definition;
            Option.map (fun value -> (value, result)) !best
        | _ -> None)
      (Query.demand database Resolve.Names.declarations module_)
  in
  match actual with
  | Some actual -> actual
  | None -> failwith (Printf.sprintf "no expression at %S" written)

(* Whether the core form of the first definition has an integer literal
   with this value. *)
let has_integer text value =
  List.exists
    (fun (node : Core.expression) ->
      match node.kind with Integer actual -> Z.equal actual (Z.of_int value) | _ -> false)
    (first_core_nodes text).expressions

(* The core nodes built from the [occurrence]th appearance of [written]. *)
let core_at text written occurrence =
  let value, (result : Infer.type_check_result) = expression_at text written occurrence in
  match result.core with
  | None -> failwith (Printf.sprintf "no core form holds %S" written)
  | Some form ->
      let nodes = ref [] in
      Core_walk.definition
        {
          Core_walk.ignore_all with
          expression =
            (fun (node : Core.expression) -> if node.origin = value.id then nodes := node :: !nodes);
        }
        form.definition;
      List.rev !nodes

(* The call built from the [occurrence]th appearance of [written], with its
   type. *)
let core_call_at text written occurrence =
  match
    List.find_map
      (fun (node : Core.expression) ->
        match node.kind with Call call -> Some (call, node.type_) | _ -> None)
      (core_at text written occurrence)
  with
  | Some call -> call
  | None -> failwith (Printf.sprintf "%S is not a call" written)

(* Whether an argument is the view of an owned collection: a call of its
   [slice]. *)
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
  let value, (result : Infer.type_check_result) = expression_at text written occurrence in
  match result.tables.types.(value.id) with
  | Some type_ ->
      if Types.show type_ <> expected then
        fail "`%s` has type %s, not %s" written (Types.show type_) expected
  | None -> fail "`%s` has no type" written

(* Literals *)

let () =
  test "a literal takes the type of the other operand" (fun () ->
      has_type Fixtures.Infer.literal_takes_the_type_of_the_other_operand "1" "UInt8");
  test "a literal nothing decides is an Int64" (fun () ->
      has_type Fixtures.Infer.literal_nothing_decides_is_an_int64 "0" "Int64");
  test "a literal takes the expected type" (fun () ->
      has_type Fixtures.Infer.literal_takes_the_expected_type "3" "UInt8");
  test "a literal multiplied by a type that is not an integer is an Int64" (fun () ->
      fine Fixtures.Infer.literal_multiplied_by_a_type_that_is_not_an);
  test "an expression of literals waits for the same decision" (fun () ->
      has_type Fixtures.Infer.expression_of_literals_waits_for_the_same_decision "60" "UInt16");
  test "a literal that does not fit its type is an error" (fun () ->
      one_diagnostic Fixtures.Infer.literal_that_does_not_fit_its_type_is_an_error
        "types.literal_out_of_range");
  test "a literal of a type an integer trait bounds is an integer of that type" (fun () ->
      fine Fixtures.Infer.literal_of_a_type_an_integer_trait_bounds_is_an);
  test "a literal of a type an integer trait bounds must fit every type that implements it"
    (fun () ->
      one_diagnostic Fixtures.Infer.literal_of_a_type_an_integer_trait_bounds_must_fit
        "types.literal_out_of_range";
      one_diagnostic Fixtures.Infer.literal_of_a_type_an_integer_trait_bounds_must_fit_2
        "types.literal_out_of_range");
  test "a literal of a type UnsignedInteger bounds cannot be negated" (fun () ->
      one_diagnostic Fixtures.Infer.literal_of_a_type_unsignedinteger_bounds_cannot_be
        "types.negated_unsigned");
  test "a USize literal must fit in 32 bits, so that the code holds on every target" (fun () ->
      one_diagnostic Fixtures.Infer.usize_literal_must_fit_in_32_bits_so_that_the_code
        "types.literal_out_of_range");
  test "a package that runs only on 64-bit targets may use 64-bit USize literals" (fun () ->
      let engine = Engine.create ~bases:[ Lazy.force Support.standard ] () in
      Database.load_package ~usize_bits:64 engine ~name:{ owner = None; name = "app" }
        ~dependencies:[]
        [ (module_of "app::main", Fixtures.Infer.package_that_runs_only_on_64_bit_targets_may_use) ];
      match check (Engine.context engine) (module_of "app::main") with
      | [] -> ()
      | actual -> fail "%s" (String.concat "; " (codes actual)));
  test "a negated literal is checked after the negation" (fun () ->
      fine Fixtures.Infer.negated_literal_is_checked_after_the_negation);
  test "an integer literal where a float is expected is an error with a fix" (fun () ->
      one_diagnostic Fixtures.Infer.integer_literal_where_a_float_is_expected_is_an
        "types.integer_for_float"
        ~fixed:Fixtures.Infer.integer_literal_where_a_float_is_expected_is_an_fixed);
  test "a literal shift amount is a USize" (fun () ->
      has_type Fixtures.Infer.literal_shift_amount_is_a_usize "3" ~occurrence:3 "USize")

(* Operators *)

let () =
  test "comparing integer types that differ is an error with a fix that converts" (fun () ->
      one_diagnostic Fixtures.Infer.comparing_integer_types_that_differ_is_an_error
        "types.mismatched_integers"
        ~fixed:Fixtures.Infer.comparing_integer_types_that_differ_is_an_error_fixed);
  test "+ on strings is an error with a fix to interpolation" (fun () ->
      one_diagnostic Fixtures.Infer.on_strings_is_an_error_with_a_fix_to_interpolation
        "types.string_addition"
        ~fixed:Fixtures.Infer.on_strings_is_an_error_with_a_fix_to_interpolation_fixed);
  test "an operator chooses the impl by both operands" (fun () ->
      let text = Fixtures.Infer.operator_chooses_the_impl_by_both_operands in
      match core_call_at text "length + extra" 1 with
      | { callee = Trait_method { evidence = Impl { impl; _ }; name = "add"; _ }; _ }, _ ->
          let shown = Path.show impl in
          if not (Substring.contains shown "Add[Int64]") then fail "the impl chosen is %s" shown
      | _ -> fail "no impl recorded");
  test "an ordering on Self in a trait's law is its compare" (fun () ->
      let text = Fixtures.Infer.ordering_on_self_in_a_traits_law_is_its_compare in
      List.iter
        (fun written ->
          match core_call_at text written 1 with
          | { callee = Trait_method { name = "compare"; evidence = Bound; _ }; _ }, result ->
              if Types.show result <> "Ordering" then
                fail "`%s` calls a `compare` that gives `%s`" written (Types.show result)
          | _ -> fail "`%s` is another call" written)
        [ "first < second"; "second < third"; "first < third" ]);
  test "an operand can be the result of an operator's method" (fun () ->
      fine Fixtures.Infer.operand_can_be_the_result_of_an_operators_method);
  test "a type without the operator's trait is an error" (fun () ->
      one_diagnostic Fixtures.Infer.type_without_the_operators_trait_is_an_error "types.no_impl")

(* Calls and arguments *)

let () =
  let functions = "fn copy_file(source: Int64, destination: Int64) {}\n\n" in
  test "an argument after the first needs a label, with a fix that adds it" (fun () ->
      one_diagnostic
        (functions ^ Fixtures.Infer.argument_after_the_first_needs_a_label_with_a_fix)
        "types.missing_label"
        ~fixed:(functions ^ Fixtures.Infer.argument_after_the_first_needs_a_label_with_a_fix_2));
  test "a variable with the parameter's name needs no label" (fun () ->
      fine (functions ^ Fixtures.Infer.variable_with_the_parameters_name_needs_no_label));
  test "arguments out of order are an error with a fix that reorders them" (fun () ->
      one_diagnostic
        (functions ^ Fixtures.Infer.arguments_out_of_order_are_an_error_with_a_fix)
        "types.out_of_order"
        ~fixed:(functions ^ Fixtures.Infer.arguments_out_of_order_are_an_error_with_a_fix_2));
  test "a missing argument is an error" (fun () ->
      one_diagnostic
        (functions ^ Fixtures.Infer.missing_argument_is_an_error)
        "types.missing_argument");
  test "an argument for a parameter with a default can be omitted" (fun () ->
      let text = Fixtures.Infer.argument_for_a_parameter_with_a_default_can_be in
      match core_call_at text "connect(1)" 1 with
      | { arguments = [ Passed _; Default ]; _ }, _ -> ()
      | _ -> fail "the omitted default is not recorded");
  test "a String passed where a StringSlice is expected is viewed" (fun () ->
      let text = Fixtures.Infer.string_passed_where_a_stringslice_is_expected_is in
      match core_call_at text "greet(name)" 1 with
      | { arguments = [ argument ]; _ }, _ when is_view argument -> ()
      | _ -> fail "no conversion recorded");
  test "a capability's method views a String argument too" (fun () ->
      let text = Fixtures.Infer.capabilitys_method_views_a_string_argument_too in
      match core_call_at text "Console.print_line(name)" 1 with
      | { arguments = [ argument ]; _ }, _ when is_view argument -> ()
      | _ -> fail "no conversion recorded");
  test "a string literal is a String, viewed where a StringSlice is expected" (fun () ->
      let text = Fixtures.Infer.string_literal_is_a_string_viewed_where_a in
      has_type text "\"hello\"" "String";
      match core_call_at text "Console.print_line(\"hello\")" 1 with
      | { arguments = [ argument ]; _ }, _ when is_view argument -> ()
      | _ -> fail "no conversion recorded");
  test "a cursor's next is the Cursor trait's, by the cursor's own impl" (fun () ->
      let text = Fixtures.Infer.cursors_next_is_the_cursor_traits_by_the_cursors in
      fine text;
      has_type text "count_to(3)" "the cursor of app::main::count_to";
      match core_at text "first.next()" 1 with
      | [ { kind = Cursor_next _; type_; _ } ] when Types.show type_ = "Option[Int64]" -> ()
      | _ -> fail "not the `next` of the cursor's own impl");
  test "an unknown label is an error with a fix to the closest" (fun () ->
      one_diagnostic
        (functions ^ Fixtures.Infer.unknown_label_is_an_error_with_a_fix_to_the)
        "types.unknown_label"
        ~fixed:(functions ^ Fixtures.Infer.unknown_label_is_an_error_with_a_fix_to_the_2));
  test "a record is built with labels in any order" (fun () ->
      fine Fixtures.Infer.record_is_built_with_labels_in_any_order);
  test "a record with one field takes a bare value" (fun () ->
      fine Fixtures.Infer.record_with_one_field_takes_a_bare_value);
  test "a generic function's type arguments are solved from its arguments" (fun () ->
      has_type Fixtures.Infer.generic_functions_type_arguments_are_solved_from "wrap(5)"
        "Option[Int64]")

(* Modes *)

let () =
  test "a mut parameter needs mut at the call, with a fix that adds it" (fun () ->
      one_diagnostic Fixtures.Infer.mut_parameter_needs_mut_at_the_call_with_a_fix
        "types.missing_mark"
        ~fixed:Fixtures.Infer.mut_parameter_needs_mut_at_the_call_with_a_fix_fixed);
  test "an own parameter needs own for a place that does not copy implicitly" (fun () ->
      one_diagnostic Fixtures.Infer.own_parameter_needs_own_for_a_place_that_does_not
        "types.missing_mark"
        ~fixed:Fixtures.Infer.own_parameter_needs_own_for_a_place_that_does_not_fixed);
  test "own on a place that copies implicitly is redundant" (fun () ->
      one_diagnostic Fixtures.Infer.own_on_a_place_that_copies_implicitly_is_redundant
        "types.redundant_mark"
        ~fixed:Fixtures.Infer.own_on_a_place_that_copies_implicitly_is_redundant_fixed);
  test "a mut receiver chooses the method's mut version" (fun () ->
      fine Fixtures.Infer.mut_receiver_chooses_the_methods_mut_version);
  test "a place calling a method that takes mut self needs the mark, with a fix that adds it"
    (fun () ->
      one_diagnostic Fixtures.Infer.place_calling_a_method_that_takes_mut_self_needs
        "types.missing_mark"
        ~fixed:Fixtures.Infer.place_calling_a_method_that_takes_mut_self_needs_fixed)

(* Statements *)

let () =
  test "a statement's value must be used, with a fix that discards it" (fun () ->
      one_diagnostic Fixtures.Infer.statements_value_must_be_used_with_a_fix_that
        "types.unused_value"
        ~fixed:Fixtures.Infer.statements_value_must_be_used_with_a_fix_that_fixed);
  test "the default of a parameter of a view type can be an owned value" (fun () ->
      fine Fixtures.Infer.default_of_a_parameter_of_a_view_type_can_be_an);
  test "`time` of a method that no bound of the type parameter declares is an error" (fun () ->
      one_diagnostic Fixtures.Infer.time_of_a_method_that_no_bound_of_the_type
        "types.unknown_member");
  test "a let cannot be assigned" (fun () ->
      one_diagnostic Fixtures.Infer.let_cannot_be_assigned "types.not_assignable");
  List.iter
    (fun (what, text) ->
      test (what ^ " cannot be marked `mut`") (fun () -> one_diagnostic text "types.wrong_mark"))
    [
      ("a read-only parameter", Fixtures.Infer.read_only_parameter);
      ("an `own` parameter", Fixtures.Infer.own_parameter);
      ("a `let`", Fixtures.Infer.let_);
      ("a field of a `let`", Fixtures.Infer.field_of_a_let);
      ("an element of a read-only parameter", Fixtures.Infer.element_of_a_read_only_parameter);
      ("a constant", Fixtures.Infer.constant);
      ("a read-only argument", Fixtures.Infer.read_only_argument);
      ( "the collection of a `for` loop that is a read-only parameter",
        Fixtures.Infer.collection_of_a_for_loop_that_is_a_read_only );
      ( "`self` in a method that takes `self` read-only",
        Fixtures.Infer.self_in_a_method_that_takes_self_read_only );
      ("`self` inside a lambda", Fixtures.Infer.self_inside_a_lambda);
      ("a local that a lambda captures", Fixtures.Infer.local_that_a_lambda_captures);
    ];
  test "a `var`, a `mut` parameter, `mut self`, and a `mut` loop variable can be marked `mut`"
    (fun () -> fine Fixtures.Infer.var_a_mut_parameter_mut_self_and_a_mut_loop);
  test "the variable of a loop over a call that yields `mut` can be marked `mut`" (fun () ->
      fine Fixtures.Infer.variable_of_a_loop_over_a_call_that_yields_mut_can);
  test "a var can be assigned" (fun () -> fine Fixtures.Infer.var_can_be_assigned);
  test "an empty list with nothing to decide its elements is an error" (fun () ->
      one_diagnostic Fixtures.Infer.empty_list_with_nothing_to_decide_its_elements_is
        "types.cannot_infer");
  test "an empty list takes its elements' type from the annotation" (fun () ->
      fine Fixtures.Infer.empty_list_takes_its_elements_type_from_the);
  test "a body's value must have the result type" (fun () ->
      one_diagnostic Fixtures.Infer.bodys_value_must_have_the_result_type "types.mismatch");
  test "an arm of type Never does not contribute to the type of the match" (fun () ->
      fine Fixtures.Infer.arm_of_type_never_does_not_contribute_to_the_type);
  test "? needs the function's error type" (fun () ->
      one_diagnostic Fixtures.Infer.needs_the_functions_error_type "types.wrong_try");
  test "? on a matching Result gives its value" (fun () ->
      has_type Fixtures.Infer.on_a_matching_result_gives_its_value "parse()?" "Int64");
  test "if without else has type Unit" (fun () ->
      has_type Fixtures.Infer.if_without_else_has_type_unit "if ready { }" "Unit")

(* Members *)

let () =
  test "an unknown field is an error with a fix to the closest" (fun () ->
      one_diagnostic Fixtures.Infer.unknown_field_is_an_error_with_a_fix_to_the
        "types.unknown_member");
  test "a method from a trait needs no import" (fun () ->
      fine Fixtures.Infer.method_from_a_trait_needs_no_import);
  test "a law's proof names the law's parameters, which have the proof's type for Self" (fun () ->
      fine Fixtures.Infer.laws_proof_names_the_laws_parameters_which_have);
  test "a law's proof for a generic impl is checked under its own generic parameters" (fun () ->
      fine Fixtures.Infer.laws_proof_for_a_generic_impl_is_checked_under_its);
  test "a law's proof names no parameter of another law" (fun () ->
      one_diagnostic Fixtures.Infer.laws_proof_names_no_parameter_of_another_law
        "resolve.unknown_name");
  test "a law's proof cannot assign to a parameter of the law" (fun () ->
      one_diagnostic Fixtures.Infer.laws_proof_cannot_assign_to_a_parameter_of_the_law
        "types.not_assignable");
  test "a variant with one field is a function" (fun () ->
      fine Fixtures.Infer.variant_with_one_field_is_a_function);
  test "a variant with several fields is not a function, because fields have no order" (fun () ->
      one_diagnostic Fixtures.Infer.variant_with_several_fields_is_not_a_function
        "types.not_a_value");
  test "a variant is looked up under its type" (fun () ->
      fine Fixtures.Infer.variant_is_looked_up_under_its_type);
  test "a constant under a type is read by name" (fun () ->
      has_type Fixtures.Infer.constant_under_a_type_is_read_by_name "UInt8.maximum" "UInt8");
  test "a trait method through a type chooses the impl by the argument" (fun () ->
      fine Fixtures.Infer.trait_method_through_a_type_chooses_the_impl_by)

(* Patterns *)

let () =
  test "an unknown variant in a pattern is an error" (fun () ->
      one_diagnostic Fixtures.Infer.unknown_variant_in_a_pattern_is_an_error "types.unknown_variant");
  test "a bare name in a record pattern binds the field it names" (fun () ->
      fine Fixtures.Infer.bare_name_in_a_record_pattern_binds_the_field_it);
  test "a bare name that names no field of a record with several is an error" (fun () ->
      one_diagnostic Fixtures.Infer.bare_name_that_names_no_field_of_a_record_with
        "types.unknown_member")

(* Lambdas *)

let () =
  test "a lambda with nothing to give its parameter types is an error" (fun () ->
      one_diagnostic Fixtures.Infer.lambda_with_nothing_to_give_its_parameter_types_is
        "types.lambda_needs_type");
  test "a lambda takes its parameter types from the function type it is passed as" (fun () ->
      has_type Fixtures.Infer.lambda_takes_its_parameter_types_from_the_function "item + 1" "Int64");
  test "concurrent code needs `Tasks`, in a block and in a loop" (fun () ->
      one_diagnostic Fixtures.Infer.concurrent_code_needs_tasks_in_a_block_and_in_a
        "capabilities.not_available";
      one_diagnostic Fixtures.Infer.concurrent_code_needs_tasks_in_a_block_and_in_a_2
        "capabilities.not_available");
  test "a branch of a concurrent block uses the capabilities around the block" (fun () ->
      fine Fixtures.Infer.branch_of_a_concurrent_block_uses_the_capabilities);
  (let sessions = Fixtures.Infer.sessions in
   test "a capability implemented by a monitor has no method with a callback that uses a capability"
     (fun () ->
       one_diagnostic
         (sessions ^ Fixtures.Infer.capability_implemented_by_a_monitor_has_no_method)
         "capabilities.callback_may_deadlock");
   test "an implementation is not a monitor if the body of its `provide` cannot use `Tasks`"
     (fun () -> fine (sessions ^ Fixtures.Infer.implementation_is_not_a_monitor_if_the_body_of_its));
   let tally = Fixtures.Infer.tally in
   test "a monitor needs `Tasks` at its `provide`, not only in a nested one" (fun () ->
       one_diagnostic
         (tally ^ Fixtures.Infer.monitor_needs_tasks_at_its_provide_not_only_in_a)
         "capabilities.monitor_needs_tasks");
   test
     "a monitor can lock through `Tasks` of its `provide`, an enclosing one, or a capability \
      parameter" (fun () ->
       fine (tally ^ Fixtures.Infer.monitor_can_lock_through_tasks_of_its_provide_an)));
  test "an assignment through an index of a map takes the key as an owned value" (fun () ->
      fine Fixtures.Infer.assignment_through_an_index_of_a_map_takes_the_key;
      one_diagnostic Fixtures.Infer.assignment_through_an_index_of_a_map_takes_the_key_2
        "types.missing_mark";
      one_diagnostic Fixtures.Infer.assignment_through_an_index_of_a_map_takes_the_key_3
        "types.not_assignable");
  (let keep = Fixtures.Infer.keep in
   test "a type that holds no view is Storable" (fun () ->
       fine (keep ^ Fixtures.Infer.type_that_holds_no_view_is_storable));
   test "an any type is Storable when its trait requires Storable" (fun () ->
       fine (keep ^ Fixtures.Infer.any_type_is_storable_when_its_trait_requires));
   test "a trait that requires Storable cannot be implemented for a view type" (fun () ->
       one_diagnostic
         (keep ^ Fixtures.Infer.trait_that_requires_storable_cannot_be_implemented)
         "types.missing_required_impl");
   List.iter
     (fun (name, body) ->
       test name (fun () -> one_diagnostic (keep ^ body) "types.unsatisfied_bound"))
     [
       ("a slice is not Storable", Fixtures.Infer.slice_is_not_storable);
       ( "a record that holds a slice is not Storable",
         Fixtures.Infer.record_that_holds_a_slice_is_not_storable );
       ( "a generic type is not Storable where its argument is not",
         Fixtures.Infer.generic_type_is_not_storable_where_its_argument_is );
       ("a function type is not Storable", Fixtures.Infer.function_type_is_not_storable);
       ( "an any type is not Storable when its trait does not require it",
         Fixtures.Infer.any_type_is_not_storable_when_its_trait_does_not );
       ( "a type parameter is Storable only when it is bounded",
         Fixtures.Infer.type_parameter_is_storable_only_when_it_is_bounded );
     ];
   test "no impl of Storable can be written" (fun () ->
       one_diagnostic (keep ^ "impl Storable for Labeled {}\n") "types.implements_built_in"));
  test "the body of a concurrent block gets its types" (fun () ->
      has_type Fixtures.Infer.body_of_a_concurrent_block_gets_its_types "2" "UInt16");
  test "a lambda's captures are the outer locals it reads" (fun () ->
      let text = Fixtures.Infer.lambdas_captures_are_the_outer_locals_it_reads in
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match node.kind with Lambda { captures; _ } -> Some captures | _ -> None)
          (first_core_nodes text).expressions
      with
      | [ [ _ ] ] -> ()
      | [ actual ] -> fail "%d captures" (List.length actual)
      | actual -> fail "%d lambdas" (List.length actual))

(* Strings and collections *)

let () =
  test "an interpolated value must implement Display" (fun () ->
      one_diagnostic Fixtures.Infer.interpolated_value_must_implement_display "types.no_impl");
  test "an array literal must have its type's length" (fun () ->
      one_diagnostic Fixtures.Infer.array_literal_must_have_its_types_length "types.mismatch");
  test "a list literal is a set where a set is expected" (fun () ->
      fine Fixtures.Infer.list_literal_is_a_set_where_a_set_is_expected)

(* Specifications *)

let () =
  test "integer arithmetic in a specification is exact" (fun () ->
      has_type Fixtures.Infer.integer_arithmetic_in_a_specification_is_exact "a + b" "Integer");
  test "comparisons in a specification may mix integer types" (fun () ->
      fine Fixtures.Infer.comparisons_in_a_specification_may_mix_integer);
  test "a lambda in a specification may give a built-in integer for an Integer" (fun () ->
      fine Fixtures.Infer.lambda_in_a_specification_may_give_a_built_in)

(* Loops *)

let () =
  test "a for loop over a range of integers is a counted loop" (fun () ->
      let text = Fixtures.Infer.for_loop_over_a_range_of_integers_is_a_counted in
      if
        not
          (List.exists
             (fun (node : Core.statement) ->
               match node.kind with For { iteration = Integer_range _; _ } -> true | _ -> false)
             (first_core_nodes text).statements)
      then fail "no counted loop");
  test "a for loop over a list drives its each" (fun () ->
      fine Fixtures.Infer.for_loop_over_a_list_drives_its_each)

(* Incremental work and determinism *)

let () =
  test "editing a function's body re-checks no caller" (fun () ->
      let text body =
        "fn callee() -> Int64 { " ^ body ^ " }\n\nfn caller() -> Int64 {\n  callee()\n}\n"
      in
      let database = setup [ ("app::main", text "1") ] in
      let engine = Engine.of_context database in
      let module_ = module_of "app::main" in
      expect_not_recomputed engine
        ~first:(fun () -> ignore (Infer.diagnostics database module_))
        ~again:(fun () ->
          Database.Testing.set_text engine module_ (text "2");
          ignore (Infer.diagnostics database module_))
        Infer.type_check_result
        [ top_key "app::main" "caller" ]);
  test "checking twice gives the same result" (fun () ->
      let text = Fixtures.Infer.checking_twice_gives_the_same_result in
      let type_check_result () =
        let database = setup [ ("app::main", text) ] in
        let key =
          Resolve.Names.key_of
            (List.hd (Query.demand database Resolve.Names.declarations (module_of "app::main")))
        in
        Query.demand database Infer.type_check_result key
      in
      if type_check_result () <> type_check_result () then fail "different")

let () =
  test "no table of the standard library holds a type inference left unsolved" (fun () ->
      let database = setup [] in
      List.iter
        (fun ((module_ : Path.module_), _) ->
          List.iter
            (fun (declaration : Resolve.Names.declaration) ->
              match
                Query.demand database Infer.type_check_result (Resolve.Names.key_of declaration)
              with
              | Some { tables; _ } ->
                  List.iter
                    (Array.iter (function
                      | Some type_
                        when Types.exists
                               (function Variable _ | Literal _ -> true | _ -> false)
                               type_ ->
                          fail "%s: an unsolved type" (Path.show declaration.path)
                      | _ -> ()))
                    [ tables.types; tables.local_types ]
              | None -> ())
            (Query.demand database Resolve.Names.declarations module_))
        Standard_library.modules)

(* What the review of body checking found *)

let point = "type Point(x: Int64)\n\n"

let () =
  test "a call's type arguments must meet their bounds" (fun () ->
      one_diagnostic
        (point ^ Fixtures.Infer.calls_type_arguments_must_meet_their_bounds)
        "types.unsatisfied_bound");
  test "a type written in a body must meet its bounds" (fun () ->
      let database =
        setup [ ("app::main", point ^ Fixtures.Infer.type_written_in_a_body_must_meet_its_bounds) ]
      in
      match codes (check database (module_of "app::main")) with
      | [ "types.unsatisfied_bound"; "types.unsatisfied_bound" ] -> ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
  test "a type written in a body that is not a type is an error" (fun () ->
      one_diagnostic Fixtures.Infer.type_written_in_a_body_that_is_not_a_type_is_an
        "types.not_a_type");
  test "an operator's result must be the type expected of it" (fun () ->
      one_diagnostic Fixtures.Infer.operators_result_must_be_the_type_expected_of_it
        "types.mismatch");
  test "an array length nothing decides is an error" (fun () ->
      one_diagnostic Fixtures.Infer.array_length_nothing_decides_is_an_error "types.cannot_infer");
  test "a qualified constant in a pattern must have the matched type" (fun () ->
      one_diagnostic Fixtures.Infer.qualified_constant_in_a_pattern_must_have_the "types.mismatch");
  test "the alternatives of a pattern bind each name with one type" (fun () ->
      one_diagnostic Fixtures.Infer.alternatives_of_a_pattern_bind_each_name_with_one
        "types.mismatch");
  test "a pattern must match every field or write .." (fun () ->
      one_diagnostic Fixtures.Infer.pattern_must_match_every_field_or_write "types.missing_argument");
  test "an opaque type cannot be matched outside its package" (fun () ->
      one_diagnostic Fixtures.Infer.opaque_type_cannot_be_matched_outside_its_package
        "types.private_field");
  test "a bitwise compound assignment works on integers only" (fun () ->
      one_diagnostic Fixtures.Infer.bitwise_compound_assignment_works_on_integers_only
        "types.no_impl");
  test "a method written in full takes its receiver's mark" (fun () ->
      one_diagnostic Fixtures.Infer.method_written_in_full_takes_its_receivers_mark
        "types.wrong_receiver");
  test "a for loop takes each version from the type or from a trait" (fun () ->
      fine Fixtures.Infer.for_loop_takes_each_version_from_the_type_or_from);
  test "a call picks a version among a type's own and its family of traits'" (fun () ->
      fine Fixtures.Infer.call_picks_a_version_among_a_types_own_and_its);
  test "two traits that give one version of a name are ambiguous at the call" (fun () ->
      one_diagnostic Fixtures.Infer.two_traits_that_give_one_version_of_a_name_are
        "types.ambiguous_method"
        ~fixed:Fixtures.Infer.two_traits_that_give_one_version_of_a_name_are_fixed);
  test "two unrelated traits that share a name are ambiguous however each takes self" (fun () ->
      one_diagnostic Fixtures.Infer.two_unrelated_traits_that_share_a_name_are
        "types.ambiguous_method");
  test "two bounds that give one version of a name are ambiguous through the type" (fun () ->
      one_diagnostic Fixtures.Infer.two_bounds_that_give_one_version_of_a_name_are
        "types.ambiguous_method");
  test "two unrelated bounds that share a name are ambiguous however each takes self" (fun () ->
      one_diagnostic Fixtures.Infer.two_unrelated_bounds_that_share_a_name_are
        "types.ambiguous_method");
  test "a bound's method is picked from its family by how the call takes self" (fun () ->
      fine Fixtures.Infer.bounds_method_is_picked_from_its_family_by_how_the);
  test "a trait's method written in full has no version for a mark it lacks" (fun () ->
      one_diagnostic Fixtures.Infer.traits_method_written_in_full_has_no_version_for_a
        "types.wrong_receiver");
  test "an associated type of an argument is normalized" (fun () ->
      fine Fixtures.Infer.associated_type_of_an_argument_is_normalized);
  test "a literal receiver has its default type" (fun () ->
      has_type Fixtures.Infer.literal_receiver_has_its_default_type "5.wrapping_add(3)" "Int64");
  test "a for loop over characters counts" (fun () ->
      fine Fixtures.Infer.for_loop_over_characters_counts);
  test "an operation on a hole is a hole" (fun () ->
      fine Fixtures.Infer.operation_on_a_hole_is_a_hole);
  test "a loop variable's type comes from the loop's header" (fun () ->
      one_diagnostic Fixtures.Infer.loop_variables_type_comes_from_the_loops_header "types.mismatch");
  test "a mistake is not reported again as a type that cannot be inferred" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Infer.mistake_is_not_reported_again_as_a_type_that) ]
      in
      if List.mem "types.cannot_infer" (codes (check database (module_of "app::main"))) then
        fail "cascaded");
  test "a Float32 literal too large is an error" (fun () ->
      one_diagnostic Fixtures.Infer.float32_literal_too_large_is_an_error
        "types.literal_out_of_range");
  test "a Float32 literal is rounded once, from its decimal" (fun () ->
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match node.kind with Float rounded -> Some rounded | _ -> None)
          (first_core_nodes Fixtures.Infer.float32_literal_is_rounded_once_from_its_decimal)
            .expressions
      with
      | [ rounded ] ->
          if rounded <> Float.of_string "0x1.000002p+0" then fail "rounded to %h" rounded
      | _ -> fail "no value");
  test "a range pattern has the values of its two bounds" (fun () ->
      match
        List.filter_map
          (fun (node : Core.pattern) ->
            match node.kind with
            | Range { start = { kind = Integer low; _ }; stop = { kind = Integer high; _ }; _ } ->
                Some (Z.to_int low, Z.to_int high)
            | _ -> None)
          (first_core_nodes Fixtures.Infer.range_pattern_has_the_values_of_its_two_bounds).patterns
      with
      | [ (1, 5) ] -> ()
      | _ -> fail "the range pattern does not have the bounds 1 and 5");
  test "a range pattern on a type that is not an integer or Character is an error" (fun () ->
      one_diagnostic Fixtures.Infer.range_pattern_on_a_type_that_is_not_an_integer_or
        "types.mismatch");
  test "an integer range on a type that is not ordered is one error" (fun () ->
      one_diagnostic Fixtures.Infer.integer_range_on_a_type_that_is_not_ordered_is_one
        "types.mismatch");
  test "a range pattern on Character is fine" (fun () ->
      fine Fixtures.Infer.range_pattern_on_character_is_fine);
  test "a Character literal is a tagged string holding its scalar value" (fun () ->
      has_type Fixtures.Infer.character_literal_is_a_tagged_string_holding_its "Character\"é\""
        "Character";
      if not (has_integer Fixtures.Infer.character_literal_is_a_tagged_string_holding_its 0xE9) then
        fail "no value");
  test "a UInt8 literal holds its ASCII character's value" (fun () ->
      if not (has_integer Fixtures.Infer.uint8_literal_holds_its_ascii_characters_value 10) then
        fail "no value");
  test "a Character literal of two scalar values is an error" (fun () ->
      one_diagnostic Fixtures.Infer.character_literal_of_two_scalar_values_is_an_error
        "types.character_scalar_count");
  test "a UInt8 literal of a character that is not ASCII is an error" (fun () ->
      one_diagnostic Fixtures.Infer.uint8_literal_of_a_character_that_is_not_ascii_is
        "types.character_scalar_count");
  test "a negated literal of an unsigned type is one error" (fun () ->
      one_diagnostic Fixtures.Infer.negated_literal_of_an_unsigned_type_is_one_error
        "types.negated_unsigned");
  test "explicit type arguments give exactly the function's own" (fun () ->
      one_diagnostic Fixtures.Infer.explicit_type_arguments_give_exactly_the_functions "types.arity");
  test "a missing label has no fix when which one is meant is not known" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Infer.missing_label_has_no_fix_when_which_one_is_meant) ]
      in
      List.iter
        (fun (diagnostic : Diagnostic.t) -> if diagnostic.fixes <> [] then fail "offered a fix")
        (check database (module_of "app::main")));
  test "the string + fix keeps escapes" (fun () ->
      one_diagnostic Fixtures.Infer.string_fix_keeps_escapes "types.string_addition"
        ~fixed:Fixtures.Infer.string_fix_keeps_escapes_fixed);
  test "a lambda cannot mutate a captured variable" (fun () ->
      one_diagnostic Fixtures.Infer.lambda_cannot_mutate_a_captured_variable "types.not_assignable")

(* Specifications on loops and on function-typed parameters *)

let () =
  test "a function-typed parameter's requires is a Bool over its inputs" (fun () ->
      fine Fixtures.Infer.function_typed_parameters_requires_is_a_bool_over);
  test "a function-typed parameter's requires must be a Bool" (fun () ->
      one_diagnostic Fixtures.Infer.function_typed_parameters_requires_must_be_a_bool
        "types.mismatch");
  test "a trait method without a body has its clauses checked" (fun () ->
      one_diagnostic Fixtures.Infer.trait_method_without_a_body_has_its_clauses "types.no_impl");
  test "==> in a compiled body" (fun () ->
      one_diagnostic Fixtures.Infer.in_a_compiled_body "types.specification_only");
  test "a quantifier over a type in a compiled body" (fun () ->
      one_diagnostic Fixtures.Infer.quantifier_over_a_type_in_a_compiled_body
        "types.specification_only");
  test "a function for specifications only has a specification for a body" (fun () ->
      fine Fixtures.Infer.function_for_specifications_only_has_a);
  test "a constant in a pattern needs structural equality" (fun () ->
      one_diagnostic Fixtures.Infer.constant_in_a_pattern_needs_structural_equality
        "types.not_structural");
  test "a constant of a derived type of integers in a pattern" (fun () ->
      fine Fixtures.Infer.constant_of_a_derived_type_of_integers_in_a);
  test "a provided method without a time clause cannot be replaced" (fun () ->
      Support.one_diagnostic ~check:Type_checker.diagnostics
        Fixtures.Infer.provided_method_without_a_time_clause_cannot_be "types.not_replaceable");
  test "a loop's cost bound is checked" (fun () ->
      one_diagnostic Fixtures.Infer.loops_cost_bound_is_checked "resolve.unknown_name")

(* Every error type carries its report, so nothing is accepted of code that
   reported nothing: what was once an error with no report is reported. *)

let identity = Fixtures.Infer.identity

let () =
  test "type arguments after a parenthesized name are read as after the name" (fun () ->
      fine (identity ^ Fixtures.Infer.type_arguments_after_a_parenthesized_name_are_read);
      one_diagnostic
        (identity ^ Fixtures.Infer.type_arguments_after_a_parenthesized_name_are_read_2)
        "types.mismatch");
  test "a parenthesized name with type arguments is a value of that function" (fun () ->
      fine (identity ^ Fixtures.Infer.parenthesized_name_with_type_arguments_is_a_value));
  test "a trait's written arguments are the ones its call uses" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Infer.traits_written_arguments_are_the_ones_its_call) ]
      in
      if not (List.mem "types.no_impl" (codes (check database (module_of "app::main")))) then
        fail "the written argument was ignored");
  test "a literal is the receiver of a trait method written in full" (fun () ->
      fine Fixtures.Infer.literal_is_the_receiver_of_a_trait_method_written);
  test "a generic parameter takes no type arguments" (fun () ->
      one_diagnostic Fixtures.Infer.generic_parameter_takes_no_type_arguments "types.arity");
  test "a member of a generic parameter that it does not have is an error" (fun () ->
      one_diagnostic Fixtures.Infer.member_of_a_generic_parameter_that_it_does_not
        "types.unknown_member");
  test "a type with no fields is not its own value" (fun () ->
      one_diagnostic Fixtures.Infer.type_with_no_fields_is_not_its_own_value "types.not_a_value");
  test "`self` outside a method is an error" (fun () ->
      one_diagnostic Fixtures.Infer.self_outside_a_method_is_an_error "types.not_a_value");
  test "`old` without what it is about is an error" (fun () ->
      one_diagnostic Fixtures.Infer.old_without_what_it_is_about_is_an_error "types.not_a_value");
  test "a type argument that nothing decides is an error at its call" (fun () ->
      one_diagnostic Fixtures.Infer.type_argument_that_nothing_decides_is_an_error_at
        "types.cannot_infer");
  test "a trait is not called" (fun () ->
      one_diagnostic Fixtures.Infer.trait_is_not_called "types.not_callable");
  test "a generic function given type arguments, as a value, must meet its bounds" (fun () ->
      one_diagnostic
        (point ^ Fixtures.Infer.generic_function_given_type_arguments_as_a_value)
        "types.unsatisfied_bound");
  test "the scrutinee of an `is` is inferred before its pattern is checked" (fun () ->
      fine Fixtures.Infer.scrutinee_of_an_is_is_inferred_before_its_pattern);
  test "a `for` over a call of `each` binds the yielded elements" (fun () ->
      fine Fixtures.Infer.for_over_a_call_of_each_binds_the_yielded_elements);
  test "`Self` in the body of a method without `self` is the method's type" (fun () ->
      fine Fixtures.Infer.self_in_the_body_of_a_method_without_self_is_the);
  test "a pattern that does not fit its type still gives its bindings a type" (fun () ->
      one_diagnostic Fixtures.Infer.pattern_that_does_not_fit_its_type_still_gives_its
        "types.unknown_variant");
  test "a `todo` that nothing decides keeps the hole type in the tables" (fun () ->
      has_type Fixtures.Infer.todo_that_nothing_decides_keeps_the_hole_type_in "todo"
        "an undecided type")

(* Bounds wherever generic parameters are filled in *)

let shape = Fixtures.Infer.shape
let source = Fixtures.Infer.source

let () =
  test "a value built of a generic type must meet the type's bounds" (fun () ->
      one_diagnostic
        (shape ^ Fixtures.Infer.value_built_of_a_generic_type_must_meet_the_types)
        "types.unsatisfied_bound");
  test "a value built of a generic type that meets its bounds is fine" (fun () ->
      fine (shape ^ Fixtures.Infer.value_built_of_a_generic_type_that_meets_its));
  test "a value built inside another must meet its type's bounds" (fun () ->
      one_diagnostic
        (shape ^ Fixtures.Infer.value_built_inside_another_must_meet_its_types)
        "types.unsatisfied_bound");
  test "a variant built of a generic type must meet the type's bounds" (fun () ->
      one_diagnostic
        (shape ^ Fixtures.Infer.variant_built_of_a_generic_type_must_meet_the)
        "types.unsatisfied_bound");
  test "a generic type named in an expression must meet its bounds" (fun () ->
      one_diagnostic
        (shape ^ Fixtures.Infer.generic_type_named_in_an_expression_must_meet_its)
        "types.unsatisfied_bound");
  test "a statement reports a bound once, however many of its parts need it" (fun () ->
      one_diagnostic
        (shape ^ Fixtures.Infer.statement_reports_a_bound_once_however_many_of_its)
        "types.unsatisfied_bound");
  test "a method used as a value must meet its bounds" (fun () ->
      one_diagnostic
        (shape ^ Fixtures.Infer.method_used_as_a_value_must_meet_its_bounds)
        "types.unsatisfied_bound");
  test "function types that count the calls of different capabilities are different types"
    (fun () ->
      let lists counted =
        "fn take(runs: List[(fn() uses Clock, Console cost calls(Console) <= 1)]) {}\n\n\
         fn f(runs: List[(fn() uses Clock, Console cost calls(" ^ counted
        ^ ") <= 1)]) {\n  take(runs)\n}\n"
      in
      fine (lists "Console");
      one_diagnostic (lists "Clock") "types.mismatch";
      one_diagnostic (lists "Console.print_line") "types.mismatch");
  test "the target of `calls` in a function type is a capability or one of its methods" (fun () ->
      one_diagnostic Fixtures.Infer.target_of_calls_in_a_function_type_is_a_capability
        "types.not_a_capability";
      one_diagnostic "fn f(run: (fn() uses Clock cost calls(Clock.later) <= 1)) {}\n"
        "types.unknown_member";
      one_diagnostic "fn f(visit: fn(), run: (fn() cost calls(visit) <= 1)) {}\n"
        "types.not_a_capability");
  test
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
  test "a method with generic parameters is not object-safe" (fun () ->
      one_diagnostic Fixtures.Infer.method_with_generic_parameters_is_not_object_safe
        "types.not_callable");
  test "a method that takes or returns Self cannot be called through any" (fun () ->
      one_diagnostic Fixtures.Infer.method_that_takes_or_returns_self_cannot_be_called
        "types.not_callable");
  test "a method whose result holds Self cannot be called through any" (fun () ->
      one_diagnostic Fixtures.Infer.method_whose_result_holds_self_cannot_be_called
        "types.not_callable");
  test "a cursor's own step and its counting can be called through any" (fun () ->
      fine Fixtures.Infer.cursors_own_step_and_its_counting_can_be_called);
  test "a method that names an associated type can be called through any" (fun () ->
      fine (source ^ Fixtures.Infer.method_that_names_an_associated_type_can_be_called));
  test "`any value` must give the associated types its type fixes" (fun () ->
      one_diagnostic
        (source ^ Fixtures.Infer.any_value_must_give_the_associated_types_its_type)
        "types.no_impl");
  test "`any value` that gives the associated types its type fixes is fine" (fun () ->
      fine (source ^ Fixtures.Infer.any_value_that_gives_the_associated_types_its_type));
  test "`any value` of a generic parameter needs a bound that fixes the associated types" (fun () ->
      one_diagnostic
        (source ^ Fixtures.Infer.any_value_of_a_generic_parameter_needs_a_bound)
        "types.no_impl");
  test "`any value` of a generic parameter whose bound fixes the associated types is fine"
    (fun () -> fine (source ^ Fixtures.Infer.any_value_of_a_generic_parameter_whose_bound_fixes));
  test "an associated type a bound fixes works out a type argument" (fun () ->
      fine (source ^ Fixtures.Infer.associated_type_a_bound_fixes_works_out_a_type));
  test "an associated type a bound fixes must be the one the impl gives" (fun () ->
      one_diagnostic
        (source ^ Fixtures.Infer.associated_type_a_bound_fixes_must_be_the_one_the)
        "types.unsatisfied_bound")

(* Constant expressions *)

let point = "type Point(x: Int64, y: Int64)\n\n"

let () =
  test "a constant is built from literals, operators on numbers, and other constants" (fun () ->
      fine Fixtures.Infer.constant_is_built_from_literals_operators_on);
  test "a constant builds records, variants, and collections of constants" (fun () ->
      fine (point ^ Fixtures.Infer.constant_builds_records_variants_and_collections));
  test "a constant cannot call a function" (fun () ->
      one_diagnostic Fixtures.Infer.constant_cannot_call_a_function "types.not_constant");
  test "a constant cannot call a capability" (fun () ->
      one_diagnostic "let started: Instant = Clock.now()\n" "types.not_constant");
  test "a constant cannot call a method" (fun () ->
      one_diagnostic "let length: USize = \"four\".length()\n" "types.not_constant");
  test "a constant cannot index a collection" (fun () ->
      one_diagnostic Fixtures.Infer.constant_cannot_index_a_collection "types.not_constant");
  test "a constant cannot branch" (fun () ->
      one_diagnostic "let chosen: Int64 = if true { 1 } else { 2 }\n" "types.not_constant");
  test "a constant cannot use an operator that a type defines" (fun () ->
      one_diagnostic Fixtures.Infer.constant_cannot_use_an_operator_that_a_type "types.not_constant");
  test "a constant's arithmetic must stay within its type" (fun () ->
      one_diagnostic "let size: USize = 0 - 1\n" "types.constant_overflow");
  test "each step of a constant's arithmetic must stay within its type" (fun () ->
      one_diagnostic "let small: UInt8 = 200 + 100 - 100\n" "types.constant_overflow");
  test "a constant's arithmetic through another constant must stay within its type" (fun () ->
      one_diagnostic Fixtures.Infer.constants_arithmetic_through_another_constant_must
        "types.constant_overflow");
  test "negating a constant's least value overflows" (fun () ->
      one_diagnostic "let flipped: Int8 = -(-128)\n" "types.constant_overflow");
  test "a constant cannot divide by zero" (fun () ->
      one_diagnostic "let nothing: Int64 = 5 / 0\n" "types.constant_overflow");
  test "a default must be a constant expression" (fun () ->
      one_diagnostic Fixtures.Infer.default_must_be_a_constant_expression
        "types.default_not_constant");
  test "a default cannot name a parameter" (fun () ->
      one_diagnostic "fn f(count: Int64, twice: Int64 = count * 2) {}\n"
        "types.default_not_constant");
  test "a method's default must be a constant expression" (fun () ->
      one_diagnostic
        (point ^ Fixtures.Infer.methods_default_must_be_a_constant_expression)
        "types.default_not_constant");
  test "a field's default must be a constant expression" (fun () ->
      one_diagnostic Fixtures.Infer.fields_default_must_be_a_constant_expression
        "types.default_not_constant");
  test "a field's default's arithmetic must stay within its type" (fun () ->
      one_diagnostic "type Settings(retries: UInt8 = 250 + 10)\n" "types.constant_overflow")

(* The body of a transparent function *)

let () =
  let transparent body =
    Printf.sprintf
      "public transparent fn shown(value: Int64) -> Int64\n  cost time O(1)\n{\n  %s\n}\n" body
  in
  let helper visibility =
    Printf.sprintf "%sfn half(value: Int64) -> Int64\n  cost time O(1)\n{\n  value - 1\n}\n\n"
      visibility
  in
  test "a transparent body calls only functions that other packages can call" (fun () ->
      one_diagnostic (helper "internal " ^ transparent "half(value)") "types.private_in_public";
      one_diagnostic (helper "" ^ transparent "half(value)") "types.private_in_public";
      fine (helper "public " ^ transparent "half(value)");
      fine (helper "public transparent " ^ transparent "half(value) + value"));
  test "a transparent body names only constants that other packages can name" (fun () ->
      one_diagnostic
        ("internal let limit: Int64 = 10\n\n" ^ transparent "value + limit")
        "types.private_in_public";
      fine ("public let limit: Int64 = 10\n\n" ^ transparent "value + limit"));
  test "a transparent body calls only public methods, and can read a hidden field" (fun () ->
      let meter visibility =
        Printf.sprintf
          "public opaque type Meter(reading: Int64)\n\n\
          \           %sfn Meter.raw(self) -> Int64\n\
          \            cost time O(1)\n\
          \           {\n\
          \            self.reading\n\
          \           }\n\n\
          \           public transparent fn Meter.shown(self) -> Int64\n\
          \            cost time O(1)\n\
          \           {\n\
          \            self.raw() + self.reading\n\
          \           }\n"
          visibility
      in
      one_diagnostic (meter "internal ") "types.private_in_public";
      fine (meter "public "));
  test "a public contract names only functions that other packages can call" (fun () ->
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
        (sorted "internal " ^ sort "public " "ensures in_order(items)")
        "types.private_in_public";
      one_diagnostic
        (sorted "" ^ sort "public " "requires in_order(items)")
        "types.private_in_public";
      fine (sorted "public " ^ sort "public " "ensures in_order(items)");
      fine (sorted "internal " ^ sort "internal " "ensures in_order(items)");
      fine (sorted "" ^ sort "" "ensures in_order(items)"));
  test "a public contract names only constants that other packages can name" (fun () ->
      let capped visibility =
        Printf.sprintf
          "%slet limit: Int64 = 10\n\n\
           public fn capped(value: Int64) -> Int64\n\
          \  ensures result <= limit\n\
           {\n\
          \  todo\n\
           }\n"
          visibility
      in
      one_diagnostic (capped "internal ") "types.private_in_public";
      fine (capped "public "));
  test
    "the contract of a public trait's method and of its impl's method names only public functions"
    (fun () ->
      let helper = Fixtures.Infer.helper in
      one_diagnostic
        (helper ^ Fixtures.Infer.contract_of_a_public_traits_method_and_of_its)
        "types.private_in_public";
      fine (helper ^ Fixtures.Infer.contract_of_a_public_traits_method_and_of_its_2);
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
      one_diagnostic (implemented "public ") "types.private_in_public";
      fine (implemented "internal "));
  test "a function that is not transparent can call a function that other packages cannot"
    (fun () ->
      fine (helper "internal " ^ Fixtures.Infer.function_that_is_not_transparent_can_call_a))
