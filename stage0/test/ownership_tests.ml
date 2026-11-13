(* The tests of moves, loans, and views. *)

open Harness
open Support

let check = Type_checker.For_testing.through Ownership
let one_diagnostic = one_diagnostic ~check
let fine text = no_diagnostics ~check [ ("app::main", text) ]
let keep = Fixtures.Ownership.keep

(* Writing through a slice *)

let () =
  let bump = Fixtures.Ownership.bump in
  List.iter
    (fun (place, text) ->
      test (place ^ " cannot be written through a slice") (fun () ->
          one_diagnostic (bump ^ text) "ownership.read_only_view"))
    [
      ("a read-only parameter", Fixtures.Ownership.read_only_parameter);
      ("a constant", Fixtures.Ownership.constant);
      ("a `let`", Fixtures.Ownership.let_);
      ("the place a slice in a field views", Fixtures.Ownership.place_a_slice_in_a_field_views);
    ];
  test "a `var` and a `mut` parameter can be written through a slice" (fun () ->
      fine (bump ^ Fixtures.Ownership.var_and_a_mut_parameter_can_be_written_through_a))

(* The operands of one operation *)

let () =
  let functions = Fixtures.Ownership.functions in
  let rejected name body code =
    test name (fun () ->
        one_diagnostic (functions ^ "fn f(items: mut List[Int64]) {\n" ^ body ^ "}\n") code)
  in
  rejected "a view cannot be passed after a `mut` borrow of the place that it views"
    "  var part = items.slice()\n  take(mut items, view: part)\n" "ownership.conflicting_loan";
  rejected "a view cannot be passed before a `mut` borrow of the place that it views"
    "  var part = items.slice()\n  give(part, items: mut items)\n" "ownership.conflicting_loan";
  rejected "a slice of a place cannot be passed with a `mut` borrow of the place"
    "  take(mut items, view: items[..1])\n" "ownership.conflicting_loan";
  test
    "a view of another place, and a value copied out of the place, can be passed with its `mut` \
     borrow" (fun () ->
      fine (functions ^ Fixtures.Ownership.view_of_another_place_and_a_value_copied_out_of));
  rejected "a later argument cannot mutate a place that an earlier argument borrows"
    "  show(items[0], count: grow(mut items))\n" "ownership.changed_while_viewed";
  rejected "a later argument cannot mutate a place that an earlier argument borrows `mut`"
    "  change(mut items[0], count: grow(mut items))\n" "ownership.changed_while_viewed";
  rejected "a later argument cannot mutate the place that an earlier argument views"
    "  count_of(items[..1], count: grow(mut items))\n" "ownership.changed_while_viewed";
  rejected "a later argument cannot mutate the place that an earlier view argument views"
    "  var part = items.slice()\n  count_of(part, count: grow(mut items))\n"
    "ownership.changed_while_viewed";
  rejected "an index key cannot mutate the indexed collection" "  let _ = items[grow(mut items)]\n"
    "ownership.changed_while_viewed";
  rejected "a slice bound cannot mutate the sliced collection"
    "  let _ = items[..grow(mut items)]\n" "ownership.changed_while_viewed";
  test "a later field cannot mutate the place that an earlier field views" (fun () ->
      one_diagnostic
        (functions ^ Fixtures.Ownership.later_field_cannot_mutate_the_place_that_an)
        "ownership.changed_while_viewed");
  test "the fields of a constructor are evaluated in the order written" (fun () ->
      fine (functions ^ Fixtures.Ownership.fields_of_a_constructor_are_evaluated_in_the_order));
  test "an operand that is a copy does not borrow its place" (fun () ->
      fine (functions ^ Fixtures.Ownership.operand_that_is_a_copy_does_not_borrow_its_place))

(* A yielded constructor that lends places *)

let () =
  let shelf = Fixtures.Ownership.shelf in
  let lends name signature body = shelf ^ "fn Shelf." ^ name ^ signature ^ " {\n" ^ body ^ "}\n" in
  test "a yielded constructor lends a place without a mark" (fun () ->
      fine
        (lends "get" "(self, index: USize) lends Option[String]"
           "  if index < self.books.length() {\n\
           \    yield Some(self.books[index])\n\
           \  } else {\n\
           \    yield None\n\
           \  }\n"
        ^ Fixtures.Ownership.yielded_constructor_lends_a_place_without_a_mark));
  test "a constructor nested in a yielded constructor lends places too" (fun () ->
      fine
        (lends "first" "(self) lends Option[First]"
           "  yield Some(First(title: self.books[0], rest: self.books[1..]))\n"));
  test "a yielded constructor that lends no place owns its fields" (fun () ->
      fine
        (lends "copied" "(self) lends Tagged"
           "  yield Tagged(tag: \"new\".copy(), book: self.books[0].copy())\n"));
  test "a `Plain` place in a yielded constructor is copied, so it lends nothing" (fun () ->
      fine
        (lends "numbered" "(self, index: USize) lends Numbered"
           "  yield Numbered(index: index, title: self.books[index].copy())\n"));
  test "a local is a place that a yielded constructor lends" (fun () ->
      fine
        (lends "tagged" "(self) lends Tagged"
           "  let tag = \"new\".copy()\n  yield Tagged(tag: tag, book: self.books[0])\n"));
  test "a yielded constructor that lends a place cannot hold an owned value" (fun () ->
      one_diagnostic
        (lends "tagged" "(self) lends Tagged"
           "  yield Tagged(tag: \"new\".copy(), book: self.books[0])\n")
        "ownership.owned_beside_lent");
  test "a place lent `mut` inside a variant is rejected" (fun () ->
      one_diagnostic
        (lends "first" "(mut self) lends mut Option[String]" "  yield Some(mut self.books[0])\n")
        "ownership.lent_mut_in_variant");
  test "a place lent `mut` inside a record inside a variant is rejected" (fun () ->
      one_diagnostic
        (lends "first" "(mut self) yields mut Option[Numbered]"
           "  yield Some(Numbered(index: 0, title: mut self.books[0]))\n")
        "ownership.lent_mut_in_variant");
  test "a constructor yielded `mut` lends the places marked `mut`" (fun () ->
      fine
        (lends "numbered" "(mut self) yields mut Numbered"
           "  var index: USize = 0\n\
           \  while index < self.books.length() {\n\
           \    yield Numbered(index: index, title: mut self.books[index])\n\
           \    index = index + 1\n\
           \  }\n"
        ^ Fixtures.Ownership.constructor_yielded_mut_lends_the_places_marked));
  test "a place in a constructor yielded `mut` needs the `mut` mark" (fun () ->
      one_diagnostic
        (lends "numbered" "(mut self) lends mut Numbered"
           "  yield Numbered(index: 0, title: self.books[0])\n")
        "types.missing_mark");
  test "a place in a constructor yielded read-only takes no `mut` mark" (fun () ->
      one_diagnostic
        (lends "numbered" "(self) lends Numbered"
           "  yield Numbered(index: 0, title: mut self.books[0])\n")
        "types.redundant_mark");
  test "a yielded constructor is not lent one place `mut` twice" (fun () ->
      one_diagnostic
        (lends "both" "(mut self) lends mut Both"
           "  yield Both(first: mut self.books, second: mut self.books)\n")
        "ownership.conflicting_loan");
  test "a method that yields a constructor of lent places cannot be pulled" (fun () ->
      one_diagnostic
        (lends "numbered" "(self) yields Numbered"
           "  var index: USize = 0\n\
           \  while index < self.books.length() {\n\
           \    yield Numbered(index: index, title: self.books[index])\n\
           \    index = index + 1\n\
           \  }\n"
        ^ Fixtures.Ownership.method_that_yields_a_constructor_of_lent_places)
        "ownership.not_pullable")

(* Lambdas that capture *)

let () =
  let helpers = Fixtures.Ownership.helpers in
  let rejected name body code = test name (fun () -> one_diagnostic (helpers ^ body) code) in
  let accepted name body = test name (fun () -> fine (helpers ^ body)) in
  rejected "a lambda that captures a parameter cannot be returned"
    Fixtures.Ownership.lambda_that_captures_a_parameter_cannot_be "ownership.view_escapes";
  rejected "a lambda that captures a local cannot be returned"
    Fixtures.Ownership.lambda_that_captures_a_local_cannot_be_returned "ownership.view_escapes";
  rejected "a capturing lambda cannot be returned through a local"
    Fixtures.Ownership.capturing_lambda_cannot_be_returned_through_a "ownership.view_escapes";
  rejected "a record that stores a capturing lambda cannot be returned"
    Fixtures.Ownership.record_that_stores_a_capturing_lambda_cannot_be "ownership.view_escapes";
  rejected "a capturing lambda cannot be stored in a `mut` parameter"
    Fixtures.Ownership.capturing_lambda_cannot_be_stored_in_a_mut "ownership.view_escapes";
  rejected "a capturing lambda cannot be passed with a `mut` parameter that holds a function"
    Fixtures.Ownership.capturing_lambda_cannot_be_passed_with_a_mut "ownership.view_escapes";
  (* A slice is a view, but no part of it holds a function, so the callee
     cannot store the lambda in it. *)
  accepted "a capturing lambda can be passed with a `mut` slice parameter"
    Fixtures.Ownership.capturing_lambda_can_be_passed_with_a_mut_slice;
  rejected "a capturing lambda cannot be passed with a `mut` slice of functions"
    Fixtures.Ownership.capturing_lambda_cannot_be_passed_with_a_mut_slice "ownership.view_escapes";
  rejected
    "a lambda that returns a view of its capture cannot be passed with a `mut` slice of views"
    Fixtures.Ownership.lambda_that_returns_a_view_of_its_capture_cannot "ownership.view_escapes";
  rejected "a capturing lambda cannot be passed to an `own` function-typed parameter"
    Fixtures.Ownership.capturing_lambda_cannot_be_passed_to_an_own "ownership.view_escapes";
  rejected
    "a function value that is not owned cannot be passed to an `own` function-typed parameter"
    Fixtures.Ownership.function_value_that_is_not_owned_cannot_be_passed "ownership.view_escapes";
  (* A generic [own] parameter is not declared with a function type, so the
     view rules track a capturing lambda that is passed to one. *)
  accepted
    "a capturing lambda can be stored in a local list and passed to a generic `own` parameter"
    Fixtures.Ownership.capturing_lambda_can_be_stored_in_a_local_list_and;
  rejected "a list that stores a capturing lambda cannot be returned"
    Fixtures.Ownership.list_that_stores_a_capturing_lambda_cannot_be "ownership.view_escapes";
  rejected "a capturing lambda returned through a generic `own` parameter cannot be returned"
    Fixtures.Ownership.capturing_lambda_returned_through_a_generic_own "ownership.view_escapes";
  accepted "a function that captures nothing can be returned, stored, and moved"
    Fixtures.Ownership.function_that_captures_nothing_can_be_returned;
  accepted "a capturing lambda can be passed to a call and stored in a local record"
    Fixtures.Ownership.capturing_lambda_can_be_passed_to_a_call_and

(* Values that refer to a place, and values taken out of one *)

let () =
  let types = Fixtures.Ownership.types in
  let rejected name body code = test name (fun () -> one_diagnostic (types ^ body) code) in
  let accepted name body = test name (fun () -> fine (types ^ body)) in
  rejected "a borrow of a value that owns data and stores a view views the value"
    Fixtures.Ownership.borrow_of_a_value_that_owns_data_and_stores_a_view
    "ownership.changed_while_viewed";
  rejected "a slice of a part of a value that owns data and stores a view views the value"
    Fixtures.Ownership.slice_of_a_part_of_a_value_that_owns_data_and
    "ownership.changed_while_viewed";
  rejected "a borrow of an `own` parameter cannot be returned"
    Fixtures.Ownership.borrow_of_an_own_parameter_cannot_be_returned "ownership.view_escapes";
  accepted "a view copied out of an `own` parameter can be returned"
    Fixtures.Ownership.view_copied_out_of_an_own_parameter_can_be;
  rejected "an `any` that stores a view of a local cannot be returned"
    Fixtures.Ownership.any_that_stores_a_view_of_a_local_cannot_be "ownership.view_escapes";
  rejected "the place that an `any` views cannot be mutated while the `any` is live"
    Fixtures.Ownership.place_that_an_any_views_cannot_be_mutated_while
    "ownership.changed_while_viewed";
  accepted "an `any` made from owned data can be returned"
    Fixtures.Ownership.any_made_from_owned_data_can_be_returned;
  rejected "a capturing lambda cannot be returned as a wider function type"
    Fixtures.Ownership.capturing_lambda_cannot_be_returned_as_a_wider "ownership.view_escapes";
  rejected "the value of an `if` has the views of its branches' tail expressions"
    Fixtures.Ownership.value_of_an_if_has_the_views_of_its_branches_tail
    "ownership.changed_while_viewed";
  rejected "the value of a `match` has the views of its arms' tail expressions"
    Fixtures.Ownership.value_of_a_match_has_the_views_of_its_arms_tail
    "ownership.changed_while_viewed";
  rejected "the value of a block has the views of its tail expression"
    Fixtures.Ownership.value_of_a_block_has_the_views_of_its_tail "ownership.changed_while_viewed";
  rejected "a view of a local cannot be returned through an `if` and a local"
    Fixtures.Ownership.view_of_a_local_cannot_be_returned_through_an_if "ownership.view_escapes";
  rejected "a copy of a view has the same views"
    Fixtures.Ownership.copy_of_a_view_has_the_same_views "ownership.changed_while_viewed";
  rejected "a record built by `with` has the views of its new fields"
    Fixtures.Ownership.record_built_by_with_has_the_views_of_its_new
    "ownership.changed_while_viewed";
  rejected "a view copied out of a loop variable views the collection that the loop iterates over"
    Fixtures.Ownership.view_copied_out_of_a_loop_variable_views_the "ownership.changed_while_viewed";
  accepted "a `Plain` loop variable is a copy, so the collection can be mutated after the loop"
    Fixtures.Ownership.plain_loop_variable_is_a_copy_so_the_collection;
  rejected "a place cannot be mutated while a `match` binding of it is live"
    Fixtures.Ownership.place_cannot_be_mutated_while_a_match_binding_of
    "ownership.changed_while_viewed";
  accepted "a place can be mutated in an arm once the `match` bindings are dead"
    Fixtures.Ownership.place_can_be_mutated_in_an_arm_once_the_match

(* Views that a method yields *)

let () =
  let reader = "type Reader(buffer: List[Int64])\n\n" in
  let rejected name body code = test name (fun () -> one_diagnostic (reader ^ body) code) in
  let accepted name body = test name (fun () -> fine (reader ^ body)) in
  rejected "a yielding method cannot yield a view of its local"
    Fixtures.Ownership.yielding_method_cannot_yield_a_view_of_its_local "ownership.view_escapes";
  rejected "a lending method cannot lend a view of its local"
    Fixtures.Ownership.lending_method_cannot_lend_a_view_of_its_local "ownership.view_escapes";
  accepted "a method can yield a view of `self`, and lend a local itself"
    Fixtures.Ownership.method_can_yield_a_view_of_self_and_lend_a_local;
  (let chunks = Fixtures.Ownership.chunks in
   rejected
     "a view from one iteration of a loop that borrows `mut` cannot be used in a later iteration"
     (chunks ^ Fixtures.Ownership.view_from_one_iteration_of_a_loop_that_borrows_mut)
     "ownership.changed_while_viewed";
   accepted "a view from an iteration of a loop that borrows `mut` can be used in that iteration"
     (chunks ^ Fixtures.Ownership.view_from_an_iteration_of_a_loop_that_borrows_mut));
  accepted "a view from a loop over a read-only source can be used after the loop"
    Fixtures.Ownership.view_from_a_loop_over_a_read_only_source_can_be

(* A place given to a [provide] block *)

let () =
  let counter = Fixtures.Ownership.counter in
  test "the body of a `provide` cannot use a place that the block borrows `mut`" (fun () ->
      one_diagnostic
        (counter ^ Fixtures.Ownership.body_of_a_provide_cannot_use_a_place_that_the)
        "ownership.conflicting_loan");
  test "the body of a `provide` cannot mutate a place that the block borrows" (fun () ->
      one_diagnostic
        (counter ^ Fixtures.Ownership.body_of_a_provide_cannot_mutate_a_place_that_the)
        "ownership.changed_while_viewed");
  test "the body of a `provide` can read a place that the block borrows read-only" (fun () ->
      fine (counter ^ Fixtures.Ownership.body_of_a_provide_can_read_a_place_that_the_block));
  test "a place that a `provide` block borrows is usable again after the block" (fun () ->
      fine (counter ^ Fixtures.Ownership.place_that_a_provide_block_borrows_is_usable_again))

(* Views in the branches of a [parallel] block *)

let () =
  test "one branch of a `parallel` block cannot mutate the place that another branch's view views"
    (fun () ->
      one_diagnostic Fixtures.Ownership.one_branch_of_a_parallel_block_cannot_mutate_the
        "ownership.data_race");
  test "two branches of a `parallel` block can read through views of one place" (fun () ->
      fine Fixtures.Ownership.two_branches_of_a_parallel_block_can_read_through)

(* Views of a temporary through a copy and a record update *)

let () =
  let make = Fixtures.Ownership.make in
  test "a copy of a view of a temporary cannot be bound" (fun () ->
      one_diagnostic
        (make ^ Fixtures.Ownership.copy_of_a_view_of_a_temporary_cannot_be_bound)
        "ownership.views_temporary");
  test "a record built by `with` cannot store a view of a temporary" (fun () ->
      one_diagnostic
        (make ^ Fixtures.Ownership.record_built_by_with_cannot_store_a_view_of_a)
        "ownership.views_temporary")

(* Quantifiers in code that runs *)

let () =
  let grow = Fixtures.Ownership.grow in
  test "the body of an executable quantifier cannot mutate the collection that it iterates over"
    (fun () ->
      one_diagnostic
        (grow ^ Fixtures.Ownership.body_of_an_executable_quantifier_cannot_mutate_the)
        "ownership.changed_while_viewed");
  test "an executable quantifier reads the collection that it iterates over" (fun () ->
      fine Fixtures.Ownership.executable_quantifier_reads_the_collection_that_it)

(* The facts a place passed [mut] keeps *)

let () =
  let reader = Fixtures.Ownership.reader in
  test "a `mut` view argument does not store a view of a borrowed argument that is not a view"
    (fun () -> fine (reader ^ Fixtures.Ownership.mut_view_argument_does_not_store_a_view_of_a))

(* Cursors that a yielding method makes *)

let () =
  test "the `Cursor` trait's own methods are called on a yielding method's cursor" (fun () ->
      fine Fixtures.Ownership.cursor_traits_own_methods_are_called_on_a_yielding);
  test "a cursor that would copy its elements cannot be passed to generic code" (fun () ->
      one_diagnostic Fixtures.Ownership.cursor_that_would_copy_its_elements_cannot_be
        "ownership.not_pullable");
  test "a cursor that would copy its elements cannot be used through the trait's methods" (fun () ->
      one_diagnostic Fixtures.Ownership.cursor_that_would_copy_its_elements_cannot_be_used
        "ownership.not_pullable");
  test "a cursor over `Plain` elements can be passed to generic code" (fun () ->
      fine Fixtures.Ownership.cursor_over_plain_elements_can_be_passed_to)

(* Views and a capability's implementation *)

let () =
  let journal = Fixtures.Ownership.journal in
  let rejected name body code = test name (fun () -> one_diagnostic (journal ^ body) code) in
  rejected "a capability's implementation cannot store a view argument"
    Fixtures.Ownership.capabilitys_implementation_cannot_store_a_view
    "ownership.view_crosses_capability";
  rejected "a capability's method cannot return a view of the implementation's state"
    Fixtures.Ownership.capabilitys_method_cannot_return_a_view_of_the
    "ownership.view_crosses_capability";
  test "an implementation can store a copy and return a view that it was constructed with"
    (fun () ->
      fine (journal ^ Fixtures.Ownership.implementation_can_store_a_copy_and_return_a_view));
  test
    "a method outside a capability's `impl` can store a view argument and return a view of `self`"
    (fun () -> fine Fixtures.Ownership.method_outside_a_capabilitys_impl_can_store_a_view)

(* Views of a name that refers to a part of a parameter *)

let () =
  let url = "type Url(scheme: String, user: Option[String])\n\n" in
  let accepted name body = test name (fun () -> fine (url ^ body)) in
  accepted "a view of a `match` binding of a parameter can be returned"
    Fixtures.Ownership.view_of_a_match_binding_of_a_parameter_can_be;
  accepted "a view of an `is` binding of a parameter can be returned"
    Fixtures.Ownership.view_of_an_is_binding_of_a_parameter_can_be;
  accepted "a view of a `let` alias of a part of a parameter can be returned"
    Fixtures.Ownership.view_of_a_let_alias_of_a_part_of_a_parameter_can;
  accepted "a view of a loop variable over a parameter can be returned"
    Fixtures.Ownership.view_of_a_loop_variable_over_a_parameter_can_be;
  test "a view of a `match` binding of a local cannot be returned" (fun () ->
      one_diagnostic Fixtures.Ownership.view_of_a_match_binding_of_a_local_cannot_be
        "ownership.view_escapes");
  test "a place cannot be mutated while a view of its `match` binding is live" (fun () ->
      one_diagnostic Fixtures.Ownership.place_cannot_be_mutated_while_a_view_of_its_match
        "ownership.changed_while_viewed")

(* Concurrent code *)

let () =
  let helpers = Fixtures.Ownership.helpers_2 in
  let rejected ?says name body code =
    test name (fun () -> one_diagnostic ?says (helpers ^ body) code)
  in
  let accepted name body = test name (fun () -> fine (helpers ^ body)) in
  rejected "one branch of a `concurrent` block cannot mutate a place that another branch uses"
    ~says:"`concurrent` block" Fixtures.Ownership.one_branch_of_a_concurrent_block_cannot_mutate_a
    "ownership.data_race";
  rejected "an iteration of a `concurrent for` can mutate only its own element and locals"
    ~says:"`concurrent for`" Fixtures.Ownership.iteration_of_a_concurrent_for_can_mutate_only_its
    "ownership.data_race";
  rejected "a `concurrent` branch must reinitialize a place that it moves out of a `mut` borrow"
    Fixtures.Ownership.concurrent_branch_must_reinitialize_a_place_that
    "ownership.not_reinitialized";
  accepted "a `concurrent` branch can move a value out of a `mut` borrow and reinitialize it"
    Fixtures.Ownership.concurrent_branch_can_move_a_value_out_of_a_mut;
  rejected
    "a place moved out before a `concurrent` block must be reinitialized where a branch returns"
    Fixtures.Ownership.place_moved_out_before_a_concurrent_block_must_be
    "ownership.not_reinitialized";
  (* A [concurrent for] over a yielding method that does not yield by
     position: its body is not a single loop over a range. *)
  let pair = Fixtures.Ownership.pair in
  let rejected_loop name ~says method_ loop =
    test name (fun () ->
        one_diagnostic ~says
          (pair ^ method_ ^ "\nfn f(pair: mut Pair)\n  uses Tasks\n{\n" ^ loop ^ "}\n")
          "ownership.task_outlives_yield")
  in
  rejected_loop "a `concurrent for` cannot iterate over a method that yields `mut` borrows"
    ~says:"`mut` borrows" Fixtures.Ownership.concurrent_for_cannot_iterate_over_a_method_that
    "  concurrent for list in mut pair.each() {\n    look(list)\n  }\n";
  rejected_loop "a task cannot borrow a place inside a `mut` parameter of the yielding method"
    ~says:"`self.first`" Fixtures.Ownership.task_cannot_borrow_a_place_inside_a_mut_parameter
    "  concurrent for list in mut pair.each() {\n    look(list)\n  }\n";
  rejected_loop "a task cannot borrow a local of the yielding method" ~says:"`local`"
    Fixtures.Ownership.task_cannot_borrow_a_local_of_the_yielding_method
    "  concurrent for list in pair.each() {\n    look(list)\n  }\n";
  rejected_loop "a task cannot keep a view of a place inside a `mut` parameter" ~says:"`self.text`"
    Fixtures.Ownership.task_cannot_keep_a_view_of_a_place_inside_a_mut
    "  concurrent for word in mut pair.words() {\n    look(word)\n  }\n";
  test "a task can borrow and view places inside a read-only parameter" (fun () ->
      fine (pair ^ Fixtures.Ownership.task_can_borrow_and_view_places_inside_a_read_only));
  test "a `concurrent for` cannot iterate over a cursor of views" (fun () ->
      one_diagnostic ~says:"`Slice[Int64]` is a view"
        (pair ^ Fixtures.Ownership.concurrent_for_cannot_iterate_over_a_cursor_of)
        "ownership.task_outlives_yield");
  test "a `concurrent for` can iterate over owned values and Plain copies" (fun () ->
      fine (pair ^ Fixtures.Ownership.concurrent_for_can_iterate_over_owned_values_and));
  test "a `concurrent for` can iterate over a method that yields by position" (fun () ->
      fine (pair ^ Fixtures.Ownership.concurrent_for_can_iterate_over_a_method_that))

(* Guards *)

let () =
  let bump = Fixtures.Ownership.bump_2 in
  test "a guard cannot mutate the scrutinee" (fun () ->
      one_diagnostic
        (bump ^ Fixtures.Ownership.guard_cannot_mutate_the_scrutinee)
        "ownership.changed_while_viewed");
  test "a guard can mutate another place, and an arm's body can mutate the scrutinee" (fun () ->
      fine (bump ^ Fixtures.Ownership.guard_can_mutate_another_place_and_an_arms_body))

(* Constants *)

let () =
  let names = "let names: List[Int64] = [1, 2]\n\n" in
  let config = Fixtures.Ownership.config in
  List.iter
    (fun (construct, text, code) ->
      test (construct ^ " is an error") (fun () -> one_diagnostic text code))
    [
      ( "moving a constant with `own`",
        keep ^ names ^ Fixtures.Ownership.moving_a_constant_with_own,
        "ownership.not_owned" );
      ( "moving a field of a constant with `own`",
        keep ^ config ^ Fixtures.Ownership.moving_a_field_of_a_constant_with_own,
        "ownership.not_owned" );
      ( "passing a constant to an `own` parameter",
        keep ^ names ^ Fixtures.Ownership.passing_a_constant_to_an_own_parameter,
        "types.missing_mark" );
      ( "passing a type's constant to an `own` parameter",
        keep ^ config ^ Fixtures.Ownership.passing_a_types_constant_to_an_own_parameter,
        "types.missing_mark" );
      ( "binding a constant with `var`",
        names ^ Fixtures.Ownership.binding_a_constant_with_var,
        "ownership.needs_owned" );
      ( "binding a type's constant with `var`",
        config ^ Fixtures.Ownership.binding_a_types_constant_with_var,
        "ownership.needs_owned" );
      ( "returning a constant",
        names ^ Fixtures.Ownership.returning_a_constant,
        "ownership.needs_owned" );
    ];
  test "an owned value from a constant is a copy, with a fix" (fun () ->
      one_diagnostic
        (names ^ Fixtures.Ownership.owned_value_from_a_constant_is_a_copy_with_a_fix)
        "ownership.needs_owned"
        ~fixed:(names ^ Fixtures.Ownership.owned_value_from_a_constant_is_a_copy_with_a_fix_2));
  test "a constant can be read, viewed, copied, and returned as a view" (fun () ->
      fine (keep ^ names ^ Fixtures.Ownership.constant_can_be_read_viewed_copied_and_returned_as));
  let bag = Fixtures.Ownership.bag in
  test "a compound assignment's operand may change the target, because it runs first" (fun () ->
      fine (bag ^ Fixtures.Ownership.compound_assignments_operand_may_change_the_target));
  test "a compound assignment's borrowed operand cannot be changed by the target's index keys"
    (fun () ->
      one_diagnostic
        (bag ^ Fixtures.Ownership.compound_assignments_borrowed_operand_cannot_be)
        "ownership.changed_while_viewed")

let () =
  test "the default of a parameter of a view type views a value that lasts for the call" (fun () ->
      fine Fixtures.Ownership.default_of_a_parameter_of_a_view_type_views_a);
  test "a moved place cannot be used, with a fix that copies at the move" (fun () ->
      one_diagnostic
        (keep ^ Fixtures.Ownership.moved_place_cannot_be_used_with_a_fix_that_copies)
        "ownership.use_after_move"
        ~fixed:(keep ^ Fixtures.Ownership.moved_place_cannot_be_used_with_a_fix_that_copies_2));
  test "a tagged string moves its parts, and a plain string reads them" (fun () ->
      let shout = Fixtures.Ownership.shout in
      one_diagnostic
        (shout ^ Fixtures.Ownership.tagged_string_moves_its_parts_and_a_plain_string)
        "ownership.needs_owned";
      fine (shout ^ Fixtures.Ownership.tagged_string_moves_its_parts_and_a_plain_string_2);
      fine (shout ^ Fixtures.Ownership.tagged_string_moves_its_parts_and_a_plain_string_3);
      fine Fixtures.Ownership.tagged_string_moves_its_parts_and_a_plain_string_4);
  test "a `Plain` place is copied, not moved" (fun () ->
      fine Fixtures.Ownership.plain_place_is_copied_not_moved);
  test "a place moved on one path cannot be used after the paths join" (fun () ->
      one_diagnostic
        (keep ^ Fixtures.Ownership.place_moved_on_one_path_cannot_be_used_after_the)
        "ownership.use_after_move");
  test "a place moved in a loop is moved in the loop's next iteration" (fun () ->
      one_diagnostic
        (keep ^ Fixtures.Ownership.place_moved_in_a_loop_is_moved_in_the_loops_next)
        "ownership.use_after_move");
  test "a place is usable again once it is assigned" (fun () ->
      fine (keep ^ Fixtures.Ownership.place_is_usable_again_once_it_is_assigned));
  test "a field can be moved out by itself" (fun () ->
      fine Fixtures.Ownership.field_can_be_moved_out_by_itself);
  test "a read-only parameter cannot be moved" (fun () ->
      one_diagnostic
        (keep ^ Fixtures.Ownership.read_only_parameter_cannot_be_moved)
        "ownership.not_owned");
  test "a field moved out of a `mut` parameter must be reinitialized" (fun () ->
      one_diagnostic Fixtures.Ownership.field_moved_out_of_a_mut_parameter_must_be
        "ownership.not_reinitialized");
  test "a local that a value is moved into has no view of the moved place" (fun () ->
      fine Fixtures.Ownership.local_that_a_value_is_moved_into_has_no_view_of);
  (let holder = "type Holder(items: List[Int64], count: USize)\n\n" in
   let accepted name body = test name (fun () -> fine (holder ^ body)) in
   let rejected name body code = test name (fun () -> one_diagnostic (holder ^ body) code) in
   accepted "a field of a `mut` borrow can be moved out and reinitialized"
     Fixtures.Ownership.field_of_a_mut_borrow_can_be_moved_out_and;
   rejected "a field moved out of `mut self` must be reinitialized"
     Fixtures.Ownership.field_moved_out_of_mut_self_must_be_reinitialized
     "ownership.not_reinitialized";
   accepted "a `mut` borrow can be moved out whole and reinitialized"
     Fixtures.Ownership.mut_borrow_can_be_moved_out_whole_and;
   rejected "a `mut` borrow that is moved out whole must be reinitialized"
     Fixtures.Ownership.mut_borrow_that_is_moved_out_whole_must_be "ownership.not_reinitialized";
   rejected "a `mut` borrow must be reinitialized on every path"
     Fixtures.Ownership.mut_borrow_must_be_reinitialized_on_every_path "ownership.not_reinitialized";
   rejected "a `mut` borrow cannot be used while it is moved out"
     Fixtures.Ownership.mut_borrow_cannot_be_used_while_it_is_moved_out "ownership.use_after_move";
   accepted "a `mut` loop variable can be moved out and reinitialized in the iteration"
     Fixtures.Ownership.mut_loop_variable_can_be_moved_out_and;
   rejected "a `mut` loop variable that is moved out must be reinitialized in the iteration"
     Fixtures.Ownership.mut_loop_variable_that_is_moved_out_must_be "ownership.not_reinitialized";
   rejected "a `mut` binding of a `match` that is moved out must be reinitialized in the arm"
     Fixtures.Ownership.mut_binding_of_a_match_that_is_moved_out_must_be
     "ownership.not_reinitialized";
   rejected "a yielding method cannot yield while a place of its caller is moved out"
     Fixtures.Ownership.yielding_method_cannot_yield_while_a_place_of_its
     "ownership.not_reinitialized";
   accepted "a lending method can yield while a place of its caller is moved out"
     Fixtures.Ownership.lending_method_can_yield_while_a_place_of_its);
  test "one place cannot be borrowed `mut` twice by one call" (fun () ->
      one_diagnostic Fixtures.Ownership.one_place_cannot_be_borrowed_mut_twice_by_one_call
        "ownership.conflicting_loan");
  test "a place cannot be mutated while a view of it is live" (fun () ->
      one_diagnostic Fixtures.Ownership.place_cannot_be_mutated_while_a_view_of_it_is_live
        "ownership.changed_while_viewed");
  test "a place can be mutated once the view of it is dead" (fun () ->
      fine Fixtures.Ownership.place_can_be_mutated_once_the_view_of_it_is_dead);
  test "a function cannot return a view of its own local" (fun () ->
      one_diagnostic Fixtures.Ownership.function_cannot_return_a_view_of_its_own_local
        "ownership.view_escapes");
  test "a function cannot return a view of its local nested in a type nested in itself" (fun () ->
      one_diagnostic Fixtures.Ownership.function_cannot_return_a_view_of_its_local_nested
        "ownership.view_escapes");
  test "a function cannot return a view of its local stored as an associated type" (fun () ->
      one_diagnostic Fixtures.Ownership.function_cannot_return_a_view_of_its_local_stored
        "ownership.view_escapes");
  test "a function can return a view of its parameter" (fun () ->
      fine Fixtures.Ownership.function_can_return_a_view_of_its_parameter);
  test "a `var` needs an owned value, with fixes that move or copy the place" (fun () ->
      one_diagnostic Fixtures.Ownership.var_needs_an_owned_value_with_fixes_that_move_or
        "ownership.needs_owned"
        ~fixed:Fixtures.Ownership.var_needs_an_owned_value_with_fixes_that_move_or_fixed);
  test "an assigned value must be owned" (fun () ->
      one_diagnostic Fixtures.Ownership.assigned_value_must_be_owned "ownership.needs_owned"
        ~fixed:Fixtures.Ownership.assigned_value_must_be_owned_fixed);
  test "a map literal's keys and values must be owned" (fun () ->
      one_diagnostic Fixtures.Ownership.map_literals_keys_and_values_must_be_owned
        "ownership.needs_owned");
  test "a constant's value and a default may hold a constant without a copy" (fun () ->
      fine Fixtures.Ownership.constants_value_and_a_default_may_hold_a_constant);
  test "a list element needs an owned value" (fun () ->
      one_diagnostic Fixtures.Ownership.list_element_needs_an_owned_value "ownership.needs_owned");
  test "a lending method yields on every path" (fun () ->
      one_diagnostic Fixtures.Ownership.lending_method_yields_on_every_path "ownership.yield_count");
  (let bag = Fixtures.Ownership.bag_2 in
   test "a lending method can yield in a loop whose body then returns" (fun () ->
       fine (bag ^ Fixtures.Ownership.lending_method_can_yield_in_a_loop_whose_body_then));
   test "a lending method cannot yield before a loop whose body yields and returns" (fun () ->
       one_diagnostic
         (bag ^ Fixtures.Ownership.lending_method_cannot_yield_before_a_loop_whose)
         "ownership.yield_count");
   test "a lending method cannot yield after a loop that yields and breaks" (fun () ->
       one_diagnostic
         (bag ^ Fixtures.Ownership.lending_method_cannot_yield_after_a_loop_that)
         "ownership.yield_count");
   test "a lending method cannot yield on each iteration of a loop" (fun () ->
       one_diagnostic
         (bag ^ Fixtures.Ownership.lending_method_cannot_yield_on_each_iteration_of_a)
         "ownership.yield_count"));
  (let grid = "type Grid(cells: List[Int64], count: USize)\n\n" in
   test "a lending method can yield in one branch of a `parallel` block" (fun () ->
       fine (grid ^ Fixtures.Ownership.lending_method_can_yield_in_one_branch_of_a));
   test "a lending method cannot yield in two branches of a `parallel` block" (fun () ->
       one_diagnostic
         (grid ^ Fixtures.Ownership.lending_method_cannot_yield_in_two_branches_of_a)
         "ownership.yield_count"));
  test "a method that yields recursively cannot be pulled" (fun () ->
      one_diagnostic Fixtures.Ownership.method_that_yields_recursively_cannot_be_pulled
        "ownership.not_pullable");
  test "a cursor of a method that can be pulled is pulled" (fun () ->
      fine Fixtures.Ownership.cursor_of_a_method_that_can_be_pulled_is_pulled);
  test "a `parallel` branch cannot mutate a place that another branch uses" (fun () ->
      one_diagnostic Fixtures.Ownership.parallel_branch_cannot_mutate_a_place_that_another
        "ownership.data_race")

(* Methods *)

let () =
  let bag = "type Bag(items: List[Int64])\n\n" in
  test "an impl method's read-only parameter may be returned as a view" (fun () ->
      fine (bag ^ Fixtures.Ownership.impl_methods_read_only_parameter_may_be_returned));
  test "an impl method cannot move a read-only parameter" (fun () ->
      one_diagnostic
        (keep ^ bag ^ Fixtures.Ownership.impl_method_cannot_move_a_read_only_parameter)
        "ownership.not_owned");
  test "an impl method may move a field of an owned self" (fun () ->
      fine (bag ^ Fixtures.Ownership.impl_method_may_move_a_field_of_an_owned_self));
  test "a trait's method with a body is checked too" (fun () ->
      one_diagnostic
        (keep ^ Fixtures.Ownership.traits_method_with_a_body_is_checked_too)
        "ownership.not_owned")

(* Loans held for a stretch of code *)

let () =
  test "a loop body cannot mutate the collection that the loop iterates over, even inside a branch"
    (fun () ->
      one_diagnostic Fixtures.Ownership.loop_body_cannot_mutate_the_collection_that_the
        "ownership.changed_while_viewed");
  test "a loop body cannot borrow `mut` the collection that the loop iterates over" (fun () ->
      one_diagnostic Fixtures.Ownership.loop_body_cannot_borrow_mut_the_collection_that
        "ownership.changed_while_viewed");
  test "a `parallel for` cannot borrow `mut` a place from outside the loop" (fun () ->
      one_diagnostic Fixtures.Ownership.parallel_for_cannot_borrow_mut_a_place_from
        "ownership.data_race");
  test "a `parallel for` cannot assign a place from outside the loop, even inside a branch"
    (fun () ->
      one_diagnostic Fixtures.Ownership.parallel_for_cannot_assign_a_place_from_outside
        "ownership.data_race");
  test "a `parallel for` can mutate its own element and locals" (fun () ->
      fine Fixtures.Ownership.parallel_for_can_mutate_its_own_element_and_locals);
  test "a call cannot take a view of a place that another argument moves" (fun () ->
      one_diagnostic Fixtures.Ownership.call_cannot_take_a_view_of_a_place_that_another
        "ownership.changed_while_viewed");
  test "a Plain place passed own is copied, so the call may use it twice" (fun () ->
      fine Fixtures.Ownership.plain_place_passed_own_is_copied_so_the_call_may)

(* Pulling and lending *)

let () =
  let tree = Fixtures.Ownership.tree in
  test "a method that yields recursively inside a branch cannot be pulled" (fun () ->
      one_diagnostic
        (tree ^ Fixtures.Ownership.method_that_yields_recursively_inside_a_branch)
        "ownership.not_pullable");
  test "mutually recursive yielding methods cannot be pulled" (fun () ->
      one_diagnostic
        (tree ^ Fixtures.Ownership.mutually_recursive_yielding_methods_cannot_be)
        "ownership.not_pullable");
  test "a call's result does not view a `Plain` argument" (fun () ->
      fine Fixtures.Ownership.calls_result_does_not_view_a_plain_argument);
  test "a diverging path of a lending method need not yield" (fun () ->
      fine Fixtures.Ownership.diverging_path_of_a_lending_method_need_not_yield)

(* Views of temporaries *)

let () =
  let same = Fixtures.Ownership.same in
  test "a cursor cannot view a temporary that the statement drops" (fun () ->
      one_diagnostic
        (same ^ Fixtures.Ownership.cursor_cannot_view_a_temporary_that_the_statement)
        "ownership.views_temporary");
  test "a cursor may view a named value" (fun () ->
      fine (same ^ Fixtures.Ownership.cursor_may_view_a_named_value));
  test "a cursor may view a string literal, which has static storage" (fun () ->
      fine (same ^ Fixtures.Ownership.cursor_may_view_a_string_literal_which_has_static));
  test "a slice cannot view a temporary list" (fun () ->
      one_diagnostic Fixtures.Ownership.slice_cannot_view_a_temporary_list
        "ownership.views_temporary");
  test "a value computed from a temporary's view is fine" (fun () ->
      fine Fixtures.Ownership.value_computed_from_a_temporarys_view_is_fine)

(* Pulling views of places *)

let () =
  test "pulling a view of a String element is an error" (fun () ->
      one_diagnostic Fixtures.Ownership.pulling_a_view_of_a_string_element_is_an_error
        "ownership.not_pullable");
  test "a `for` loop over a stored cursor of `String` elements is an error too" (fun () ->
      one_diagnostic Fixtures.Ownership.for_loop_over_a_stored_cursor_of_string_elements
        "ownership.not_pullable");
  test "a method that yields owned values can be pulled whatever its element" (fun () ->
      fine Fixtures.Ownership.method_that_yields_owned_values_can_be_pulled);
  test "a for loop over a marked call drives the method, not a cursor" (fun () ->
      fine Fixtures.Ownership.for_loop_over_a_marked_call_drives_the_method_not);
  test "a recursive mut walk may loop over itself" (fun () ->
      fine Fixtures.Ownership.recursive_mut_walk_may_loop_over_itself);
  test "looping over a method that yields views of String elements is fine" (fun () ->
      fine Fixtures.Ownership.looping_over_a_method_that_yields_views_of_string)

let () =
  test "is on a temporary binds its parts as owned, as match does" (fun () ->
      fine Fixtures.Ownership.is_on_a_temporary_binds_its_parts_as_owned_as);
  test "a let of a marked call's result binds it owned" (fun () ->
      fine Fixtures.Ownership.let_of_a_marked_calls_result_binds_it_owned);
  test "is on a place binds views of its parts" (fun () ->
      one_diagnostic Fixtures.Ownership.is_on_a_place_binds_views_of_its_parts "ownership.not_owned")

let () =
  let make = Fixtures.Ownership.make_2 in
  test "a binding inside a loop is a new one each time, so it may be moved" (fun () ->
      fine (make ^ Fixtures.Ownership.binding_inside_a_loop_is_a_new_one_each_time_so_it));
  test "an `is` binding of a `while` condition may be moved in every iteration" (fun () ->
      fine (make ^ Fixtures.Ownership.is_binding_of_a_while_condition_may_be_moved_in));
  test "an is binding in an if inside a loop may be moved" (fun () ->
      fine (make ^ Fixtures.Ownership.is_binding_in_an_if_inside_a_loop_may_be_moved));
  test "a let-else binding inside a loop may be moved" (fun () ->
      fine (make ^ Fixtures.Ownership.let_else_binding_inside_a_loop_may_be_moved));
  (* The body runs only where the whole condition is true, so where [text]
     was bound again. *)
  test "an `is` binding after `&&` in a `while` condition may be moved in every iteration"
    (fun () ->
      fine (make ^ Fixtures.Ownership.is_binding_after_and_in_a_while_condition_may_be_moved))

(* The lends of an [if] or a [while] condition *)

let () =
  test "a `Plain` name that an `if` condition binds is a copy, which views nothing" (fun () ->
      fine Fixtures.Ownership.copy_bound_by_an_if_condition_does_not_view_the);
  test "the then-block may mutate the lender when the condition binds only copies" (fun () ->
      fine Fixtures.Ownership.then_block_may_mutate_the_lender_when_the_condition);
  test "a name bound before a test after `&&` fails ends with the part it aliases" (fun () ->
      fine Fixtures.Ownership.name_bound_before_a_false_test_ends_with_the);
  test "the else-block may mutate the lender" (fun () ->
      fine Fixtures.Ownership.else_block_may_mutate_the_lender);
  test
    "the then-block cannot mutate the lender while a name the condition binds aliases the lent part"
    (fun () ->
      one_diagnostic Fixtures.Ownership.then_block_cannot_mutate_the_lender_while_a_name_the
        "ownership.changed_while_viewed");
  test
    "a `while` body cannot mutate the lender while a name the condition binds aliases the lent part"
    (fun () ->
      one_diagnostic Fixtures.Ownership.while_body_cannot_mutate_the_lender_while_a_name_the
        "ownership.changed_while_viewed")

(* The prover's part *)

(* How many [Disjoint] obligations a definition leaves to the prover. *)
let disjoint_obligations text =
  let database = setup [ ("app::main", text) ] in
  let file = file_of "app::main" in
  List.fold_left
    (fun total declaration ->
      match Query.demand database Ownership.ownership (Resolve.Names.key_of declaration) with
      | Some result -> total + List.length result.Ownership.disjoint
      | None -> total)
    0
    (Query.demand database Resolve.Names.declarations_in file)

let () =
  test "two slices of one list borrowed by one call produce a `Disjoint` obligation" (fun () ->
      let actual =
        disjoint_obligations Fixtures.Ownership.two_slices_of_one_list_borrowed_by_one_call
      in
      if actual <> 1 then fail "%d obligations" actual);
  test "`parallel` branches that mutate two elements produce a `Disjoint` obligation" (fun () ->
      let actual =
        disjoint_obligations Fixtures.Ownership.parallel_branches_that_mutate_two_elements_produce
      in
      if actual <> 1 then fail "%d obligations" actual);
  test "a `mut` slice argument that may alias a view argument produces a `Disjoint` obligation"
    (fun () ->
      let actual =
        disjoint_obligations Fixtures.Ownership.mut_slice_argument_that_may_alias_a_view_argument
      in
      if actual <> 1 then fail "%d obligations" actual);
  test "a `mut` element argument that may alias a view argument produces a `Disjoint` obligation"
    (fun () ->
      let actual =
        disjoint_obligations Fixtures.Ownership.mut_element_argument_that_may_alias_a_view
      in
      if actual <> 1 then fail "%d obligations" actual)

(* Lending: a call of a lending method is a part, lent for the rest of the
   statement, and the place it is lent from is lent whole for as long. *)

let grid = Fixtures.Ownership.grid
let counter = Fixtures.Ownership.counter_2
let tally = Fixtures.Ownership.tally

let () =
  test "a part lent `mut` is changed through its `mut self` method, with no mark of its own"
    (fun () -> fine (grid ^ Fixtures.Ownership.part_lent_mut_is_changed_through_its_mut_self));
  test "a part lent `mut` is assigned to" (fun () ->
      fine (grid ^ Fixtures.Ownership.part_lent_mut_is_assigned_to));
  test "a part lent read-only is not assigned to" (fun () ->
      one_diagnostic
        (grid ^ Fixtures.Ownership.part_lent_read_only_is_not_assigned_to)
        "types.not_assignable");
  test "a part lent read-only is not passed `mut`" (fun () ->
      one_diagnostic
        (grid ^ Fixtures.Ownership.part_lent_read_only_is_not_passed_mut)
        "types.wrong_mark");
  test "a lent part cannot be moved" (fun () ->
      one_diagnostic (grid ^ Fixtures.Ownership.lent_part_cannot_be_moved) "types.missing_mark");
  test "a lent part cannot be returned" (fun () ->
      one_diagnostic (grid ^ Fixtures.Ownership.lent_part_cannot_be_returned) "ownership.not_owned");
  test "a `let` cannot bind a lent part" (fun () ->
      one_diagnostic
        (grid ^ Fixtures.Ownership.let_cannot_bind_a_lent_part)
        "ownership.keeps_lent_part");
  test "a `let` copies a `Plain` lent part" (fun () ->
      fine (counter ^ Fixtures.Ownership.let_copies_a_plain_lent_part));
  test "a `match` on a lent part binds views of it, which cannot be moved" (fun () ->
      one_diagnostic
        (grid ^ Fixtures.Ownership.match_on_a_lent_part_binds_views_of_it_which)
        "ownership.not_owned");
  test
    "a lending call borrows its whole receiver, so two parts cannot be lent `mut` in one statement"
    (fun () ->
      one_diagnostic
        (grid ^ Fixtures.Ownership.lending_call_borrows_its_whole_receiver_so_two)
        "ownership.conflicting_loan");
  test "a place and a part that it lends `mut` cannot be passed to one call" (fun () ->
      one_diagnostic
        (grid ^ Fixtures.Ownership.place_and_a_part_that_it_lends_mut_cannot_be)
        "ownership.changed_while_viewed");
  test "a receiver that a lending call borrows read-only cannot be mutated in the same statement"
    (fun () ->
      one_diagnostic
        (tally ^ Fixtures.Ownership.receiver_that_a_lending_call_borrows_read_only)
        "ownership.changed_while_viewed");
  test "two parts of a place are lent read-only in one statement" (fun () ->
      fine (tally ^ Fixtures.Ownership.two_parts_of_a_place_are_lent_read_only_in_one));
  test "a lending call's loan ends with its statement" (fun () ->
      fine (grid ^ Fixtures.Ownership.lending_calls_loan_ends_with_its_statement));
  test "a loan started in a `while` condition ends before the loop body" (fun () ->
      fine (counter ^ Fixtures.Ownership.loan_started_in_a_while_condition_ends_before_the));
  test "two indexes of a user-defined collection cannot be lent `mut` in one statement" (fun () ->
      one_diagnostic
        (tally ^ Fixtures.Ownership.two_indexes_of_a_user_defined_collection_cannot_be)
        "ownership.conflicting_loan");
  test "two `mut` indexes of a list in one call produce a `Disjoint` obligation" (fun () ->
      fine Fixtures.Ownership.two_mut_indexes_of_a_list_in_one_call_produce_a)

(* Values that come to hold a view *)

let window = "type Window(view: Slice[Int64])\n\n"

let () =
  test "a `mut` list argument stores the call's view arguments" (fun () ->
      one_diagnostic Fixtures.Ownership.mut_list_argument_stores_the_calls_view_arguments
        "ownership.changed_while_viewed");
  test "the views stored in a `mut` list argument end when the list is dead" (fun () ->
      fine Fixtures.Ownership.views_stored_in_a_mut_list_argument_end_when_the);
  test "a `mut` argument of a function stores the function's view arguments" (fun () ->
      one_diagnostic Fixtures.Ownership.mut_argument_of_a_function_stores_the_functions
        "ownership.changed_while_viewed");
  test "a view stored in a place inside a branch is still stored after the branch" (fun () ->
      one_diagnostic Fixtures.Ownership.view_stored_in_a_place_inside_a_branch_is_still
        "ownership.changed_while_viewed");
  test "a record whose field is assigned a view has the value's views" (fun () ->
      one_diagnostic
        (window ^ Fixtures.Ownership.record_whose_field_is_assigned_a_view_has_the)
        "ownership.changed_while_viewed");
  test "a `mut` argument cannot store a view of a temporary" (fun () ->
      one_diagnostic Fixtures.Ownership.mut_argument_cannot_store_a_view_of_a_temporary
        "ownership.views_temporary");
  test "a view of a local cannot be stored in a `mut` parameter" (fun () ->
      one_diagnostic Fixtures.Ownership.view_of_a_local_cannot_be_stored_in_a_mut
        "ownership.view_escapes");
  test "a view argument can be stored in a `mut` parameter" (fun () ->
      fine Fixtures.Ownership.view_argument_can_be_stored_in_a_mut_parameter);
  test "a view of a borrowed parameter that is not a view cannot be stored in a `mut` parameter"
    (fun () ->
      one_diagnostic Fixtures.Ownership.view_of_a_borrowed_parameter_that_is_not_a_view
        "ownership.view_escapes");
  test "a place that a `mut` parameter views cannot be mutated in the rest of the function"
    (fun () ->
      one_diagnostic Fixtures.Ownership.place_that_a_mut_parameter_views_cannot_be_mutated
        "ownership.changed_while_viewed");
  test "a `mut self` method cannot store a view of a local in `self`" (fun () ->
      one_diagnostic
        (window ^ Fixtures.Ownership.mut_self_method_cannot_store_a_view_of_a_local_in)
        "ownership.view_escapes");
  test "a `mut self` method can store a view argument in `self`" (fun () ->
      fine (window ^ Fixtures.Ownership.mut_self_method_can_store_a_view_argument_in_self));
  test
    "a `mut self` method cannot store in `self` a view of a borrowed parameter that is not a view"
    (fun () ->
      one_diagnostic
        (window ^ Fixtures.Ownership.mut_self_method_cannot_store_in_self_a_view_of_a)
        "ownership.view_escapes");
  test "a `mut self` method cannot make `self` self-referential" (fun () ->
      one_diagnostic Fixtures.Ownership.mut_self_method_cannot_make_self_self_referential
        "ownership.self_referential");
  test "the receiver of a `mut self` method stores the method's view arguments" (fun () ->
      one_diagnostic
        (window ^ Fixtures.Ownership.receiver_of_a_mut_self_method_stores_the_methods)
        "ownership.changed_while_viewed");
  test "a call's result views its `mut` arguments" (fun () ->
      one_diagnostic Fixtures.Ownership.calls_result_views_its_mut_arguments
        "ownership.changed_while_viewed");
  test "a function cannot return a view of an `own` parameter" (fun () ->
      one_diagnostic Fixtures.Ownership.function_cannot_return_a_view_of_an_own_parameter
        "ownership.view_escapes");
  test "a function can return a view that it received as an `own` argument" (fun () ->
      fine Fixtures.Ownership.function_can_return_a_view_that_it_received_as_an);
  test "a function can return a local that views its parameter" (fun () ->
      fine Fixtures.Ownership.function_can_return_a_local_that_views_its);
  test "a function can return a record that views its parameter" (fun () ->
      fine (window ^ Fixtures.Ownership.function_can_return_a_record_that_views_its));
  test "a function cannot return a local that views its local" (fun () ->
      one_diagnostic Fixtures.Ownership.function_cannot_return_a_local_that_views_its
        "ownership.view_escapes")

(* Short-circuit operators *)

let () =
  let take = Fixtures.Ownership.take in
  let moved_twice operator condition =
    test (operator ^ " may have evaluated its right operand") (fun () ->
        one_diagnostic
          (take
          ^ Printf.sprintf
              "fn f(flag: Bool, box: own Box) -> Bool {\n\
              \  let first = %s\n\
              \  first && take(own box)\n\
               }\n"
              condition)
          "ownership.use_after_move")
  in
  moved_twice "`&&`" "flag && take(own box)";
  moved_twice "`||`" "flag || take(own box)";
  moved_twice "a negated `&&`" "!(flag && take(own box))";
  test "an operand that is evaluated last sees the moves of the operands before it" (fun () ->
      one_diagnostic
        (take ^ Fixtures.Ownership.operand_that_is_evaluated_last_sees_the_moves_of)
        "ownership.use_after_move";
      one_diagnostic
        (take ^ Fixtures.Ownership.operand_that_is_evaluated_last_sees_the_moves_of_2)
        "ownership.use_after_move");
  test "a move in the right operand is the only move of the place" (fun () ->
      fine (take ^ Fixtures.Ownership.move_in_the_right_operand_is_the_only_move_of_the);
      fine (take ^ Fixtures.Ownership.move_in_the_right_operand_is_the_only_move_of_the_2));
  test "the moves in a chain of thousands of `&&` are checked" (fun () ->
      let chain = String.concat " && " (List.init 4000 (fun _ -> "flag")) in
      one_diagnostic
        (take
        ^ Printf.sprintf
            "fn f(flag: Bool, box: own Box) -> Bool {\n  %s && take(own box) && take(own box)\n}\n"
            chain)
        "ownership.use_after_move")
