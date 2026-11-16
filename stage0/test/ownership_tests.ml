let check packages =
  Database.For_testing.list_diagnostics
    [ Resolve; Interface; Infer; Patterns; Usage; Ownership ]
    (Support.database packages)

let one_diagnostic = Support.one_diagnostic ~check
let fine text = Support.no_diagnostics ~check [ ("app::main", text) ]
let keep = Fixtures.Ownership.keep

let () =
  let bump = Fixtures.Ownership.bump in
  List.iter
    (fun (place, text) ->
      Harness.test (place ^ " cannot be written through a slice") (fun () ->
          one_diagnostic (bump ^ text) "ownership.read_only_view"))
    [
      ("a read-only parameter", Fixtures.Ownership.slice_of_a_read_only_parameter_bumped);
      ("a constant", Fixtures.Ownership.slice_of_a_constant_list);
      ("a `let`", Fixtures.Ownership.slice_of_a_let_list_assigned);
      ("the place a slice in a field views", Fixtures.Ownership.window_rest_bumped);
    ];
  Harness.test "a `var` and a `mut` parameter can be written through a slice" (fun () ->
      fine (bump ^ Fixtures.Ownership.writes_through_slices_of_a_var_and_a_mut_parameter));
  Harness.test "a read-only `Slice` parameter cannot be written through" (fun () ->
      one_diagnostic Fixtures.Ownership.read_only_slice_written "types.not_assignable")

let () =
  let functions = Fixtures.Ownership.functions in
  let rejected name body code =
    Harness.test name (fun () ->
        one_diagnostic (functions ^ "fn f(items: mut List[Int64]) {\n" ^ body ^ "}\n") code)
  in
  rejected "a view cannot be passed after a `mut` borrow of the place that it views"
    "  var part = items.slice()\n  take(mut items, view: part)\n" "ownership.conflicting_loan";
  rejected "a view cannot be passed before a `mut` borrow of the place that it views"
    "  var part = items.slice()\n  give(part, items: mut items)\n" "ownership.conflicting_loan";
  rejected "a slice of a place cannot be passed with a `mut` borrow of the place"
    "  take(mut items, view: items[..1])\n" "ownership.conflicting_loan";
  Harness.test
    "a view of another place, and a value copied out of the place, can be passed with its `mut` \
     borrow" (fun () -> fine (functions ^ Fixtures.Ownership.take_and_measure_of_a_mut_list));
  rejected "a later argument cannot mutate a place that an earlier argument borrows"
    "  show(items[0], count: grow(mut items))\n" "ownership.mutated_while_viewed";
  rejected "a later argument cannot mutate a place that an earlier argument borrows `mut`"
    "  change(mut items[0], count: grow(mut items))\n" "ownership.mutated_while_viewed";
  rejected "a later argument cannot mutate the place that an earlier argument views"
    "  count_of(items[..1], count: grow(mut items))\n" "ownership.mutated_while_viewed";
  rejected "a later argument cannot mutate the place that an earlier view argument views"
    "  var part = items.slice()\n  count_of(part, count: grow(mut items))\n"
    "ownership.mutated_while_viewed";
  rejected "an index key cannot mutate the indexed collection" "  let _ = items[grow(mut items)]\n"
    "ownership.mutated_while_viewed";
  rejected "a slice bound cannot mutate the sliced collection"
    "  let _ = items[..grow(mut items)]\n" "ownership.mutated_while_viewed";
  Harness.test "a later field cannot mutate the place that an earlier field views" (fun () ->
      one_diagnostic
        (functions ^ Fixtures.Ownership.counted_built_with_view_first)
        "ownership.mutated_while_viewed");
  Harness.test "the fields of a constructor are evaluated in the order written" (fun () ->
      fine (functions ^ Fixtures.Ownership.counted_built_with_count_first));
  Harness.test "an operand that is a copy does not borrow its place" (fun () ->
      fine (functions ^ Fixtures.Ownership.copied_operand_beside_a_bump))

let () =
  let shelf = Fixtures.Ownership.shelf in
  let lends name signature body = shelf ^ "fn Shelf." ^ name ^ signature ^ " {\n" ^ body ^ "}\n" in
  Harness.test "a lent constructor lends a place without a mode keyword" (fun () ->
      fine
        (lends "get" "(self, index: UInt64) lends Option[String]"
           "  if index < self.books.length() {\n\
           \    Some(self.books[index])\n\
           \  } else {\n\
           \    None\n\
           \  }\n"
        ^ Fixtures.Ownership.shelf_title_matched));
  Harness.test "a constructor nested in a lent constructor lends places too" (fun () ->
      fine
        (lends "first" "(self) lends Option[First]"
           "  Some(First(title: self.books[0], rest: self.books[1..]))\n"));
  Harness.test "a lent constructor that lends no place owns its fields" (fun () ->
      fine
        (lends "copied" "(self) lends Tagged"
           "  Tagged(tag: \"new\".copy(), book: self.books[0].copy())\n"));
  Harness.test "a `Plain` place in a lent constructor is copied, so it lends nothing" (fun () ->
      fine
        (lends "numbered" "(self, index: UInt64) lends Numbered"
           "  Numbered(index: index, title: self.books[index].copy())\n"));
  Harness.test "a local is a place that a lent constructor lends" (fun () ->
      fine
        (lends "tagged" "(self) lends Tagged"
           "  let tag = \"new\".copy()\n  Tagged(tag: tag, book: self.books[0])\n"));
  Harness.test "a lent constructor that lends a place owns a value that the method made" (fun () ->
      fine
        (lends "tagged" "(self) lends Tagged" "  Tagged(tag: \"new\".copy(), book: self.books[0])\n"));
  Harness.test "a place lent `mut` inside a variant is rejected" (fun () ->
      one_diagnostic
        (lends "first" "(mut self) lends mut Option[String]" "  Some(mut self.books[0])\n")
        "ownership.lent_mut_in_variant");
  Harness.test "a place lent `mut` inside a record inside a variant is rejected" (fun () ->
      one_diagnostic
        (lends "first" "(mut self) lends mut Option[Numbered]"
           "  Some(Numbered(index: 0, title: mut self.books[0]))\n")
        "ownership.lent_mut_in_variant");
  Harness.test "a constructor lent `mut` lends the places passed `mut`" (fun () ->
      fine
        (lends "numbered" "(mut self, index: UInt64) lends mut Numbered"
           "  Numbered(index: index, title: mut self.books[index])\n"
        ^ Fixtures.Ownership.title_cleared_through_numbered));
  Harness.test "a place in a constructor lent `mut` needs the `mut` keyword" (fun () ->
      one_diagnostic
        (lends "numbered" "(mut self) lends mut Numbered"
           "  Numbered(index: 0, title: self.books[0])\n")
        "types.missing_mode");
  Harness.test "a place in a constructor lent read-only takes no `mut` keyword" (fun () ->
      one_diagnostic
        (lends "numbered" "(self) lends Numbered" "  Numbered(index: 0, title: mut self.books[0])\n")
        "types.redundant_mode");
  Harness.test "a lending method cannot lend a part of a local it owns" (fun () ->
      one_diagnostic ~says:"a part of `sorted`"
        (lends "first_sorted" "(self) lends String"
           "  var sorted = self.books.copy()\n  mut sorted.sort()\n  sorted[0]\n")
        "ownership.view_escapes");
  Harness.test "a lending method cannot lend a part of a temporary" (fun () ->
      one_diagnostic ~says:"of a temporary"
        (lends "first_copied" "(self) lends String" "  self.books.copy()[0]\n")
        "ownership.view_escapes");
  Harness.test "a lending method cannot lend a field of a local it owns inside a constructor"
    (fun () ->
      one_diagnostic ~says:"a part of `both`"
        (lends "tagged" "(self) lends Tagged"
           "  let both = Tagged(tag: \"new\".copy(), book: \"old\".copy())\n\
           \  Tagged(tag: both.tag, book: self.books[0])\n")
        "ownership.view_escapes");
  Harness.test "a lending method can lend the whole of a local it owns" (fun () ->
      fine
        (lends "first_sorted" "(self) lends List[String]"
           "  var sorted = self.books.copy()\n  mut sorted.sort()\n  sorted\n"));
  Harness.test "a lending method can lend a `Plain` part of a local it owns, which is a copy"
    (fun () ->
      fine
        (lends "longest" "(self) lends UInt64"
           "  var lengths: List[UInt64] = []\n\
           \  for book in self.books {\n\
           \    mut lengths.push(book.length())\n\
           \  }\n\
           \  mut lengths.sort()\n\
           \  lengths[0]\n"));
  (let catalog = "type Catalog(titles: Map[String, String])\n\n" in
   let lends name signature body =
     catalog ^ "fn Catalog." ^ name ^ signature ^ " {\n" ^ body ^ "}\n"
   in
   Harness.test "a lending method forwards a part that a key it owns selects" (fun () ->
       fine
         (lends "title" "(self, prefix: String) lends String"
            "  let key = prefix.copy()\n  self.titles[key]\n"));
   Harness.test "a lending method forwards a part inside a constructor" (fun () ->
       fine
         (lends "find" "(self, prefix: String) lends Option[String]"
            "  let key = prefix.copy()\n\
            \  if self.titles.contains(key) {\n\
            \    Some(self.titles[key])\n\
            \  } else {\n\
            \    None\n\
            \  }\n"));
   Harness.test "a lending method cannot forward a part of a map it owns" (fun () ->
       one_diagnostic ~says:"a view of `copied`"
         (lends "title" "(self, key: String) lends String"
            "  let copied = self.titles.copy()\n  copied[key]\n")
         "ownership.view_escapes");
   Harness.test "a lending method cannot forward a part of a map it owns inside a constructor"
     (fun () ->
       one_diagnostic ~says:"a view of `copied`"
         (lends "find" "(self, key: String) lends Option[String]"
            "  let copied = self.titles.copy()\n  Some(copied[key])\n")
         "ownership.view_escapes");
   Harness.test "a lending method cannot lend a part of a parameter that is not its first"
     (fun () ->
       one_diagnostic ~says:"a part of `other`"
         (lends "first_of" "(self, other: List[String]) lends String" "  other[0]\n")
         "ownership.lends_other_parameter");
   Harness.test "a lending method cannot forward a part of a map that is not its first parameter"
     (fun () ->
       one_diagnostic ~says:"a part of `other`"
         (lends "title_in" "(self, other: Map[String, String], key: String) lends String"
            "  other[key]\n")
         "ownership.lends_other_parameter");
   Harness.test "a lending method can lend a `Plain` part of a parameter that is not its first"
     (fun () -> fine (lends "count_of" "(self, other: List[UInt64]) lends UInt64" "  other[0]\n")));
  (let shelves = "type Shelves(titles: Map[String, List[String]])\n\n" in
   let lends name signature body =
     shelves ^ "fn Shelves." ^ name ^ signature ^ " {\n" ^ body ^ "}\n"
   in
   Harness.test "a lending method forwards an element of a list that a lending call lent" (fun () ->
       fine (lends "first" "(self, shelf: String) lends String" "  self.titles[shelf][0]\n"));
   Harness.test "a lending method cannot forward an element of a list in a map it owns" (fun () ->
       one_diagnostic ~says:"a view of `copied`"
         (lends "first" "(self, shelf: String) lends String"
            "  let copied = self.titles.copy()\n  copied[shelf][0]\n")
         "ownership.view_escapes");
   Harness.test "an element of a list that a lending call lent is not bound with `let`" (fun () ->
       one_diagnostic
         (lends "first_length" "(self, shelf: String) -> UInt64"
            "  let first = self.titles[shelf][0]\n  first.length()\n")
         "ownership.lent_part_escapes"));
  Harness.test "a lent constructor is not lent one place `mut` twice" (fun () ->
      one_diagnostic
        (lends "both" "(mut self) lends mut Both"
           "  Both(first: mut self.books, second: mut self.books)\n")
        "ownership.conflicting_loan")

let () =
  let helpers = Fixtures.Ownership.handlers_and_lambda_callees in
  let rejected name body code =
    Harness.test name (fun () -> one_diagnostic (helpers ^ body) code)
  in
  let accepted name body = Harness.test name (fun () -> fine (helpers ^ body)) in
  rejected "a lambda that captures a parameter cannot be returned"
    Fixtures.Ownership.lambda_capturing_a_parameter_returned "ownership.view_escapes";
  rejected "a lambda that captures a local cannot be returned"
    Fixtures.Ownership.lambda_capturing_a_local_returned "ownership.view_escapes";
  rejected "a capturing lambda cannot be returned through a local"
    Fixtures.Ownership.capturing_lambda_returned "ownership.view_escapes";
  rejected "a record that stores a capturing lambda cannot be returned"
    Fixtures.Ownership.handlers_of_a_capturing_lambda_returned "ownership.view_escapes";
  rejected "a capturing lambda cannot be stored in a `mut` parameter"
    Fixtures.Ownership.capturing_lambda_assigned_to_a_mut_field "ownership.view_escapes";
  rejected "a capturing lambda cannot be passed with a `mut` parameter that holds a function"
    Fixtures.Ownership.capturing_lambda_stored_into_mut_handlers "ownership.view_escapes";

  accepted "a capturing lambda can be passed with a `mut` slice parameter"
    Fixtures.Ownership.capturing_lambda_passed_beside_a_mut_slice;
  rejected "a capturing lambda cannot be passed with a `mut` slice of functions"
    Fixtures.Ownership.capturing_lambda_filled_into_a_mut_slice "ownership.view_escapes";
  rejected
    "a lambda that returns a view of its capture cannot be passed with a `mut` slice of views"
    Fixtures.Ownership.lambda_returning_a_view_of_its_capture "ownership.view_escapes";
  rejected "a capturing lambda cannot be passed to an `own` function-typed parameter"
    Fixtures.Ownership.capturing_lambda_passed_own "ownership.view_escapes";
  rejected
    "a function value that is not owned cannot be passed to an `own` function-typed parameter"
    Fixtures.Ownership.borrowed_handler_passed_own "ownership.view_escapes";

  accepted
    "a capturing lambda can be stored in a local list and passed to a generic `own` parameter"
    Fixtures.Ownership.capturing_lambda_in_a_local_list;
  rejected "a list that stores a capturing lambda cannot be returned"
    Fixtures.Ownership.list_of_a_capturing_lambda_returned "ownership.view_escapes";
  rejected "a capturing lambda returned through a generic `own` parameter cannot be returned"
    Fixtures.Ownership.capturing_lambda_returned_through_a_generic_own "ownership.view_escapes";
  accepted "a function that captures nothing can be returned, stored, and moved"
    Fixtures.Ownership.functions_capturing_nothing_returned;
  accepted "an owned local that a lambda captures can be moved once the lambda is dead"
    (keep ^ Fixtures.Ownership.captured_local_moved_after_the_call);
  accepted "a capturing lambda can be passed to a call and stored in a local record"
    Fixtures.Ownership.capturing_lambda_passed_and_stored_in_a_local

let () =
  let types = Fixtures.Ownership.types in
  let rejected name body code = Harness.test name (fun () -> one_diagnostic (types ^ body) code) in
  let accepted name body = Harness.test name (fun () -> fine (types ^ body)) in
  rejected "a borrow of a value that owns data and stores a view views the value"
    Fixtures.Ownership.labeled_reassigned_while_borrowed "ownership.mutated_while_viewed";
  rejected "a slice of a part of a value that owns data and stores a view views the value"
    Fixtures.Ownership.labeled_reassigned_while_its_name_is_viewed "ownership.mutated_while_viewed";
  rejected "a borrow of an `own` parameter cannot be returned"
    Fixtures.Ownership.slice_of_an_own_parameter_returned "ownership.view_escapes";
  accepted "a view copied out of an `own` parameter can be returned"
    Fixtures.Ownership.view_field_of_an_own_parameter_returned;
  rejected "an `any` that stores a view of a local cannot be returned"
    Fixtures.Ownership.any_runner_viewing_a_local "ownership.view_escapes";
  rejected "the place that an `any` views cannot be mutated while the `any` is live"
    Fixtures.Ownership.push_while_an_any_views_the_list "ownership.mutated_while_viewed";
  accepted "an `any` made from owned data can be returned"
    Fixtures.Ownership.any_runner_of_owned_items;
  rejected "a capturing lambda cannot be returned as a wider function type"
    Fixtures.Ownership.capturing_lambda_returned_as_a_wider_type "ownership.view_escapes";
  rejected "the value of an `if` has the views of its branches' tail expressions"
    Fixtures.Ownership.if_whose_branches_view_a_list "ownership.mutated_while_viewed";
  rejected "the value of a `match` has the views of its arms' tail expressions"
    Fixtures.Ownership.match_whose_arms_view_a_list "ownership.mutated_while_viewed";
  rejected "the value of a block has the views of its tail expression"
    Fixtures.Ownership.block_whose_tail_views_a_list "ownership.mutated_while_viewed";
  rejected "a view of a local cannot be returned through an `if` and a local"
    Fixtures.Ownership.if_viewing_a_local_returned "ownership.view_escapes";
  rejected "a copy of a view has the same views" Fixtures.Ownership.copy_of_a_view_then_a_push
    "ownership.mutated_while_viewed";
  rejected "a record built by `with` has the views of its new fields"
    Fixtures.Ownership.sized_with_a_new_view "ownership.mutated_while_viewed";
  rejected "a view copied out of a loop variable views the collection that the loop iterates over"
    Fixtures.Ownership.view_copied_out_of_a_loop_variable "ownership.mutated_while_viewed";
  accepted "a `Plain` loop variable is a copy, so the collection can be mutated after the loop"
    Fixtures.Ownership.plain_loop_variable_copied;
  rejected "a place cannot be mutated while a `match` binding of it is live"
    Fixtures.Ownership.slot_assigned_while_its_binding_lives "ownership.mutated_while_viewed";
  accepted "a place can be mutated in an arm once the `match` bindings are dead"
    Fixtures.Ownership.slot_assigned_after_its_binding_ends

let () =
  let reader = "type Reader(buffer: List[Int64])\n\n" in
  let rejected name body code = Harness.test name (fun () -> one_diagnostic (reader ^ body) code) in
  let accepted name body = Harness.test name (fun () -> fine (reader ^ body)) in
  rejected "a lending method cannot lend a view of its local"
    Fixtures.Ownership.reader_lending_a_view_of_a_local "ownership.view_escapes";
  accepted "a method can lend a view of `self`, and lend a local itself"
    Fixtures.Ownership.reader_lending_a_view_of_self;
  (let chunks = Fixtures.Ownership.chunks in

   rejected "a view of an element lent `mut` cannot be used in the next iteration"
     (chunks ^ Fixtures.Ownership.view_of_a_mut_chunk_read_in_the_next_iteration)
     "ownership.mutated_while_viewed";
   accepted "a view of the last element lent `mut` can be used after the loop"
     (chunks ^ Fixtures.Ownership.view_of_a_mut_chunk_read_after_the_loop);
   accepted "a view of an element lent `mut` to an iteration can be used in that iteration"
     (chunks ^ Fixtures.Ownership.view_of_a_mut_chunk_read_in_its_iteration);
   accepted "a view from a loop over a read-only collection can be used after the loop"
     (chunks ^ Fixtures.Ownership.view_of_a_chunk_kept_after_the_loop));
  accepted "a view is not in use between its last read and a new value, so its original can change"
    Fixtures.Ownership.view_reassigned_after_a_push

let () =
  let counter = Fixtures.Ownership.counter in
  Harness.test "the body of a `provide` cannot use a place that the block borrows `mut`" (fun () ->
      one_diagnostic
        (counter ^ Fixtures.Ownership.provide_body_reading_its_mut_provided_place)
        "ownership.conflicting_loan");
  Harness.test "the body of a `provide` cannot mutate a place that the block borrows" (fun () ->
      one_diagnostic
        (counter ^ Fixtures.Ownership.provide_body_assigning_its_provided_place)
        "ownership.mutated_while_viewed");
  Harness.test "the body of a `provide` can read a place that the block borrows read-only"
    (fun () -> fine (counter ^ Fixtures.Ownership.provide_body_reading_its_provided_place));
  Harness.test "a place that a `provide` block borrows is usable again after the block" (fun () ->
      fine (counter ^ Fixtures.Ownership.tally_read_after_its_provide))

let () =
  Harness.test
    "one branch of a `parallel` block cannot mutate the place that another branch's view views"
    (fun () ->
      one_diagnostic Fixtures.Ownership.parallel_branch_mutating_a_viewed_list "ownership.data_race");
  Harness.test "two branches of a `parallel` block can read through views of one place" (fun () ->
      fine Fixtures.Ownership.parallel_branches_reading_one_view)

let () =
  let make = Fixtures.Ownership.make in
  Harness.test "a copy of a view of a temporary cannot be bound" (fun () ->
      one_diagnostic
        (make ^ Fixtures.Ownership.copy_of_a_view_of_a_temporary)
        "ownership.views_temporary");
  Harness.test "a record built by `with` cannot store a view of a temporary" (fun () ->
      one_diagnostic
        (make ^ Fixtures.Ownership.sized_with_a_view_of_a_temporary)
        "ownership.views_temporary")

let () =
  Harness.test "an executable quantifier reads the collection that it iterates over" (fun () ->
      fine Fixtures.Ownership.quantifiers_over_a_list)

let () =
  let reader = Fixtures.Ownership.reader in
  Harness.test
    "a `mut` view argument does not store a view of a borrowed argument that is not a view"
    (fun () -> fine (reader ^ Fixtures.Ownership.reader_reading_into_a_list))

let () =
  Harness.test "the `Cursor` trait's own methods are called on a cursor" (fun () ->
      fine Fixtures.Ownership.find_and_fold_on_cursors);
  Harness.test "a cursor over `Plain` elements can be passed to generic code" (fun () ->
      fine Fixtures.Ownership.collect_of_a_list_cursor)

let () =
  let journal = Fixtures.Ownership.journal in
  let rejected name body code =
    Harness.test name (fun () -> one_diagnostic (journal ^ body) code)
  in
  rejected "a capability's implementation cannot store a view argument"
    Fixtures.Ownership.journal_keeping_a_view "ownership.view_crosses_capability";
  rejected "a capability's method cannot return a view of the implementation's state"
    Fixtures.Ownership.journal_returning_a_view_of_its_lines "ownership.view_crosses_capability";
  Harness.test "an implementation can store a copy and return a view that it was constructed with"
    (fun () -> fine (journal ^ Fixtures.Ownership.journal_storing_a_copy_and_lending_its_label));
  Harness.test
    "a method outside a capability's `impl` can store a view argument and return a view of `self`"
    (fun () -> fine Fixtures.Ownership.keeper_storing_a_view)

let () =
  let url = "type Url(scheme: String, user: Option[String])\n\n" in
  let accepted name body = Harness.test name (fun () -> fine (url ^ body)) in
  accepted "a view of a `match` binding of a parameter can be returned"
    Fixtures.Ownership.url_user_through_a_match;
  accepted "a view of an `is` binding of a parameter can be returned"
    Fixtures.Ownership.url_user_through_an_is;
  accepted "a view of a `let` alias of a part of a parameter can be returned"
    Fixtures.Ownership.url_scheme_through_a_let;
  accepted "a view of a loop variable over a parameter can be returned"
    Fixtures.Ownership.first_name_returned_from_a_loop;
  Harness.test "a view of a `match` binding of a local cannot be returned" (fun () ->
      one_diagnostic Fixtures.Ownership.view_of_a_match_binding_of_a_local_returned
        "ownership.view_escapes");
  Harness.test "a place cannot be mutated while a view of its `match` binding is live" (fun () ->
      one_diagnostic Fixtures.Ownership.user_assigned_while_a_view_of_its_binding_lives
        "ownership.mutated_while_viewed")

let () =
  let helpers = Fixtures.Ownership.holder_and_wait in
  let rejected ?says name body code =
    Harness.test name (fun () -> one_diagnostic ?says (helpers ^ body) code)
  in
  let accepted name body = Harness.test name (fun () -> fine (helpers ^ body)) in
  rejected "one branch of a `concurrent` block cannot mutate a place that another branch uses"
    ~says:"`concurrent` block" Fixtures.Ownership.concurrent_branch_mutating_a_viewed_list
    "ownership.data_race";
  rejected "an iteration of a `concurrent for` can mutate only its own element and locals"
    ~says:"`concurrent for`" Fixtures.Ownership.concurrent_for_mutating_a_total
    "ownership.data_race";
  rejected "a `concurrent` branch must reinitialize a place that it moves out of a `mut` borrow"
    Fixtures.Ownership.concurrent_branch_leaving_a_holder_moved "ownership.not_reinitialized";
  accepted "a `concurrent` branch can move a value out of a `mut` borrow and reinitialize it"
    Fixtures.Ownership.concurrent_branch_moving_out_of_a_mut_holder;
  rejected
    "a place moved out before a `concurrent` block must be reinitialized where a branch returns"
    Fixtures.Ownership.holder_items_moved_before_a_concurrent_block "ownership.not_reinitialized";
  let pair = Fixtures.Ownership.pair in

  Harness.test
    "a `concurrent for` cannot change the elements of a collection that is not a `List`, a \
     `Slice`, or an `Array`" (fun () ->
      one_diagnostic ~says:"Only a `List`, a `Slice`, or an `Array`"
        (pair ^ Fixtures.Ownership.concurrent_for_changing_elements_of_a_pair)
        "ownership.data_race");
  Harness.test
    "a `parallel for` cannot change the elements of a collection that is not a `List`, a `Slice`, \
     or an `Array`" (fun () ->
      one_diagnostic ~says:"`parallel for`"
        (pair ^ Fixtures.Ownership.parallel_for_changing_elements_of_a_pair)
        "ownership.data_race");
  Harness.test "a `concurrent for` can mutate the elements of a `List`" (fun () ->
      fine (pair ^ Fixtures.Ownership.concurrent_for_mutating_rows));
  Harness.test "a `concurrent for` can read the elements of any collection" (fun () ->
      fine (pair ^ Fixtures.Ownership.concurrent_for_reading_every_collection));
  Harness.test "a `concurrent for` cannot iterate over a cursor of views" (fun () ->
      one_diagnostic ~says:"`Slice[Int64]` is a view"
        (pair ^ Fixtures.Ownership.concurrent_for_over_a_cursor_of_views)
        "ownership.task_outlives_view");
  Harness.test "a `concurrent for` can iterate over a cursor of owned values or of `Plain` copies"
    (fun () -> fine (pair ^ Fixtures.Ownership.concurrent_for_over_owned_and_plain_cursors))

let () =
  let bump = Fixtures.Ownership.bump_returning_false in
  Harness.test "a guard cannot mutate the scrutinee" (fun () ->
      one_diagnostic
        (bump ^ Fixtures.Ownership.guard_mutating_the_scrutinee)
        "ownership.mutated_while_viewed");
  Harness.test "a guard can mutate another place, and an arm's body can mutate the scrutinee"
    (fun () -> fine (bump ^ Fixtures.Ownership.guard_mutating_another_place))

let () =
  let names = "let names: List[Int64] = [1, 2]\n\n" in
  let config = Fixtures.Ownership.config in
  List.iter
    (fun (construct, text, code) ->
      Harness.test (construct ^ " is an error") (fun () -> one_diagnostic text code))
    [
      ( "moving a constant with `own`",
        keep ^ names ^ Fixtures.Ownership.moving_a_constant_with_own,
        "ownership.not_owned" );
      ( "moving a field of a constant with `own`",
        keep ^ config ^ Fixtures.Ownership.moving_a_field_of_a_constant_with_own,
        "ownership.not_owned" );
      ( "passing a constant to an `own` parameter",
        keep ^ names ^ Fixtures.Ownership.passing_a_constant_to_an_own_parameter,
        "types.missing_mode" );
      ( "passing a type's constant to an `own` parameter",
        keep ^ config ^ Fixtures.Ownership.passing_a_types_constant_to_an_own_parameter,
        "types.missing_mode" );
      ( "binding a constant with `var`",
        names ^ Fixtures.Ownership.binding_a_constant_with_var,
        "ownership.needs_owned" );
      ( "binding a type's constant with `var`",
        config ^ Fixtures.Ownership.binding_a_types_constant_with_var,
        "ownership.needs_owned" );
      ( "returning a constant",
        names ^ Fixtures.Ownership.constant_list_returned,
        "ownership.needs_owned" );
    ];
  Harness.test "an owned value from a constant is a copy, with a fix" (fun () ->
      one_diagnostic
        (names ^ Fixtures.Ownership.constant_list_returned)
        "ownership.needs_owned"
        ~fixed:(names ^ Fixtures.Ownership.copy_of_a_constant_list_returned));
  Harness.test "a constant can be read, viewed, copied, and returned as a view" (fun () ->
      fine (keep ^ names ^ Fixtures.Ownership.constant_read_viewed_copied_and_returned));
  let bag = Fixtures.Ownership.bag in
  Harness.test "a compound assignment's operand may mutate the target, because it runs first"
    (fun () -> fine (bag ^ Fixtures.Ownership.compound_assignment_whose_operand_grows_its_target));
  Harness.test
    "a compound assignment's borrowed operand cannot be mutated by the target's index keys"
    (fun () ->
      one_diagnostic
        (bag ^ Fixtures.Ownership.compound_assignment_whose_index_spoils_its_operand)
        "ownership.mutated_while_viewed")

let () =
  Harness.test "the default of a parameter of a view type views a value that lasts for the call"
    (fun () -> fine Fixtures.Ownership.view_parameters_with_owned_defaults);
  Harness.test "a moved place cannot be used, with a fix that copies at the move" (fun () ->
      one_diagnostic
        (keep ^ Fixtures.Ownership.list_moved_then_read)
        "ownership.use_after_move"
        ~fixed:(keep ^ Fixtures.Ownership.list_copied_then_read));
  Harness.test "a tagged string moves its parts, and a plain string reads them" (fun () ->
      let shout = Fixtures.Ownership.shout in
      one_diagnostic (shout ^ Fixtures.Ownership.shout_of_a_name) "ownership.needs_owned";
      fine (shout ^ Fixtures.Ownership.shout_of_a_copied_name);
      fine (shout ^ Fixtures.Ownership.shout_of_an_own_name);
      fine Fixtures.Ownership.plain_string_of_a_name);
  Harness.test "a `Plain` place is copied, not moved" (fun () ->
      fine Fixtures.Ownership.plain_place_passed_own);
  Harness.test "a place moved by an argument cannot be read by a later argument of the same call"
    (fun () ->
      one_diagnostic Fixtures.Ownership.call_moving_then_reading_a_list "ownership.use_after_move");
  Harness.test "a place moved on one path cannot be used after the paths join" (fun () ->
      one_diagnostic (keep ^ Fixtures.Ownership.list_moved_on_one_path) "ownership.use_after_move");
  Harness.test "a place moved in a loop is moved in the loop's next iteration" (fun () ->
      one_diagnostic (keep ^ Fixtures.Ownership.list_moved_in_a_loop) "ownership.use_after_move");
  Harness.test "a place is usable again once it is assigned" (fun () ->
      fine (keep ^ Fixtures.Ownership.moved_var_reassigned));
  Harness.test
    "a field of a place moved out whole cannot be assigned, which prevents a double free of its \
     other fields" (fun () ->
      one_diagnostic Fixtures.Ownership.field_assigned_after_its_pair_moved
        "ownership.use_after_move");
  Harness.test "a field can be moved out by itself" (fun () ->
      fine Fixtures.Ownership.field_of_a_config_moved_out);
  Harness.test "a read-only parameter cannot be moved" (fun () ->
      one_diagnostic (keep ^ Fixtures.Ownership.read_only_list_moved) "ownership.not_owned");
  Harness.test "a field moved out of a `mut` parameter must be reinitialized" (fun () ->
      one_diagnostic Fixtures.Ownership.field_moved_out_of_a_mut_config
        "ownership.not_reinitialized");
  Harness.test "a local that a value is moved into has no view of the moved place" (fun () ->
      fine Fixtures.Ownership.local_moved_into_then_reassigned);
  (let holder = "type Holder(items: List[Int64], count: UInt64)\n\n" in
   let accepted name body = Harness.test name (fun () -> fine (holder ^ body)) in
   let rejected name body code =
     Harness.test name (fun () -> one_diagnostic (holder ^ body) code)
   in
   accepted "a field of a `mut` borrow can be moved out and reinitialized"
     Fixtures.Ownership.field_of_mut_self_moved_out_and_reinitialized;
   rejected "a field moved out of `mut self` must be reinitialized"
     Fixtures.Ownership.field_moved_out_of_mut_self "ownership.not_reinitialized";
   accepted "a `mut` borrow can be moved out whole and reinitialized"
     Fixtures.Ownership.mut_slot_moved_out_and_reset;
   rejected "a `mut` borrow that is moved out whole must be reinitialized"
     Fixtures.Ownership.mut_holder_moved_out_whole "ownership.not_reinitialized";
   rejected "a `mut` borrow must be reinitialized on every path"
     Fixtures.Ownership.mut_holder_reinitialized_on_one_path "ownership.not_reinitialized";
   rejected "a `mut` borrow cannot be used while it is moved out"
     Fixtures.Ownership.mut_holder_read_while_moved_out "ownership.use_after_move";
   accepted "a `mut` loop variable can be moved out and reinitialized in the iteration"
     Fixtures.Ownership.mut_loop_variable_moved_out_and_reinitialized;
   rejected "a `mut` loop variable that is moved out must be reinitialized in the iteration"
     Fixtures.Ownership.mut_loop_variable_moved_out "ownership.not_reinitialized";
   rejected "a `mut` binding of a `match` that is moved out must be reinitialized in the arm"
     Fixtures.Ownership.mut_match_binding_moved_out "ownership.not_reinitialized";
   rejected "a lending method must reinitialize a place of its caller that it moved out"
     Fixtures.Ownership.holder_lending_its_moved_items "ownership.not_reinitialized");
  Harness.test "one place cannot be borrowed `mut` twice by one call" (fun () ->
      one_diagnostic Fixtures.Ownership.swap_of_one_place "ownership.conflicting_loan");
  Harness.test "a place cannot be mutated while a view of it is live" (fun () ->
      one_diagnostic Fixtures.Ownership.push_while_a_view_lives "ownership.mutated_while_viewed");
  Harness.test "a place can be mutated once the view of it is dead" (fun () ->
      fine Fixtures.Ownership.push_after_a_view_is_dead);
  Harness.test "a function cannot return a view of its own local" (fun () ->
      one_diagnostic Fixtures.Ownership.view_of_a_local_returned "ownership.view_escapes");
  Harness.test "a function cannot return a view of its local nested in a type nested in itself"
    (fun () ->
      one_diagnostic Fixtures.Ownership.nested_holder_of_a_local_view_returned
        "ownership.view_escapes");
  Harness.test "a function cannot return a view of its local stored as an associated type"
    (fun () ->
      one_diagnostic Fixtures.Ownership.associated_part_of_a_local_returned "ownership.view_escapes");
  Harness.test "a function can return a view of its parameter" (fun () ->
      fine Fixtures.Ownership.view_of_a_parameter_returned);
  Harness.test "a view-typed local that views nothing can be returned" (fun () ->
      fine Fixtures.Ownership.static_slice_local_returned);
  Harness.test "a `var` needs an owned value, with fixes that move or copy the place" (fun () ->
      one_diagnostic Fixtures.Ownership.var_initialized_from_an_own_parameter
        "ownership.needs_owned"
        ~fixed:Fixtures.Ownership.var_initialized_from_an_own_parameter_fixed);
  Harness.test "an assigned value must be owned" (fun () ->
      one_diagnostic Fixtures.Ownership.assignment_of_an_own_parameter_to_a_var
        "ownership.needs_owned"
        ~fixed:Fixtures.Ownership.assignment_of_an_own_parameter_to_a_var_fixed);
  Harness.test "a map literal's keys and values must be owned" (fun () ->
      one_diagnostic Fixtures.Ownership.map_literal_of_an_own_name "ownership.needs_owned");
  Harness.test "a constant's value and a default may hold a constant without a copy" (fun () ->
      fine Fixtures.Ownership.constants_and_defaults_holding_a_constant);
  Harness.test "a list element needs an owned value" (fun () ->
      one_diagnostic Fixtures.Ownership.list_of_a_string_parameter "ownership.needs_owned");
  Harness.test "a lending method can lend from a `return` inside a loop" (fun () ->
      fine Fixtures.Ownership.bag_lending_from_a_loop);
  Harness.test "a `parallel` branch cannot mutate a place that another branch uses" (fun () ->
      one_diagnostic Fixtures.Ownership.parallel_branches_bumping_and_reading "ownership.data_race")

let () =
  let bag = "type Bag(items: List[Int64])\n\n" in
  Harness.test "an impl method's read-only parameter may be returned as a view" (fun () ->
      fine (bag ^ Fixtures.Ownership.impl_method_returning_a_view_of_its_parameter));
  Harness.test "an impl method cannot move a read-only parameter" (fun () ->
      one_diagnostic
        (keep ^ bag ^ Fixtures.Ownership.impl_method_moving_a_read_only_parameter)
        "ownership.not_owned");
  Harness.test "an impl method may move a field of an owned self" (fun () ->
      fine (bag ^ Fixtures.Ownership.impl_method_moving_a_field_of_own_self));
  Harness.test "a trait's method with a body is checked too" (fun () ->
      one_diagnostic
        (keep ^ Fixtures.Ownership.trait_method_body_moving_a_read_only_parameter)
        "ownership.not_owned")

let () =
  Harness.test
    "a loop body cannot mutate the collection that the loop iterates over, even inside a branch"
    (fun () ->
      one_diagnostic Fixtures.Ownership.loop_mutating_its_list_in_a_branch
        "ownership.mutated_while_viewed");
  Harness.test "a loop body cannot borrow `mut` the collection that the loop iterates over"
    (fun () ->
      one_diagnostic Fixtures.Ownership.loop_pushing_onto_its_list "ownership.mutated_while_viewed");
  Harness.test "a `parallel for` cannot borrow `mut` a place from outside the loop" (fun () ->
      one_diagnostic Fixtures.Ownership.parallel_for_pushing_onto_an_outer_list
        "ownership.data_race");
  Harness.test "a `parallel for` cannot assign a place from outside the loop, even inside a branch"
    (fun () ->
      one_diagnostic Fixtures.Ownership.parallel_for_assigning_an_outer_var "ownership.data_race");
  Harness.test "a `parallel for` can mutate its own element and locals" (fun () ->
      fine Fixtures.Ownership.parallel_for_mutating_its_element_and_locals);
  Harness.test "a call cannot take a view of a place that another argument moves" (fun () ->
      one_diagnostic Fixtures.Ownership.call_viewing_and_moving_one_list
        "ownership.mutated_while_viewed");
  Harness.test "a Plain place passed own is copied, so the call may use it twice" (fun () ->
      fine Fixtures.Ownership.plain_place_passed_twice)

let () =
  Harness.test "a call's result does not view a `Plain` argument" (fun () ->
      fine Fixtures.Ownership.window_of_a_plain_start);
  Harness.test "a diverging path of a lending method need not lend" (fun () ->
      fine Fixtures.Ownership.grid_cell_that_may_diverge)

let () =
  Harness.test "a cursor cannot view a temporary that the statement drops" (fun () ->
      one_diagnostic Fixtures.Ownership.cursor_over_a_temporary_string "ownership.views_temporary");
  Harness.test "a cursor may view a named value" (fun () ->
      fine Fixtures.Ownership.cursor_over_a_named_string);
  Harness.test "a cursor may view a string literal, which has static storage" (fun () ->
      fine Fixtures.Ownership.cursor_over_a_string_literal);
  Harness.test "a value computed from a temporary's view is fine" (fun () ->
      fine Fixtures.Ownership.length_of_a_slice_of_a_temporary);
  Harness.test "a view of a temporary cannot be returned" (fun () ->
      one_diagnostic
        (Fixtures.Ownership.make ^ Fixtures.Ownership.slice_of_a_temporary_returned)
        "ownership.view_escapes")

let () =
  let make = Fixtures.Ownership.make in
  Harness.test "a `let` can bind a slice of a temporary list" (fun () ->
      fine Fixtures.Ownership.let_of_a_slice_of_a_temporary);
  Harness.test "a `let` keeps a temporary that a record field it constructs slices" (fun () ->
      fine (make ^ Fixtures.Ownership.let_of_a_record_slicing_a_temporary));
  Harness.test "a `let` does not keep a temporary that is a method's receiver" (fun () ->
      one_diagnostic
        (make ^ Fixtures.Ownership.let_of_a_slice_of_a_temporary_receiver)
        "ownership.views_temporary");
  Harness.test "a slice of a temporary cannot outlive the `let` that keeps the temporary" (fun () ->
      one_diagnostic Fixtures.Ownership.slice_of_a_kept_temporary_outliving_its_block
        "ownership.views_temporary");
  Harness.test "a view of a string literal outlives the function" (fun () ->
      fine Fixtures.Ownership.slice_of_a_string_literal_returned);
  Harness.test "a match of string literals where a StringSlice is expected is one" (fun () ->
      fine Fixtures.Ownership.match_of_string_literals);
  Harness.test "a `let` bound to a string literal is a view" (fun () ->
      fine Fixtures.Ownership.string_literal_let_read_twice);
  Harness.test "a `let` bound to a string literal is not owned" (fun () ->
      one_diagnostic Fixtures.Ownership.string_literal_let_returned "ownership.needs_owned")

let () =
  Harness.test "a view of a local cannot outlive the local's block" (fun () ->
      one_diagnostic
        (Fixtures.Ownership.make ^ Fixtures.Ownership.view_of_a_block_local_kept)
        "ownership.view_escapes");
  Harness.test "a view of a part that a loop owns cannot outlive the iteration" (fun () ->
      one_diagnostic Fixtures.Ownership.view_of_an_owned_loop_variable_kept "ownership.view_escapes");
  Harness.test "a view of a part that a loop lends can outlive the iteration" (fun () ->
      fine Fixtures.Ownership.view_of_a_lent_loop_variable_kept)

let () =
  Harness.test "assigning a `var` a new view ends its view of a local" (fun () ->
      fine (Fixtures.Ownership.make ^ Fixtures.Ownership.var_reassigned_from_a_local_view));
  Harness.test "assigning a `var` a new view ends its view of the old place" (fun () ->
      fine Fixtures.Ownership.var_reassigned_from_one_view_to_another);
  Harness.test "assigning a field a new view keeps the record's other views" (fun () ->
      one_diagnostic Fixtures.Ownership.field_assigned_a_new_view "ownership.mutated_while_viewed")

let () =
  Harness.test "a loop over a list of `String` elements is lent each element" (fun () ->
      fine Fixtures.Ownership.loop_over_a_list_of_strings)

let () =
  Harness.test "is on a temporary binds its parts as owned, as match does" (fun () ->
      fine Fixtures.Ownership.is_on_a_temporary_kept);
  Harness.test "a let of the result of a call with a mode keyword binds it owned" (fun () ->
      fine Fixtures.Ownership.let_of_a_mut_pop_kept);
  Harness.test "is on a place binds views of its parts" (fun () ->
      one_diagnostic Fixtures.Ownership.is_on_a_parameter_kept "ownership.not_owned")

let () =
  let make = Fixtures.Ownership.make_an_option_of_a_string in
  Harness.test "a binding inside a loop is a new one each time, so it may be moved" (fun () ->
      fine (make ^ Fixtures.Ownership.binding_moved_inside_a_loop));
  Harness.test "an `is` binding of a `while` condition may be moved in every iteration" (fun () ->
      fine (make ^ Fixtures.Ownership.is_binding_moved_in_a_while_condition));
  Harness.test "an is binding in an if inside a loop may be moved" (fun () ->
      fine (make ^ Fixtures.Ownership.is_binding_moved_in_an_if_in_a_loop));
  Harness.test "a let-else binding inside a loop may be moved" (fun () ->
      fine (make ^ Fixtures.Ownership.let_else_binding_moved_in_a_loop));

  Harness.test "an `is` binding after `&&` in a `while` condition may be moved in every iteration"
    (fun () -> fine (make ^ Fixtures.Ownership.is_binding_after_and_moved_in_a_while_condition))

let () =
  Harness.test "a `Plain` name that an `if` condition binds is a copy, which views nothing"
    (fun () -> fine Fixtures.Ownership.plain_copy_bound_by_an_if);
  Harness.test "the then-block may mutate the lender when the condition binds only copies"
    (fun () -> fine Fixtures.Ownership.word_counts);
  Harness.test "a name bound before a test after `&&` fails ends with the part it aliases"
    (fun () -> fine Fixtures.Ownership.is_binding_before_a_failing_and);
  Harness.test "the else-block may mutate the lender" (fun () ->
      fine Fixtures.Ownership.else_block_mutating_the_lender);
  Harness.test
    "the then-block cannot mutate the lender while a name the condition binds aliases the lent part"
    (fun () ->
      one_diagnostic Fixtures.Ownership.then_block_mutating_the_lender
        "ownership.mutated_while_viewed");
  Harness.test
    "a `while` body cannot mutate the lender while a name the condition binds aliases the lent part"
    (fun () ->
      one_diagnostic Fixtures.Ownership.while_body_mutating_the_lender
        "ownership.mutated_while_viewed")

let disjoint_obligations text =
  let packages = Support.setup [ ("app::main", text) ] in
  let file = Support.file_of "app::main" in
  let database = Support.database packages in
  Database.check database [ file.module_.package ];
  List.fold_left
    (fun total declaration ->
      match Database.For_testing.read_ownership database (Resolve.Names.key_of declaration) with
      | Value must_be_disjoint -> total + List.length must_be_disjoint
      | Failed _ | Blocked -> total)
    0
    ((Support.names packages file.module_.package).declarations_in file)

let () =
  Harness.test "two slices of one list borrowed by one call produce one `Disjoint` obligation"
    (fun () ->
      let actual = disjoint_obligations Fixtures.Ownership.two_mut_slices_of_one_list in
      if actual <> 1 then Harness.fail "%d obligations" actual);
  Harness.test "`parallel` branches that mutate two elements produce one `Disjoint` obligation"
    (fun () ->
      let actual =
        disjoint_obligations Fixtures.Ownership.parallel_branches_assigning_two_elements
      in
      if actual <> 1 then Harness.fail "%d obligations" actual);
  Harness.test
    "a `mut` slice argument that may alias a view argument produces one `Disjoint` obligation"
    (fun () ->
      let actual =
        disjoint_obligations Fixtures.Ownership.mut_slice_beside_a_view_of_the_same_list
      in
      if actual <> 1 then Harness.fail "%d obligations" actual);
  Harness.test
    "a `mut` element argument that may alias a view argument produces one `Disjoint` obligation"
    (fun () ->
      let actual =
        disjoint_obligations Fixtures.Ownership.mut_element_beside_a_view_of_the_same_list
      in
      if actual <> 1 then Harness.fail "%d obligations" actual)

let grid = Fixtures.Ownership.grid
let counter = Fixtures.Ownership.counter_lending_its_count
let tally = Fixtures.Ownership.tally

let () =
  Harness.test
    "a part lent `mut` is mutated through its `mut self` method, with no mode keyword of its own"
    (fun () -> fine (grid ^ Fixtures.Ownership.grid_cell_visited_through_mut));
  Harness.test "a part lent `mut` is assigned to" (fun () ->
      fine (grid ^ Fixtures.Ownership.grid_cell_name_assigned_through_mut));
  Harness.test "a part lent read-only is not assigned to" (fun () ->
      one_diagnostic (grid ^ Fixtures.Ownership.grid_cell_name_assigned) "types.not_assignable");
  Harness.test "a part lent read-only is not passed `mut`" (fun () ->
      one_diagnostic (grid ^ Fixtures.Ownership.grid_cell_passed_as_mut) "types.wrong_mode");
  Harness.test "a lent part cannot be moved" (fun () ->
      one_diagnostic (grid ^ Fixtures.Ownership.grid_cell_moved) "types.missing_mode");
  Harness.test "a lent part cannot be returned" (fun () ->
      one_diagnostic (grid ^ Fixtures.Ownership.grid_cell_returned) "ownership.not_owned");
  Harness.test "a `let` cannot bind a lent part" (fun () ->
      one_diagnostic (grid ^ Fixtures.Ownership.let_of_a_grid_cell) "ownership.lent_part_escapes");
  Harness.test "a `let` copies a `Plain` lent part" (fun () ->
      fine (counter ^ Fixtures.Ownership.let_of_a_lent_count));
  Harness.test "a `match` on a lent part binds views of it, which cannot be moved" (fun () ->
      one_diagnostic (grid ^ Fixtures.Ownership.match_on_a_grid_cell) "ownership.not_owned");
  Harness.test
    "a lending call borrows its whole receiver, so two parts cannot be lent `mut` in one statement"
    (fun () ->
      one_diagnostic
        (grid ^ Fixtures.Ownership.two_grid_cells_lent_mut_in_one_call)
        "ownership.conflicting_loan");
  Harness.test "a place and a part that it lends `mut` cannot be passed to one call" (fun () ->
      one_diagnostic
        (grid ^ Fixtures.Ownership.grid_and_its_cell_passed_together)
        "ownership.mutated_while_viewed");
  Harness.test
    "a receiver that a lending call borrows read-only cannot be mutated in the same statement"
    (fun () ->
      one_diagnostic
        (tally ^ Fixtures.Ownership.tally_element_assigned_from_another)
        "ownership.mutated_while_viewed");
  Harness.test "two parts of a place are lent read-only in one statement" (fun () ->
      fine (tally ^ Fixtures.Ownership.sum_of_two_tally_indexes));
  Harness.test "a lending call's loan ends with its statement" (fun () ->
      fine (grid ^ Fixtures.Ownership.grid_cell_visited_then_counted));
  Harness.test "a loan started in a `while` condition ends before the loop body" (fun () ->
      fine (counter ^ Fixtures.Ownership.while_condition_reading_a_lent_count));
  Harness.test "two indexes of a user-defined collection cannot be lent `mut` in one statement"
    (fun () ->
      one_diagnostic
        (tally ^ Fixtures.Ownership.two_tally_indexes_lent_mut)
        "ownership.conflicting_loan");
  Harness.test "two `mut` indexes of a list in one call produce a `Disjoint` obligation" (fun () ->
      fine Fixtures.Ownership.two_mut_list_indexes_in_one_call)

let window = "type Window(view: Slice[Int64])\n\n"

let () =
  Harness.test "a `mut` list argument stores the call's view arguments" (fun () ->
      one_diagnostic Fixtures.Ownership.views_pushed_onto_a_mut_list
        "ownership.mutated_while_viewed");
  Harness.test "the views stored in a `mut` list argument end when the list is dead" (fun () ->
      fine Fixtures.Ownership.data_pushed_after_its_views_die);
  Harness.test "a `mut` argument of a function stores the function's view arguments" (fun () ->
      one_diagnostic Fixtures.Ownership.mut_list_keeping_a_view_argument
        "ownership.mutated_while_viewed");
  Harness.test "a view stored in a place inside a branch is still stored after the branch"
    (fun () ->
      one_diagnostic Fixtures.Ownership.view_pushed_in_a_branch "ownership.mutated_while_viewed");
  Harness.test "a record whose field is assigned a view has the value's views" (fun () ->
      one_diagnostic
        (window ^ Fixtures.Ownership.window_assigned_a_view_of_data)
        "ownership.mutated_while_viewed");
  Harness.test "a `mut` argument cannot store a view of a temporary" (fun () ->
      one_diagnostic Fixtures.Ownership.mut_argument_storing_a_view_of_a_temporary
        "ownership.views_temporary");
  Harness.test "a view of a local cannot be stored in a `mut` parameter" (fun () ->
      one_diagnostic Fixtures.Ownership.view_of_a_local_pushed_onto_a_mut_list
        "ownership.view_escapes");
  Harness.test "a view argument can be stored in a `mut` parameter" (fun () ->
      fine Fixtures.Ownership.view_parameter_pushed_onto_a_mut_list);
  Harness.test
    "a view of a borrowed parameter that is not a view cannot be stored in a `mut` parameter"
    (fun () ->
      one_diagnostic Fixtures.Ownership.view_of_a_list_parameter_pushed_onto_a_mut_list
        "ownership.view_escapes");
  Harness.test "a place that a `mut` parameter views cannot be mutated in the rest of the function"
    (fun () ->
      one_diagnostic Fixtures.Ownership.source_reassigned_after_a_push_of_its_view
        "ownership.mutated_while_viewed");
  Harness.test "a `mut self` method cannot store a view of a local in `self`" (fun () ->
      one_diagnostic
        (window ^ Fixtures.Ownership.window_narrowed_to_a_local)
        "ownership.view_escapes");
  Harness.test "a `mut self` method can store a view argument in `self`" (fun () ->
      fine (window ^ Fixtures.Ownership.window_widened_with_a_view));
  Harness.test
    "a `mut self` method cannot store in `self` a view of a borrowed parameter that is not a view"
    (fun () ->
      one_diagnostic
        (window ^ Fixtures.Ownership.window_widened_with_a_view_of_a_list)
        "ownership.view_escapes");
  Harness.test "a `mut self` method cannot make `self` self-referential" (fun () ->
      one_diagnostic Fixtures.Ownership.cached_viewing_its_own_items "ownership.self_referential");
  Harness.test "the receiver of a `mut self` method stores the method's view arguments" (fun () ->
      one_diagnostic
        (window ^ Fixtures.Ownership.window_widened_then_its_data_pushed)
        "ownership.mutated_while_viewed");
  Harness.test "a call's result views its `mut` arguments" (fun () ->
      one_diagnostic Fixtures.Ownership.first_of_a_mut_list_kept "ownership.mutated_while_viewed");
  Harness.test "a function cannot return a view of an `own` parameter" (fun () ->
      one_diagnostic Fixtures.Ownership.view_of_an_own_parameter_returned "ownership.view_escapes");
  Harness.test "a function can return a view that it received as an `own` argument" (fun () ->
      fine Fixtures.Ownership.own_view_returned);
  Harness.test "a function can return a local that views its parameter" (fun () ->
      fine Fixtures.Ownership.local_view_of_a_parameter_returned);
  Harness.test "a function can return a record that views its parameter" (fun () ->
      fine (window ^ Fixtures.Ownership.window_of_a_parameter_returned));
  Harness.test "a function cannot return a local that views its local" (fun () ->
      one_diagnostic Fixtures.Ownership.local_view_of_a_local_returned "ownership.view_escapes")

let () =
  let take = Fixtures.Ownership.take in
  let moved_twice operator condition =
    Harness.test (operator ^ " may have evaluated its right operand") (fun () ->
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
  Harness.test "an operand that is evaluated last sees the moves of the operands before it"
    (fun () ->
      one_diagnostic (take ^ Fixtures.Ownership.two_moves_in_an_and) "ownership.use_after_move";
      one_diagnostic
        (take ^ Fixtures.Ownership.moves_in_an_or_and_an_and)
        "ownership.use_after_move");
  Harness.test "a move in the right operand is the only move of the place" (fun () ->
      fine (take ^ Fixtures.Ownership.move_in_the_right_operand_of_and);
      fine (take ^ Fixtures.Ownership.move_in_the_right_operand_of_or));
  Harness.test "the moves in a chain of thousands of `&&` are checked" (fun () ->
      let chain = String.concat " && " (List.init 4000 (fun _ -> "flag")) in
      one_diagnostic
        (take
        ^ Printf.sprintf
            "fn f(flag: Bool, box: own Box) -> Bool {\n  %s && take(own box) && take(own box)\n}\n"
            chain)
        "ownership.use_after_move")
