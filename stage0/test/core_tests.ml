(* Tests of the core form. Most tests check a program and compare its
   printed core form with the expected text. *)

open Harness
open Support

(* The printed core form of the definition [name] of the program [text]. *)
let printed_definition text name =
  let database = setup [ ("app::main", text) ] in
  let module_ = module_of "app::main" in
  (match
     List.map
       (fun message -> Diagnostic.make ~code:(Types Mismatch) (Source.span 0 0) message)
       (parse_errors database module_)
     @ Resolve.diagnostics database module_
     @ Interface.diagnostics database module_
     @ Infer.diagnostics database module_
   with
  | [] -> ()
  | actual ->
      failwith
        (String.concat "; "
           (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual)));
  let actual =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        if Path.show key.path = "app::main::" ^ name then Query.demand database Infer.core key
        else None)
      (Query.demand database Resolve.Names.declarations module_)
  in
  match actual with
  | Some form -> Core_print.show form
  | None -> failwith (Printf.sprintf "`%s` has no core form" name)

(* The printed body of the function [name]: the last line of its printed
   core form. Node ids, as in [concurrent #50], are renumbered from [#1] in
   order of first appearance, since an id depends on every node lowered
   before it. *)
let printed_body text name =
  let body =
    match List.rev (String.split_on_char '\n' (printed_definition text name)) with
    | last :: _ -> last
    | [] -> ""
  in
  let renumbered = Buffer.create (String.length body) and ids = Hashtbl.create 4 in
  let length = String.length body in
  let rec digits_end at =
    if at < length && '0' <= body.[at] && body.[at] <= '9' then digits_end (at + 1) else at
  in
  let rec copy at =
    if at < length then
      if body.[at] = '#' && at > 0 && body.[at - 1] = ' ' && digits_end (at + 1) > at + 1 then begin
        let stop = digits_end (at + 1) in
        let id = String.sub body (at + 1) (stop - at - 1) in
        if not (Hashtbl.mem ids id) then Hashtbl.add ids id (Hashtbl.length ids + 1);
        Buffer.add_string renumbered (Printf.sprintf "#%d" (Hashtbl.find ids id));
        copy stop
      end
      else begin
        Buffer.add_char renumbered body.[at];
        copy (at + 1)
      end
  in
  copy 0;
  Buffer.contents renumbered

let expect_definition name text expected =
  test name (fun () ->
      let actual = printed_definition text "second_example" in
      if actual <> expected then fail "found:\n%s" actual)

let expect_body name text expected =
  test name (fun () ->
      let actual = printed_body text "second_example" in
      if actual <> expected then fail "found:\n%s" actual)

let meters = Fixtures.Core.meters
let shape = Fixtures.Core.shape

(* Operators *)

let () =
  expect_body "an operator and a method call on built-in integers both become an Operator"
    Fixtures.Core.operator_and_a_method_call_on_built_in_integers
    "{ add(left, multiply(right, 2)) }";
  expect_body "a comparison of built-in integers becomes a Compare"
    Fixtures.Core.comparison_of_built_in_integers_becomes_a_compare
    "{ ((left <= right) && (left != 0)) }";
  expect_body
    "`<=` on a user type tests the result of `compare`, and `!=` negates a call of `equal`"
    (meters ^ Fixtures.Core.on_a_user_type_tests_the_result_of_compare_and)
    "{ (!(Ordered.compare for Meters by app::main::impl Ordered for Meters(place first, place \
     second) is Greater) || !Equal.equal for Meters by app::main::impl Equal for Meters(place \
     first, place second)) }";
  expect_body "a compound assignment binds its operand, and evaluates its target once"
    Fixtures.Core.compound_assignment_binds_its_operand_and
    "{ compound_assign lent Index.at for List[Int64] by standard::list::impl Index for \
     List[Element](mut place items, 0) lends mut = add(current_target, synthetic#0) with \
     synthetic#0 = 2 }";
  expect_definition "arithmetic in a specification converts its operands to Integer"
    Fixtures.Core.arithmetic_in_a_specification_converts_its
    "fn(count: Int64)\n\
     ensures (add(to_integer(result), to_integer(1)) > to_integer(count))\n\
     { count }"

(* Calls *)

let () =
  expect_body "a call has one argument per parameter, in parameter order"
    Fixtures.Core.call_has_one_argument_per_parameter_in_parameter
    "{ app::main::connect(1, default, false) }";
  expect_body "a read-only parameter receives a place, and an `own` parameter receives a value"
    Fixtures.Core.read_only_parameter_receives_a_place_and_an_own
    "{ app::main::keep(own items, place limit) }";
  expect_body "the first argument of a method call is the receiver"
    Fixtures.Core.first_argument_of_a_method_call_is_the_receiver
    "{ standard::list::List.push(mut self)[Int64](mut place items, own 4); \
     standard::list::List.length[Int64](place items) }";
  expect_body "a String passed as a StringSlice becomes a call of `slice`"
    Fixtures.Core.string_passed_as_a_stringslice_becomes_a_call_of
    "{ app::main::greet(standard::text::String.slice(place name)) }";
  expect_body "a capability method call, and a built-in copy"
    Fixtures.Core.capability_method_call_and_a_built_in_copy
    "{ let _ = standard::capabilities::Clock.now(); copy(place count) }";
  expect_body "a lambda lists its parameters and its captures"
    Fixtures.Core.lambda_lists_its_parameters_and_its_captures
    "{ Iterable.map for List[Int64] by standard::list::impl Iterable for List[Element](place \
     items, lambda(item) capturing step { add(item, step) }) }"

(* Values *)

let () =
  expect_body "a constructor lists every field, and marks an omitted field as default"
    (shape ^ Fixtures.Core.constructor_lists_every_field_and_marks_an_omitted)
    "{ Shape.Square(side: 2, label: default) }";
  expect_body "a range expression becomes a Range record"
    Fixtures.Core.range_expression_becomes_a_range_record
    "{ Range[Int64](start: 1, stop: 5, inclusive: false) }";
  expect_body "an interpolated string becomes a text builder, a call for each piece, and `finish`"
    Fixtures.Core.interpolated_string_becomes_a_text_builder_a_call
    "{ { let var own builder = standard::text::TextBuilder.new(); Display.display for String by \
     standard::text::impl Display for String(place name, mut place builder); \
     standard::text::TextBuilder.write(mut self)(mut place builder, \": \"); Display.display for \
     Int64 by standard::numbers::signed::impl Display for Int64(place count, mut place builder); \
     standard::text::TextBuilder.finish(own self)(own builder) } }";
  expect_body "a list literal, a slice, and an index"
    Fixtures.Core.list_literal_a_slice_and_an_index
    "{ let own numbers = { let var own storage = intrinsic::storage_with_capacity(3); \
     intrinsic::storage_push(mut place storage, own 1); intrinsic::storage_push(mut place storage, \
     own 2); intrinsic::storage_push(mut place storage, own 3); \
     standard::list::List.from_storage[Int64](own storage) }; let _ = slice \
     standard::list::List.slice_range[Int64](place numbers, 1, \
     standard::list::List.length[Int64](place numbers)); lent Index.at for List[Int64] by \
     standard::list::impl Index for List[Element](place numbers, 0) lends }";
  expect_body "a set literal becomes `with_capacity` and one `insert` per element"
    Fixtures.Core.set_literal_becomes_with_capacity_and_one_insert
    "{ { let var own set = standard::set::Set.with_capacity[String](2); \
     standard::set::Set.insert(mut self)[String](mut place set, own first); \
     standard::set::Set.insert(mut self)[String](mut place set, own second); set } }";
  expect_body "a map literal becomes `with_capacity` and one `insert_absent` per entry"
    Fixtures.Core.map_literal_becomes_with_capacity_and_one_insert
    "{ { let var own map = standard::map::Map.with_capacity[Int64, Int64](2); \
     standard::map::Map.insert_absent(mut self)[Int64, Int64](mut place map, own 1, own 2); \
     standard::map::Map.insert_absent(mut self)[Int64, Int64](mut place map, own 3, own 4); map } \
     }";
  expect_body "an empty set literal is the call of `with_capacity`"
    Fixtures.Core.empty_set_literal_is_the_call_of_with_capacity
    "{ standard::set::Set.with_capacity[Int64](0) }";
  expect_body "a slice holds the call of `slice_range`, with an inclusive stop as `stop + 1`"
    Fixtures.Core.slice_holds_the_call_of_slice_range_with_an
    "{ slice standard::list::List.slice_range[Int64](place items, 0, add(last, 1)) }";
  expect_body "a slice of a slice calls the slice's `slice_range`"
    Fixtures.Core.slice_of_a_slice_calls_the_slices_slice_range
    "{ slice standard::list::Slice.slice_range[Int64](place items, 1, 3) }";
  expect_body "a record update lists the replaced fields, and expands the shorthand"
    Fixtures.Core.record_update_lists_the_replaced_fields_and "{ config with (port: port) }"

(* Control flow *)

let () =
  expect_body "`?` becomes a match that returns the error"
    Fixtures.Core.becomes_a_match_that_returns_the_error
    "{ let own value = match app::main::parse(place text) { Ok(value: own value) => { value } \
     Err(error: own error) => { return Result[Int64, String].Err(error: error) } }; Result[Int64, \
     String].Ok(value: value) }";
  expect_body "a match on a place borrows the place"
    (shape ^ Fixtures.Core.match_on_a_place_borrows_the_place)
    "{ match place shape { Circle(radius: radius) => { radius } Square(side: side) if (side > 2) \
     => { side } _ => { 0 } } }";
  expect_body "a `match` or `is` on a value binds `own`, even if the receiver of the call is marked"
    Fixtures.Core.match_or_is_on_a_value_binds_own_even_if_the
    "{ if (app::main::Queue.take(mut self)(mut place queue) is Some(value: own first)) { return \
     standard::list::List.length[Int64](place first) }; match app::main::Queue.take(mut self)(mut \
     place queue) { Some(value: own second) => { standard::list::List.length[Int64](place second) \
     } None => { 0 } } }";
  expect_body "`is` becomes a Matches"
    (shape ^ Fixtures.Core.is_becomes_a_matches)
    "{ if (place shape is Circle(radius: radius)) { return radius }; 0 }";
  expect_body
    "a `for` loop over a collection calls `each`, and one over a range is an Integer_range"
    Fixtures.Core.for_loop_over_a_collection_calls_each_and_one_over
    "{ let var own total = 0; for item in yielding_call standard::list::impl Iterable for \
     List[Element].each[Int64](place items) { compound_assign total = add(current_target, \
     synthetic#0) with synthetic#0 = item }; for step in integer_range 0..=total {  }; while \
     (total < 3) { compound_assign total = add(current_target, synthetic#1) with synthetic#1 = 1 \
     }; total }"

let () =
  expect_body "a `for` loop over the result of a call calls `each` on the result"
    Fixtures.Core.for_loop_over_the_result_of_a_call_calls_each_on
    "{ for item in yielding_call standard::list::impl Iterable for \
     List[Element].each[Int64](app::main::make()) { let _ = place item } }"

(* Specifications *)

let () =
  expect_definition "first_value `requires` clause with a quantifier is not executable"
    Fixtures.Core.requires_clause_with_a_quantifier_is_not
    "fn(items: List[Int64], limit: Int64)\n\
     requires (limit > 0)\n\
     requires forall index in 0..standard::list::List.length[Int64](place items) { (lent Index.at \
     for List[Int64] by standard::list::impl Index for List[Element](place items, place index) \
     lends < limit) } (not executable)\n\
     ensures (result >= 0)\n\
     { proof { assert (limit > 0) }; limit }"

(* Other constructs *)

let () =
  expect_body "a tagged string becomes a call of `from_template`"
    Fixtures.Core.tagged_string_becomes_a_call_of_from_template
    "{ template(\"hey \", \"!\") call FromTemplate.from_template for Shout by app::main::impl \
     FromTemplate for Shout(own Template[String](literals: { let var own storage = \
     intrinsic::storage_with_capacity(2); intrinsic::storage_push(mut place storage, own \
     Literal(text: \"hey \")); intrinsic::storage_push(mut place storage, own Literal(text: \
     \"!\")); standard::list::List.from_storage[Literal](own storage) }, parts: { let var own \
     storage = intrinsic::storage_with_capacity(1); intrinsic::storage_push(mut place storage, own \
     name); standard::list::List.from_storage[String](own storage) })) }";
  expect_body "a cursor is advanced by a `for` loop or by a call of `next`"
    Fixtures.Core.cursor_is_advanced_by_a_for_loop_or_by_a_call_of
    "{ let var own first = app::main::count_to(3); while (cursor_next(first) is Some(value: own \
     left)) { let _ = place left }; for value in yielding_call app::main::count_to(2) {  }; for \
     value in cursor first {  } }";
  expect_body "a conversion to `any` records the impl, and a method call on `any` is dynamic"
    Fixtures.Core.conversion_to_any_records_the_impl_and_a_method
    "{ let own source = any Source[Item = Int64](numbers by app::main::impl Source for Numbers); \
     Source[Item = Int64].first for any Source[Item = Int64] by any(place source) }";
  expect_body "the result of a `lends mut` method is a place that can be assigned"
    Fixtures.Core.result_of_a_lends_mut_method_is_a_place_that_can
    "{ lent app::main::Grid.cell(mut self)(mut place grid, 0) lends mut.state = 4 }";
  expect_body
    "a `mut self` method called on an indexed element indexes with the `mut self` version of `at`"
    Fixtures.Core.mut_self_method_called_on_an_indexed_element
    "{ app::main::Worker.reset(mut self)(mut place lent Index.at for List[Worker] by \
     standard::list::impl Index for List[Element](mut place workers, place index) lends mut) }";
  expect_body "a `for` loop over a `mut` element indexes with the `mut self` version of `at`"
    Fixtures.Core.for_loop_over_a_mut_element_indexes_with_the_mut
    "{ for mut cell in yielding_call standard::list::List.each(mut self)[Int64](mut place lent \
     Index.at for List[List[Int64]] by standard::list::impl Index for List[Element](mut place \
     rows, 0) lends mut) { cell = 0 } }";
  test "a `lends mut` method yields a mutable place" (fun () ->
      let actual =
        printed_body Fixtures.Core.lends_mut_method_yields_a_mutable_place "Grid.cell(mut self)"
      in
      if
        actual
        <> "{ yield mut place lent Index.at for List[Cell] by standard::list::impl Index for \
            List[Element](mut place self.cells, place index) lends mut }"
      then fail "found:\n%s" actual);
  test "a yielded constructor lends the places among its fields" (fun () ->
      let actual =
        printed_body Fixtures.Core.yielded_constructor_lends_the_places_among_its "Shelf.first"
      in
      if
        actual
        <> "{ if standard::list::List.is_empty[String](place self.books) { yield \
            Option[First].None() } else { yield Option[First].Some(value: First(title: place lent \
            Index.at for List[String] by standard::list::impl Index for List[Element](place \
            self.books, 0) lends, rest: slice standard::list::List.slice_range[String](place \
            self.books, 1, standard::list::List.length[String](place self.books)))) } }"
      then fail "found:\n%s" actual);
  test "a constructor yielded `mut` lends the places that are marked `mut`" (fun () ->
      let actual =
        printed_body Fixtures.Core.constructor_yielded_mut_lends_the_places_that_are
          "Shelf.numbered(mut self)"
      in
      if
        actual
        <> "{ let var own index = 0; while (index < standard::list::List.length[String](place \
            self.books)) { yield mut Numbered(index: index, title: place lent Index.at for \
            List[String] by standard::list::impl Index for List[Element](mut place self.books, \
            place index) lends mut); index = add(index, 1) } }"
      then fail "found:\n%s" actual);
  expect_definition "a quantifier over a collection calls `each` in code, and not in a contract"
    Fixtures.Core.quantifier_over_a_collection_calls_each_in_code
    "fn(items: List[Int64])\n\
     ensures (result == exists item in items { (item < 0) })\n\
     { exists item in yielding_call standard::list::impl Iterable for \
     List[Element].each[Int64](place items) { (item < 0) } }";
  expect_body "a method of `Cursor` on a yielding method's cursor is a call, and `next` is not"
    Fixtures.Core.method_of_cursor_on_a_yielding_methods_cursor_is_a
    "{ let var own cursor = standard::list::impl Iterable for List[Element].each[Int64](place \
     items); let _ = cursor_next(cursor); Cursor.count for Skip[the cursor of standard::list::impl \
     Iterable for List[Element].each] by standard::cursors::impl Cursor for Skip[Source](own \
     Cursor.skip for the cursor of standard::list::impl Iterable for List[Element].each by derived \
     standard::core::Cursor for standard::list::impl Iterable for List[Element].each(own \
     standard::list::impl Iterable for List[Element].each[Int64](place items), 1)) }";
  expect_body "an early exit from concurrent code names the tasks that it ends"
    Fixtures.Core.early_exit_from_concurrent_code_names_the_tasks
    "{ for item in yielding_call standard::list::impl Iterable for List[Element].each[Int64](place \
     items) { concurrent #1 { let own first = match app::main::fetch(place item) { Ok(value: own \
     value) => { value } Err(error: own error) => { task_exit branch 0 of #1 { return \
     Result[Int64, Int64].Err(error: error) } } }; if (item > 3) { task_exit branch 1 of #1 { \
     break } } }; let _ = place first }; concurrent #2 for item in yielding_call \
     standard::list::impl Iterable for List[Element].each[Int64](place items) { if (item > 5) { \
     task_exit an iteration of #2 { break } }; if (item > 4) { continue }; if (item > 3) { \
     task_exit an iteration of #2 { return Result[Int64, Int64].Err(error: item) } } }; \
     Result[Int64, Int64].Ok(value: 0) }";
  expect_body "an assignment through an index calls `assign` where the type has it"
    Fixtures.Core.assignment_through_an_index_calls_assign_where_the
    "{ let var own ports = { let var own map = standard::map::Map.with_capacity[String, Int64](1); \
     standard::map::Map.insert_absent(mut self)[String, Int64](mut place map, own \"http\", own \
     80); map }; let var own scores = { let var own storage = intrinsic::storage_with_capacity(1); \
     intrinsic::storage_push(mut place storage, own 1); \
     standard::list::List.from_storage[Int64](own storage) }; IndexAssign.assign for Map[String, \
     Int64] by standard::map::impl core::IndexAssign for Map[Key, Value](mut place ports, own \
     name, own 8080); lent Index.at for List[Int64] by standard::list::impl Index for \
     List[Element](mut place scores, 0) lends mut = 5 }";
  expect_body "patterns of constants, ranges, and strings"
    Fixtures.Core.patterns_of_constants_ranges_and_strings
    "{ let own size = match place count { app::main::limit => { 1 } 0..5 => { 2 } 7 | 8 => { 3 } _ \
     => { 4 } }; match place name { equal to \"yes\" => { size } _ => { 0 } } }";
  expect_definition "a quantifier over a type, and old" Fixtures.Core.quantifier_over_a_type_and_old
    "fn(count: Int64)\n\
     ensures (result == forall value: Int64 { (add(to_integer(value), to_integer(0)) == \
     to_integer(value)) })\n\
     ensures (old(count) == count)\n\
     { true }"

let () =
  expect_body "a `mut` parameter receives a slice of a place"
    Fixtures.Core.mut_parameter_receives_a_slice_of_a_place
    "{ app::main::sort_part(mut slice standard::list::List.slice_range[Int64](place items, 0, 2)) }"

(* Holes *)

let () =
  expect_body
    "a use of a local whose type is a hole is a Todo, and a pattern on a hole is a Wildcard"
    Fixtures.Core.use_of_a_local_whose_type_is_a_hole_is_a_todo_and "{ let _ = todo; todo }";
  expect_body "an operation on a hole evaluates its operands and ends in a Todo"
    Fixtures.Core.operation_on_a_hole_evaluates_its_operands_and
    "{ let _ = todo; { let _ = todo; let _ = place count; let _ = 1; todo } }";
  List.iter
    (fun statement ->
      test (Printf.sprintf "`%s` on a hole has a core form" statement) (fun () ->
          no_diagnostics
            ~check:(fun database module_ ->
              Resolve.diagnostics database module_
              @ Interface.diagnostics database module_
              @ Infer.diagnostics database module_)
            [
              ( "app::main",
                "type Config(port: Int64)\n\n\
                 fn take(count: Int64) -> Int64 {\n\
                \  count\n\
                 }\n\n\
                 fn second_example(items: List[Int64], config: Config) -> Int64 {\n\
                \  var hole = todo\n\
                \  " ^ statement ^ "\n  config.port\n}\n" );
            ]))
    [
      "let member = hole.field";
      "let called = hole(1, items)";
      "let result = hole.method(items)";
      "let mapped = items.map(fn(item) { item + hole })";
      "let indexed = hole[0]";
      "let sliced = hole[1..]";
      "let sum = hole + 1";
      "let negated = -hole";
      "let same = hole == 1";
      "let less = 1 < hole";
      "let tried = hole?";
      "let updated = hole with (port: 1)";
      "let text = \"${hole} and ${items.length()}\"";
      "let listed = [hole, hole]";
      "let passed = take(hole)";
      "let chosen = if hole is Some(inner) { inner } else { 0 }";
      "let matched = match hole {\n    Some(inner) if inner > 0 => inner\n    _ => 0\n  }";
      "let Some(bound) = hole else { return 0 }";
      "for item in hole {\n    let _ = item\n  }";
      "hole.field = 1";
      "hole += 1";
      "hole = 2";
      "while hole is Some(inner) {\n    let _ = inner\n  }";
      "let shown = echo hole";
      "let field = Config(port: hole)";
    ]

(* Capabilities *)

let () =
  let apply = Fixtures.Core.apply in
  expect_body "a capability parameter is inferred as the set of capabilities the argument uses"
    (apply ^ Fixtures.Core.capability_parameter_is_inferred_as_the_set_of)
    "{ app::main::apply[{Console}](lambda() { \
     standard::capabilities::Console.print_line(standard::text::String.slice(\"inside\")) }) }";
  expect_body "a named function passed for a capability-generic parameter is a Function_value"
    (apply ^ Fixtures.Core.named_function_passed_for_a_capability_generic)
    "{ app::main::apply[{Console}](fn app::main::shout) }";
  test "a call's `uses` and a lambda's type contain the inferred set, not the callee's parameter"
    (fun () ->
      let text = apply ^ Fixtures.Core.calls_uses_and_a_lambdas_type_contain_the_inferred in
      let database = setup [ ("app::main", text) ] in
      let actual = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.show key.path = "app::main::second_example" then
            match Query.demand database Infer.core key with
            | Some form ->
                Core_walk.definition
                  {
                    Core_walk.ignore_all with
                    expression =
                      (fun (node : Core.expression) ->
                        match node.kind with
                        | Call { callee = Function { path; _ }; uses; _ }
                          when Path.show path = "app::main::apply" ->
                            actual :=
                              ("needs " ^ Types.show_argument (Capabilities uses)) :: !actual
                        | Lambda _ -> actual := Types.show node.type_ :: !actual
                        | _ -> ());
                  }
                  form.definition
            | None -> fail "no core form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main"));
      if List.sort compare !actual <> [ "(fn() uses Console)"; "needs {Console}" ] then
        fail "found [%s]" (String.concat "; " !actual));
  test "a capability parameter in a result type is inferred separately for each call" (fun () ->
      let text = Fixtures.Core.capability_parameter_in_a_result_type_is_inferred in
      let database = setup [ ("app::main", text) ] in
      let actual = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.show key.path = "app::main::second_example" then
            match Query.demand database Infer.core key with
            | Some form ->
                Core_walk.definition
                  {
                    Core_walk.ignore_all with
                    pattern =
                      (fun (node : Core.pattern) ->
                        match node.kind with
                        | Bind { name; _ } ->
                            actual := (name ^ ": " ^ Types.show node.type_) :: !actual
                        | _ -> ());
                  }
                  form.definition
            | None -> fail "no core form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main"));
      if List.sort compare !actual <> [ "first: (fn() uses Console)"; "second: (fn() uses Clock)" ]
      then fail "found [%s]" (String.concat "; " !actual))

(* Origins *)

let () =
  test "a node's origin gives its source span" (fun () ->
      let text = Fixtures.Core.nodes_origin_gives_its_source_span in
      let database = setup [ ("app::main", text) ] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          match
            ( Query.demand database Infer.core key,
              Query.demand database Resolve.Names.spans key,
              Query.demand database Resolve.Names.text key )
          with
          | Some form, Some spans, Some written ->
              let actual = ref [] in
              Core_walk.definition
                {
                  Core_walk.ignore_all with
                  statement =
                    (fun (node : Core.statement) ->
                      match node.kind with
                      | Compound_assign _ ->
                          let span = spans.(node.origin) in
                          actual :=
                            String.sub written span.start (span.stop - span.start) :: !actual
                      | _ -> ());
                }
                form.definition;
              if !actual <> [ "total += item" ] then fail "found [%s]" (String.concat "; " !actual)
          | _ -> fail "no core form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main")))

let () =
  expect_definition "a cost clause names its resource" Fixtures.Core.cost_clause_names_its_resource
    "fn(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
     cost calls(visit) == standard::list::List.length[Int64](place items)\n\
     cost calls(standard::capabilities::Clock.now) <= 1\n\
     cost time O(multiply(to_integer(standard::list::List.length[Int64](place items)), time(visit)))\n\
     {  }"

let () =
  expect_definition "`log` and `power` are specification functions outside a cost bound too"
    Fixtures.Core.log_and_power_are_specification_functions_outside
    "fn(value: UInt64)\n\
     ensures (to_integer(result) <= add(log(value), 1))\n\
     ensures (power(2, result) >= 1)\n\
     { todo }";
  expect_definition "a function of the file named `power` is called in a specification"
    Fixtures.Core.function_of_the_file_named_power_is_called_in_a
    "fn(value: Int64)\nensures (result == app::main::power(place value, 1))\n{ value }";
  expect_definition "the time of a method of a type parameter's bound names the trait method"
    Fixtures.Core.time_of_a_method_of_a_type_parameters_bound_names
    "fn(items: List[Element], item: Element)\n\
     cost time O(multiply(to_integer(standard::list::List.length[Element](place items)), \
     time(Equal.equal for Element by a bound)))\n\
     { todo }";
  test "in a trait, `time(Self.method)` names the trait's own method" (fun () ->
      no_diagnostics
        ~check:(fun database module_ ->
          Resolve.diagnostics database module_
          @ Interface.diagnostics database module_
          @ Infer.diagnostics database module_)
        [ ("app::main", Fixtures.Core.in_a_trait_time_self_method_names_the_traits_own) ])

let () =
  test "the origin of a cost is its cost clause" (fun () ->
      let text = Fixtures.Core.origin_of_a_cost_is_its_cost_clause in
      let database = setup [ ("app::main", text) ] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          match
            ( Query.demand database Infer.core key,
              Query.demand database Resolve.Names.spans key,
              Query.demand database Resolve.Names.text key )
          with
          | ( Some { definition = Function { contract = { costs = [ cost ]; _ }; _ }; _ },
              Some spans,
              Some written ) ->
              let span = spans.(cost.origin) in
              let quoted = String.sub written span.start (span.stop - span.start) in
              if quoted <> "cost time O(items.length())" then fail "found `%s`" quoted
          | _ -> fail "no core form with exactly one cost")
        (Query.demand database Resolve.Names.declarations (module_of "app::main")))

(* The standard library's core forms satisfy the invariants. *)

let () =
  let database = setup [] in
  let forms = ref 0 in
  List.iter
    (fun ((module_ : Path.module_), _) ->
      test
        (Printf.sprintf "%s's core forms satisfy the invariants" (Path.show_module module_))
        (fun () -> forms := !forms + check_module_core_invariants database module_))
    Standard_library.modules;
  test "the standard library has core forms" (fun () ->
      if !forms < 500 then fail "only %d of its definitions have one" !forms)

(* Derived methods *)

let printed_derived text type_name trait name receiver =
  let database = setup [ ("app::main", text) ] in
  let path : Path.t =
    Method
      {
        owner =
          Derived
            {
              type_ = Top { module_ = module_of "app::main"; name = type_name };
              trait =
                List.find
                  (fun (path : Path.t) ->
                    match path with Top { name; _ } -> name = trait | _ -> false)
                  (List.map Well_known.path Well_known.all);
            };
        name;
        receiver;
      }
  in
  match Query.demand database Infer.derived path with
  | Some form -> Core_print.show form
  | None -> failwith "the derived method has no core form"

let expect_derived test_name text type_name trait name receiver expected =
  test test_name (fun () ->
      let actual = printed_derived text type_name trait name receiver in
      if actual <> expected then fail "found:\n%s" actual)

let pair =
  "type Pair[Second](first: Int64, second: Second)\n  derives Equal, Hash, Ordered, Default\n\n"

let light = Fixtures.Core.light
let reading = Fixtures.Core.reading
let signal = Fixtures.Core.signal

let () =
  expect_derived "a record's derived equal compares each field" pair "Pair" "Equal" "equal" Read
    "fn(self: Pair[Second], other: Pair[Second])\n\
     { (Equal.equal for Int64 by standard::numbers::signed::impl Equal for Int64(place self.first, \
     place other.first) && Equal.equal for Second by a bound(place self.second, place \
     other.second)) }";
  expect_derived
    "first_value sum type's derived equal compares the fields of matching variants, and is false \
     for different variants"
    light "Light" "Equal" "equal" Read
    "fn(self: Light, other: Light)\n\
     { match place self { Off => { (place other is Off) } Dim(level: level) => { match place other \
     { Dim(level: other_level) => { Equal.equal for Int64 by standard::numbers::signed::impl Equal \
     for Int64(place level, place other_level) } _ => { false } } } On => { (place other is On) } \
     } }";
  expect_derived "a derived hash writes the variant's index and then each field" light "Light"
    "Hash" "hash" Read
    "fn(self: Light, mut hasher: Hasher)\n\
     { match place self { Off => { standard::core::Hasher.write(mut self)(mut place hasher, 0) } \
     Dim(level: level) => { standard::core::Hasher.write(mut self)(mut place hasher, 1); Hash.hash \
     for Int64 by standard::numbers::signed::impl Hash for Int64(place level, mut place hasher) } \
     On => { standard::core::Hasher.write(mut self)(mut place hasher, 2) } } }";
  expect_derived
    "a record's derived compare compares the next field only if the previous fields are equal" pair
    "Pair" "Ordered" "compare" Read
    "fn(self: Pair[Second], other: Pair[Second])\n\
     { match Ordered.compare for Int64 by standard::numbers::signed::impl Ordered for Int64(place \
     self.first, place other.first) { Equal => { Ordered.compare for Second by a bound(place \
     self.second, place other.second) } own decided => { decided } } }";
  expect_derived "a sum type's derived compare orders by variant index, then by fields" light
    "Light" "Ordered" "compare" Read
    "fn(self: Light, other: Light)\n\
     { let own theirs = match place other { Off => { 0 } Dim => { 1 } On => { 2 } }; match place \
     self { Off => { match place other { Off => { Ordering.Equal() } _ => { if (0 < theirs) { \
     Ordering.Less() } else { Ordering.Greater() } } } } Dim(level: level) => { match place other \
     { Dim(level: other_level) => { Ordered.compare for Int64 by standard::numbers::signed::impl \
     Ordered for Int64(place level, place other_level) } _ => { if (1 < theirs) { Ordering.Less() \
     } else { Ordering.Greater() } } } } On => { match place other { On => { Ordering.Equal() } _ \
     => { if (2 < theirs) { Ordering.Less() } else { Ordering.Greater() } } } } } }";
  expect_derived "a derived default calls `default` for each field" pair "Pair" "Default" "default"
    Static
    "fn()\n\
     { Pair[Second](first: Default.default for Int64 by standard::numbers::signed::impl Default \
     for Int64(), second: Default.default for Second by a bound()) }";
  expect_derived "a record's derived serialize writes each field by name, in declaration order"
    reading "Reading" "Serialize" "serialize" Read
    "fn(self: Reading, mut sink: Sink)\n\
     { Serializer.begin_record for Sink by a bound(mut place sink, 2); Serializer.field for Sink \
     by a bound(mut place sink, \"sensor\"); Serialize.serialize for String by \
     standard::serialization::impl Serialize for String(place self.sensor, mut place sink); \
     Serializer.field for Sink by a bound(mut place sink, \"value\"); Serialize.serialize for \
     Int64 by standard::serialization::impl Serialize for Int64(place self.value, mut place sink); \
     Serializer.end_record for Sink by a bound(mut place sink) }";
  expect_derived "a record's derived deserialize reads a field with a default only if it is present"
    reading "Reading" "Deserialize" "deserialize" Static
    "fn(mut source: Source)\n\
     { match Deserializer.begin_record for Source by a bound(mut place source) { Ok(value: own \
     value) => { value } Err(error: own error) => { return Result[Reading, Error].Err(error: \
     error) } }; let own sensor = match standard::serialization::required[String, Source](mut \
     place source, \"sensor\") { Ok(value: own value) => { value } Err(error: own error) => { \
     return Result[Reading, Error].Err(error: error) } }; let var own built = Reading(sensor: \
     sensor, value: default); match match standard::serialization::optional[Int64, Source](mut \
     place source, \"value\") { Ok(value: own value) => { value } Err(error: own error) => { \
     return Result[Reading, Error].Err(error: error) } } { Some(value: own value) => { built.value \
     = value } _ => {  } }; Deserializer.end_record for Source by a bound(mut place source); \
     Result[Reading, Error].Ok(value: built) }";
  expect_derived "a sum type's derived serialize writes the variant's name, then its fields" signal
    "Signal" "Serialize" "serialize" Read
    "fn(self: Signal, mut sink: Sink)\n\
     { match place self { Off => { Serializer.begin_variant for Sink by a bound(mut place sink, \
     \"Off\", 0); Serializer.end_variant for Sink by a bound(mut place sink) } Level(value: value) \
     => { Serializer.begin_variant for Sink by a bound(mut place sink, \"Level\", 1); \
     Serializer.field for Sink by a bound(mut place sink, \"value\"); Serialize.serialize for \
     Int64 by standard::serialization::impl Serialize for Int64(place value, mut place sink); \
     Serializer.end_variant for Sink by a bound(mut place sink) } } }";
  expect_derived "a sum type's derived deserialize reads the variant by its name" signal "Signal"
    "Deserialize" "deserialize" Static
    "fn(mut source: Source)\n\
     { let own name = match Deserializer.variant for Source by a bound(mut place source) { \
     Ok(value: own value) => { value } Err(error: own error) => { return Result[Signal, \
     Error].Err(error: error) } }; match place name { equal to \"Off\" => { let own built = \
     Signal.Off(); Deserializer.end_variant for Source by a bound(mut place source); \
     Result[Signal, Error].Ok(value: built) } equal to \"Level\" => { let own value = match \
     standard::serialization::required[Int64, Source](mut place source, \"value\") { Ok(value: own \
     value) => { value } Err(error: own error) => { return Result[Signal, Error].Err(error: error) \
     } }; let own built = Signal.Level(value: value); Deserializer.end_variant for Source by a \
     bound(mut place source); Result[Signal, Error].Ok(value: built) } _ => { return \
     Result[Signal, Error].Err(error: standard::serialization::unknown_variant[Source](place \
     source, place name)) } } }";
  test "a `todo` type has no derived core form" (fun () ->
      let database = setup [ ("app::main", "type Later = todo\n  derives Equal\n") ] in
      let path : Path.t =
        Method
          {
            owner =
              Derived
                {
                  type_ = Top { module_ = module_of "app::main"; name = "Later" };
                  trait = Well_known.path Equal;
                };
            name = "equal";
            receiver = Read;
          }
      in
      if Query.demand database Infer.derived path <> None then fail "it has a core form");
  test "every method of a derived impl in the standard library has a core form" (fun () ->
      let database = setup [] in
      let derived =
        List.filter_map
          (fun (_, (impl : Path.t)) -> match impl with Derived _ -> Some impl | _ -> None)
          (Query.demand database Interface.Impls.index Path.standard_package)
      in
      if derived = [] then fail "the standard library derives nothing";
      List.iter
        (fun impl ->
          match Interface.Impls.impl_interface database impl with
          | None -> fail "`%s` has no interface" (Path.show impl)
          | Some interface ->
              let provided =
                match
                  Query.demand database Interface.Environment.trait_interface
                    interface.implements.trait
                with
                | Some trait ->
                    List.filter_map
                      (fun (method_ : Types.trait_method) ->
                        if method_.provided then Some method_.method_name else None)
                      trait.methods
                | None -> []
              in
              List.iter
                (fun (name, receiver, _) ->
                  match
                    Query.demand database Infer.derived (Method { owner = impl; name; receiver })
                  with
                  | Some _ -> ()
                  | None ->
                      if not (List.mem name provided) then
                        fail "`%s` has no core form for `%s`" (Path.show impl) name
                  | exception Compiler_bug.Bug bug ->
                      fail "`%s`, `%s`: %s" (Path.show impl) name (Compiler_bug.to_string bug))
                interface.impl_methods)
        derived)

(* [Infer.core_of_path] *)

let () =
  let text = Fixtures.Core.described_both in
  let both : Path.t = Top { module_ = module_of "app::main"; name = "Both" } in
  let described : Types.trait_reference =
    {
      trait = Top { module_ = module_of "app::main"; name = "Described" };
      trait_arguments = [];
      associated = [];
    }
  in
  let core_of_method name =
    let database = setup [ ("app::main", text) ] in
    let parameter : Types.parameter = { owner = both; name = "Value" } in
    let bounds (actual : Types.parameter) = if actual = parameter then [ described ] else [] in
    let owner =
      match
        Interface.Impls.implements database ~bounds
          (Types.named both [ Types.Parameter parameter ])
          described
      with
      | Some (From_impl { impl; _ }) -> impl
      | _ -> failwith "no impl"
    in
    match Query.demand database Infer.core_of_path (Method { owner; name; receiver = Read }) with
    | Some (form, substitution) ->
        ( List.hd (List.rev (String.split_on_char '\n' (Core_print.show form))),
          List.map
            (fun ((parameter : Types.parameter), argument) ->
              parameter.name ^ " = " ^ Types.show_argument argument)
            substitution )
    | None -> failwith "no core form"
  in
  test "a method defined in an impl has its own core form" (fun () ->
      match core_of_method "describe" with
      | "{ Described.describe for Value by a bound(place self.first) }", [] -> ()
      | actual, _ -> fail "found %s" actual);
  test
    "a method inherited from a trait has the default method's core form and a substitution for Self"
    (fun () ->
      match core_of_method "twice" with
      | ( "{ add(Described.describe for Self by a bound(place self), Described.describe for Self \
           by a bound(place self)) }",
          [ "Self = Both[Value]" ] ) ->
          ()
      | actual, substitution -> fail "found %s with [%s]" actual (String.concat "; " substitution));
  test "a method of a derived impl has the generated core form" (fun () ->
      let database = setup [ ("app::main", text) ] in
      let owner : Path.t = Derived { type_ = both; trait = Well_known.path Equal } in
      match
        ( Query.demand database Infer.core_of_path
            (Method { owner; name = "equal"; receiver = Read }),
          Query.demand database Infer.core_of_path
            (Method { owner; name = "not_equal"; receiver = Read }) )
      with
      | Some (_, []), Some (_, [ _ ]) -> ()
      | _ ->
          fail "expected the derived method with no substitution and the inherited method with one")

(* A law's proof *)

let pair_ordering = Fixtures.Core.pair_ordering

let () =
  test "a law's proof has the law's parameters, with the proof's type for Self" (fun () ->
      let actual =
        printed_definition
          (pair_ordering
         ^ "proof Ordered.agrees_with_equal for Pair {\n  only_equal(first, second: second)\n}\n")
          "proof Ordered.agrees_with_equal for Pair"
      in
      let expected =
        "proof(first: Pair, second: Pair) { app::main::only_equal(place synthetic#0, place \
         synthetic#1) }"
      in
      if actual <> expected then fail "found:\n%s" actual)

(* [Infer.specification] *)

let () =
  let specification text name =
    let database = setup [ ("app::main", text) ] in
    let actual =
      List.find_map
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.show key.path = "app::main::" ^ name then
            Option.map
              (fun form -> (database, key, form))
              (Query.demand database Infer.specification key)
          else None)
        (Query.demand database Resolve.Names.declarations (module_of "app::main"))
    in
    match actual with
    | Some actual -> actual
    | None -> failwith (Printf.sprintf "`%s` has no specification" name)
  in
  let equal first second name =
    let _, _, first = specification first name and _, _, second = specification second name in
    first = second
  in
  let bump body =
    "fn bump(counter: mut Int64, by: Int64)\n  requires by > 0\n  cost time O(1)\n{\n  " ^ body
    ^ "\n}\n"
  in
  let double body = "fn double(value: Int64) -> Int64\n  cost time O(1)\n{\n  " ^ body ^ "\n}\n" in
  test "editing the body of a function that mutates an argument leaves its specification equal"
    (fun () ->
      if not (equal (bump "counter += by") (bump "counter = counter + by + 0") "bump") then
        fail "the specification changed");
  test "editing the body of a function without a time clause leaves its specification equal"
    (fun () ->
      let slow body = "fn slow(value: Int64) -> Int64 {\n  " ^ body ^ "\n}\n" in
      if not (equal (slow "value") (slow "let same = value\n  same") "slow") then
        fail "the specification changed");
  test "editing a clause changes the specification" (fun () ->
      if
        equal (bump "counter += by") Fixtures.Core.editing_a_clause_changes_the_specification "bump"
      then fail "the specification did not change");
  test "editing the body of a function in the logic changes its specification" (fun () ->
      if equal (double "value + value") (double "value * 2") "double" then
        fail "the specification did not change");
  test "a specification without its body meets the core form's invariants" (fun () ->
      let database, key, form = specification (bump "counter += by") "bump" in
      (match form.definition with
      | Function { body = None; _ } -> ()
      | _ -> fail "the body is in the specification");
      check_core_invariants database key form);
  test "the specification that other packages read has the body of a transparent function only"
    (fun () ->
      let exported modifier =
        let database =
          setup
            [
              ( "app::main",
                Printf.sprintf
                  "public%s fn double(value: Int64) -> Int64\n\
                  \  cost time O(1)\n\
                   {\n\
                  \  value + value\n\
                   }\n"
                  modifier );
            ]
        in
        List.find_map
          (fun (declaration : Resolve.Names.declaration) ->
            Query.demand database Infer.exported_specification (Resolve.Names.key_of declaration))
          (Query.demand database Resolve.Names.declarations (module_of "app::main"))
      in
      (match exported " transparent" with
      | Some { definition = Function { body = Some _; _ }; _ } -> ()
      | _ -> fail "the body of a transparent function is not in the exported specification");
      match exported "" with
      | Some { definition = Function { body = None; _ }; _ } -> ()
      | _ -> fail "the body of a function that is not transparent is in the exported specification");
  test "a theorem's specification has no body" (fun () ->
      let _, _, form = specification Fixtures.Core.theorems_specification_has_no_body "doubled" in
      match form.definition with
      | Function { body = None; _ } -> ()
      | _ -> fail "the body is in the specification");
  test "the body that a trait provides for a method is in the method's specification" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Core.body_that_a_trait_provides_for_a_method_is_in_the) ]
      in
      let actual =
        List.find_map
          (fun (declaration : Resolve.Names.declaration) ->
            match declaration.path with
            | Method { name = "bump"; _ } ->
                Query.demand database Infer.specification (Resolve.Names.key_of declaration)
            | _ -> None)
          (Query.demand database Resolve.Names.declarations (module_of "app::main"))
      in
      match actual with
      | Some { definition = Function { body = Some _; _ }; _ } -> ()
      | _ -> fail "the provided body is not in the specification")
