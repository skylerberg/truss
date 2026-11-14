(* Truss source compiled with the standard library and run: the basics. *)

open Codegen_support

let () =
  test "a test calls a function that uses the standard library's arithmetic" (fun () ->
      expect_output Fixtures.Source.test_calls_a_function_that_uses_the_standard
        "test 0 passed\n\
         test 1 failed\n\
         message 51\n\
         assert square(3) == 10\n\
        \  at example/main.truss:10:3\n")

let () =
  passes "loops, variables, and comparisons run" Fixtures.Source.loops_variables_and_comparisons_run;
  passes "a counted for loop runs once per value"
    Fixtures.Source.counted_for_loop_runs_once_per_value;
  passes "records are built and read, and sums matched"
    Fixtures.Source.records_are_built_and_read_and_sums_matched;
  passes "an if is a value, and a return leaves early"
    Fixtures.Source.if_is_a_value_and_a_return_leaves_early;
  passes "the standard library's Option methods run"
    Fixtures.Source.standard_librarys_option_methods_run

let () =
  passes "lists are built, pushed onto, indexed, and looped over"
    Fixtures.Source.lists_are_built_pushed_onto_indexed_and_looped;
  passes "a question mark returns an error early"
    Fixtures.Source.question_mark_returns_an_error_early

let () =
  passes "a string interpolates its parts" Fixtures.Source.string_interpolates_its_parts;
  passes "a record is updated with with" Fixtures.Source.record_is_updated_with_with;
  passes "a lambda reads its caller's locals" Fixtures.Source.lambda_reads_its_callers_locals

let () =
  passes "integers display in decimal, negative ones too"
    Fixtures.Source.integers_display_in_decimal_negative_ones_too;
  passes "strings compare, order, and trim" Fixtures.Source.strings_compare_order_and_trim

let () =
  passes "constants are static data, computed exactly"
    Fixtures.Source.constants_are_static_data_computed_exactly

let () =
  passes "a named function is passed as a function value"
    Fixtures.Source.named_function_is_passed_as_a_function_value;
  passes "a field left out takes its default" Fixtures.Source.field_left_out_takes_its_default;
  passes "a parameter left out takes its default"
    Fixtures.Source.parameter_left_out_takes_its_default;
  passes "an any value calls its implementation's method"
    Fixtures.Source.any_value_calls_its_implementations_method

let () =
  passes "a constant that compares constants is folded"
    Fixtures.Source.constant_that_compares_constants_is_folded;
  passes "a constant made of one that is computed by running is computed by running too"
    Fixtures.Source.constant_made_of_one_that_is_computed_by_running;
  test "a constant whose sum does not fit its type is an error before any code is run" (fun () ->
      let database = Engine.context (Engine.create ~bases:[ Lazy.force checked_standard ] ()) in
      Database.load_package (Engine.of_context database)
        ~name:{ owner = None; name = "example" }
        ~dependencies:[]
        [ (example_file, "let big: Int8 = 100\nlet bigger: Int8 = big + big\n") ];
      match
        List.map
          (fun (diagnostic : Diagnostic.t) -> Diagnostic.Code.name diagnostic.code)
          (Checks.diagnostics database example_file)
      with
      | [ "types.constant_overflow" ] -> ()
      | actual -> fail "got [%s]" (String.concat "; " actual))

let () =
  test "a derived equal stops at the first field that differs" (fun () ->
      let _, compile = load "type Both(first: Int64, second: Int64)\n  derives Equal\n" in
      let equal : Instance.key =
        Code
          {
            path =
              Method
                {
                  owner =
                    Derived
                      {
                        type_ = Top { module_ = example; name = "Both" };
                        trait = Well_known.path Equal;
                      };
                  name = "equal";
                  receiver = Read;
                };
            type_arguments = [];
          }
      in
      let c = Emit_c.For_testing.c (Compile.For_testing.compiled compile equal) in
      let branches =
        List.length
          (String.split_on_char '\n' c
          |> List.filter (fun line -> String.starts_with ~prefix:"  switch (" line))
      in
      if branches <> 2 then fail "expected a branch after each field, got %d:\n%s" branches c)

(* A method of the standard library that only forwards to another lending
   call is not called: the caller makes the inner call itself. An index of
   a list, a slice, or an array, and a loop over one, then cost no call and
   no lend record. *)
let () =
  test "an index of a list, a slice, or an array, and a loop over one, call no lending method"
    (fun () ->
      let _, compile =
        load
          "fn list_at(items: List[Int64]) -> Int64 {\n\
          \  items[2]\n\
           }\n\n\
           fn slice_at(items: Slice[Int64]) -> Int64 {\n\
          \  items[2]\n\
           }\n\n\
           fn array_at(items: Array[Int64, 4]) -> Int64 {\n\
          \  items[2]\n\
           }\n\n\
           fn list_add(items: mut List[Int64]) {\n\
          \  items[2] += 5\n\
           }\n\n\
           fn array_add(items: mut Array[Int64, 4]) {\n\
          \  items[2] += 5\n\
           }\n\n\
           fn list_sum(items: List[Int64]) -> Int64 {\n\
          \  var total: Int64 = 0\n\
          \  for item in items {\n\
          \    total += item\n\
          \  }\n\
          \  total\n\
           }\n\n\
           fn array_sum(items: Array[Int64, 4]) -> Int64 {\n\
          \  var total: Int64 = 0\n\
          \  for item in items {\n\
          \    total += item\n\
          \  }\n\
          \  total\n\
           }\n\n\
           fn list_bump(items: mut List[Int64]) {\n\
          \  for item in mut items {\n\
          \    item += 1\n\
          \  }\n\
           }\n"
      in
      List.iter
        (fun name ->
          let function_ : Instance.key =
            Code { path = Top { module_ = example; name }; type_arguments = [] }
          in
          let c = Emit_c.For_testing.c (Compile.For_testing.compiled compile function_) in
          if contains c "t_lend" then fail "expected no lend record in `%s`:\n%s" name c)
        [
          "list_at";
          "slice_at";
          "array_at";
          "list_add";
          "array_add";
          "list_sum";
          "array_sum";
          "list_bump";
        ])

let () =
  test "negating the least value of a signed type panics, where the checks are on" (fun () ->
      expect_output Fixtures.Source.negating_the_least_value_of_a_signed_type_panics
        "test 0 panicked\nmessage 47\narithmetic overflow\n  at example/main.truss:2:3\n")
