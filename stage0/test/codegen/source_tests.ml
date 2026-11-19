let () =
  Codegen_support.test "a test calls a function that uses the standard library's arithmetic"
    (fun () ->
      Codegen_support.expect_output Fixtures.Source.square_test
        "test 0 passed\n\
         test 1 failed\n\
         message 52\n\
         assert square(3) == 10\n\
        \  at example/main.truss:10:10\n")

let () =
  Codegen_support.test "a failed assert of a pattern test quotes the whole condition" (fun () ->
      Codegen_support.expect_output Fixtures.Source.failed_assert_of_a_pattern
        "test 0 failed\nmessage 51\nassert find(1) is None\n  at example/main.truss:6:10\n")

let () =
  Codegen_support.test
    "a constant whose sum does not fit its type is an error before any code is run" (fun () ->
      let packages =
        Codegen_support.make_example_package
          [ (Codegen_support.example_file, "let big: Int8 = 100\nlet bigger: Int8 = big + big\n") ]
      in
      match
        List.map
          (fun (diagnostic : Diagnostic.t) -> Diagnostic.Code.name diagnostic.code)
          (Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers
             (Codegen_support.make_database packages)
             Codegen_support.example_file)
      with
      | [ "types.constant_overflow" ] -> ()
      | actual -> Codegen_support.fail "got [%s]" (String.concat "; " actual))

let () =
  Codegen_support.test "a derived equal stops at the first field that differs" (fun () ->
      let equal : Lowered.Item.t =
        Code
          {
            path =
              Well_known.make_impl_method_path Equal_equal
                ~impl:
                  (Derived
                     {
                       type_ = Top { module_ = Codegen_support.example; name = "Both" };
                       trait = Well_known.make_path Equal;
                     });
            instantiation = Ground.no_instantiation;
          }
      in
      let _, backend =
        Codegen_support.load ~roots:[ equal ]
          "type Both(first: Int64, second: Int64)\n  derives Equal\n"
      in
      let c = Emit_c.For_testing.render_c (Backend.For_testing.compile_fragment backend equal) in
      let branches =
        List.length
          (String.split_on_char '\n' c
          |> List.filter (fun line -> String.starts_with ~prefix:"  if (" line))
      in
      if branches <> 1 then
        Codegen_support.fail "expected a branch after each field but the last, got %d:\n%s" branches
          c)

let () =
  Codegen_support.test
    "an index of a list, a slice, or an array, and a loop over one, call no lending method"
    (fun () ->
      let names =
        [
          "list_at";
          "slice_at";
          "array_at";
          "list_add";
          "array_add";
          "list_sum";
          "array_sum";
          "list_bump";
        ]
      in
      let function_ name : Lowered.Item.t =
        Code
          {
            path = Top { module_ = Codegen_support.example; name };
            instantiation = Ground.no_instantiation;
          }
      in
      let _, backend =
        Codegen_support.load ~roots:(List.map function_ names)
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
          let c =
            Emit_c.For_testing.render_c
              (Backend.For_testing.compile_fragment backend (function_ name))
          in
          if String.includes ~affix:"t_lend" c then
            Codegen_support.fail "expected no lend record in `%s`:\n%s" name c)
        names)

let () =
  Codegen_support.test "a C local is named after the Truss local it holds, and no other is named"
    (fun () ->
      let sum : Lowered.Item.t =
        Code
          {
            path = Top { module_ = Codegen_support.example; name = "sum" };
            instantiation = Ground.no_instantiation;
          }
      in
      let _, backend =
        Codegen_support.load ~roots:[ sum ]
          "fn sum(items: List[Int64]) -> Int64 {\n\
          \  var total: Int64 = 0\n\
          \  for item in items {\n\
          \    total += item\n\
          \  }\n\
          \  total\n\
           }\n"
      in
      let c = Emit_c.For_testing.render_c (Backend.For_testing.compile_fragment backend sum) in
      List.iter
        (fun name ->
          if not (String.includes ~affix:name c) then Codegen_support.fail "no %s in:\n%s" name c)
        [ "_items"; "_total"; "_item" ];
      List.iter
        (fun name -> if String.includes ~affix:name c then Codegen_support.fail "%s in:\n%s" name c)
        [ "_binding"; "_index"; "_position" ])

let () =
  Codegen_support.test "negating the least value of a signed type panics in a test" (fun () ->
      Codegen_support.expect_output Fixtures.Source.flip_of_an_int8
        "test 0 panicked\nmessage 47\narithmetic overflow\n  at example/main.truss:2:3\n")
