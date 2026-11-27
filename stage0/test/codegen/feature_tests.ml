let () =
  Codegen_support.test "values echo as Truss writes them" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.value_echoes
        "test 0 passed\n\
         echo 265\n\
         example/main.truss:4:11: Some(true)\n\
         example/main.truss:5:11: Some(1.5)\n\
         example/main.truss:6:11: [1, 2, 3]\n\
         example/main.truss:7:11: \"hi\\n \\${x} \\u{1}\"\n\
         example/main.truss:8:11: Point(x: 0.1, y: 2.0)\n\
         example/main.truss:9:11: -7\n\
         example/main.truss:10:11: Character\"\195\169\"\n\n");
  Codegen_support.test "signed integers narrower than Int64 echo as their values" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.narrow_signed_integer_echoes
        "test 0 passed\n\
         echo 86\n\
         example/main.truss:5:11: -8\n\
         example/main.truss:6:11: -16\n\
         example/main.truss:7:11: -32\n\n")

let () =
  Codegen_support.test
    "a missing field of a variant or a record takes its default when deserialized" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.defaulted_fields_deserialize
        "test 0 passed\ntest 1 passed\ntest 2 passed\ntest 3 passed\ntest 4 passed\n")

let () =
  Codegen_support.test "a list inserts and removes an element of zero size" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.zero_size_elements_inserted_and_removed
        "test 0 passed\ntest 1 passed\n")
