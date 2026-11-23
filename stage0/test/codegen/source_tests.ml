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
            assumes_condition = false;
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
            assumes_condition = false;
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
          if String.includes ~affix:"truss_lend" c then
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
            assumes_condition = false;
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

let make_example_item name : Lowered.Item.t =
  Code
    {
      path = Top { module_ = Codegen_support.example; name };
      instantiation = Ground.no_instantiation;
      assumes_condition = false;
    }

type presumed_line = { text : string; file : string; line : int }

let list_presumed_lines unit_text =
  let file = ref "" and line = ref 0 in
  List.filter_map
    (fun text ->
      match Scanf.sscanf_opt text "#line %d %S%!" (fun number name -> (number, name)) with
      | Some (number, name) ->
          line := number;
          file := name;
          None
      | None ->
          let presumed = { text; file = !file; line = !line } in
          incr line;
          Some presumed)
    (String.split_on_char '\n' unit_text)

let render_unit ~profile source name =
  let item = make_example_item name in
  let _, backend = Codegen_support.load ~profile ~roots:[ item ] source in
  Backend.For_testing.render_unit backend item

let find_last_presumed_line unit_text ~affix =
  match
    List.find_opt
      (fun (presumed : presumed_line) -> String.includes ~affix presumed.text)
      (List.rev (list_presumed_lines unit_text))
  with
  | Some presumed -> presumed
  | None -> Printf.ksprintf failwith "no line has %s in:\n%s" affix unit_text

let expect_presumed_at unit_text ~affix ~line =
  let presumed = find_last_presumed_line unit_text ~affix in
  if presumed.file <> "example/main.truss" || presumed.line <> line then
    Codegen_support.fail "%s is at %s:%d, not example/main.truss:%d, in:\n%s" affix presumed.file
      presumed.line line unit_text

let calls affix = Emit_c.make_symbol (make_example_item affix) ^ "("

let () =
  Codegen_support.test "a release unit puts each call on the line of the Truss call" (fun () ->
      let unit_text = render_unit ~profile:Release Fixtures.Source.calls_on_two_lines "scale" in
      expect_presumed_at unit_text ~affix:(calls "scale") ~line:1;
      expect_presumed_at unit_text ~affix:(calls "multiply") ~line:2;
      expect_presumed_at unit_text ~affix:(calls "offset") ~line:3)

let () =
  Codegen_support.test "a development unit has no line control" (fun () ->
      let unit_text = render_unit ~profile:Development Fixtures.Source.calls_on_two_lines "scale" in
      if String.includes ~affix:"#line" unit_text then
        Codegen_support.fail "a line control in:\n%s" unit_text)

let () =
  Codegen_support.test "every C line of an allocating assignment is on the line of its Truss call"
    (fun () ->
      let unit_text = render_unit ~profile:Release Fixtures.Source.indirect_variant "box" in
      let allocating =
        List.filter
          (fun (presumed : presumed_line) ->
            presumed.file = "example/main.truss" && String.includes ~affix:"block" presumed.text)
          (list_presumed_lines unit_text)
      in
      if List.length allocating < 3 then
        Codegen_support.fail "an allocating assignment of fewer than three lines in:\n%s" unit_text;
      List.iter
        (fun (presumed : presumed_line) ->
          if presumed.line <> 6 then
            Codegen_support.fail "`%s` is at line %d, not 6, in:\n%s" presumed.text presumed.line
              unit_text)
        allocating)

let () =
  Codegen_support.test "every line of a release unit for a drop is on <generated>" (fun () ->
      let named =
        Ground.Named
          { path = Top { module_ = Codegen_support.example; name = "Named" }; arguments = [] }
      in
      let drop : Lowered.Item.t = Drop named in
      let _, backend =
        Codegen_support.load ~profile:Release ~roots:[ drop ] "type Named(name: String)\n"
      in
      let unit_text = Backend.For_testing.render_unit backend drop in
      match
        List.find_opt
          (fun (presumed : presumed_line) -> presumed.text <> "" && presumed.file <> "<generated>")
          (list_presumed_lines unit_text)
      with
      | Some presumed ->
          Codegen_support.fail "`%s` is at %s:%d, in:\n%s" presumed.text presumed.file presumed.line
            unit_text
      | None -> ())

let () =
  Codegen_support.test "moving a definition changes only the line numbers of its release unit"
    (fun () ->
      let moved = "\n\n" ^ Fixtures.Source.calls_on_two_lines in
      let read_fragment source =
        let item = make_example_item "scale" in
        let _, backend = Codegen_support.load ~roots:[ item ] source in
        Emit_c.hash (Backend.For_testing.compile_fragment backend item)
      in
      if read_fragment moved <> read_fragment Fixtures.Source.calls_on_two_lines then
        Codegen_support.fail "the fragment's hash changed when its definition moved";
      let render ~profile source = render_unit ~profile source "scale" in
      Codegen_support.expect_string
        ~expected:(render ~profile:Development Fixtures.Source.calls_on_two_lines)
        (render ~profile:Development moved);
      expect_presumed_at (render ~profile:Release moved) ~affix:(calls "multiply") ~line:4)

let () =
  Codegen_support.test
    "a caller without `Panic` calls a copy of a callee with a condition on values that panics \
     nowhere" (fun () ->
      let make_item ?(assumes_condition = false) name : Lowered.Item.t =
        Code
          {
            path = Top { module_ = Codegen_support.example; name };
            instantiation = Ground.no_instantiation;
            assumes_condition;
          }
      in
      let proven = make_item "five_thousand" and panicking = make_item "scaled_or_panic" in
      let _, backend =
        Codegen_support.load ~profile:Release ~roots:[ proven; panicking ]
          Fixtures.Source.callee_with_a_condition_on_values
      in
      let called item = Emit_c.references (Backend.For_testing.compile_fragment backend item) in
      let render item =
        Emit_c.For_testing.render_c (Backend.For_testing.compile_fragment backend item)
      in
      let assuming = make_item ~assumes_condition:true "scaled" and checking = make_item "scaled" in
      if not (List.mem assuming (called proven)) then
        Codegen_support.fail "five_thousand calls no copy of scaled that assumes its condition";
      if not (List.mem checking (called panicking)) then
        Codegen_support.fail "scaled_or_panic calls no copy of scaled that checks";
      if String.includes ~affix:"truss_runtime_panic" (render assuming) then
        Codegen_support.fail "the copy that assumes the condition panics:\n%s" (render assuming);
      if not (String.includes ~affix:"truss_runtime_panic" (render checking)) then
        Codegen_support.fail "the copy that checks does not panic:\n%s" (render checking));
  Codegen_support.test
    "a call through a bound reaches the copy of an impl's method that the caller's capabilities \
     pick" (fun () ->
      let make_item name =
        Lowered.Item.make_code
          (Top { module_ = Codegen_support.example; name })
          Ground.no_instantiation
      in
      let proven = make_item "proven" and panicking = make_item "panicking" in
      let _, backend =
        Codegen_support.load ~profile:Release ~roots:[ proven; panicking ]
          Fixtures.Source.trait_method_with_a_condition_on_values
      in
      let called item = Emit_c.references (Backend.For_testing.compile_fragment backend item) in
      let find_instance name item =
        List.find_opt
          (function
            | Lowered.Item.Code { path = Top { name = callee; _ }; _ } -> callee = name | _ -> false)
          (called item)
      in
      let list_scaled_copies item =
        List.filter_map
          (function
            | Lowered.Item.Code { path = Method { name = "scaled"; _ }; assumes_condition; _ } ->
                Some assumes_condition
            | _ -> None)
          (called item)
      in
      (match Option.map list_scaled_copies (find_instance "five_thousand" proven) with
      | Some [ true ] -> ()
      | _ -> Codegen_support.fail "five_thousand calls no copy of scaled that assumes its condition");
      match Option.map list_scaled_copies (find_instance "scaled_or_panic" panicking) with
      | Some [ false ] -> ()
      | _ -> Codegen_support.fail "scaled_or_panic calls no copy of scaled that checks");
  Codegen_support.test
    "a call of a function value in a copy that assumes its condition is unreachable" (fun () ->
      let small =
        Lowered.Item.make_code
          (Top { module_ = Codegen_support.example; name = "small" })
          Ground.no_instantiation
      and measured : Lowered.Item.t =
        Code
          {
            path = Top { module_ = Codegen_support.example; name = "measured" };
            instantiation = Ground.no_instantiation;
            assumes_condition = true;
          }
      in
      let _, backend =
        Codegen_support.load ~profile:Release ~roots:[ small ]
          Fixtures.Source.call_of_a_function_value_in_a_copy_that_assumes_its_condition
      in
      if
        not
          (List.mem measured
             (Emit_c.references (Backend.For_testing.compile_fragment backend small)))
      then Codegen_support.fail "small calls no copy of measured that assumes its condition";
      let rendered =
        Emit_c.For_testing.render_c (Backend.For_testing.compile_fragment backend measured)
      in
      if String.includes ~affix:"truss_runtime_panic" rendered then
        Codegen_support.fail "the copy that assumes the condition panics:\n%s" rendered)
