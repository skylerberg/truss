let parse_module = Support.parse_module
let parse_file = Support.parse_file

let standard =
  [
    ("standard::option", "public type Option[Value] = Some(value: Value) | None\n");
    ("standard::result", "public type Result[Value, Error] = Ok(value: Value) | Err(error: Error)\n");
    ("standard::core", Fixtures.Resolve.standard_core);
    ("standard::list", "public opaque type List[Element](length: UInt64)\n");
  ]

let setup ?dependencies files = Support.setup ?dependencies (standard @ files)
let check packages = Database.For_testing.list_diagnostics [ Resolve ] (Database.create packages)
let list_diagnostics packages name = Support.run_check ~check packages name
let list_codes = Support.list_codes

let expect_no_diagnostics files =
  let packages = setup files in
  List.iter
    (fun (name, _) ->
      match list_diagnostics packages name with
      | [] -> ()
      | reported ->
          Harness.fail "%s: %s" name
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) reported)))
    files

let expect_one_diagnostic = Support.expect_one_diagnostic ~setup:(fun files -> setup files) ~check

let locate_name packages name text occurrence =
  let file = parse_file name in
  let source = Source.text (Support.read_source packages file) in
  let offset = Support.locate_occurrence ~sub:text ~occurrence source in
  let located =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = declaration.key in
        match
          ( (Support.make_names packages).read_definition key,
            (Support.make_names packages).read_spans key,
            (Support.make_names packages).read_place key,
            Database.read_resolved (Support.make_database packages) key )
        with
        | definition, spans, { base; _ }, Some resolved ->
            Option.map
              (fun (name : Syntax.name) -> (name, spans, base, resolved))
              (List.find_opt
                 (fun (name : Syntax.name) -> base + spans.(name.id).start = offset)
                 (Syntax_walk.collect_names spans definition))
        | _ -> None)
      ((Support.make_names packages).list_declarations_in file)
  in
  match located with
  | Some located -> located
  | None -> failwith (Printf.sprintf "no name at %S" text)

let describe (spans : Source.Definition_span.t array) base (target : Resolve.target option) =
  let compute_offset id = base + spans.(id).start in
  match target with
  | None -> "nothing"
  | Some Binding -> "binding"
  | Some (Local id) -> Printf.sprintf "local at %d" (compute_offset id)
  | Some (Law_parameter index) -> Printf.sprintf "law parameter %d" index
  | Some (Type_parameter parameter | Capability_parameter parameter | Value_parameter parameter) ->
      Printf.sprintf "generic %s of %s" parameter.name (Path.show parameter.owner)
  | Some (Definition (_, path)) -> Path.show path
  | Some (Variant (type_, name)) -> Printf.sprintf "variant %s of %s" name (Path.show type_)
  | Some (Module module_) -> "module " ^ Path.show_module module_
  | Some (Field name) -> "field " ^ name
  | Some Result_value -> "result"
  | Some Old -> "old"
  | Some Identical -> "identical"
  | Some Visited -> "visited"
  | Some Final -> "final"
  | Some (Specification_function _) -> "specification function"
  | Some (Unknown _) -> "unknown"

let expect_reference ?(others = []) text ~name:(written, occurrence) expected =
  let packages = setup (("app::main", text) :: others) in
  let name, spans, base, resolved = locate_name packages "app::main" written occurrence in
  let actual = describe spans base resolved.names.(name.id) in
  if actual <> expected then
    Harness.fail "`%s` #%d is %s, not %s" written occurrence actual expected

let expect_binding_reference text ~use ~binding =
  let packages = setup [ ("app::main", text) ] in
  let binding_offset =
    Support.locate_occurrence ~sub:(fst binding) ~occurrence:(snd binding) text
  in
  let name, spans, base, resolved = locate_name packages "app::main" (fst use) (snd use) in
  let actual = describe spans base resolved.names.(name.id) in
  let expected = Printf.sprintf "local at %d" binding_offset in
  if actual <> expected then Harness.fail "`%s` is %s, not %s" (fst use) actual expected

let () =
  Harness.test "a local refers to the let that binds it" (fun () ->
      expect_binding_reference Fixtures.Resolve.let_then_read ~use:("count", 2) ~binding:("count", 1));
  Harness.test "a parameter is a local of the body" (fun () ->
      expect_binding_reference Fixtures.Resolve.parameter_returned ~use:("count", 2)
        ~binding:("count", 1));
  Harness.test "a function type's input is the binding its requires refers to" (fun () ->
      expect_binding_reference "fn f(visit: (fn(index: UInt64) requires index < 3)) {}\n"
        ~use:("index", 2) ~binding:("index", 1));
  Harness.test "a name bound by is is in scope in the if's block" (fun () ->
      expect_binding_reference Fixtures.Resolve.is_binding_read_in_the_if_block ~use:("value", 2)
        ~binding:("value", 1));
  Harness.test "a name bound by is is in scope in the rest of its && chain" (fun () ->
      expect_binding_reference Fixtures.Resolve.is_binding_read_after_and ~use:("value", 2)
        ~binding:("value", 1));
  Harness.test "a name bound by is is not in scope in the else" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.is_binding_read_in_the_else "resolve.unknown_name");
  Harness.test "a name bound by is is not in scope after ||" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.is_binding_read_after_or "resolve.unknown_name");
  Harness.test "a name bound by let else is in scope after it" (fun () ->
      expect_binding_reference Fixtures.Resolve.let_else_binding_read_after_it ~use:("value", 2)
        ~binding:("value", 1));
  Harness.test "a name bound in a match arm is in scope in its guard and body" (fun () ->
      expect_binding_reference Fixtures.Resolve.arm_binding_read_in_its_guard ~use:("value", 3)
        ~binding:("value", 1));
  Harness.test "a let in a parallel branch is in scope after the block" (fun () ->
      expect_binding_reference Fixtures.Resolve.parallel_lets_read_after_the_block ~use:("left", 2)
        ~binding:("left", 1));
  Harness.test "a let in a parallel branch is not in scope in another branch" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.parallel_let_read_by_a_sibling "resolve.unknown_name");
  Harness.test "a let in a concurrent branch is in scope after the block, and in no other branch"
    (fun () ->
      expect_binding_reference Fixtures.Resolve.concurrent_lets_read_after_the_block
        ~use:("left", 2) ~binding:("left", 1);
      expect_one_diagnostic Fixtures.Resolve.concurrent_let_read_by_a_sibling "resolve.unknown_name");
  Harness.test "a lambda's parameter is in scope in its body" (fun () ->
      expect_binding_reference Fixtures.Resolve.lambda_returning_its_parameter ~use:("item", 2)
        ~binding:("item", 1));
  Harness.test "a range loop's index is in scope in its clauses" (fun () ->
      expect_binding_reference Fixtures.Resolve.range_loop_invariant_naming_its_index
        ~use:("index", 2) ~binding:("index", 1));
  Harness.test "a loop's element is not in scope in its clauses" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.for_loop_invariant_naming_its_element
        "resolve.unknown_name");
  Harness.test "a local is not in scope after its block" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.local_read_after_its_block "resolve.unknown_name")

let () =
  Harness.test "a local cannot shadow a local of an enclosing block" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.let_shadowing_an_enclosing_let "resolve.shadowed_name");
  Harness.test "a local cannot shadow a parameter" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.let_shadowing_a_parameter "resolve.shadowed_name");
  Harness.test "a local may shadow a function of its module, and its uses are the local" (fun () ->
      expect_binding_reference Fixtures.Resolve.let_named_like_a_function ~use:("total", 3)
        ~binding:("total", 2));
  Harness.test "a local may shadow a definition in another file of its module" (fun () ->
      expect_no_diagnostics
        [
          ("app::main", "fn f() -> Int64 {\n  let total = 2\n  total\n}\n");
          ("app::main/sums", "fn total() -> Int64 { 0 }\n");
        ]);
  Harness.test "a let binds the name of a constant of its module, which its uses then name"
    (fun () ->
      expect_binding_reference Fixtures.Resolve.let_named_like_a_constant ~use:("limit", 3)
        ~binding:("limit", 2));
  Harness.test "a generic parameter cannot shadow a type of its module" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.generic_named_like_a_type_of_its_module
        ~says:"a type of this module" "resolve.shadowed_name");
  Harness.test "a generic parameter cannot shadow a prelude type" (fun () ->
      expect_one_diagnostic "fn f[Option](value: Option) {}\n" "resolve.shadowed_name");
  Harness.test "locals in sibling blocks may share a name" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Resolve.lets_of_one_name_in_sibling_blocks) ])

let () =
  Harness.test "a file names a private definition of another file of its module without a module"
    (fun () ->
      expect_reference "fn f() -> Int64 {\n  size()\n}\n"
        ~others:[ ("app::main/grid", "fn size() -> Int64 { 9 }\n") ]
        ~name:("size", 1) "app::main::size");
  Harness.test "two files of a module that define one name make a duplicate" (fun () ->
      expect_one_diagnostic "fn size() -> Int64 { 9 }\n"
        ~others:[ ("app::main/grid", "fn size() -> Int64 { 3 }\n") ]
        ~says:"already defined in app/main/grid.truss" "resolve.duplicate_definition");
  Harness.test
    "impls in two files that spell one trait the same but import different modules are two"
    (fun () ->
      expect_no_diagnostics
        [
          ("app::one::codec", "public trait Marker {\n}\n");
          ("app::two::codec", "public trait Marker {\n}\n");
          ( "app::main",
            "use app::one::codec\n\n\
             public type Point(x: Int64)\n\n\
             impl codec::Marker for Point {\n\
             }\n" );
          ("app::main/second", "use app::two::codec\n\nimpl codec::Marker for Point {\n}\n");
        ]);
  Harness.test "one impl written with two spellings of its trait is a duplicate" (fun () ->
      expect_one_diagnostic
        "use app::one::codec\n\n\
         public type Point(x: Int64)\n\n\
         impl codec::Marker for Point {\n\
         }\n\n\
         impl app::one::codec::Marker for Point {\n\
         }\n"
        ~others:[ ("app::one::codec", "public trait Marker {\n}\n") ]
        ~says:"already defined in this file" "resolve.duplicate_definition");
  Harness.test "a file names a module only through its own imports" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.area_call_without_an_import
        ~others:
          [
            ("app::shapes", "internal fn area() -> Int64 { 0 }\n");
            ("app::main/other", Fixtures.Resolve.second_file_importing_shapes);
          ]
        "resolve.unknown_module")

let () =
  Harness.test "a bare name in a pattern binds where a constant has its name" (fun () ->
      expect_reference Fixtures.Resolve.bare_name_arm_named_like_a_constant ~name:("limit", 2)
        "binding");
  Harness.test "a constant of its own module in a pattern is written with its module" (fun () ->
      expect_reference Fixtures.Resolve.qualified_constant_arm ~name:("limit", 2) "app::main::limit");
  Harness.test "the alternatives of a pattern must bind the same names" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.or_pattern_binding_different_names
        "resolve.alternative_bindings");
  Harness.test "an alternative's name refers to the first alternative's binding" (fun () ->
      expect_binding_reference Fixtures.Resolve.or_pattern_binding_value_in_both ~use:("value", 3)
        ~binding:("value", 1))

let () =
  Harness.test "an unknown name is an error with a fix to the closest name" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.misspelled_parameter "resolve.unknown_name"
        ~fixed:Fixtures.Resolve.misspelled_parameter_fixed);
  Harness.test "null is an error with a fix that writes None" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.null_literal "resolve.null"
        ~fixed:Fixtures.Resolve.null_literal_fixed);
  Harness.test "an unknown type is an error" (fun () ->
      expect_one_diagnostic "fn f(value: Strng) {}\n" "resolve.unknown_name")

let () =
  Harness.test "a prelude type is the standard library's" (fun () ->
      expect_reference "fn f(value: Option[Int64]) {}\n" ~name:("Option", 1)
        "standard::option::Option");
  Harness.test "a built-in type is the intrinsic module's" (fun () ->
      expect_reference "fn f(value: Int64) {}\n" ~name:("Int64", 1) "standard::intrinsic::Int64");
  Harness.test "a prelude variant is written bare" (fun () ->
      expect_reference Fixtures.Resolve.bare_some ~name:("Some", 1)
        "variant Some of standard::option::Option")

let find_bracket text written occurrence =
  let packages = setup [ ("app::main", text) ] in
  let offset = Support.locate_occurrence ~sub:written ~occurrence text in
  let declarations = Support.list_declarations packages (Support.parse_module "app::main") in
  List.find_map
    (fun (declaration : Resolve.Names.declaration) ->
      let key = declaration.key in
      match
        ( (Support.make_names packages).read_definition key,
          (Support.make_names packages).read_spans key,
          (Support.make_names packages).read_place key,
          Database.read_resolved (Support.make_database packages) key )
      with
      | definition, spans, { base; _ }, Some resolved ->
          let bracket = ref None in
          Syntax_walk.visit_definition
            (let rec visit (value : Syntax.expression) =
               (match value.kind with
               | Bracket _ when base + spans.(value.id).start = offset ->
                   bracket := resolved.brackets.(value.id)
               | _ -> ());
               Syntax_walk.visit_children visit value
             in
             visit)
            definition;
          !bracket
      | _ -> None)
    declarations

let () =
  Harness.test "brackets after a generic function give type arguments" (fun () ->
      let text = Fixtures.Resolve.brackets_after_a_generic_function in
      match find_bracket text "parse[Int64]" 1 with
      | Some Resolve.Type_arguments -> ()
      | _ -> Harness.fail "not type arguments");
  Harness.test "brackets after a local index it" (fun () ->
      let text = Fixtures.Resolve.brackets_after_a_local in
      match find_bracket text "items[0]" 1 with
      | Some Resolve.Index -> ()
      | _ -> Harness.fail "not an index");
  Harness.test "brackets after a method are left to type checking" (fun () ->
      let text = Fixtures.Resolve.brackets_after_a_method in
      match find_bracket text "items.map[Int64]" 1 with
      | Some Resolve.Method_bracket -> ()
      | _ -> Harness.fail "decided");
  Harness.test "brackets after a function without generic parameters are an error" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.brackets_after_a_plain_function "resolve.not_generic");
  Harness.test "brackets after a function with only a capability parameter are an error" (fun () ->
      expect_one_diagnostic
        Fixtures.Resolve.brackets_after_a_function_with_only_a_capability_parameter
        "resolve.not_generic")

let () =
  Harness.test "a capability parameter named only in its function's own uses is an error" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.capability_parameter_named_only_in_uses
        "resolve.unconstrained_capability_parameter"
        ~says:
          "`generic Granted` appears only in the function's own `uses`, so no argument gives it \
           capabilities, and it stands for none. Name it in the type of a parameter, as in `visit: \
           (fn() uses generic Granted)`.");
  Harness.test "a body names only the capability parameters of its signature" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.body_naming_a_capability_parameter_of_no_signature
        "resolve.unknown_name");
  Harness.test "a body can name a capability parameter of its signature" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Resolve.body_naming_its_capability_parameter) ]);
  Harness.test "a capability parameter without `generic` is an error with a fix that writes it"
    (fun () ->
      expect_one_diagnostic Fixtures.Resolve.capability_parameter_without_its_marker
        "resolve.unknown_name" ~fixed:Fixtures.Resolve.capability_parameter_without_its_marker_fixed);
  Harness.test "a capability parameter cannot share its name with a type parameter" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.capability_parameter_named_like_a_type_parameter
        "resolve.shadowed_name");
  Harness.test "a capability parameter cannot shadow a capability" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.capability_parameter_named_like_a_capability
        "resolve.shadowed_name")

let () =
  Harness.test "mut before a call to a function is an error with a fix that removes it" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.mut_before_a_function_call "resolve.not_a_place"
        ~fixed:Fixtures.Resolve.mut_before_a_function_call_fixed);
  Harness.test "mut before a local's field and method call is a place" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Resolve.mut_push_onto_a_local) ]);
  Harness.test "a ? after a call with a mode keyword works on its result" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Resolve.question_mark_after_a_mut_pop) ]);
  Harness.test "a ? before any method call does not make a place" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.mut_call_through_a_question_mark "resolve.not_a_place")

let () =
  Harness.test "result in ensures is the return value" (fun () ->
      expect_reference Fixtures.Resolve.ensures_reading_result ~name:("result", 1) "result");
  Harness.test "result outside a specification is an ordinary name" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.body_reading_result "resolve.unknown_name");
  Harness.test "old in a specification is the value on entry" (fun () ->
      expect_reference Fixtures.Resolve.ensures_reading_old ~name:("old", 1) "old");
  Harness.test "log in a cost bound is the specification function" (fun () ->
      expect_reference Fixtures.Resolve.cost_logarithmic_in_a_count ~name:("log", 1)
        "specification function");
  Harness.test "a call of log in a cost bound is the specification function despite a local"
    (fun () ->
      expect_reference Fixtures.Resolve.cost_calling_log_on_a_parameter_named_log ~name:("log", 2)
        "specification function";
      expect_binding_reference Fixtures.Resolve.cost_calling_log_on_a_parameter_named_log
        ~use:("log", 3) ~binding:("log", 1));
  Harness.test "a cost function's name in a cost bound is a local where it is not called" (fun () ->
      expect_binding_reference Fixtures.Resolve.cost_bound_reading_a_parameter_named_time
        ~use:("time", 3) ~binding:("time", 1));
  Harness.test "a local named log takes precedence over log in a specification" (fun () ->
      expect_binding_reference Fixtures.Resolve.requires_calling_a_parameter_named_log
        ~use:("log", 2) ~binding:("log", 1));
  Harness.test "a function of the module named log takes precedence over log in a specification"
    (fun () ->
      expect_reference Fixtures.Resolve.requires_calling_a_function_named_log ~name:("log", 2)
        "app::main::log");
  Harness.test "log in a specification is the specification function where it is not called"
    (fun () ->
      expect_reference Fixtures.Resolve.requires_naming_log_without_arguments ~name:("log", 1)
        "specification function");
  Harness.test "visited in a for loop's clauses is the values of the iterations before" (fun () ->
      expect_reference Fixtures.Resolve.loop_clause_reading_visited ~name:("visited", 1) "visited");
  Harness.test "a local named visited shadows the word in a for loop's clauses" (fun () ->
      expect_binding_reference Fixtures.Resolve.loop_clause_reading_a_local_named_visited
        ~use:("visited", 2) ~binding:("visited", 1));
  Harness.test "a quantifier's binding named result shadows the return value in ensures" (fun () ->
      expect_binding_reference Fixtures.Resolve.ensures_binding_result_in_a_quantifier
        ~use:("result", 2) ~binding:("result", 1));
  Harness.test "a function type's requires in an ensures does not name the return value" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.function_type_requires_naming_result_in_an_ensures
        "resolve.unknown_name" ~at:("result", 1));
  Harness.test "a function type's requires in a loop invariant does not name visited" (fun () ->
      expect_one_diagnostic
        Fixtures.Resolve.function_type_requires_naming_visited_in_a_loop_invariant
        "resolve.unknown_name" ~at:("visited", 1));
  Harness.test "a function type's input named log shadows log in its requires in a cost bound"
    (fun () ->
      expect_binding_reference
        Fixtures.Resolve.function_type_requires_calling_its_input_log_in_a_cost_bound
        ~use:("log", 2) ~binding:("log", 1));
  Harness.test "a record's fields are in scope in its invariant" (fun () ->
      expect_reference "type Range(low: Int64, high: Int64)\n  invariant low <= high\n"
        ~name:("low", 2) "field low")

let others = [ ("app::shapes", Fixtures.Resolve.others_shapes) ]

let () =
  Harness.test "a name after an imported module is that module's" (fun () ->
      expect_reference ~others Fixtures.Resolve.area_call_with_an_import ~name:("area", 1)
        "app::shapes::area");
  Harness.test "a full path needs no use" (fun () ->
      expect_reference ~others Fixtures.Resolve.area_call_through_a_full_path ~name:("area", 1)
        "app::shapes::area");
  Harness.test "a private definition of another file is not visible" (fun () ->
      expect_one_diagnostic ~others Fixtures.Resolve.call_of_another_files_private_function
        "resolve.not_visible");
  Harness.test "an import nothing uses is an error with a fix that deletes it" (fun () ->
      expect_one_diagnostic ~others Fixtures.Resolve.unused_import "resolve.unused_import"
        ~fixed:"\nfn f() {}\n");
  Harness.test "an import used only in an interpolation is used" (fun () ->
      expect_no_diagnostics
        (others
        @ [ ("app::main", "use app::shapes\n\nfn f() {\n  let text = \"${shapes::area()}\"\n}\n") ]
        ));
  Harness.test "a path through an import that names no module is that path's error alone" (fun () ->
      expect_one_diagnostic ~others
        "use app::shapes\n\nfn f() -> Int64 {\n  shapes::missing::area()\n}\n"
        "resolve.unknown_module");
  Harness.test "a file with a syntax error reports no unused import" (fun () ->
      let packages =
        setup
          (others
          @ [ ("app::main", "use app::shapes\n\nfn f() -> Int64 {\n  let = shapes::area()\n}\n") ])
      in
      let file = parse_file "app::main" in
      let database = Database.create packages in
      if Database.For_testing.list_diagnostics [ Parse ] database file = [] then
        Harness.fail "parsed";
      match Database.For_testing.list_diagnostics [ Resolve ] database file with
      | [] -> ()
      | reported -> Harness.fail "reported %s" (String.concat "; " (list_codes reported)));
  Harness.test "an import of a module that does not exist is an error" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.import_of_a_missing_module "resolve.unknown_module");
  Harness.test "a path that starts with no package or import names the file's module" (fun () ->
      expect_one_diagnostic "fn f() -> Int64 {\n  main::lucky\n}\n" "resolve.unknown_module"
        ~says:
          "No module `main` is imported or exists. Every path starts with a package name, even \
           inside the package. This file's module is `app::main`.");
  Harness.test "an import that starts with no package names the file's module" (fun () ->
      expect_one_diagnostic "use shapes\n\nfn f() {}\n" "resolve.unknown_module"
        ~says:
          "No module `shapes` exists. Every path starts with a package name, even inside the \
           package. This file's module is `app::main`.");
  Harness.test "a missing module under an import or a package says only that it is missing"
    (fun () ->
      List.iter
        (fun (text, expected) ->
          match list_diagnostics (setup (("app::main", text) :: others)) "app::main" with
          | [ diagnostic ] -> Harness.expect_string ~expected diagnostic.message
          | reported -> Harness.fail "found [%s]" (String.concat "; " (list_codes reported)))
        [
          ( "use app::shapes\n\nfn f() -> Int64 {\n  shapes::missing::area()\n}\n",
            "No module `shapes::missing` is imported or exists." );
          ( "fn f() -> Int64 {\n  app::missing::area()\n}\n",
            "No module `app::missing` is imported or exists." );
          ("use app::missing\n\nfn f() {}\n", "No module `app::missing` exists.");
        ]);
  Harness.test "two imports with one last name are an error at the second" (fun () ->
      Support.expect_one_diagnostic ~check
        ~setup:(setup ~dependencies:[ ("app", "other") ])
        ~others:
          [
            ("app::shapes", "public fn area() -> Int64 { 0 }\n");
            ("other::shapes", "public fn area() -> Int64 { 0 }\n");
          ]
        Fixtures.Resolve.two_imports_ending_in_shapes "resolve.duplicate_import");
  Harness.test "only the standard package can import standard::intrinsic" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.import_of_standard_intrinsic "resolve.intrinsic_import")

let () =
  Harness.test "a second definition with one name is an error" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.two_functions_of_one_name
        "resolve.duplicate_definition");
  Harness.test "a method's type head names its type" (fun () ->
      let packages = setup [ ("app::main", Fixtures.Resolve.counter_method) ] in
      let owner = Path.Top { module_ = parse_module "app::main"; name = "Counter" } in
      match (Support.make_names packages).list_members owner "get" with
      | [ { path = Method { receiver = Instance Read; _ }; _ } ] -> ()
      | reported -> Harness.fail "found %d members" (List.length reported));
  Harness.test "a method can be written in another file of its type's package" (fun () ->
      let packages =
        setup
          [
            ("app::main", "public type Counter(count: Int64)\n");
            ("app::extra", Fixtures.Resolve.counter_method_in_another_file);
          ]
      in
      let owner = Path.Top { module_ = parse_module "app::main"; name = "Counter" } in
      match (Support.make_names packages).list_members owner "get" with
      | [ _ ] -> ()
      | reported -> Harness.fail "found %d members" (List.length reported));
  Harness.test "a body the parser could not read is not resolved" (fun () ->
      let packages = setup [ ("app::main", Fixtures.Resolve.body_with_a_broken_let) ] in
      let file = parse_file "app::main" in
      let database = Database.create packages in
      if Database.For_testing.list_diagnostics [ Parse ] database file = [] then
        Harness.fail "parsed";
      match Database.For_testing.list_diagnostics [ Resolve ] database file with
      | [] -> ()
      | reported ->
          Harness.fail "resolved the broken body: %s" (String.concat "; " (list_codes reported)))

let () =
  Harness.test "a method in another file of its type's package is resolved, and its import counts"
    (fun () ->
      let packages =
        setup
          [
            ("app::main", "public type Counter(count: Int64)\n");
            ("app::extra", Fixtures.Resolve.counter_method_in_another_file_reading_missing);
          ]
      in
      match list_codes (list_diagnostics packages "app::extra") with
      | [ "resolve.unknown_name" ] -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " reported));
  Harness.test "an import used only in a part the parser could not read is not unused" (fun () ->
      let packages =
        setup
          [
            ("app::shapes", "public fn area() -> Int64 { 0 }\n");
            ("app::main", Fixtures.Resolve.import_used_only_in_a_broken_let);
          ]
      in
      match
        Database.For_testing.list_diagnostics [ Resolve ] (Database.create packages)
          (parse_file "app::main")
      with
      | [] -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " (list_codes reported)));
  Harness.test "an element of a field is a place" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Resolve.mut_element_of_a_field) ]);
  Harness.test "two parallel branches cannot bind one name" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.parallel_lets_of_one_name "resolve.shadowed_name");
  Harness.test "two concurrent branches cannot bind one name" (fun () ->
      expect_one_diagnostic Fixtures.Resolve.concurrent_lets_of_one_name "resolve.shadowed_name");
  List.iter
    (fun name ->
      Harness.test (Printf.sprintf "a definition cannot take the prelude name `%s`" name) (fun () ->
          expect_one_diagnostic
            (Printf.sprintf "type %s(count: Int64)\n" name)
            "resolve.shadowed_name"))
    [ "List"; "Unit"; "Clock"; "Duration" ];
  Harness.test "a generic parameter cannot take a prelude variant's name" (fun () ->
      expect_one_diagnostic "fn f[Some](value: Some) {}\n" "resolve.shadowed_name");
  Harness.test "a trait whose header did not parse is not resolved" (fun () ->
      let packages = setup [ ("app::main", Fixtures.Resolve.trait_with_a_broken_header) ] in
      match
        Database.For_testing.list_diagnostics [ Resolve ] (Database.create packages)
          (parse_file "app::main")
      with
      | [] -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " (list_codes reported)))

let () =
  let geometry : Path.module_ =
    { package = { Path.owner = Some "acme"; name = "geometry" }; modules = [ "vector" ] }
  in
  let with_geometry ~dependencies text =
    Support.with_dependencies
      (setup [ ("app::main", text) ]
      @ [
          {
            name = { Path.owner = Some "acme"; name = "geometry" };
            dependencies = [];
            files = [ ({ module_ = geometry; name = "vector" }, Fixtures.Resolve.geometry_length) ];
          };
        ])
      { Path.owner = None; name = "app" }
      (List.map (fun package -> { Manifest.package; capabilities = [] }) dependencies)
  in
  let uses_both = Fixtures.Resolve.uses_both in
  Harness.test "a path into a package with an owner starts with the owner and the name" (fun () ->
      let packages =
        with_geometry ~dependencies:[ { Path.owner = Some "acme"; name = "geometry" } ] uses_both
      in
      (match list_diagnostics packages "app::main" with
      | [] -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " (list_codes reported)));
      match
        (Support.make_names packages).list_imports
          {
            module_ = (parse_file "app::main").module_;
            path = Top { module_ = (parse_file "app::main").module_; name = "f" };
            ordinal = 0;
          }
      with
      | [ ("vector", imported) ] when imported = geometry -> ()
      | _ -> Harness.fail "imported differently");
  Harness.test "a package with an owner that the manifest does not list cannot be named" (fun () ->
      let packages = with_geometry ~dependencies:[] uses_both in
      match list_codes (list_diagnostics packages "app::main") with
      | "resolve.unknown_module" :: _ -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " reported));
  Harness.test "an owner alone names no package" (fun () ->
      let packages =
        with_geometry
          ~dependencies:[ { Path.owner = Some "acme"; name = "geometry" } ]
          Fixtures.Resolve.import_of_an_owner_alone
      in
      match list_codes (list_diagnostics packages "app::main") with
      | "resolve.unknown_module" :: _ -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " reported))

let () =
  Harness.test "a name used through an import of standard::intrinsic is not an error of its own"
    (fun () ->
      expect_one_diagnostic Fixtures.Resolve.call_through_standard_intrinsic
        "resolve.intrinsic_import");
  Harness.test "a type head through standard::intrinsic outside the standard package names no type"
    (fun () ->
      let packages =
        setup [ ("app::main", Fixtures.Resolve.method_of_standard_intrinsic_outside_standard) ]
      in
      (match Support.list_declarations packages (parse_module "app::main") with
      | [ { key = { path = Method { owner; _ }; _ }; _ } ] when not (Path.is_resolved owner) -> ()
      | declarations ->
          Harness.fail "declared [%s]"
            (String.concat "; "
               (List.map
                  (fun (declaration : Resolve.Names.declaration) -> Path.show declaration.key.path)
                  declarations)));
      match list_codes (check packages (parse_file "app::main")) with
      | [ "resolve.intrinsic_import" ] -> ()
      | reported -> Harness.fail "reported [%s]" (String.concat "; " reported))

let () =
  Harness.test "impls rejected for different function type arguments are not duplicates" (fun () ->
      let packages =
        setup
          [ ("app::main", Fixtures.Resolve.impls_rejected_for_different_function_type_arguments) ]
      in
      let file = parse_file "app::main" in
      let database = Database.create packages in
      if Database.For_testing.list_diagnostics [ Parse ] database file = [] then
        Harness.fail "parsed";
      match list_codes (Database.For_testing.list_diagnostics [ Resolve ] database file) with
      | [] -> ()
      | reported -> Harness.fail "reported [%s]" (String.concat "; " reported));
  Harness.test "impls rejected for different function type arguments have distinct keys" (fun () ->
      let packages =
        setup
          [ ("app::main", Fixtures.Resolve.impls_rejected_for_different_function_type_arguments) ]
      in
      match
        List.sort compare
          (List.filter_map
             (fun (declaration : Resolve.Names.declaration) ->
               match declaration.key.path with
               | Impl _ -> Some (Path.show declaration.key.path, declaration.key.ordinal)
               | _ -> None)
             (Support.list_declarations packages (parse_module "app::main")))
      with
      | [
       ("app::main::impl app::main::Wraps[fn(Bool) -> Int64] for app::main::Box", 0);
       ("app::main::impl app::main::Wraps[fn(Int64) -> Int64] for app::main::Box", 0);
      ] ->
          ()
      | impls ->
          Harness.fail "declared [%s]"
            (String.concat "; "
               (List.map
                  (fun (shown, ordinal) -> Printf.sprintf "%s, ordinal %d" shown ordinal)
                  impls)))
