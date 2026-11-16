let module_of = Support.module_of
let file_of = Support.file_of

let standard =
  [
    ("standard::option", "public type Option[Value] = Some(value: Value) | None\n");
    ("standard::result", "public type Result[Value, Error] = Ok(value: Value) | Err(error: Error)\n");
    ("standard::core", Fixtures.Resolve.standard_core);
    ("standard::list", "public opaque type List[Element](length: UInt64)\n");
  ]

let setup ?dependencies files = Support.setup ?dependencies (standard @ files)

let diagnostics packages name =
  let file = file_of name in
  (match Support.parse_errors packages file with
  | [] -> ()
  | errors -> Harness.fail "the test input does not parse: %s" (String.concat " " errors));
  Database.For_testing.list_diagnostics [ Resolve ] (Database.create packages) file

let codes = Support.codes

let no_diagnostics files =
  let packages = setup files in
  List.iter
    (fun (name, _) ->
      match diagnostics packages name with
      | [] -> ()
      | reported ->
          Harness.fail "%s: %s" name
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) reported)))
    files

let check packages = Database.For_testing.list_diagnostics [ Resolve ] (Database.create packages)
let one_diagnostic = Support.one_diagnostic ~setup:(fun files -> setup files) ~check

let name_at packages name text occurrence =
  let file = file_of name in
  let source = Source.text (Support.source packages file) in
  let offset = Option.get (Substring.For_testing.find ~occurrence source text) in
  if offset < 0 then failwith (Printf.sprintf "no occurrence %d of %S" occurrence text);
  let located =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        match
          ( (Support.names packages key.module_.package).definition key,
            (Support.names packages key.module_.package).spans key,
            (Support.names packages key.module_.package).place key,
            Database.read_resolved (Support.database packages) key )
        with
        | definition, spans, { base; _ }, Some resolved ->
            Option.map
              (fun (name : Syntax.name) -> (name, spans, base, resolved))
              (List.find_opt
                 (fun (name : Syntax.name) -> base + spans.(name.id).start = offset)
                 (Syntax_walk.collect_names spans definition))
        | _ -> None)
      ((Support.names packages file.module_.package).declarations_in file)
  in
  match located with
  | Some located -> located
  | None -> failwith (Printf.sprintf "no name at %S" text)

let describe (spans : Source.Definition_span.t array) base (target : Resolve.target option) =
  let offset id = base + spans.(id).start in
  match target with
  | None -> "nothing"
  | Some Binding -> "binding"
  | Some (Local id) -> Printf.sprintf "local at %d" (offset id)
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

let refers ?(others = []) text ~name:(written, occurrence) expected =
  let packages = setup (("app::main", text) :: others) in
  let name, spans, base, resolved = name_at packages "app::main" written occurrence in
  let actual = describe spans base resolved.names.(name.id) in
  if actual <> expected then
    Harness.fail "`%s` #%d is %s, not %s" written occurrence actual expected

let refers_to_binding text ~use ~binding =
  let packages = setup [ ("app::main", text) ] in
  let source = text in
  let binding_offset =
    Option.get (Substring.For_testing.find ~occurrence:(snd binding) source (fst binding))
  in
  let name, spans, base, resolved = name_at packages "app::main" (fst use) (snd use) in
  let actual = describe spans base resolved.names.(name.id) in
  let expected = Printf.sprintf "local at %d" binding_offset in
  if actual <> expected then Harness.fail "`%s` is %s, not %s" (fst use) actual expected

let () =
  Harness.test "a local refers to the let that binds it" (fun () ->
      refers_to_binding Fixtures.Resolve.let_then_read ~use:("count", 2) ~binding:("count", 1));
  Harness.test "a parameter is a local of the body" (fun () ->
      refers_to_binding Fixtures.Resolve.parameter_returned ~use:("count", 2) ~binding:("count", 1));
  Harness.test "a function type's input is the binding its requires refers to" (fun () ->
      refers_to_binding "fn f(visit: (fn(index: UInt64) requires index < 3)) {}\n" ~use:("index", 2)
        ~binding:("index", 1));
  Harness.test "a name bound by is is in scope in the if's block" (fun () ->
      refers_to_binding Fixtures.Resolve.is_binding_read_in_the_if_block ~use:("value", 2)
        ~binding:("value", 1));
  Harness.test "a name bound by is is in scope in the rest of its && chain" (fun () ->
      refers_to_binding Fixtures.Resolve.is_binding_read_after_and ~use:("value", 2)
        ~binding:("value", 1));
  Harness.test "a name bound by is is not in scope in the else" (fun () ->
      one_diagnostic Fixtures.Resolve.is_binding_read_in_the_else "resolve.unknown_name");
  Harness.test "a name bound by is is not in scope after ||" (fun () ->
      one_diagnostic Fixtures.Resolve.is_binding_read_after_or "resolve.unknown_name");
  Harness.test "a name bound by let else is in scope after it" (fun () ->
      refers_to_binding Fixtures.Resolve.let_else_binding_read_after_it ~use:("value", 2)
        ~binding:("value", 1));
  Harness.test "a name bound in a match arm is in scope in its guard and body" (fun () ->
      refers_to_binding Fixtures.Resolve.arm_binding_read_in_its_guard ~use:("value", 3)
        ~binding:("value", 1));
  Harness.test "a let in a parallel branch is in scope after the block" (fun () ->
      refers_to_binding Fixtures.Resolve.parallel_lets_read_after_the_block ~use:("left", 2)
        ~binding:("left", 1));
  Harness.test "a let in a parallel branch is not in scope in another branch" (fun () ->
      one_diagnostic Fixtures.Resolve.parallel_let_read_by_a_sibling "resolve.unknown_name");
  Harness.test "a let in a concurrent branch is in scope after the block, and in no other branch"
    (fun () ->
      refers_to_binding Fixtures.Resolve.concurrent_lets_read_after_the_block ~use:("left", 2)
        ~binding:("left", 1);
      one_diagnostic Fixtures.Resolve.concurrent_let_read_by_a_sibling "resolve.unknown_name");
  Harness.test "a lambda's parameter is in scope in its body" (fun () ->
      refers_to_binding Fixtures.Resolve.lambda_returning_its_parameter ~use:("item", 2)
        ~binding:("item", 1));
  Harness.test "a range loop's index is in scope in its clauses" (fun () ->
      refers_to_binding Fixtures.Resolve.range_loop_invariant_naming_its_index ~use:("index", 2)
        ~binding:("index", 1));
  Harness.test "a loop's element is not in scope in its clauses" (fun () ->
      one_diagnostic Fixtures.Resolve.for_loop_invariant_naming_its_element "resolve.unknown_name");
  Harness.test "a local is not in scope after its block" (fun () ->
      one_diagnostic Fixtures.Resolve.local_read_after_its_block "resolve.unknown_name")

let () =
  Harness.test "a local cannot shadow a local of an enclosing block" (fun () ->
      one_diagnostic Fixtures.Resolve.let_shadowing_an_enclosing_let "resolve.shadowed_name");
  Harness.test "a local cannot shadow a parameter" (fun () ->
      one_diagnostic Fixtures.Resolve.let_shadowing_a_parameter "resolve.shadowed_name");
  Harness.test "a local may shadow a function of its module, and its uses are the local" (fun () ->
      refers_to_binding Fixtures.Resolve.let_named_like_a_function ~use:("total", 3)
        ~binding:("total", 2));
  Harness.test "a local may shadow a definition in another file of its module" (fun () ->
      no_diagnostics
        [
          ("app::main", "fn f() -> Int64 {\n  let total = 2\n  total\n}\n");
          ("app::main/sums", "fn total() -> Int64 { 0 }\n");
        ]);
  Harness.test "a let binds the name of a constant of its module, which its uses then name"
    (fun () ->
      refers_to_binding Fixtures.Resolve.let_named_like_a_constant ~use:("limit", 3)
        ~binding:("limit", 2));
  Harness.test "a generic parameter cannot shadow a type of its module" (fun () ->
      one_diagnostic Fixtures.Resolve.generic_named_like_a_type_of_its_module
        ~says:"a type of this module" "resolve.shadowed_name");
  Harness.test "a generic parameter cannot shadow a prelude type" (fun () ->
      one_diagnostic "fn f[Option](value: Option) {}\n" "resolve.shadowed_name");
  Harness.test "locals in sibling blocks may share a name" (fun () ->
      no_diagnostics [ ("app::main", Fixtures.Resolve.lets_of_one_name_in_sibling_blocks) ])

let () =
  Harness.test "a file names a private definition of another file of its module without a module"
    (fun () ->
      refers "fn f() -> Int64 {\n  size()\n}\n"
        ~others:[ ("app::main/grid", "fn size() -> Int64 { 9 }\n") ]
        ~name:("size", 1) "app::main::size");
  Harness.test "two files of a module that define one name make a duplicate" (fun () ->
      one_diagnostic "fn size() -> Int64 { 9 }\n"
        ~others:[ ("app::main/grid", "fn size() -> Int64 { 3 }\n") ]
        ~says:"already defined in app/main/grid.truss" "resolve.duplicate_definition");
  Harness.test
    "impls in two files that spell one trait the same but import different modules are two"
    (fun () ->
      no_diagnostics
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
      one_diagnostic
        "use app::one::codec\n\n\
         public type Point(x: Int64)\n\n\
         impl codec::Marker for Point {\n\
         }\n\n\
         impl app::one::codec::Marker for Point {\n\
         }\n"
        ~others:[ ("app::one::codec", "public trait Marker {\n}\n") ]
        ~says:"already defined in this file" "resolve.duplicate_definition");
  Harness.test "a file names a module only through its own imports" (fun () ->
      one_diagnostic Fixtures.Resolve.area_call_without_an_import
        ~others:
          [
            ("app::shapes", "internal fn area() -> Int64 { 0 }\n");
            ("app::main/other", Fixtures.Resolve.second_file_importing_shapes);
          ]
        "resolve.unknown_module")

let () =
  Harness.test "a bare name in a pattern binds where a constant has its name" (fun () ->
      refers Fixtures.Resolve.bare_name_arm_named_like_a_constant ~name:("limit", 2) "binding");
  Harness.test "a constant of its own module in a pattern is written with its module" (fun () ->
      refers Fixtures.Resolve.qualified_constant_arm ~name:("limit", 2) "app::main::limit");
  Harness.test "the alternatives of a pattern must bind the same names" (fun () ->
      one_diagnostic Fixtures.Resolve.or_pattern_binding_different_names
        "resolve.alternative_bindings");
  Harness.test "an alternative's name refers to the first alternative's binding" (fun () ->
      refers_to_binding Fixtures.Resolve.or_pattern_binding_value_in_both ~use:("value", 3)
        ~binding:("value", 1))

let () =
  Harness.test "an unknown name is an error with a fix to the closest name" (fun () ->
      one_diagnostic Fixtures.Resolve.misspelled_parameter "resolve.unknown_name"
        ~fixed:Fixtures.Resolve.misspelled_parameter_fixed);
  Harness.test "null is an error with a fix that writes None" (fun () ->
      one_diagnostic Fixtures.Resolve.null_literal "resolve.null"
        ~fixed:Fixtures.Resolve.null_literal_fixed);
  Harness.test "an unknown type is an error" (fun () ->
      one_diagnostic "fn f(value: Strng) {}\n" "resolve.unknown_name")

let () =
  Harness.test "a prelude type is the standard library's" (fun () ->
      refers "fn f(value: Option[Int64]) {}\n" ~name:("Option", 1) "standard::option::Option");
  Harness.test "a built-in type is the intrinsic module's" (fun () ->
      refers "fn f(value: Int64) {}\n" ~name:("Int64", 1) "standard::intrinsic::Int64");
  Harness.test "a prelude variant is written bare" (fun () ->
      refers Fixtures.Resolve.bare_some ~name:("Some", 1) "variant Some of standard::option::Option")

let bracket_of text written occurrence =
  let packages = setup [ ("app::main", text) ] in
  let offset = Option.get (Substring.For_testing.find ~occurrence text written) in
  let declarations = Support.declarations packages (Support.module_of "app::main") in
  List.find_map
    (fun (declaration : Resolve.Names.declaration) ->
      let key = Resolve.Names.key_of declaration in
      match
        ( (Support.names packages key.module_.package).definition key,
          (Support.names packages key.module_.package).spans key,
          (Support.names packages key.module_.package).place key,
          Database.read_resolved (Support.database packages) key )
      with
      | definition, spans, { base; _ }, Some resolved ->
          let bracket = ref None in
          Syntax_walk.definition
            (let rec visit (value : Syntax.expression) =
               (match value.kind with
               | Bracket _ when base + spans.(value.id).start = offset ->
                   bracket := resolved.brackets.(value.id)
               | _ -> ());
               Syntax_walk.children visit value
             in
             visit)
            definition;
          !bracket
      | _ -> None)
    declarations

let () =
  Harness.test "brackets after a generic function give type arguments" (fun () ->
      let text = Fixtures.Resolve.brackets_after_a_generic_function in
      match bracket_of text "parse[Int64]" 1 with
      | Some Resolve.Type_arguments -> ()
      | _ -> Harness.fail "not type arguments");
  Harness.test "brackets after a local index it" (fun () ->
      let text = Fixtures.Resolve.brackets_after_a_local in
      match bracket_of text "items[0]" 1 with
      | Some Resolve.Index -> ()
      | _ -> Harness.fail "not an index");
  Harness.test "brackets after a method are left to type checking" (fun () ->
      let text = Fixtures.Resolve.brackets_after_a_method in
      match bracket_of text "items.map[Int64]" 1 with
      | Some Resolve.Method_bracket -> ()
      | _ -> Harness.fail "decided");
  Harness.test "brackets after a function without generic parameters are an error" (fun () ->
      one_diagnostic Fixtures.Resolve.brackets_after_a_plain_function "resolve.not_generic")

let () =
  Harness.test "mut before a call to a function is an error with a fix that removes it" (fun () ->
      one_diagnostic Fixtures.Resolve.mut_before_a_function_call "resolve.not_a_place"
        ~fixed:Fixtures.Resolve.mut_before_a_function_call_fixed);
  Harness.test "mut before a local's field and method call is a place" (fun () ->
      no_diagnostics [ ("app::main", Fixtures.Resolve.mut_push_onto_a_local) ]);
  Harness.test "a ? after a call with a mode keyword works on its result" (fun () ->
      no_diagnostics [ ("app::main", Fixtures.Resolve.question_mark_after_a_mut_pop) ]);
  Harness.test "a ? before any method call does not make a place" (fun () ->
      one_diagnostic Fixtures.Resolve.mut_call_through_a_question_mark "resolve.not_a_place")

let () =
  Harness.test "result in ensures is the return value" (fun () ->
      refers Fixtures.Resolve.ensures_reading_result ~name:("result", 1) "result");
  Harness.test "result outside a specification is an ordinary name" (fun () ->
      one_diagnostic Fixtures.Resolve.body_reading_result "resolve.unknown_name");
  Harness.test "old in a specification is the value on entry" (fun () ->
      refers Fixtures.Resolve.ensures_reading_old ~name:("old", 1) "old");
  Harness.test "log in a cost bound is the specification function" (fun () ->
      refers Fixtures.Resolve.cost_logarithmic_in_a_count ~name:("log", 1) "specification function");
  Harness.test "a record's fields are in scope in its invariant" (fun () ->
      refers "type Range(low: Int64, high: Int64)\n  invariant low <= high\n" ~name:("low", 2)
        "field low")

let others = [ ("app::shapes", Fixtures.Resolve.others_shapes) ]

let () =
  Harness.test "a name after an imported module is that module's" (fun () ->
      refers ~others Fixtures.Resolve.area_call_with_an_import ~name:("area", 1) "app::shapes::area");
  Harness.test "a full path needs no use" (fun () ->
      refers ~others Fixtures.Resolve.area_call_through_a_full_path ~name:("area", 1)
        "app::shapes::area");
  Harness.test "a private definition of another file is not visible" (fun () ->
      one_diagnostic ~others Fixtures.Resolve.call_of_another_files_private_function
        "resolve.not_visible");
  Harness.test "an import nothing uses is an error with a fix that deletes it" (fun () ->
      one_diagnostic ~others Fixtures.Resolve.unused_import "resolve.unused_import"
        ~fixed:"\nfn f() {}\n");
  Harness.test "an import used only in an interpolation is used" (fun () ->
      no_diagnostics
        (others
        @ [ ("app::main", "use app::shapes\n\nfn f() {\n  let text = \"${shapes::area()}\"\n}\n") ]
        ));
  Harness.test "a path through an import that names no module is that path's error alone" (fun () ->
      one_diagnostic ~others "use app::shapes\n\nfn f() -> Int64 {\n  shapes::missing::area()\n}\n"
        "resolve.unknown_module");
  Harness.test "a file where the parser recovered reports no unused import" (fun () ->
      let packages =
        setup
          (others
          @ [ ("app::main", "use app::shapes\n\nfn f() -> Int64 {\n  let = shapes::area()\n}\n") ])
      in
      let file = file_of "app::main" in
      if Support.parse_errors packages file = [] then Harness.fail "parsed";
      match Database.For_testing.list_diagnostics [ Resolve ] (Database.create packages) file with
      | [] -> ()
      | reported -> Harness.fail "reported %s" (String.concat "; " (codes reported)));
  Harness.test "an import of a module that does not exist is an error" (fun () ->
      one_diagnostic Fixtures.Resolve.import_of_a_missing_module "resolve.unknown_module");
  Harness.test "two imports with one last name are an error at the second" (fun () ->
      Support.one_diagnostic ~check
        ~setup:(setup ~dependencies:[ ("app", "other") ])
        ~others:
          [
            ("app::shapes", "public fn area() -> Int64 { 0 }\n");
            ("other::shapes", "public fn area() -> Int64 { 0 }\n");
          ]
        Fixtures.Resolve.two_imports_ending_in_shapes "resolve.duplicate_import");
  Harness.test "only the standard package can import standard::intrinsic" (fun () ->
      one_diagnostic Fixtures.Resolve.import_of_standard_intrinsic "resolve.intrinsic_import")

let () =
  Harness.test "a second definition with one name is an error" (fun () ->
      one_diagnostic Fixtures.Resolve.two_functions_of_one_name "resolve.duplicate_definition");
  Harness.test "a method's type head names its type" (fun () ->
      let packages = setup [ ("app::main", Fixtures.Resolve.counter_method) ] in
      let owner = Path.Top { module_ = module_of "app::main"; name = "Counter" } in
      let owner_package = (module_of "app::main").package in
      match (Support.names packages owner_package).members owner "get" with
      | [ { path = Method { receiver = Read; _ }; _ } ] -> ()
      | reported -> Harness.fail "found %d members" (List.length reported));
  Harness.test "a method can be written in another file of its type's package" (fun () ->
      let packages =
        setup
          [
            ("app::main", "public type Counter(count: Int64)\n");
            ("app::extra", Fixtures.Resolve.counter_method_in_another_file);
          ]
      in
      let owner = Path.Top { module_ = module_of "app::main"; name = "Counter" } in
      let owner_package = (module_of "app::main").package in
      match (Support.names packages owner_package).members owner "get" with
      | [ _ ] -> ()
      | reported -> Harness.fail "found %d members" (List.length reported));
  Harness.test "a body the parser could not read is not resolved" (fun () ->
      let packages = setup [ ("app::main", Fixtures.Resolve.body_with_a_broken_let) ] in
      let file = file_of "app::main" in
      if Support.parse_errors packages file = [] then Harness.fail "parsed";
      match Database.For_testing.list_diagnostics [ Resolve ] (Database.create packages) file with
      | [] -> ()
      | reported ->
          Harness.fail "resolved the broken body: %s" (String.concat "; " (codes reported)))

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
      match codes (diagnostics packages "app::extra") with
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
          (file_of "app::main")
      with
      | [] -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " (codes reported)));
  Harness.test "an element of a field is a place" (fun () ->
      no_diagnostics [ ("app::main", Fixtures.Resolve.mut_element_of_a_field) ]);
  Harness.test "two parallel branches cannot bind one name" (fun () ->
      one_diagnostic Fixtures.Resolve.parallel_lets_of_one_name "resolve.shadowed_name");
  Harness.test "two concurrent branches cannot bind one name" (fun () ->
      one_diagnostic Fixtures.Resolve.concurrent_lets_of_one_name "resolve.shadowed_name");
  Harness.test "a definition cannot take a prelude name" (fun () ->
      one_diagnostic "type List(count: Int64)\n" "resolve.shadowed_name");
  Harness.test "a generic parameter cannot take a prelude variant's name" (fun () ->
      one_diagnostic "fn f[Some](value: Some) {}\n" "resolve.shadowed_name");
  Harness.test "a trait whose header did not parse is not resolved" (fun () ->
      let packages = setup [ ("app::main", Fixtures.Resolve.trait_with_a_broken_header) ] in
      match
        Database.For_testing.list_diagnostics [ Resolve ] (Database.create packages)
          (file_of "app::main")
      with
      | [] -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " (codes reported)))

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
      (match diagnostics packages "app::main" with
      | [] -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " (codes reported)));
      match
        (Support.names packages (file_of "app::main").module_.package).imports
          {
            module_ = (file_of "app::main").module_;
            path = Top { module_ = (file_of "app::main").module_; name = "f" };
            ordinal = 0;
          }
      with
      | [ ("vector", imported) ] when imported = geometry -> ()
      | _ -> Harness.fail "imported differently");
  Harness.test "a package with an owner that the manifest does not list cannot be named" (fun () ->
      let packages = with_geometry ~dependencies:[] uses_both in
      match codes (diagnostics packages "app::main") with
      | "resolve.unknown_module" :: _ -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " reported));
  Harness.test "an owner alone names no package" (fun () ->
      let packages =
        with_geometry
          ~dependencies:[ { Path.owner = Some "acme"; name = "geometry" } ]
          Fixtures.Resolve.import_of_an_owner_alone
      in
      match codes (diagnostics packages "app::main") with
      | "resolve.unknown_module" :: _ -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " reported))

let () =
  Harness.test "a name used through an import of standard::intrinsic is not an error of its own"
    (fun () ->
      one_diagnostic Fixtures.Resolve.call_through_standard_intrinsic "resolve.intrinsic_import")
