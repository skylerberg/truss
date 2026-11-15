open Harness

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

let diagnostics database name =
  let file = file_of name in
  (match Support.parse_errors database file with
  | [] -> ()
  | errors -> fail "the test input does not parse: %s" (String.concat " " errors));
  Pipeline.For_testing.(diagnostics [ Resolve ]) (Pipeline.create database) file

let codes = Support.codes

let no_diagnostics files =
  let database = setup files in
  List.iter
    (fun (name, _) ->
      match diagnostics database name with
      | [] -> ()
      | reported ->
          fail "%s: %s" name
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) reported)))
    files

let check database = Pipeline.For_testing.(diagnostics [ Resolve ]) (Pipeline.create database)
let one_diagnostic = Support.one_diagnostic ~setup:(fun files -> setup files) ~check

let name_at database name text occurrence =
  let file = file_of name in
  let source = Source.text (Support.source database file) in
  let offset = Option.get (Substring.find ~occurrence source text) in
  if offset < 0 then failwith (Printf.sprintf "no occurrence %d of %S" occurrence text);
  let located =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        match
          ( (Support.names database key.module_.package).definition key,
            (Support.names database key.module_.package).spans key,
            (Support.names database key.module_.package).place key,
            Pipeline.resolved (Support.pipeline database) key )
        with
        | Some definition, Some spans, Some { base; _ }, Some resolved ->
            Option.map
              (fun (name : Syntax.name) -> (name, spans, base, resolved))
              (List.find_opt
                 (fun (name : Syntax.name) -> base + spans.(name.id).start = offset)
                 (Syntax_walk.collect_names spans definition))
        | _ -> None)
      ((Support.names database file.module_.package).declarations_in file)
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
  let database = setup (("app::main", text) :: others) in
  let name, spans, base, resolved = name_at database "app::main" written occurrence in
  let actual = describe spans base resolved.names.(name.id) in
  if actual <> expected then fail "`%s` #%d is %s, not %s" written occurrence actual expected

let refers_to_binding text ~use ~binding =
  let database = setup [ ("app::main", text) ] in
  let source = text in
  let binding_offset = Option.get (Substring.find ~occurrence:(snd binding) source (fst binding)) in
  let name, spans, base, resolved = name_at database "app::main" (fst use) (snd use) in
  let actual = describe spans base resolved.names.(name.id) in
  let expected = Printf.sprintf "local at %d" binding_offset in
  if actual <> expected then fail "`%s` is %s, not %s" (fst use) actual expected

let () =
  test "a local refers to the let that binds it" (fun () ->
      refers_to_binding Fixtures.Resolve.local_refers_to_the_let_that_binds_it ~use:("count", 2)
        ~binding:("count", 1));
  test "a parameter is a local of the body" (fun () ->
      refers_to_binding Fixtures.Resolve.parameter_is_a_local_of_the_body ~use:("count", 2)
        ~binding:("count", 1));
  test "a function type's input is the binding its requires refers to" (fun () ->
      refers_to_binding "fn f(visit: (fn(index: UInt64) requires index < 3)) {}\n" ~use:("index", 2)
        ~binding:("index", 1));
  test "a name bound by is is in scope in the if's block" (fun () ->
      refers_to_binding Fixtures.Resolve.name_bound_by_is_is_in_scope_in_the_ifs_block
        ~use:("value", 2) ~binding:("value", 1));
  test "a name bound by is is in scope in the rest of its && chain" (fun () ->
      refers_to_binding Fixtures.Resolve.name_bound_by_is_is_in_scope_in_the_rest_of_its
        ~use:("value", 2) ~binding:("value", 1));
  test "a name bound by is is not in scope in the else" (fun () ->
      one_diagnostic Fixtures.Resolve.name_bound_by_is_is_not_in_scope_in_the_else
        "resolve.unknown_name");
  test "a name bound by is is not in scope after ||" (fun () ->
      one_diagnostic Fixtures.Resolve.name_bound_by_is_is_not_in_scope_after "resolve.unknown_name");
  test "a name bound by let else is in scope after it" (fun () ->
      refers_to_binding Fixtures.Resolve.name_bound_by_let_else_is_in_scope_after_it
        ~use:("value", 2) ~binding:("value", 1));
  test "a name bound in a match arm is in scope in its guard and body" (fun () ->
      refers_to_binding Fixtures.Resolve.name_bound_in_a_match_arm_is_in_scope_in_its_guard
        ~use:("value", 3) ~binding:("value", 1));
  test "a let in a parallel branch is in scope after the block" (fun () ->
      refers_to_binding Fixtures.Resolve.let_in_a_parallel_branch_is_in_scope_after_the
        ~use:("left", 2) ~binding:("left", 1));
  test "a let in a parallel branch is not in scope in another branch" (fun () ->
      one_diagnostic Fixtures.Resolve.let_in_a_parallel_branch_is_not_in_scope_in
        "resolve.unknown_name");
  test "a let in a concurrent branch is in scope after the block, and in no other branch" (fun () ->
      refers_to_binding Fixtures.Resolve.let_in_a_concurrent_branch_is_in_scope_after_the
        ~use:("left", 2) ~binding:("left", 1);
      one_diagnostic Fixtures.Resolve.let_in_a_concurrent_branch_is_in_scope_after_the_2
        "resolve.unknown_name");
  test "a lambda's parameter is in scope in its body" (fun () ->
      refers_to_binding Fixtures.Resolve.lambdas_parameter_is_in_scope_in_its_body ~use:("item", 2)
        ~binding:("item", 1));
  test "a range loop's index is in scope in its clauses" (fun () ->
      refers_to_binding Fixtures.Resolve.range_loops_index_is_in_scope_in_its_clauses
        ~use:("index", 2) ~binding:("index", 1));
  test "a loop's element is not in scope in its clauses" (fun () ->
      one_diagnostic Fixtures.Resolve.loops_element_is_not_in_scope_in_its_clauses
        "resolve.unknown_name");
  test "a local is not in scope after its block" (fun () ->
      one_diagnostic Fixtures.Resolve.local_is_not_in_scope_after_its_block "resolve.unknown_name")

let () =
  test "a local cannot shadow a local of an enclosing block" (fun () ->
      one_diagnostic Fixtures.Resolve.local_cannot_shadow_a_local_of_an_enclosing_block
        "resolve.shadowed_name");
  test "a local cannot shadow a parameter" (fun () ->
      one_diagnostic Fixtures.Resolve.local_cannot_shadow_a_parameter "resolve.shadowed_name");
  test "a local may shadow a function of its module, and its uses are the local" (fun () ->
      refers_to_binding Fixtures.Resolve.local_may_shadow_a_function_of_its_module ~use:("total", 3)
        ~binding:("total", 2));
  test "a local may shadow a definition in another file of its module" (fun () ->
      no_diagnostics
        [
          ("app::main", "fn f() -> Int64 {\n  let total = 2\n  total\n}\n");
          ("app::main/sums", "fn total() -> Int64 { 0 }\n");
        ]);
  test "a let binds the name of a constant of its module, which its uses then name" (fun () ->
      refers_to_binding Fixtures.Resolve.let_may_shadow_a_constant_of_its_module ~use:("limit", 3)
        ~binding:("limit", 2));
  test "a generic parameter cannot shadow a type of its module" (fun () ->
      one_diagnostic Fixtures.Resolve.generic_parameter_cannot_shadow_a_type_of_its_module
        ~says:"a type of this module" "resolve.shadowed_name");
  test "a generic parameter cannot shadow a prelude type" (fun () ->
      one_diagnostic "fn f[Option](value: Option) {}\n" "resolve.shadowed_name");
  test "locals in sibling blocks may share a name" (fun () ->
      no_diagnostics [ ("app::main", Fixtures.Resolve.locals_in_sibling_blocks_may_share_a_name) ])

let () =
  test "a file names a private definition of another file of its module without a module" (fun () ->
      refers "fn f() -> Int64 {\n  size()\n}\n"
        ~others:[ ("app::main/grid", "fn size() -> Int64 { 9 }\n") ]
        ~name:("size", 1) "app::main::size");
  test "two files of a module that define one name make a duplicate" (fun () ->
      one_diagnostic "fn size() -> Int64 { 9 }\n"
        ~others:[ ("app::main/grid", "fn size() -> Int64 { 3 }\n") ]
        ~says:"already defined in app/main/grid.truss" "resolve.duplicate_definition");
  test "a file names a module only through its own imports" (fun () ->
      one_diagnostic Fixtures.Resolve.file_without_the_use_cannot_name_the_module
        ~others:
          [
            ("app::shapes", "internal fn area() -> Int64 { 0 }\n");
            ("app::main/other", Fixtures.Resolve.file_without_the_use_cannot_name_the_module_2);
          ]
        "resolve.unknown_module")

let () =
  test "a bare name in a pattern binds where a constant has its name" (fun () ->
      refers Fixtures.Resolve.bare_name_in_a_pattern_binds_where_a_constant_has ~name:("limit", 2)
        "binding");
  test "a constant of its own module in a pattern is written with its module" (fun () ->
      refers Fixtures.Resolve.constant_of_its_own_module_in_a_pattern_is_written ~name:("limit", 2)
        "app::main::limit");
  test "the alternatives of a pattern must bind the same names" (fun () ->
      one_diagnostic Fixtures.Resolve.alternatives_of_a_pattern_must_bind_the_same_names
        "resolve.alternative_bindings");
  test "an alternative's name refers to the first alternative's binding" (fun () ->
      refers_to_binding Fixtures.Resolve.alternatives_name_refers_to_the_first_alternatives
        ~use:("value", 3) ~binding:("value", 1))

let () =
  test "an unknown name is an error with a fix to the closest name" (fun () ->
      one_diagnostic Fixtures.Resolve.unknown_name_is_an_error_with_a_fix_to_the_closest
        "resolve.unknown_name"
        ~fixed:Fixtures.Resolve.unknown_name_is_an_error_with_a_fix_to_the_closest_fixed);
  test "null is an error with a fix that writes None" (fun () ->
      one_diagnostic Fixtures.Resolve.null_is_an_error_with_a_fix_that_writes_none "resolve.null"
        ~fixed:Fixtures.Resolve.null_is_an_error_with_a_fix_that_writes_none_fixed);
  test "an unknown type is an error" (fun () ->
      one_diagnostic "fn f(value: Strng) {}\n" "resolve.unknown_name")

let () =
  test "a prelude type is the standard library's" (fun () ->
      refers "fn f(value: Option[Int64]) {}\n" ~name:("Option", 1) "standard::option::Option");
  test "a built-in type is the intrinsic module's" (fun () ->
      refers "fn f(value: Int64) {}\n" ~name:("Int64", 1) "standard::intrinsic::Int64");
  test "a prelude variant is written bare" (fun () ->
      refers Fixtures.Resolve.prelude_variant_is_written_bare ~name:("Some", 1)
        "variant Some of standard::option::Option")

let bracket_of text written occurrence =
  let database = setup [ ("app::main", text) ] in
  let offset = Option.get (Substring.find ~occurrence text written) in
  let declarations = Support.declarations database (Support.module_of "app::main") in
  List.find_map
    (fun (declaration : Resolve.Names.declaration) ->
      let key = Resolve.Names.key_of declaration in
      match
        ( (Support.names database key.module_.package).definition key,
          (Support.names database key.module_.package).spans key,
          (Support.names database key.module_.package).place key,
          Pipeline.resolved (Support.pipeline database) key )
      with
      | Some definition, Some spans, Some { base; _ }, Some resolved ->
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
  test "brackets after a generic function give type arguments" (fun () ->
      let text = Fixtures.Resolve.brackets_after_a_generic_function_give_type in
      match bracket_of text "parse[Int64]" 1 with
      | Some Resolve.Type_arguments -> ()
      | _ -> fail "not type arguments");
  test "brackets after a local index it" (fun () ->
      let text = Fixtures.Resolve.brackets_after_a_local_index_it in
      match bracket_of text "items[0]" 1 with Some Resolve.Index -> () | _ -> fail "not an index");
  test "brackets after a method are left to type checking" (fun () ->
      let text = Fixtures.Resolve.brackets_after_a_method_are_left_to_type_checking in
      match bracket_of text "items.map[Int64]" 1 with
      | Some Resolve.Method_bracket -> ()
      | _ -> fail "decided");
  test "brackets after a function without generic parameters are an error" (fun () ->
      one_diagnostic Fixtures.Resolve.brackets_after_a_function_without_generic
        "resolve.not_generic")

let () =
  test "mut before a call to a function is an error with a fix that removes it" (fun () ->
      one_diagnostic Fixtures.Resolve.mut_before_a_call_to_a_function_is_an_error_with_a
        "resolve.not_a_place"
        ~fixed:Fixtures.Resolve.mut_before_a_call_to_a_function_is_an_error_with_a_fixed);
  test "mut before a local's field and method call is a place" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Resolve.mut_before_a_locals_field_and_method_call_is_a) ]);
  test "a ? after a call with a mode keyword works on its result" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Resolve.after_a_call_with_a_mode_keyword_works_on_its_result) ]);
  test "a ? before any method call does not make a place" (fun () ->
      one_diagnostic Fixtures.Resolve.before_any_method_call_does_not_make_a_place
        "resolve.not_a_place")

let () =
  test "result in ensures is the return value" (fun () ->
      refers Fixtures.Resolve.result_in_ensures_is_the_return_value ~name:("result", 1) "result");
  test "result outside a specification is an ordinary name" (fun () ->
      one_diagnostic Fixtures.Resolve.result_outside_a_specification_is_an_ordinary_name
        "resolve.unknown_name");
  test "old in a specification is the value on entry" (fun () ->
      refers Fixtures.Resolve.old_in_a_specification_is_the_value_on_entry ~name:("old", 1) "old");
  test "log in a cost bound is the specification function" (fun () ->
      refers Fixtures.Resolve.log_in_a_cost_bound_is_the_specification_function ~name:("log", 1)
        "specification function");
  test "a record's fields are in scope in its invariant" (fun () ->
      refers "type Range(low: Int64, high: Int64)\n  invariant low <= high\n" ~name:("low", 2)
        "field low")

let others = [ ("app::shapes", Fixtures.Resolve.others_shapes) ]

let () =
  test "a name after an imported module is that module's" (fun () ->
      refers ~others Fixtures.Resolve.name_after_an_imported_module_is_that_modules
        ~name:("area", 1) "app::shapes::area");
  test "a full path needs no use" (fun () ->
      refers ~others Fixtures.Resolve.full_path_needs_no_use ~name:("area", 1) "app::shapes::area");
  test "a private definition of another file is not visible" (fun () ->
      one_diagnostic ~others Fixtures.Resolve.private_definition_of_another_file_is_not_visible
        "resolve.not_visible");
  test "an import nothing uses is an error with a fix that deletes it" (fun () ->
      one_diagnostic ~others Fixtures.Resolve.import_nothing_uses_is_an_error_with_a_fix_that
        "resolve.unused_import" ~fixed:"\nfn f() {}\n");
  test "an import used only in an interpolation is used" (fun () ->
      no_diagnostics
        (others
        @ [ ("app::main", "use app::shapes\n\nfn f() {\n  let text = \"${shapes::area()}\"\n}\n") ]
        ));
  test "a path through an import that names no module is that path's error alone" (fun () ->
      one_diagnostic ~others "use app::shapes\n\nfn f() -> Int64 {\n  shapes::missing::area()\n}\n"
        "resolve.unknown_module");
  test "a file where the parser recovered reports no unused import" (fun () ->
      let database =
        setup
          (others
          @ [ ("app::main", "use app::shapes\n\nfn f() -> Int64 {\n  let = shapes::area()\n}\n") ])
      in
      let file = file_of "app::main" in
      if Support.parse_errors database file = [] then fail "parsed";
      match Pipeline.For_testing.(diagnostics [ Resolve ]) (Pipeline.create database) file with
      | [] -> ()
      | reported -> fail "reported %s" (String.concat "; " (codes reported)));
  test "an import of a module that does not exist is an error" (fun () ->
      one_diagnostic Fixtures.Resolve.import_of_a_module_that_does_not_exist_is_an_error
        "resolve.unknown_module");
  test "two imports with one last name are an error at the second" (fun () ->
      Support.one_diagnostic ~check
        ~setup:(setup ~dependencies:[ ("app", "other") ])
        ~others:
          [
            ("app::shapes", "public fn area() -> Int64 { 0 }\n");
            ("other::shapes", "public fn area() -> Int64 { 0 }\n");
          ]
        Fixtures.Resolve.two_imports_with_one_last_name_are_an_error_at_the
        "resolve.duplicate_import");
  test "only the standard package can import standard::intrinsic" (fun () ->
      one_diagnostic Fixtures.Resolve.only_the_standard_package_can_import_standard
        "resolve.intrinsic_import")

let () =
  test "a second definition with one name is an error" (fun () ->
      one_diagnostic Fixtures.Resolve.second_definition_with_one_name_is_an_error
        "resolve.duplicate_definition");
  test "a method's type head names its type" (fun () ->
      let database = setup [ ("app::main", Fixtures.Resolve.methods_type_head_names_its_type) ] in
      let owner = Path.Top { module_ = module_of "app::main"; name = "Counter" } in
      let owner_package = (module_of "app::main").package in
      match (Support.names database owner_package).members owner "get" with
      | [ { path = Method { receiver = Read; _ }; _ } ] -> ()
      | reported -> fail "found %d members" (List.length reported));
  test "a method can be written in another file of its type's package" (fun () ->
      let database =
        setup
          [
            ("app::main", "public type Counter(count: Int64)\n");
            ("app::extra", Fixtures.Resolve.method_can_be_written_in_another_file_of_its_types_extra);
          ]
      in
      let owner = Path.Top { module_ = module_of "app::main"; name = "Counter" } in
      let owner_package = (module_of "app::main").package in
      match (Support.names database owner_package).members owner "get" with
      | [ _ ] -> ()
      | reported -> fail "found %d members" (List.length reported));
  test "a body the parser could not read is not resolved" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Resolve.body_the_parser_could_not_read_is_not_resolved) ]
      in
      let file = file_of "app::main" in
      if Support.parse_errors database file = [] then fail "parsed";
      match Pipeline.For_testing.(diagnostics [ Resolve ]) (Pipeline.create database) file with
      | [] -> ()
      | reported -> fail "resolved the broken body: %s" (String.concat "; " (codes reported)))

let () =
  test "a method in another file of its type's package is resolved, and its import counts"
    (fun () ->
      let database =
        setup
          [
            ("app::main", "public type Counter(count: Int64)\n");
            ("app::extra", Fixtures.Resolve.method_in_another_file_of_its_types_package_is_extra);
          ]
      in
      match codes (diagnostics database "app::extra") with
      | [ "resolve.unknown_name" ] -> ()
      | reported -> fail "found [%s]" (String.concat "; " reported));
  test "an import used only in a part the parser could not read is not unused" (fun () ->
      let database =
        setup
          [
            ("app::shapes", "public fn area() -> Int64 { 0 }\n");
            ("app::main", Fixtures.Resolve.import_used_only_in_a_part_the_parser_could_not);
          ]
      in
      match
        Pipeline.For_testing.(diagnostics [ Resolve ])
          (Pipeline.create database) (file_of "app::main")
      with
      | [] -> ()
      | reported -> fail "found [%s]" (String.concat "; " (codes reported)));
  test "an element of a field is a place" (fun () ->
      no_diagnostics [ ("app::main", Fixtures.Resolve.element_of_a_field_is_a_place) ]);
  test "two parallel branches cannot bind one name" (fun () ->
      one_diagnostic Fixtures.Resolve.two_parallel_branches_cannot_bind_one_name
        "resolve.shadowed_name");
  test "two concurrent branches cannot bind one name" (fun () ->
      one_diagnostic Fixtures.Resolve.two_concurrent_branches_cannot_bind_one_name
        "resolve.shadowed_name");
  test "a definition cannot take a prelude name" (fun () ->
      one_diagnostic "type List(count: Int64)\n" "resolve.shadowed_name");
  test "a generic parameter cannot take a prelude variant's name" (fun () ->
      one_diagnostic "fn f[Some](value: Some) {}\n" "resolve.shadowed_name");
  test "a trait whose header did not parse is not resolved" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Resolve.trait_whose_header_did_not_parse_is_not_resolved) ]
      in
      match
        Pipeline.For_testing.(diagnostics [ Resolve ])
          (Pipeline.create database) (file_of "app::main")
      with
      | [] -> ()
      | reported -> fail "found [%s]" (String.concat "; " (codes reported)))

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
  test "a path into a package with an owner starts with the owner and the name" (fun () ->
      let database =
        with_geometry ~dependencies:[ { Path.owner = Some "acme"; name = "geometry" } ] uses_both
      in
      (match diagnostics database "app::main" with
      | [] -> ()
      | reported -> fail "found [%s]" (String.concat "; " (codes reported)));
      match
        (Support.names database (file_of "app::main").module_.package).imports
          {
            module_ = (file_of "app::main").module_;
            path = Top { module_ = (file_of "app::main").module_; name = "f" };
            ordinal = 0;
          }
      with
      | [ ("vector", imported) ] when imported = geometry -> ()
      | _ -> fail "imported differently");
  test "a package with an owner that the manifest does not list cannot be named" (fun () ->
      let database = with_geometry ~dependencies:[] uses_both in
      match codes (diagnostics database "app::main") with
      | "resolve.unknown_module" :: _ -> ()
      | reported -> fail "found [%s]" (String.concat "; " reported));
  test "an owner alone names no package" (fun () ->
      let database =
        with_geometry
          ~dependencies:[ { Path.owner = Some "acme"; name = "geometry" } ]
          Fixtures.Resolve.owner_alone_names_no_package
      in
      match codes (diagnostics database "app::main") with
      | "resolve.unknown_module" :: _ -> ()
      | reported -> fail "found [%s]" (String.concat "; " reported))

let () =
  test "a name used through an import of standard::intrinsic is not an error of its own" (fun () ->
      one_diagnostic Fixtures.Resolve.name_used_through_an_import_of_standard_intrinsic
        "resolve.intrinsic_import")
