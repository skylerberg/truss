let check packages =
  Database.For_testing.list_diagnostics [ Resolve; Interface ] (Support.make_database packages)

let expect_one_diagnostic = Support.expect_one_diagnostic ~check
let expect_no_diagnostics = Support.expect_no_diagnostics ~check
let app name : Path.t = Top { module_ = Support.parse_module "app::main"; name }

let make_interface packages =
  Database.make_interface_lookups (Support.make_database packages)
    [ (Support.parse_module "app::main").package ]

let make_standard_path = Path.make_standard_path
let int64 = Types.make_builtin Int64

let () =
  let packages = Support.setup [] in
  List.iter
    (fun ((file : Path.file), text) ->
      Harness.test
        (Printf.sprintf "%s has no interface errors" (Path.show_file file))
        (fun () ->
          let source = Source.create ~path:(Path.show_file file) text in
          List.iter
            (fun diagnostic -> Harness.fail "%s" (Diagnostic.render source diagnostic))
            (Database.For_testing.list_diagnostics [ Interface ] (Support.make_database packages)
               file)))
    Standard_library.files

let () =
  Harness.test "a function's signature is elaborated" (fun () ->
      let packages =
        Support.setup
          [
            ("app::main", "fn count(items: List[Int64], limit: own Int64 = 3) -> UInt64 { todo }\n");
          ]
      in
      match
        Interface.Definition.find_declared_signature (make_interface packages) (app "count")
      with
      | Some { parameters = [ items; limit ]; output = Returns output; _ } ->
          if Types.show items.type_ <> "List[Int64]" then
            Harness.fail "items: %s" (Types.show items.type_);
          if limit.mode <> Own || not limit.has_default then Harness.fail "limit";
          if not (Types.is_builtin UInt64 output) then Harness.fail "output %s" (Types.show output)
      | _ -> Harness.fail "no signature");
  Harness.test "a method's receiver has its type's generic parameters" (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Interface.method_head_with_generics) ]
      in
      let path : Path.t = Method { owner = app "Box"; name = "get"; receiver = Read } in
      match Interface.Definition.find_declared_signature (make_interface packages) path with
      | Some { receiver = Some (Read, self); _ } ->
          if Types.show self <> "Box[Value]" then Harness.fail "self: %s" (Types.show self)
      | _ -> Harness.fail "no receiver");
  Harness.test "a type with the wrong number of arguments is an error" (fun () ->
      expect_one_diagnostic "fn f(value: Option[Int64, Int64]) {}\n" "types.arity");
  Harness.test "a parameter whose bound is an error is an error, not an unbounded parameter"
    (fun () ->
      expect_one_diagnostic
        "fn sum[Item: Add](left: Item, right: Item) -> Item.Output {\n  todo\n}\n" "types.arity");
  Harness.test "a trait in a type position is an error" (fun () ->
      expect_one_diagnostic "fn f(value: Equal) {}\n" "types.not_a_type");
  Harness.test "a type argument must meet the type's bounds" (fun () ->
      expect_one_diagnostic Fixtures.Interface.sorted_of_an_unordered_point
        "types.unsatisfied_bound");
  Harness.test "a generic parameter's bound meets a bound the type needs" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Interface.sorted_of_an_ordered_item) ]);
  Harness.test "a public signature cannot mention a private type" (fun () ->
      expect_one_diagnostic Fixtures.Interface.public_function_taking_a_private_type
        "types.private_in_public");
  Harness.test "a method must be in its type's package" (fun () ->
      expect_one_diagnostic "fn Int64.double(self) -> Int64 { todo }\n"
        "types.method_outside_package");
  Harness.test "main must have its fixed signature" (fun () ->
      expect_one_diagnostic ~file:"app" "fn main() -> ExitCode { todo }\n" "types.main_signature");
  Harness.test "main with its fixed signature is accepted" (fun () ->
      expect_no_diagnostics [ ("app", Fixtures.Interface.main_with_arguments_and_exit_code) ]);
  Harness.test "a main outside the root module may have any signature" (fun () ->
      expect_no_diagnostics [ ("app::menu", "fn main() -> ExitCode { todo }\n") ]);
  Harness.test "a default may build a record from constants" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Interface.record_default_argument) ]);
  Harness.test "an associated type no bound declares is an error" (fun () ->
      expect_one_diagnostic "fn f[Items: Iterable](items: Items) -> Items.Key { todo }\n"
        "types.unknown_associated_type");
  Harness.test "an associated type of a bound is a projection" (fun () ->
      let packages =
        Support.setup
          [
            ( "app::main",
              "fn first[Items: Iterable](items: Items) -> Option[Items.Element] { todo }\n" );
          ]
      in
      match
        Interface.Definition.find_declared_signature (make_interface packages) (app "first")
      with
      | Some { output = Returns output; _ } ->
          if Types.show output <> "Option[Items.Element]" then
            Harness.fail "output %s" (Types.show output)
      | _ -> Harness.fail "no signature")

let () =
  Harness.test "two fields with one name are an error" (fun () ->
      expect_one_diagnostic "type Point(x: Int64, x: Int64)\n" "types.duplicate_field");
  Harness.test "deriving needs every field to implement the trait" (fun () ->
      expect_one_diagnostic Fixtures.Interface.equal_derived_over_an_opaque_field
        "types.cannot_derive");
  Harness.test "only a record derives Default" (fun () ->
      expect_one_diagnostic Fixtures.Interface.variant_type_deriving_default "types.cannot_derive";
      expect_no_diagnostics [ ("app::main", "type Point(x: Int64, y: Int64)\n  derives Default\n") ]);
  Harness.test "a field with a default needs no Default of its type to derive Default" (fun () ->
      expect_no_diagnostics
        [
          ( "app::main",
            "type Token(text: String)\n\n\
             type Session(token: Token = Token(text: \"none\"), count: Int64)\n\
            \  derives Default\n" );
        ]);
  Harness.test "deriving Serialize needs every field to implement it" (fun () ->
      expect_one_diagnostic Fixtures.Interface.serialize_derived_over_an_opaque_field
        "types.cannot_derive";
      expect_no_diagnostics
        [ ("app::main", Fixtures.Interface.serialize_derived_over_a_defaulted_list) ]);
  Harness.test "deriving Ordered needs Equal derived too" (fun () ->
      expect_one_diagnostic "type Point(x: Int64)\n  derives Ordered\n" "types.cannot_derive");
  Harness.test "a generic type derives under conditions on its parameters" (fun () ->
      expect_no_diagnostics [ ("app::main", "type Box[Value](value: Value)\n  derives Equal\n") ]);
  Harness.test
    "declaring Copyable on a type that is not opaque is an error with a fix that removes it"
    (fun () ->
      expect_one_diagnostic "type Point(x: Int64)\n  derives Copyable\n" "types.derives_inferred"
        ~fixed:"type Point(x: Int64)\n  \n")

let () =
  Harness.test "an opaque type cannot declare Copyable when a field is not Copyable" (fun () ->
      expect_one_diagnostic
        "public type Session = todo\n\
         public opaque type Login(session: Session)\n\
        \  derives Copyable\n"
        "types.cannot_derive");
  Harness.test "an opaque type cannot declare Plain when a variant is held indirectly" (fun () ->
      expect_one_diagnostic
        "public opaque type Tree =\n\
        \  | Leaf\n\
        \  | indirect Node(left: Tree, right: Tree)\n\
        \  derives Plain\n"
        "types.cannot_derive");
  Harness.test "an opaque type declares Copyable on the condition that its arguments are Copyable"
    (fun () ->
      expect_no_diagnostics
        [ ("app::main", "public opaque type Box[Value](inner: Value)\n  derives Copyable\n") ]);
  Harness.test "an impl must give every method without a body" (fun () ->
      expect_one_diagnostic Fixtures.Interface.empty_equal_impl "types.missing_member");
  Harness.test "an impl may leave out a method with a body" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Interface.equal_impl_giving_only_equal) ]);
  Harness.test "an impl's method must have the trait's signature" (fun () ->
      expect_one_diagnostic Fixtures.Interface.equal_impl_with_a_renamed_parameter
        "types.signature_mismatch");
  Harness.test "an impl cannot give a method its trait does not declare" (fun () ->
      expect_one_diagnostic Fixtures.Interface.equal_impl_with_an_extra_method "types.extra_member");
  Harness.test "an impl must give every associated type" (fun () ->
      expect_one_diagnostic Fixtures.Interface.add_impl_without_output "types.missing_member");
  Harness.test "the traits a trait requires must be implemented" (fun () ->
      expect_one_diagnostic Fixtures.Interface.ordered_impl_without_equal
        "types.missing_required_impl");
  Harness.test "nothing can implement Panic" (fun () ->
      expect_one_diagnostic Fixtures.Interface.panic_impl "types.implements_panic");
  Harness.test "every standard capability except Panic has exactly one real implementation"
    (fun () ->
      let packages = Support.setup [] in
      let interface = make_interface packages in
      let capabilities =
        List.filter
          (fun (declaration : Resolve.Names.declaration) -> declaration.kind = Capability)
          (List.concat_map
             (Support.list_declarations packages)
             (List.sort_uniq compare
                (List.map (fun ((file : Path.file), _) -> file.module_) Standard_library.files)))
      in
      let has_real_implementation (capability : Resolve.Names.declaration) =
        Option.is_some (Interface.Definition.find_real_implementation interface capability.path)
      in
      match
        List.partition
          (fun (capability : Resolve.Names.declaration) -> Well_known.is Panic capability.path)
          capabilities
      with
      | [ panic ], others ->
          if has_real_implementation panic then Harness.fail "Panic has a real implementation";
          List.iter
            (fun (capability : Resolve.Names.declaration) ->
              if not (has_real_implementation capability) then
                Harness.fail "%s has no real implementation" (Path.show capability.path))
            others
      | _ -> Harness.fail "the standard library does not declare Panic exactly once");
  Harness.test "a test cannot declare Panic, with a fix that removes its uses" (fun () ->
      expect_one_diagnostic "test \"t\" uses Panic {\n  assert 1 + 1 == 2\n}\n"
        "types.no_real_implementation" ~fixed:"test \"t\" {\n  assert 1 + 1 == 2\n}\n");
  Harness.test "the fix removes Panic and one comma beside it from a test's uses" (fun () ->
      List.iter
        (fun (written, fixed) ->
          expect_one_diagnostic
            (Printf.sprintf "test \"t\" uses %s {}\n" written)
            "types.no_real_implementation"
            ~fixed:(Printf.sprintf "test \"t\" uses %s {}\n" fixed))
        [
          ("Clock, Panic", "Clock");
          ("Panic, Clock", "Clock");
          ("Clock, Panic, Random", "Clock, Random");
        ]);
  Harness.test "a test cannot declare a capability that has no real implementation" (fun () ->
      expect_one_diagnostic "capability Greeter {\n  fn greet()\n}\n\ntest \"t\" uses Greeter {}\n"
        "types.no_real_implementation"
        ~says:"`Greeter` has no real implementation, so the runtime cannot provide it to a test.");
  Harness.test "main cannot declare a capability that has no real implementation" (fun () ->
      expect_one_diagnostic ~file:"app" Fixtures.Interface.main_using_a_greeter
        "types.no_real_implementation"
        ~says:"`Greeter` has no real implementation, so the runtime cannot provide it to `main`.");
  Harness.test "main can declare Panic and the standard capabilities" (fun () ->
      expect_no_diagnostics
        [
          ( "app",
            "fn main(arguments: List[String]) -> ExitCode\n\
            \  uses Panic, Console, Clock\n\
             {\n\
            \  todo\n\
             }\n" );
        ]);
  Harness.test "a trait's impl cannot have uses" (fun () ->
      expect_one_diagnostic Fixtures.Interface.equal_impl_with_uses "types.impl_uses");
  Harness.test "a capability's impl takes a receiver and may have uses" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Interface.clock_impl_using_random) ]);
  Harness.test "a capability's impl method may repeat its impl's uses" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Interface.clock_impl_method_repeating_uses) ]);
  Harness.test "an impl's method may declare its trait's set or the capabilities in it" (fun () ->
      expect_no_diagnostics
        [ ("app::main", Fixtures.Interface.countdown_cursor_naming_its_set_of_panic) ];
      expect_no_diagnostics
        [ ("app::main", Fixtures.Interface.countdown_cursor_declaring_the_panic_its_set_holds) ]);
  Harness.test "an impl's method cannot declare a capability outside its trait's set" (fun () ->
      expect_one_diagnostic Fixtures.Interface.countdown_cursor_declaring_a_clock_its_set_lacks
        "types.impl_uses");
  Harness.test "a method of a capability's impl cannot declare `uses`" (fun () ->
      expect_one_diagnostic Fixtures.Interface.clock_impl_method_declaring_uses "types.impl_uses");
  Harness.test "an impl's method can rename its generic parameters" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Interface.impl_renaming_method_generics) ]);
  Harness.test "traits cannot require each other in a cycle" (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Interface.traits_requiring_each_other) ]
      in
      match Support.list_codes (check packages (Support.parse_file "app::main")) with
      | [ "types.trait_cycle"; "types.trait_cycle" ] -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " reported));
  Harness.test "a trait hierarchy of many diamonds is checked quickly" (fun () ->
      let levels = 24 in
      let make_level_source index =
        let body = if index = 0 then "{\n  fn size(self) -> UInt64\n}" else "{}" in
        Printf.sprintf "trait T%d: A%d + B%d %s\n\ntrait A%d: T%d {}\n\ntrait B%d: T%d {}\n\n" index
          index index body index (index + 1) index (index + 1)
      in
      let text =
        String.concat ""
          (List.init levels make_level_source
          @ [
              Printf.sprintf "trait T%d {}\n\n" levels;
              "fn measure[Value: T0](value: Value) -> UInt64 {\n  value.size()\n}\n\n";
              "fn measure_any(value: any T0) -> UInt64 {\n  value.size()\n}\n";
            ])
      in
      let started = Sys.time () in
      expect_no_diagnostics [ ("app::main", text) ];
      if Sys.time () -. started > 5.0 then Harness.fail "took %.1f seconds" (Sys.time () -. started));
  Harness.test "a bound keeps a trait that it requires twice with different arguments" (fun () ->
      expect_no_diagnostics
        [
          ( "app::main",
            "trait Convert[Target] {\n\
            \  fn convert(self) -> Target\n\
             }\n\n\
             trait ToCount: Convert[Int64] {}\n\n\
             trait ToText: Convert[String] {}\n\n\
             trait Both: ToCount + ToText {}\n\n\
             fn needs_text[Value: Convert[String]](value: Value) {}\n\n\
             fn passes[Value: Both](value: Value) {\n\
            \  needs_text(value)\n\
             }\n" );
        ]);
  Harness.test "a trait cannot redeclare a method of a trait it requires" (fun () ->
      expect_one_diagnostic Fixtures.Interface.subtrait_redeclaring_compare
        "types.redeclared_method");
  Harness.test "a trait may add an overload of a method of a trait it requires" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Interface.subtrait_overloading_element) ])

let () =
  let expect_signature_mismatch text ~declared =
    expect_one_diagnostic text "types.signature_mismatch" ~says:declared
  in
  Harness.test "an impl's callback type cannot add a time clause to its trait's" (fun () ->
      expect_signature_mismatch Fixtures.Interface.walk_impl_adding_a_time_clause_to_its_callback
        ~declared:
          "`each` must have the signature `each(self, visit: fn(Int64))` that `Walk` declares.");
  Harness.test "an impl's callback type cannot drop its trait's time clause" (fun () ->
      expect_signature_mismatch
        Fixtures.Interface.walk_impl_dropping_the_time_clause_of_its_callback
        ~declared:"`each(self, visit: (fn(Int64) cost time finite))`");
  Harness.test "an impl's callback type cannot bound the time that its trait's leaves finite"
    (fun () ->
      expect_signature_mismatch Fixtures.Interface.walk_impl_bounding_the_time_of_its_callback
        ~declared:"`each(self, visit: (fn(Int64) cost time finite))`");
  Harness.test "an impl's callback type cannot drop `amortized` from its trait's cost" (fun () ->
      expect_signature_mismatch
        Fixtures.Interface.walk_impl_dropping_amortized_from_the_cost_of_its_callback
        ~declared:"`each(self, visit: (fn(Int64) cost amortized time O(...)))`");
  Harness.test "an impl's callback type cannot use fewer capabilities than its trait's" (fun () ->
      expect_signature_mismatch Fixtures.Interface.walk_impl_dropping_a_capability_of_its_callback
        ~declared:"`each(self, visit: (fn(Int64) uses Log))`");
  Harness.test "an impl's callback type cannot use more capabilities than its trait's" (fun () ->
      expect_signature_mismatch Fixtures.Interface.walk_impl_adding_a_capability_to_its_callback
        ~declared:"`each(self, visit: (fn(Int64) uses Log))`");
  Harness.test "an impl's callback type cannot add a time clause beside a capability parameter"
    (fun () ->
      expect_signature_mismatch
        Fixtures.Interface.walk_impl_adding_a_time_clause_to_its_polymorphic_callback
        ~declared:"`each(self, visit: (fn(Int64) uses Granted))`");
  Harness.test "an impl may repeat its trait's polymorphic callback type and rename its parameter"
    (fun () ->
      expect_no_diagnostics
        [ ("app::main", Fixtures.Interface.walk_impls_repeating_a_polymorphic_callback) ]);
  Harness.test "an impl's callback type may name its trait's capability set or list the set"
    (fun () ->
      expect_no_diagnostics
        [ ("app::main", Fixtures.Interface.walk_impls_naming_their_capability_set_in_a_callback) ]);
  Harness.test "an impl may name the capability set of a parameter that a subtrait bounds"
    (fun () ->
      expect_no_diagnostics
        [
          ("app::main", Fixtures.Interface.walk_impl_naming_the_capability_set_of_a_subtrait_bound);
        ]);
  Harness.test "an impl's callback type cannot list a capability outside its trait's set" (fun () ->
      expect_signature_mismatch
        Fixtures.Interface.walk_impl_listing_a_capability_outside_its_set_in_a_callback
        ~declared:"`each(self, visit: (fn(Int64) uses Log))`");
  Harness.test "an unknown capability in an impl's callback type is reported once" (fun () ->
      expect_one_diagnostic
        Fixtures.Interface.walk_impl_naming_an_unknown_capability_in_its_callback
        "resolve.unknown_name");
  Harness.test "a capability's implementation cannot add a time clause to a callback type"
    (fun () ->
      expect_signature_mismatch Fixtures.Interface.runner_impl_adding_a_time_clause_to_its_callback
        ~declared:
          "`run` must have the signature `run(self, work: fn(Int64))` that `Runner` declares.");
  Harness.test "an impl that overrides a provided method cannot add a time clause to its callback"
    (fun () ->
      expect_signature_mismatch
        Fixtures.Interface.walk_impl_overriding_each_with_a_time_clause_on_its_callback
        ~declared:"`each(self, visit: fn(Int64))`");
  Harness.test "an impl's result type cannot drop the time clause of its trait's function type"
    (fun () ->
      expect_signature_mismatch
        Fixtures.Interface.chooses_impl_dropping_the_time_clause_of_its_result
        ~declared:"`choose(self) -> (fn(Int64) -> Int64 cost time finite)`")

let expect_property name expected text make_type check =
  Harness.test name (fun () ->
      let packages = Support.setup [ ("app::main", text) ] in
      let actual =
        check (make_interface packages) ~list_bounds:(fun _ -> []) (make_type packages)
      in
      if actual <> expected then Harness.fail "expected %b" expected)

let option type_ = Types.make_named (make_standard_path [ "option" ] "Option") [ type_ ]
let list type_ = Types.make_named (make_standard_path [ "list" ] "List") [ type_ ]
let slice type_ = Types.make_named (make_standard_path [ "list" ] "Slice") [ type_ ]
let string = Types.make_named (make_standard_path [ "text" ] "String") []

let () =
  expect_property "an integer is Plain" true "" (fun _ -> int64) Interface.Impls.is_plain;
  expect_property "an Option of plain data is Plain" true ""
    (fun _ -> option int64)
    Interface.Impls.is_plain;
  expect_property "a List is Copyable" true "" (fun _ -> list int64) Interface.Impls.is_copyable;
  expect_property "a handle is not Copyable" false ""
    (fun _ -> Types.make_named (Intrinsic.make_builtin_path Handle) [])
    Interface.Impls.is_copyable;
  expect_property "a handle is not Plain" false ""
    (fun _ -> Types.make_named (Intrinsic.make_builtin_path Handle) [])
    Interface.Impls.is_plain;
  expect_property "an Option of a handle is not Copyable" false ""
    (fun _ -> option (Types.make_named (Intrinsic.make_builtin_path Handle) []))
    Interface.Impls.is_copyable;
  expect_property "an Option of a handle is not Plain" false ""
    (fun _ -> option (Types.make_named (Intrinsic.make_builtin_path Handle) []))
    Interface.Impls.is_plain;
  expect_property "a List is not Plain" false "" (fun _ -> list int64) Interface.Impls.is_plain;
  expect_property "an Option of a Slice is a view" true ""
    (fun _ -> option (slice int64))
    Interface.Impls.is_view;
  expect_property "a List of integers is not a view" false ""
    (fun _ -> list int64)
    Interface.Impls.is_view;
  expect_property "a record of plain fields is Plain" true "type Point(x: Int64, y: Int64)\n"
    (fun _ -> Types.make_named (app "Point") [])
    Interface.Impls.is_plain;
  expect_property "a variant held indirectly is not Plain" false
    Fixtures.Interface.tree_of_leaves_and_nodes
    (fun _ -> Types.make_named (app "Tree") [])
    Interface.Impls.is_plain;
  expect_property "a recursive type is still Copyable" true
    Fixtures.Interface.tree_of_leaves_and_nodes
    (fun _ -> Types.make_named (app "Tree") [])
    Interface.Impls.is_copyable;
  expect_property "an opaque type is not Copyable unless it says so" false
    "public opaque type Token(code: Int64)\n"
    (fun _ -> Types.make_named (app "Token") [])
    Interface.Impls.is_copyable;
  expect_property "an opaque type that derives Plain is Plain" true
    "public opaque type Token(code: Int64)\n  derives Plain\n"
    (fun _ -> Types.make_named (app "Token") [])
    Interface.Impls.is_plain;
  expect_property "a generic opaque type is Plain when the fields that hold its argument are" false
    "public opaque type Box[Value](inner: Value)\n  derives Plain\n"
    (fun _ -> Types.make_named (app "Box") [ string ])
    Interface.Impls.is_plain;
  expect_property "an opaque type is Plain whatever an argument that no field holds is" true
    "public opaque type Id[Entity](value: UInt64)\n  derives Plain\n"
    (fun _ -> Types.make_named (app "Id") [ string ])
    Interface.Impls.is_plain;
  expect_property "a Slice is Plain whatever its elements are" true ""
    (fun _ -> slice string)
    Interface.Impls.is_plain;
  expect_property "a type defined as todo is not Copyable" false "type Session = todo\n"
    (fun _ -> Types.make_named (app "Session") [])
    Interface.Impls.is_copyable

let show_decision : Interface.Properties.decision -> string = function
  | Holds -> "Holds"
  | Fails -> "Fails"
  | Depends_on open_type -> "Depends_on " ^ Types.show open_type

let expect_decision name expected type_ property =
  Harness.test name (fun () ->
      let actual =
        Interface.Impls.decide_property property
          (make_interface (Support.setup [ ("app::main", "") ]))
          ~list_bounds:(fun _ -> [])
          type_
      in
      if actual <> expected then
        Harness.fail "expected %s, got %s" (show_decision expected) (show_decision actual))

let () =
  expect_decision "whether an Option of an open type is Plain depends on that type"
    (Depends_on Types.Hole) (option Types.Hole) Plain;
  expect_decision "whether an open type is a view depends on that type" (Depends_on Types.Hole)
    Types.Hole View;
  expect_decision "a List of an open type is not Plain" Fails (list Types.Hole) Plain;
  expect_decision "a Slice of an open type is Plain" Holds (slice Types.Hole) Plain;
  expect_decision "an Option of a Slice of an open type is a view" Holds
    (option (slice Types.Hole))
    View;
  Harness.test "is_plain of a type whose decision depends on an open type is a compiler bug"
    (fun () ->
      match
        Interface.Impls.is_plain
          (make_interface (Support.setup [ ("app::main", "") ]))
          ~list_bounds:(fun _ -> [])
          (option Types.Hole)
      with
      | exception Compiler_bug.Bug _ -> ()
      | holds -> Harness.fail "answered %b" holds)

let holder = "type Holder[Value](value: Value)\n"
let held type_ = Types.make_named (app "Holder") [ type_ ]
let chain = Fixtures.Interface.chain
let projection_holder = Fixtures.Interface.projection_holder

let () =
  expect_property "an Option of an Option of a List is not Plain" false ""
    (fun _ -> option (option (list int64)))
    Interface.Impls.is_plain;
  expect_property "an Option of an Option of plain data is Plain" true ""
    (fun _ -> option (option int64))
    Interface.Impls.is_plain;
  expect_property "a type nested in itself around a Slice is a view" true holder
    (fun _ -> held (held (slice int64)))
    Interface.Impls.is_view;
  expect_property "a type nested in itself around a List is not a view" false holder
    (fun _ -> held (held (list int64)))
    Interface.Impls.is_view;
  expect_property "a type nested in itself around a List is not Plain" false holder
    (fun _ -> held (held (list int64)))
    Interface.Impls.is_plain;
  expect_property "a type that contains itself is a view when its argument is" true chain
    (fun _ -> Types.make_named (app "Chain") [ slice int64 ])
    Interface.Impls.is_view;
  expect_property "a type that contains itself is not a view when its argument is not" false chain
    (fun _ -> Types.make_named (app "Chain") [ int64 ])
    Interface.Impls.is_view;
  expect_property "a type that contains itself around a Slice is a view" true
    Fixtures.Interface.nest_of_growing_slices
    (fun _ -> Types.make_named (app "Nest") [ int64 ])
    Interface.Impls.is_view;
  expect_property "types that hold each other are Copyable when nothing in them says otherwise" true
    Fixtures.Interface.even_and_odd_of_copyable_fields
    (fun _ -> Types.make_named (app "Even") [])
    Interface.Impls.is_copyable;
  expect_property "types that hold each other are not Copyable when one holds a type that is not"
    false Fixtures.Interface.even_and_odd_holding_an_opaque_token
    (fun _ -> Types.make_named (app "Even") [])
    Interface.Impls.is_copyable;
  expect_property "a type that holds an associated type is a view when that type is one" true
    projection_holder
    (fun _ -> Types.make_named (app "Kept") [ Types.make_named (app "Numbers") [] ])
    Interface.Impls.is_view;
  expect_property "a type that holds an associated type is not a view when that type is not" false
    projection_holder
    (fun _ -> Types.make_named (app "Kept") [ Types.make_named (app "Counted") [] ])
    Interface.Impls.is_view;
  expect_property "a type that holds an associated type is Plain when that type is" true
    projection_holder
    (fun _ -> Types.make_named (app "Kept") [ Types.make_named (app "Counted") [] ])
    Interface.Impls.is_plain;
  expect_property
    "a type that holds a type holding an associated type is a view when that type is one" true
    (projection_holder ^ "\ntype Outer(held: Kept[Numbers])\n")
    (fun _ -> Types.make_named (app "Outer") [])
    Interface.Impls.is_view;
  let through_itself = projection_holder ^ Fixtures.Interface.tree_through_an_associated_type in
  expect_property "a type that contains itself through an associated type is Copyable" true
    through_itself
    (fun _ -> Types.make_named (app "Tree") [])
    Interface.Impls.is_copyable;
  expect_property "a type that contains itself through an associated type is not a view" false
    through_itself
    (fun _ -> Types.make_named (app "Tree") [])
    Interface.Impls.is_view

let trait name arguments : Types.trait_reference =
  {
    trait = make_standard_path [ "core" ] name;
    trait_arguments = List.map (fun type_ -> Types.Type type_) arguments;
    associated = [];
  }

let () =
  Harness.test "Int64 implements Add[Int64] with Output Int64" (fun () ->
      let packages = Support.setup [] in
      match
        Interface.Impls.project_associated_type (make_interface packages)
          ~list_bounds:(fun _ -> [])
          int64 (trait "Add" [ int64 ]) "Output"
      with
      | Some output when Types.equal output int64 -> ()
      | Some output -> Harness.fail "output %s" (Types.show output)
      | None -> Harness.fail "no impl");
  Harness.test "Int64 does not implement Add[Int32]" (fun () ->
      let packages = Support.setup [] in
      if
        Option.is_some
          (Interface.Impls.find_evidence (make_interface packages)
             ~list_bounds:(fun _ -> [])
             int64
             (trait "Add" [ Types.make_builtin Int32 ]))
      then Harness.fail "found an impl");
  Harness.test "a derived impl holds when its conditions do" (fun () ->
      let packages = Support.setup [] in
      if
        Option.is_none
          (Interface.Impls.find_evidence (make_interface packages)
             ~list_bounds:(fun _ -> [])
             (option int64) (trait "Equal" []))
      then Harness.fail "no impl");
  Harness.test "a derived impl does not hold when its conditions do not" (fun () ->
      let packages = Support.setup [ ("app::main", "type Opaque(x: Int64)\n") ] in
      let opaque = Types.make_named (app "Opaque") [] in
      if
        Option.is_some
          (Interface.Impls.find_evidence (make_interface packages)
             ~list_bounds:(fun _ -> [])
             (option opaque) (trait "Equal" []))
      then Harness.fail "found an impl");
  Harness.test "an impl of a conversion is found by the argument's type" (fun () ->
      let packages = Support.setup [] in
      if
        Option.is_none
          (Interface.Impls.find_evidence (make_interface packages)
             ~list_bounds:(fun _ -> [])
             int64
             (trait "From" [ Types.make_builtin Int32 ]))
      then Harness.fail "no impl")

let () =
  let text = Fixtures.Interface.described in
  let read_impl packages type_ wanted : Path.t =
    match
      Interface.Impls.find_evidence (make_interface packages)
        ~list_bounds:(fun _ -> [])
        type_ wanted
    with
    | Some (From_impl { impl; _ }) -> impl
    | _ -> failwith "no impl"
  in
  let read_method_signature packages type_ wanted name : Types.signature =
    let owner = read_impl packages type_ wanted in
    match
      Interface.Impls.read_signature (make_interface packages)
        (Method { owner; name; receiver = Read })
    with
    | Some signature -> signature
    | None -> failwith "no signature"
  in
  let show_generics (signature : Types.signature) =
    String.concat ", "
      (List.map (fun (generic : Types.generic) -> generic.generic.name) signature.generics)
  in
  let both = Types.make_named (app "Both") [ Types.make_named (app "One") [] ] in
  let described : Types.trait_reference =
    { trait = app "Described"; trait_arguments = []; associated = [] }
  in
  Harness.test "a method written inside an impl is generic over the impl's parameters" (fun () ->
      let packages = Support.setup [ ("app::main", text) ] in
      let signature = read_method_signature packages both described "describe" in
      if show_generics signature <> "Value" then
        Harness.fail "generics: %s" (show_generics signature));
  Harness.test "a method an impl leaves to its trait has the trait's signature there" (fun () ->
      let packages = Support.setup [ ("app::main", text) ] in
      let signature = read_method_signature packages both described "beside" in
      if show_generics signature <> "Value, Other" then
        Harness.fail "generics: %s" (show_generics signature);
      match signature.output with
      | Returns output when Types.show output = "Both[Value]" -> ()
      | Returns output -> Harness.fail "output %s" (Types.show output)
      | _ -> Harness.fail "no result");
  Harness.test "a derived impl's method has a signature" (fun () ->
      let packages = Support.setup [] in
      let signature = read_method_signature packages (option int64) (trait "Equal" []) "equal" in
      match (signature.generics, signature.receiver, signature.parameters) with
      | [ _ ], Some (Read, self), [ other ] when Types.equal self other.type_ -> ()
      | _ -> Harness.fail "generics: %s" (show_generics signature));
  Harness.test "a method of a capability's impl uses the impl's capabilities" (fun () ->
      let packages = Support.setup [ ("app::main", text) ] in
      let clock : Types.trait_reference =
        {
          trait = make_standard_path [ "capabilities" ] "Clock";
          trait_arguments = [];
          associated = [];
        }
      in
      let signature =
        read_method_signature packages (Types.make_named (app "FixedClock") []) clock "now"
      in
      match (Types.remove_divergence signature.uses :> Types.capability list) with
      | [ Capability _ ] -> ()
      | uses -> Harness.fail "%d uses" (List.length uses))

let () =
  let monoid = Fixtures.Interface.monoid in
  Harness.test "a law's proof names a law of its trait and a type that implements the trait"
    (fun () ->
      expect_no_diagnostics [ ("app::main", monoid ^ "proof Joined.associative for Meters {\n}\n") ];
      expect_one_diagnostic
        (monoid ^ "proof Joined.commutative for Meters {\n}\n")
        "types.unknown_member";
      expect_one_diagnostic (monoid ^ "proof Joined.associative for Feet {\n}\n") "types.no_impl");
  let boxed = monoid ^ Fixtures.Interface.boxed in
  Harness.test
    "a law's proof for a generic impl names the impl's type with its own generic parameters"
    (fun () ->
      expect_no_diagnostics
        [ ("app::main", boxed ^ "proof Joined.associative for Box[Element: Joined] {\n}\n") ]);
  Harness.test "a law's proof gives a generic parameter the bounds that the impl requires"
    (fun () ->
      expect_one_diagnostic
        (boxed ^ "proof Joined.associative for Box[Item] {\n}\n")
        "types.no_impl");
  Harness.test "a law's proof cannot assume a bound that the impl does not require" (fun () ->
      expect_one_diagnostic
        (boxed ^ "proof Joined.associative for Box[Item: Joined + Equal] {\n}\n")
        "types.unsatisfied_bound");
  Harness.test "a law's proof names every generic parameter of its type" (fun () ->
      expect_one_diagnostic (boxed ^ "proof Joined.associative for Box {\n}\n") "types.arity")

let () =
  Harness.test "a type that contains itself with growing arguments does not hang" (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Interface.nested_type_with_growing_arguments) ]
      in
      ignore
        (Interface.Impls.is_copyable (make_interface packages)
           ~list_bounds:(fun _ -> [])
           (Types.make_named (app "Nested") [ int64 ])));
  Harness.test "an impl's method may have the trait method's own generic parameters" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Interface.impl_method_with_its_own_generic) ]);
  Harness.test "associated types inside function types are substituted in an impl" (fun () ->
      expect_no_diagnostics
        [ ("app::main", Fixtures.Interface.impl_visiting_with_an_associated_element) ]);
  Harness.test "an associated type of a required trait is checked in an impl" (fun () ->
      expect_one_diagnostic Fixtures.Interface.impl_of_a_subtrait_naming_a_base_key
        "types.signature_mismatch");
  Harness.test "an impl's associated type must meet the trait's bound on it" (fun () ->
      expect_one_diagnostic Fixtures.Interface.keyed_impl_with_an_unhashable_key
        "types.unsatisfied_bound");
  Harness.test "an associated type's declared bound holds where it is used" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Interface.keyed_trait_with_a_bounded_key) ]);
  Harness.test "Self in a required trait is substituted by the bounded type" (fun () ->
      expect_no_diagnostics [ ("app::main", Fixtures.Interface.trait_requiring_add_of_self) ]);
  Harness.test "a trait whose header did not parse satisfies every bound that names it" (fun () ->
      let packages = Support.setup [ ("app::main", Fixtures.Interface.bound_on_a_broken_trait) ] in
      match
        Database.For_testing.list_diagnostics [ Interface ] (Support.make_database packages)
          (Support.parse_file "app::main")
      with
      | [] -> ()
      | reported -> Harness.fail "found [%s]" (String.concat "; " (Support.list_codes reported)));
  Harness.test "an opaque generic type is Copyable by its declaration and its arguments" (fun () ->
      let packages =
        Support.setup
          [ ("app::main", "public opaque type Box[Value](inner: Value)\n  derives Copyable\n") ]
      in
      if
        not
          (Interface.Impls.is_copyable (make_interface packages)
             ~list_bounds:(fun _ -> [])
             (Types.make_named (app "Box") [ int64 ]))
      then Harness.fail "not Copyable");
  Harness.test "only some traits can be derived" (fun () ->
      expect_one_diagnostic "type P()\n  derives Iterable\n" "types.not_derivable");
  Harness.test "a capability's impl must give every method" (fun () ->
      expect_one_diagnostic Fixtures.Interface.journal_impl_missing_a_method "types.missing_member");
  Harness.test "a capability's impl takes self or mut self" (fun () ->
      expect_one_diagnostic Fixtures.Interface.clock_impl_taking_own_self "types.wrong_receiver");
  Harness.test "a method's head names every generic parameter of its type" (fun () ->
      expect_one_diagnostic Fixtures.Interface.method_head_without_generics "types.arity");
  Harness.test "a type argument must be of its parameter's kind" (fun () ->
      expect_one_diagnostic "fn f(items: List[3]) {}\n" "types.argument_kind");
  Harness.test "a constant in a type argument must have a value" (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Interface.array_length_from_circular_constants) ]
      in
      if
        not
          (List.mem "types.arity"
             (Support.list_codes
                (Database.For_testing.list_diagnostics [ Interface ]
                   (Support.make_database packages) (Support.parse_file "app::main"))))
      then Harness.fail "accepted");
  Harness.test "any must fix every associated type" (fun () ->
      expect_one_diagnostic "fn f(items: any Iterable) {}\n" "types.associated_type_not_fixed");
  Harness.test "nothing can implement Copyable" (fun () ->
      expect_one_diagnostic Fixtures.Interface.copyable_impl "types.implements_built_in");
  Harness.test "a public constant cannot have a private type" (fun () ->
      expect_one_diagnostic Fixtures.Interface.public_constant_of_a_private_type
        "types.private_in_public");
  Harness.test "uses names a capability parameter, not a type parameter" (fun () ->
      expect_one_diagnostic Fixtures.Interface.uses_naming_a_type_parameter "types.not_a_capability");
  Harness.test "Never implements no trait" (fun () ->
      let packages = Support.setup [] in
      if
        Option.is_some
          (Interface.Impls.find_evidence (make_interface packages)
             ~list_bounds:(fun _ -> [])
             Types.Never (trait "Hash" []))
      then Harness.fail "it does");
  Harness.test "an any value implements its trait only with the same arguments" (fun () ->
      let packages = Support.setup [] in
      let any = Types.Any (trait "From" [ int64 ]) in
      if
        Option.is_some
          (Interface.Impls.find_evidence (make_interface packages)
             ~list_bounds:(fun _ -> [])
             any
             (trait "From" [ Types.make_builtin Int32 ]))
      then Harness.fail "it does")

let () =
  Harness.test "`Self.Item` outside a trait and an impl of one is an error" (fun () ->
      expect_one_diagnostic Fixtures.Interface.method_returning_self_item
        "types.unknown_associated_type");
  Harness.test "a generic parameter is not a bound" (fun () ->
      expect_one_diagnostic Fixtures.Interface.generic_bounded_by_another_generic
        "types.not_a_trait");
  Harness.test "`Self` in a capability is an error" (fun () ->
      expect_one_diagnostic Fixtures.Interface.capability_method_taking_self_type
        "types.misplaced_self_type");
  Harness.test "`Self` in a function that is not a method is an error" (fun () ->
      expect_one_diagnostic "fn f(value: Self) {}\n" "types.misplaced_self_type");
  Harness.test "a trait is not the head of a method" (fun () ->
      expect_one_diagnostic Fixtures.Interface.method_headed_by_a_trait "types.not_a_type");
  Harness.test "a capability parameter is not a type" (fun () ->
      expect_one_diagnostic "fn f[capability Granted](value: Granted) {}\n" "types.not_a_type");
  Harness.test "a method of an unknown type keeps its head's generic parameters" (fun () ->
      expect_one_diagnostic Fixtures.Interface.method_of_an_unknown_generic_type
        "resolve.unknown_name")

let () =
  Harness.test "every definition the compiler names is in the standard library" (fun () ->
      let packages = Support.setup [] in
      let declared =
        List.map
          (fun (declaration : Resolve.Names.declaration) -> declaration.path)
          ((Support.make_names packages Path.standard_package).list_package_declarations
             Path.standard_package)
      in
      List.iter
        (fun known ->
          let path = Well_known.make_path known in
          if not (List.exists (Path.equal path) declared) then
            Harness.fail "the standard library has no `%s`" (Path.show path))
        Well_known.For_testing.all);
  Harness.test "a well-known definition is found by its path" (fun () ->
      List.iter
        (fun known ->
          if Well_known.of_path (Well_known.make_path known) <> Some known then
            Harness.fail "`%s` is not found by its path" (Path.show (Well_known.make_path known)))
        Well_known.For_testing.all)
