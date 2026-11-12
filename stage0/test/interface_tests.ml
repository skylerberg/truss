(* The tests of checking interfaces: signatures, types, traits, [impl]s, the
   properties of types, and finding [impl]s. Each gives a few definitions
   and states one fact. *)

open Harness
open Support

(* Everything the checker reports so far: resolution and interfaces. *)
let check = Type_checker.through Interface
let one_diagnostic = one_diagnostic ~check
let no_diagnostics = no_diagnostics ~check
let app name : Path.t = Top { module_ = module_of "app::main"; name }
let standard = Path.standard
let int64 = Types.builtin Int64

(* The standard library *)

let () =
  let database = setup [] in
  List.iter
    (fun ((module_ : Path.module_), _) ->
      test
        (Printf.sprintf "%s has no interface errors" (Path.show_module module_))
        (fun () ->
          let file = Query.demand database Workspace.file module_ in
          List.iter
            (fun diagnostic -> fail "%s" (Diagnostic.render file.source diagnostic))
            (Interface.diagnostics database module_)))
    Standard_library.modules

(* Signatures *)

let () =
  test "a function's signature is lowered" (fun () ->
      let database =
        setup
          [
            ("app::main", "fn count(items: List[Int64], limit: own Int64 = 3) -> USize { todo }\n");
          ]
      in
      match Query.demand database Interface.Environment.signature (app "count") with
      | Some { parameters = [ items; limit ]; output = Returns output; _ } ->
          if Types.show items.type_ <> "List[Int64]" then fail "items: %s" (Types.show items.type_);
          if limit.mode <> Own || not limit.has_default then fail "limit";
          if not (Types.is_builtin USize output) then fail "output %s" (Types.show output)
      | _ -> fail "no signature");
  test "a method's receiver has its type's generic parameters" (fun () ->
      let database =
        setup
          [ ("app::main", Fixtures.Interface.methods_receiver_has_its_types_generic_parameters) ]
      in
      let path : Path.t = Method { owner = app "Box"; name = "get"; receiver = Read } in
      match Query.demand database Interface.Environment.signature path with
      | Some { receiver = Some (Read, self); _ } ->
          if Types.show self <> "Box[Value]" then fail "self: %s" (Types.show self)
      | _ -> fail "no receiver");
  test "a type with the wrong number of arguments is an error" (fun () ->
      one_diagnostic "fn f(value: Option[Int64, Int64]) {}\n" "types.arity");
  test "a trait in a type position is an error" (fun () ->
      one_diagnostic "fn f(value: Equal) {}\n" "types.not_a_type");
  test "a type argument must meet the type's bounds" (fun () ->
      one_diagnostic Fixtures.Interface.type_argument_must_meet_the_types_bounds
        "types.unsatisfied_bound");
  test "a generic parameter's bound meets a bound the type needs" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Interface.generic_parameters_bound_meets_a_bound_the_type) ]);
  test "a public signature cannot mention a private type" (fun () ->
      one_diagnostic Fixtures.Interface.public_signature_cannot_mention_a_private_type
        "types.private_in_public");
  test "a method must be in its type's package" (fun () ->
      one_diagnostic "fn Int64.double(self) -> Int64 { todo }\n" "types.method_outside_package");
  test "main must have its fixed signature" (fun () ->
      one_diagnostic "fn main() -> ExitCode { todo }\n" "types.main_signature");
  test "main with its fixed signature is accepted" (fun () ->
      no_diagnostics [ ("app::main", Fixtures.Interface.main_with_its_fixed_signature_is_accepted) ]);
  test "a default may build a record from constants" (fun () ->
      no_diagnostics [ ("app::main", Fixtures.Interface.default_may_build_a_record_from_constants) ]);
  test "an associated type no bound declares is an error" (fun () ->
      one_diagnostic "fn f[Items: Iterable](items: Items) -> Items.Key { todo }\n"
        "types.unknown_associated_type");
  test "an associated type of a bound is a projection" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "fn first[Items: Iterable](items: Items) -> Option[Items.Element] { todo }\n" );
          ]
      in
      match Query.demand database Interface.Environment.signature (app "first") with
      | Some { output = Returns output; _ } ->
          if Types.show output <> "Option[Items.Element]" then fail "output %s" (Types.show output)
      | _ -> fail "no signature")

(* Types *)

let () =
  test "two fields with one name are an error" (fun () ->
      one_diagnostic "type Point(x: Int64, x: Int64)\n" "types.duplicate_field");
  test "deriving needs every field to implement the trait" (fun () ->
      one_diagnostic Fixtures.Interface.deriving_needs_every_field_to_implement_the_trait
        "types.cannot_derive");
  test "only a record derives Default" (fun () ->
      one_diagnostic Fixtures.Interface.only_a_record_derives_default "types.cannot_derive";
      no_diagnostics [ ("app::main", "type Point(x: Int64, y: Int64)\n  derives Default\n") ]);
  test "deriving Serialize needs every field to implement it" (fun () ->
      one_diagnostic Fixtures.Interface.deriving_serialize_needs_every_field_to_implement
        "types.cannot_derive";
      no_diagnostics
        [ ("app::main", Fixtures.Interface.deriving_serialize_needs_every_field_to_implement_2) ]);
  test "deriving Ordered needs Equal derived too" (fun () ->
      one_diagnostic "type Point(x: Int64)\n  derives Ordered\n" "types.cannot_derive");
  test "a generic type derives under conditions on its parameters" (fun () ->
      no_diagnostics [ ("app::main", "type Box[Value](value: Value)\n  derives Equal\n") ]);
  test "declaring Copyable on a type that is not opaque is an error with a fix that removes it"
    (fun () ->
      one_diagnostic "type Point(x: Int64)\n  derives Copyable\n" "types.derives_inferred"
        ~fixed:"type Point(x: Int64)\n  \n")

(* Traits and impls *)

let () =
  test "an impl must give every method without a body" (fun () ->
      one_diagnostic Fixtures.Interface.impl_must_give_every_method_without_a_body
        "types.missing_member");
  test "an impl may leave out a method with a body" (fun () ->
      no_diagnostics [ ("app::main", Fixtures.Interface.impl_may_leave_out_a_method_with_a_body) ]);
  test "an impl's method must have the trait's signature" (fun () ->
      one_diagnostic Fixtures.Interface.impls_method_must_have_the_traits_signature
        "types.signature_mismatch");
  test "an impl cannot give a method its trait does not declare" (fun () ->
      one_diagnostic Fixtures.Interface.impl_cannot_give_a_method_its_trait_does_not
        "types.extra_member");
  test "an impl must give every associated type" (fun () ->
      one_diagnostic Fixtures.Interface.impl_must_give_every_associated_type "types.missing_member");
  test "the traits a trait requires must be implemented" (fun () ->
      one_diagnostic Fixtures.Interface.traits_a_trait_requires_must_be_implemented
        "types.missing_required_impl");
  test "nothing can implement Panic" (fun () ->
      one_diagnostic Fixtures.Interface.nothing_can_implement_panic "types.implements_panic");
  test "a trait's impl cannot have uses" (fun () ->
      one_diagnostic Fixtures.Interface.traits_impl_cannot_have_uses "types.impl_uses");
  test "a capability's impl takes a receiver and may have uses" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Interface.capabilitys_impl_takes_a_receiver_and_may_have) ]);
  test "a capability's impl method may repeat its impl's uses" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Interface.capabilitys_impl_method_may_repeat_its_impls_uses) ]);
  test "a method of a capability's impl cannot declare `uses`" (fun () ->
      one_diagnostic Fixtures.Interface.method_of_a_capabilitys_impl_cannot_declare_uses
        "types.impl_uses");
  test "an impl's method can rename its generic parameters" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Interface.impls_method_can_rename_its_generic_parameters) ]);
  test "traits cannot require each other in a cycle" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Interface.traits_cannot_require_each_other_in_a_cycle) ]
      in
      match codes (check database (module_of "app::main")) with
      | [ "types.trait_cycle"; "types.trait_cycle" ] -> ()
      | reported -> fail "found [%s]" (String.concat "; " reported));
  test "a trait cannot redeclare a method of a trait it requires" (fun () ->
      one_diagnostic Fixtures.Interface.trait_cannot_redeclare_a_method_of_a_trait_it
        "types.redeclared_method");
  test "a trait may add a version of a method of a trait it requires" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Interface.trait_may_add_a_version_of_a_method_of_a_trait_it) ])

(* Properties *)

let property name expected text type_ check =
  test name (fun () ->
      let database = setup [ ("app::main", text) ] in
      let actual = check database ~bounds:(fun _ -> []) (type_ database) in
      if actual <> expected then fail "expected %b" expected)

let option type_ = Types.named (standard [ "option" ] "Option") [ type_ ]
let list type_ = Types.named (standard [ "list" ] "List") [ type_ ]
let slice type_ = Types.named (standard [ "list" ] "Slice") [ type_ ]
let string = Types.named (standard [ "text" ] "String") []

let () =
  property "an integer is Plain" true "" (fun _ -> int64) Interface.Impls.plain;
  property "an Option of plain data is Plain" true "" (fun _ -> option int64) Interface.Impls.plain;
  property "a List is Copyable" true "" (fun _ -> list int64) Interface.Impls.copyable;
  property "a handle is not Copyable" false ""
    (fun _ -> Types.named (Intrinsic.builtin_path Handle) [])
    Interface.Impls.copyable;
  property "a handle is not Plain" false ""
    (fun _ -> Types.named (Intrinsic.builtin_path Handle) [])
    Interface.Impls.plain;
  property "an Option of a handle is not Copyable" false ""
    (fun _ -> option (Types.named (Intrinsic.builtin_path Handle) []))
    Interface.Impls.copyable;
  property "an Option of a handle is not Plain" false ""
    (fun _ -> option (Types.named (Intrinsic.builtin_path Handle) []))
    Interface.Impls.plain;
  property "a List is not Plain" false "" (fun _ -> list int64) Interface.Impls.plain;
  property "an Option of a Slice is a view" true ""
    (fun _ -> option (slice int64))
    Interface.Impls.is_view;
  property "a List of integers is not a view" false "" (fun _ -> list int64) Interface.Impls.is_view;
  property "a record of plain fields is Plain" true "type Point(x: Int64, y: Int64)\n"
    (fun _ -> Types.named (app "Point") [])
    Interface.Impls.plain;
  property "a variant held indirectly is not Plain" false
    Fixtures.Interface.variant_held_indirectly_is_not_plain
    (fun _ -> Types.named (app "Tree") [])
    Interface.Impls.plain;
  property "a recursive type is still Copyable" true
    Fixtures.Interface.recursive_type_is_still_copyable
    (fun _ -> Types.named (app "Tree") [])
    Interface.Impls.copyable;
  property "an opaque type is not Copyable unless it says so" false
    "public opaque type Token(code: Int64)\n"
    (fun _ -> Types.named (app "Token") [])
    Interface.Impls.copyable;
  property "an opaque type that derives Plain is Plain" true
    "public opaque type Token(code: Int64)\n  derives Plain\n"
    (fun _ -> Types.named (app "Token") [])
    Interface.Impls.plain;
  property "a generic opaque type is Plain when the fields that hold its argument are" false
    "public opaque type Box[Value](inner: Value)\n  derives Plain\n"
    (fun _ -> Types.named (app "Box") [ string ])
    Interface.Impls.plain;
  property "an opaque type is Plain whatever an argument that no field holds is" true
    "public opaque type Id[Entity](value: UInt64)\n  derives Plain\n"
    (fun _ -> Types.named (app "Id") [ string ])
    Interface.Impls.plain;
  property "a Slice is Plain whatever its elements are" true ""
    (fun _ -> slice string)
    Interface.Impls.plain;
  property "a type defined as todo is not Copyable" false "type Session = todo\n"
    (fun _ -> Types.named (app "Session") [])
    Interface.Impls.copyable

(* Properties of types that hold types of their own kind *)

let holder = "type Holder[Value](value: Value)\n"
let held type_ = Types.named (app "Holder") [ type_ ]
let chain = Fixtures.Interface.chain
let projection_holder = Fixtures.Interface.projection_holder

let () =
  property "an Option of an Option of a List is not Plain" false ""
    (fun _ -> option (option (list int64)))
    Interface.Impls.plain;
  property "an Option of an Option of plain data is Plain" true ""
    (fun _ -> option (option int64))
    Interface.Impls.plain;
  property "a type nested in itself around a Slice is a view" true holder
    (fun _ -> held (held (slice int64)))
    Interface.Impls.is_view;
  property "a type nested in itself around a List is not a view" false holder
    (fun _ -> held (held (list int64)))
    Interface.Impls.is_view;
  property "a type nested in itself around a List is not Plain" false holder
    (fun _ -> held (held (list int64)))
    Interface.Impls.plain;
  property "a type that contains itself is a view when its argument is" true chain
    (fun _ -> Types.named (app "Chain") [ slice int64 ])
    Interface.Impls.is_view;
  property "a type that contains itself is not a view when its argument is not" false chain
    (fun _ -> Types.named (app "Chain") [ int64 ])
    Interface.Impls.is_view;
  property "a type that contains itself around a Slice is a view" true
    Fixtures.Interface.type_that_contains_itself_around_a_slice_is_a_view
    (fun _ -> Types.named (app "Nest") [ int64 ])
    Interface.Impls.is_view;
  property "types that hold each other are Copyable when nothing in them says otherwise" true
    Fixtures.Interface.types_that_hold_each_other_are_copyable_when
    (fun _ -> Types.named (app "Even") [])
    Interface.Impls.copyable;
  property "types that hold each other are not Copyable when one holds what is not" false
    Fixtures.Interface.types_that_hold_each_other_are_not_copyable_when
    (fun _ -> Types.named (app "Even") [])
    Interface.Impls.copyable;
  property "a type that holds an associated type is a view when that type is one" true
    projection_holder
    (fun _ -> Types.named (app "Kept") [ Types.named (app "Numbers") [] ])
    Interface.Impls.is_view;
  property "a type that holds an associated type is not a view when that type is not" false
    projection_holder
    (fun _ -> Types.named (app "Kept") [ Types.named (app "Counted") [] ])
    Interface.Impls.is_view;
  property "a type that holds an associated type is Plain when that type is" true projection_holder
    (fun _ -> Types.named (app "Kept") [ Types.named (app "Counted") [] ])
    Interface.Impls.plain;
  property "a type that holds a type holding an associated type is a view when that type is one"
    true
    (projection_holder ^ "\ntype Outer(held: Kept[Numbers])\n")
    (fun _ -> Types.named (app "Outer") [])
    Interface.Impls.is_view;
  let through_itself = projection_holder ^ Fixtures.Interface.through_itself in
  property "a type that contains itself through an associated type is Copyable" true through_itself
    (fun _ -> Types.named (app "Tree") [])
    Interface.Impls.copyable;
  property "a type that contains itself through an associated type is not a view" false
    through_itself
    (fun _ -> Types.named (app "Tree") [])
    Interface.Impls.is_view

(* Finding impls *)

let trait name arguments : Types.trait_reference =
  {
    trait = standard [ "core" ] name;
    trait_arguments = List.map (fun type_ -> Types.Type type_) arguments;
    associated = [];
  }

let () =
  test "Int64 implements Add[Int64] with Output Int64" (fun () ->
      let database = setup [] in
      match
        Interface.Impls.associated_type database
          ~bounds:(fun _ -> [])
          int64 (trait "Add" [ int64 ]) "Output"
      with
      | Some output when Types.equal output int64 -> ()
      | Some output -> fail "output %s" (Types.show output)
      | None -> fail "no impl");
  test "Int64 does not implement Add[Int32]" (fun () ->
      let database = setup [] in
      if
        Option.is_some
          (Interface.Impls.implements database
             ~bounds:(fun _ -> [])
             int64
             (trait "Add" [ Types.builtin Int32 ]))
      then fail "found an impl");
  test "a derived impl holds when its conditions do" (fun () ->
      let database = setup [] in
      if
        Option.is_none
          (Interface.Impls.implements database
             ~bounds:(fun _ -> [])
             (option int64) (trait "Equal" []))
      then fail "no impl");
  test "a derived impl does not hold when its conditions do not" (fun () ->
      let database = setup [ ("app::main", "type Opaque(x: Int64)\n") ] in
      let opaque = Types.named (app "Opaque") [] in
      if
        Option.is_some
          (Interface.Impls.implements database
             ~bounds:(fun _ -> [])
             (option opaque) (trait "Equal" []))
      then fail "found an impl");
  test "an impl of a conversion is found by the argument's type" (fun () ->
      let database = setup [] in
      if
        Option.is_none
          (Interface.Impls.implements database
             ~bounds:(fun _ -> [])
             int64
             (trait "From" [ Types.builtin Int32 ]))
      then fail "no impl")

(* Methods at an [impl] *)

let () =
  let text = Fixtures.Interface.described in
  let impl_of database type_ wanted : Path.t =
    match Interface.Impls.implements database ~bounds:(fun _ -> []) type_ wanted with
    | Some (From_impl { impl; _ }) -> impl
    | _ -> failwith "no impl"
  in
  let at database type_ wanted name : Types.signature =
    let owner = impl_of database type_ wanted in
    match Interface.Impls.signature database (Method { owner; name; receiver = Read }) with
    | Some signature -> signature
    | None -> failwith "no signature"
  in
  let generics (signature : Types.signature) =
    String.concat ", "
      (List.map (fun (generic : Types.generic) -> generic.generic.name) signature.generics)
  in
  let both = Types.named (app "Both") [ Types.named (app "One") [] ] in
  let described : Types.trait_reference =
    { trait = app "Described"; trait_arguments = []; associated = [] }
  in
  test "a method written inside an impl is generic over the impl's parameters" (fun () ->
      let database = setup [ ("app::main", text) ] in
      let signature = at database both described "describe" in
      if generics signature <> "Value" then fail "generics: %s" (generics signature));
  test "a method an impl leaves to its trait has the trait's signature there" (fun () ->
      let database = setup [ ("app::main", text) ] in
      let signature = at database both described "beside" in
      if generics signature <> "Value, Other" then fail "generics: %s" (generics signature);
      match signature.output with
      | Returns output when Types.show output = "Both[Value]" -> ()
      | Returns output -> fail "output %s" (Types.show output)
      | _ -> fail "no result");
  test "a derived impl's method has a signature" (fun () ->
      let database = setup [] in
      let signature = at database (option int64) (trait "Equal" []) "equal" in
      match (signature.generics, signature.receiver, signature.parameters) with
      | [ _ ], Some (Read, self), [ other ] when Types.equal self other.type_ -> ()
      | _ -> fail "generics: %s" (generics signature));
  test "a method of a capability's impl uses the impl's capabilities" (fun () ->
      let database = setup [ ("app::main", text) ] in
      let clock : Types.trait_reference =
        { trait = standard [ "capabilities" ] "Clock"; trait_arguments = []; associated = [] }
      in
      let signature = at database (Types.named (app "FixedClock") []) clock "now" in
      match (signature.uses :> Types.capability list) with
      | [ Capability _ ] -> ()
      | uses -> fail "%d uses" (List.length uses))

(* Transparent functions *)

let () =
  test "a transparent function is one whose body is its definition" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Interface.transparent_function_is_one_whose_body_is_its) ];
      one_diagnostic Fixtures.Interface.transparent_function_is_one_whose_body_is_its_2
        "types.not_a_definition";
      one_diagnostic Fixtures.Interface.transparent_function_is_one_whose_body_is_its_3
        "types.not_a_definition";
      one_diagnostic Fixtures.Interface.transparent_function_is_one_whose_body_is_its_4
        "types.not_a_definition")

(* Law proofs *)

let () =
  let monoid = Fixtures.Interface.monoid in
  test "a law's proof names a law of its trait and a type that implements the trait" (fun () ->
      no_diagnostics [ ("app::main", monoid ^ "proof Joined.associative for Meters {\n}\n") ];
      one_diagnostic (monoid ^ "proof Joined.commutative for Meters {\n}\n") "types.unknown_member";
      one_diagnostic (monoid ^ "proof Joined.associative for Feet {\n}\n") "types.no_impl");
  let boxed = monoid ^ Fixtures.Interface.boxed in
  test "a law's proof for a generic impl names the impl's type with its own generic parameters"
    (fun () ->
      no_diagnostics
        [ ("app::main", boxed ^ "proof Joined.associative for Box[Element: Joined] {\n}\n") ]);
  test "a law's proof gives a generic parameter the bounds that the impl requires" (fun () ->
      one_diagnostic (boxed ^ "proof Joined.associative for Box[Item] {\n}\n") "types.no_impl");
  test "a law's proof cannot assume a bound that the impl does not require" (fun () ->
      one_diagnostic
        (boxed ^ "proof Joined.associative for Box[Item: Joined + Equal] {\n}\n")
        "types.unsatisfied_bound");
  test "a law's proof names every generic parameter of its type" (fun () ->
      one_diagnostic (boxed ^ "proof Joined.associative for Box {\n}\n") "types.arity")

(* Real implementations *)

let () =
  test "a capability's real implementation is the one standard::system holds" (fun () ->
      let database = setup [] in
      match Interface.Impls.real_implementation database (standard [ "capabilities" ] "Clock") with
      | Some (Impl { module_; _ }) when Well_known.in_system module_ -> ()
      | Some impl -> fail "found %s" (Path.show impl)
      | None -> fail "none found");
  test "a trait that is no capability has no real implementation" (fun () ->
      let database = setup [] in
      if Option.is_some (Interface.Impls.real_implementation database (standard [ "core" ] "Equal"))
      then fail "found one")

(* Incremental work *)

let () =
  test "adding an impl of one trait re-checks nothing that asked about another" (fun () ->
      let base = Fixtures.Interface.base in
      let database = setup [ ("app::main", base) ] in
      let point = Types.named (app "Point") [] in
      let asker =
        Query.query ~name:"asker" ~phase:Phases.bodies
          ~show:(fun () -> "")
          (fun database () ->
            Option.is_some
              (Interface.Impls.implements database ~bounds:(fun _ -> []) point (trait "Equal" [])))
      in
      let engine = Engine.of_context database in
      expect_not_recomputed engine
        ~first:(fun () -> if not (Query.demand database asker ()) then fail "no impl of Equal")
        ~again:(fun () ->
          Database.Testing.set_text engine (module_of "app::main")
            (base ^ Fixtures.Interface.adding_an_impl_of_one_trait_re_checks_nothing_that);
          ignore (Query.demand database asker ()))
        asker [ () ])

let () =
  test "a type that contains itself with growing arguments does not hang" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Interface.type_that_contains_itself_with_growing_arguments) ]
      in
      ignore
        (Interface.Impls.copyable database
           ~bounds:(fun _ -> [])
           (Types.named (app "Nested") [ int64 ])));
  test "an impl's method may have the trait method's own generic parameters" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Interface.impls_method_may_have_the_trait_methods_own) ]);
  test "associated types inside function types are substituted in an impl" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Interface.associated_types_inside_function_types_are) ]);
  test "an associated type of a required trait is checked in an impl" (fun () ->
      one_diagnostic Fixtures.Interface.associated_type_of_a_required_trait_is_checked_in
        "types.signature_mismatch");
  test "an impl's associated type must meet the trait's bound on it" (fun () ->
      one_diagnostic Fixtures.Interface.impls_associated_type_must_meet_the_traits_bound
        "types.unsatisfied_bound");
  test "an associated type's declared bound holds where it is used" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Interface.associated_types_declared_bound_holds_where_it_is) ]);
  test "Self in a required trait is substituted by the bounded type" (fun () ->
      no_diagnostics
        [ ("app::main", Fixtures.Interface.self_in_a_required_trait_is_substituted_by_the) ]);
  test "a trait whose header did not parse satisfies every bound that names it" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Interface.trait_whose_header_did_not_parse_satisfies_every) ]
      in
      match Interface.diagnostics database (module_of "app::main") with
      | [] -> ()
      | reported -> fail "found [%s]" (String.concat "; " (codes reported)));
  test "an opaque generic type is Copyable by its declaration and its arguments" (fun () ->
      let database =
        setup [ ("app::main", "public opaque type Box[Value](inner: Value)\n  derives Copyable\n") ]
      in
      if
        not
          (Interface.Impls.copyable database
             ~bounds:(fun _ -> [])
             (Types.named (app "Box") [ int64 ]))
      then fail "not Copyable");
  test "only some traits can be derived" (fun () ->
      one_diagnostic "type P()\n  derives Iterable\n" "types.not_derivable");
  test "a capability's impl must give every method" (fun () ->
      one_diagnostic Fixtures.Interface.capabilitys_impl_must_give_every_method
        "types.missing_member");
  test "a capability's impl takes self or mut self" (fun () ->
      one_diagnostic Fixtures.Interface.capabilitys_impl_takes_self_or_mut_self
        "types.wrong_receiver");
  test "a method's head names every generic parameter of its type" (fun () ->
      one_diagnostic Fixtures.Interface.methods_head_names_every_generic_parameter_of_its
        "types.arity");
  test "a type argument must be of its parameter's kind" (fun () ->
      one_diagnostic "fn f(items: List[3]) {}\n" "types.argument_kind");
  test "a constant in a type argument must have a value" (fun () ->
      let database =
        setup [ ("app::main", Fixtures.Interface.constant_in_a_type_argument_must_have_a_value) ]
      in
      if
        not
          (List.mem "types.arity" (codes (Interface.diagnostics database (module_of "app::main"))))
      then fail "accepted");
  test "any must fix every associated type" (fun () ->
      one_diagnostic "fn f(items: any Iterable) {}\n" "types.associated_type_not_fixed");
  test "nothing can implement Copyable" (fun () ->
      one_diagnostic Fixtures.Interface.nothing_can_implement_copyable "types.implements_built_in");
  test "a public constant cannot have a private type" (fun () ->
      one_diagnostic Fixtures.Interface.public_constant_cannot_have_a_private_type
        "types.private_in_public");
  test "uses names a capability parameter, not a type parameter" (fun () ->
      one_diagnostic Fixtures.Interface.uses_names_a_capability_parameter_not_a_type
        "types.not_a_capability");
  test "Never implements no trait" (fun () ->
      let database = setup [] in
      if
        Option.is_some
          (Interface.Impls.implements database ~bounds:(fun _ -> []) Types.Never (trait "Hash" []))
      then fail "it does");
  test "an any value implements its trait only with the same arguments" (fun () ->
      let database = setup [] in
      let any = Types.Any (trait "From" [ int64 ]) in
      if
        Option.is_some
          (Interface.Impls.implements database
             ~bounds:(fun _ -> [])
             any
             (trait "From" [ Types.builtin Int32 ]))
      then fail "it does")

(* Every error type carries its report: these once lowered to an error with
   no report. *)

let () =
  test "`Self.Item` outside a trait and an impl of one is an error" (fun () ->
      one_diagnostic Fixtures.Interface.self_item_outside_a_trait_and_an_impl_of_one_is_an
        "types.unknown_associated_type");
  test "a generic parameter is not a bound" (fun () ->
      one_diagnostic Fixtures.Interface.generic_parameter_is_not_a_bound "types.not_a_trait");
  test "`Self` in a capability is an error" (fun () ->
      one_diagnostic Fixtures.Interface.self_in_a_capability_is_an_error "types.misplaced_self_type");
  test "`Self` in a function that is not a method is an error" (fun () ->
      one_diagnostic "fn f(value: Self) {}\n" "types.misplaced_self_type");
  test "a trait is not the head of a method" (fun () ->
      one_diagnostic Fixtures.Interface.trait_is_not_the_head_of_a_method "types.not_a_type");
  test "a capability parameter is not a type" (fun () ->
      one_diagnostic "fn f[capability Granted](value: Granted) {}\n" "types.not_a_type");
  test "a method of an unknown type keeps its head's generic parameters" (fun () ->
      one_diagnostic Fixtures.Interface.method_of_an_unknown_type_keeps_its_heads_generic
        "resolve.unknown_name")

(* Well-known definitions *)

let () =
  test "every definition the compiler names is in the standard library" (fun () ->
      let database = setup [] in
      let declared =
        List.map
          (fun (declaration : Resolve.Names.declaration) -> declaration.path)
          (Query.demand database Resolve.Names.package_declarations Path.standard_package)
      in
      List.iter
        (fun known ->
          let path = Well_known.path known in
          if not (List.exists (Path.equal path) declared) then
            fail "the standard library has no `%s`" (Path.show path))
        Well_known.all);
  test "a well-known definition is found by its path" (fun () ->
      List.iter
        (fun known ->
          if Well_known.of_path (Well_known.path known) <> Some known then
            fail "`%s` is not found by its path" (Path.show (Well_known.path known)))
        Well_known.all)
