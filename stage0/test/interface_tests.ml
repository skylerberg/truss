(* The tests of checking interfaces: signatures, types, traits, [impl]s, the
   properties of types, and finding [impl]s. Each gives a few definitions
   and states one fact. See TYPECHECKER.md, "Checking signatures and
   definitions" and "Testing". *)

open Harness
open Support

(* Everything the checker reports so far: resolution and interfaces. *)
let check database module_ =
  Resolve.diagnostics database module_ @ Interface.diagnostics database module_

let one_diagnostic = one_diagnostic ~check
let no_diagnostics = no_diagnostics ~check
let app name : Path.t = Top { module_ = module_of "app::main"; name }
let standard modules name : Path.t = Top { module_ = { package = "standard"; modules }; name }
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
          [
            ( "app::main",
              "type Box[Value](value: Value)\n\nfn Box[Value].get(self) -> Value { todo }\n" );
          ]
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
      one_diagnostic
        "type Sorted[Element: Ordered](items: List[Element])\n\n\
         type Point(x: Int64)\n\n\
         fn f(points: Sorted[Point]) {}\n"
        "types.unsatisfied_bound");
  test "a generic parameter's bound meets a bound the type needs" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "type Sorted[Element: Ordered](items: List[Element])\n\n\
             fn f[Item: Ordered](items: Sorted[Item]) {}\n" );
        ]);
  test "a public signature cannot mention a private type" (fun () ->
      one_diagnostic "type Secret(code: Int64)\n\npublic fn f(secret: Secret) {}\n"
        "types.private_in_public");
  test "a method must be in its type's package" (fun () ->
      one_diagnostic "fn Int64.double(self) -> Int64 { todo }\n" "types.method_outside_package");
  test "main must have its fixed signature" (fun () ->
      one_diagnostic "fn main() -> ExitCode { todo }\n" "types.main_signature");
  test "main with its fixed signature is accepted" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "fn main(arguments: List[String]) -> ExitCode\n  uses Console\n{\n  todo\n}\n" );
        ]);
  test "a default must be a constant expression" (fun () ->
      one_diagnostic "fn compute() -> Int64 { 1 }\n\nfn f(count: Int64 = compute()) {}\n"
        "types.default_not_constant");
  test "a default may build a record from constants" (fun () ->
      no_diagnostics
        [
          ("app::main", "type Point(x: Int64, y: Int64)\n\nfn f(at: Point = Point(x: 0, y: 1)) {}\n");
        ]);
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
      one_diagnostic "type Opaque(x: Int64)\n\ntype Point(inner: Opaque)\n  derives Equal\n"
        "types.cannot_derive");
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
      one_diagnostic "type Point(x: Int64)\n\nimpl Equal for Point {}\n" "types.missing_member");
  test "an impl may leave out a method with a body" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "type Point(x: Int64)\n\n\
             impl Equal for Point {\n\
            \  fn equal(self, other: Point) -> Bool { todo }\n\
             }\n" );
        ]);
  test "an impl's method must have the trait's signature" (fun () ->
      one_diagnostic
        "type Point(x: Int64)\n\n\
         impl Equal for Point {\n\
        \  fn equal(self, value: Point) -> Bool { todo }\n\
         }\n"
        "types.signature_mismatch");
  test "an impl cannot give a method its trait does not declare" (fun () ->
      one_diagnostic
        "type Point(x: Int64)\n\n\
         impl Equal for Point {\n\
        \  fn equal(self, other: Point) -> Bool { todo }\n\
        \  fn extra(self) {}\n\
         }\n"
        "types.extra_member");
  test "an impl must give every associated type" (fun () ->
      one_diagnostic
        "type Meters(value: Int64)\n\n\
         impl Add[Meters] for Meters {\n\
        \  fn add(self, right: Meters) -> Self.Output { todo }\n\
         }\n"
        "types.missing_member");
  test "the traits a trait requires must be implemented" (fun () ->
      one_diagnostic
        "type Point(x: Int64)\n\n\
         impl Ordered for Point {\n\
        \  fn compare(self, other: Point) -> Ordering { todo }\n\
         }\n"
        "types.missing_required_impl");
  test "nothing can implement Panic" (fun () ->
      one_diagnostic
        "type Quiet()\n\n\
         impl Panic for Quiet {\n\
        \  fn crash(self, message: StringSlice) -> Never { todo }\n\
         }\n"
        "types.implements_panic");
  test "a trait's impl cannot have uses" (fun () ->
      one_diagnostic
        "type Point(x: Int64)\n\n\
         impl Equal for Point\n\
        \  uses Clock\n\
         {\n\
        \  fn equal(self, other: Point) -> Bool { todo }\n\
         }\n"
        "types.impl_uses");
  test "a capability's impl takes a receiver and may have uses" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "type FixedClock(time: Instant)\n\n\
             impl Clock for FixedClock\n\
            \  uses Random\n\
             {\n\
            \  fn now(self) -> Instant { todo }\n\
             }\n" );
        ]);
  test "traits cannot require each other in a cycle" (fun () ->
      let database =
        setup [ ("app::main", "trait First: Second {}\n\ntrait Second: First {}\n") ]
      in
      match codes (check database (module_of "app::main")) with
      | [ "types.trait_cycle"; "types.trait_cycle" ] -> ()
      | found -> fail "found [%s]" (String.concat "; " found));
  test "a trait cannot redeclare a method of a trait it requires" (fun () ->
      one_diagnostic "trait Sorted: Ordered {\n  fn compare(self, other: Self) -> Ordering\n}\n"
        "types.redeclared_method")

(* Properties *)

let property name expected text type_ check =
  test name (fun () ->
      let database = setup [ ("app::main", text) ] in
      let actual = check database ~bounds:(fun _ -> []) (type_ database) in
      if actual <> expected then fail "expected %b" expected)

let option type_ = Types.named (standard [ "option" ] "Option") [ type_ ]
let list type_ = Types.named (standard [ "list" ] "List") [ type_ ]
let slice type_ = Types.named (standard [ "list" ] "Slice") [ type_ ]

let () =
  property "an integer is Plain" true "" (fun _ -> int64) Interface.Properties.plain;
  property "an Option of plain data is Plain" true ""
    (fun _ -> option int64)
    Interface.Properties.plain;
  property "a List is Copyable" true "" (fun _ -> list int64) Interface.Properties.copyable;
  property "a handle is not Copyable" false ""
    (fun _ -> Types.named (Intrinsic.builtin_path Handle) [])
    Interface.Properties.copyable;
  property "a handle is not Plain" false ""
    (fun _ -> Types.named (Intrinsic.builtin_path Handle) [])
    Interface.Properties.plain;
  property "an Option of a handle is not Copyable" false ""
    (fun _ -> option (Types.named (Intrinsic.builtin_path Handle) []))
    Interface.Properties.copyable;
  property "an Option of a handle is not Plain" false ""
    (fun _ -> option (Types.named (Intrinsic.builtin_path Handle) []))
    Interface.Properties.plain;
  property "a List is not Plain" false "" (fun _ -> list int64) Interface.Properties.plain;
  property "an Option of a Slice is a view" true ""
    (fun _ -> option (slice int64))
    Interface.Properties.is_view;
  property "a List of integers is not a view" false ""
    (fun _ -> list int64)
    Interface.Properties.is_view;
  property "a record of plain fields is Plain" true "type Point(x: Int64, y: Int64)\n"
    (fun _ -> Types.named (app "Point") [])
    Interface.Properties.plain;
  property "a variant held indirectly is not Plain" false
    "type Tree =\n  | Leaf\n  | indirect Node(left: Tree, right: Tree)\n"
    (fun _ -> Types.named (app "Tree") [])
    Interface.Properties.plain;
  property "a recursive type is still Copyable" true
    "type Tree =\n  | Leaf\n  | indirect Node(left: Tree, right: Tree)\n"
    (fun _ -> Types.named (app "Tree") [])
    Interface.Properties.copyable;
  property "an opaque type is not Copyable unless it says so" false
    "public opaque type Token(code: Int64)\n"
    (fun _ -> Types.named (app "Token") [])
    Interface.Properties.copyable;
  property "an opaque type that derives Plain is Plain" true
    "public opaque type Token(code: Int64)\n  derives Plain\n"
    (fun _ -> Types.named (app "Token") [])
    Interface.Properties.plain;
  property "a type defined as todo is not Copyable" false "type Session = todo\n"
    (fun _ -> Types.named (app "Session") [])
    Interface.Properties.copyable

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

(* Incremental work *)

let () =
  test "adding an impl of one trait re-checks nothing that asked about another" (fun () ->
      let base =
        "type Point(x: Int64)\n\n\
         impl Equal for Point {\n\
        \  fn equal(self, other: Point) -> Bool { todo }\n\
         }\n"
      in
      let database = setup [ ("app::main", base) ] in
      let point = Types.named (app "Point") [] in
      let asker =
        Query.query ~name:"asker"
          ~show:(fun () -> "")
          (fun database () ->
            Option.is_some
              (Interface.Impls.implements database ~bounds:(fun _ -> []) point (trait "Equal" [])))
      in
      if not (Query.demand database asker ()) then fail "no impl of Equal";
      Engine.set (Engine.of_context database) Workspace.file_text (module_of "app::main")
        (base ^ "\nimpl Hash for Point {\n  fn hash(self, hasher: mut Hasher) {}\n}\n");
      Engine.clear_log (Engine.of_context database);
      ignore (Query.demand database asker ());
      if List.mem "asker()" (Engine.executed (Engine.of_context database)) then fail "asked again")

(* What the review of interfaces found *)

let () =
  test "a type that contains itself with growing arguments does not hang" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "type Nested[Element] =\n\
              \  | Leaf(value: Element)\n\
              \  | indirect Node(inner: Nested[List[Element]])\n" );
          ]
      in
      ignore
        (Interface.Properties.copyable database
           ~bounds:(fun _ -> [])
           (Types.named (app "Nested") [ int64 ])));
  test "an impl's method may have the trait method's own generic parameters" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "trait Mapper {\n\
            \  fn apply[Output](self, value: Output) -> Output\n\
             }\n\n\
             type Point(x: Int64)\n\n\
             impl Mapper for Point {\n\
            \  fn apply[Output](self, value: Output) -> Output { todo }\n\
             }\n" );
        ]);
  test "associated types inside function types are substituted in an impl" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "trait Visits {\n\
            \  type Element\n\
            \  fn visit(self, each: fn(Self.Element) -> Bool)\n\
             }\n\n\
             type Bag(count: Int64)\n\n\
             impl Visits for Bag {\n\
            \  type Element = Int64\n\
            \  fn visit(self, each: fn(Int64) -> Bool) {}\n\
             }\n" );
        ]);
  test "an associated type of a required trait is checked in an impl" (fun () ->
      one_diagnostic
        "trait Base {\n\
        \  type Key\n\
         }\n\n\
         trait Sub: Base {\n\
        \  fn get(self) -> Self.Key\n\
         }\n\n\
         type P(x: Int64)\n\n\
         impl Base for P {\n\
        \  type Key = Int64\n\
         }\n\n\
         impl Sub for P {\n\
        \  fn get(self) -> String { todo }\n\
         }\n"
        "types.signature_mismatch");
  test "an impl's associated type must meet the trait's bound on it" (fun () ->
      one_diagnostic
        "trait Keyed {\n\
        \  type Key: Hash\n\
         }\n\n\
         type Opaque(x: Int64)\n\n\
         type P(x: Int64)\n\n\
         impl Keyed for P {\n\
        \  type Key = Opaque\n\
         }\n"
        "types.unsatisfied_bound");
  test "an associated type's declared bound holds where it is used" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "trait Keyed {\n  type Key: Hash + Ordered\n  fn keys(self) -> Set[Self.Key]\n}\n" );
        ]);
  test "Self in what a trait requires stands for the bounded type" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "trait Summable: Add[Self] {}\n\n\
             type Needs[Value: Add[Value]](value: Value)\n\n\
             fn f[Item: Summable](items: Needs[Item]) {}\n" );
        ]);
  test "a trait whose header did not parse satisfies every bound that names it" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "trait Shape[ {\n\
               }\n\n\
               type Holder[Value: Shape](value: Value)\n\n\
               type P(x: Int64)\n\n\
               fn f(holder: Holder[P]) {}\n" );
          ]
      in
      match Interface.diagnostics database (module_of "app::main") with
      | [] -> ()
      | found -> fail "found [%s]" (String.concat "; " (codes found)));
  test "an opaque generic type is Copyable by its declaration and its arguments" (fun () ->
      let database =
        setup [ ("app::main", "public opaque type Box[Value](inner: Value)\n  derives Copyable\n") ]
      in
      if
        not
          (Interface.Properties.copyable database
             ~bounds:(fun _ -> [])
             (Types.named (app "Box") [ int64 ]))
      then fail "not Copyable");
  test "only some traits can be derived" (fun () ->
      one_diagnostic "type P()\n  derives Iterable\n" "types.not_derivable");
  test "a capability's impl must give every method" (fun () ->
      one_diagnostic
        "capability Log {\n\
        \  fn write(text: StringSlice)\n\
        \  fn flush()\n\
         }\n\n\
         type Silent()\n\n\
         impl Log for Silent {\n\
        \  fn write(self, text: StringSlice) {}\n\
         }\n"
        "types.missing_member");
  test "a capability's impl takes self or mut self" (fun () ->
      one_diagnostic
        "type Fixed()\n\nimpl Clock for Fixed {\n  fn now(own self) -> Instant { todo }\n}\n"
        "types.wrong_receiver");
  test "a method's head names every generic parameter of its type" (fun () ->
      one_diagnostic "type Box[Value](value: Value)\n\nfn Box.get(self) -> Int64 { todo }\n"
        "types.arity");
  test "a type argument must be of its parameter's kind" (fun () ->
      one_diagnostic "fn f(items: List[3]) {}\n" "types.arity");
  test "a constant in a type argument must have a value" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "let first: USize = second\n\n\
               let second: USize = first\n\n\
               fn f(values: Array[Int64, first]) {}\n" );
          ]
      in
      if
        not
          (List.mem "types.arity" (codes (Interface.diagnostics database (module_of "app::main"))))
      then fail "accepted");
  test "any must fix every associated type" (fun () ->
      one_diagnostic "fn f(items: any Iterable) {}\n" "types.associated_type_not_fixed");
  test "nothing can implement Copyable" (fun () ->
      one_diagnostic "type P(x: Int64)\n\nimpl Copyable for P {\n  fn copy(self) -> P { todo }\n}\n"
        "types.implements_built_in");
  test "a public constant cannot have a private type" (fun () ->
      one_diagnostic "type Secret(code: Int64)\n\npublic let secret: Secret = Secret(code: 1)\n"
        "types.private_in_public");
  test "uses names a capability parameter, not a type parameter" (fun () ->
      one_diagnostic "fn f[Value](value: Value)\n  uses Value\n{\n}\n" "types.not_a_capability");
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

let () = finish ()
