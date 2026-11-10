(* The tests of checking interfaces: signatures, types, traits, [impl]s, the
   properties of types, and finding [impl]s. Each gives a few definitions
   and states one fact. *)

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
  test "only a record derives Default" (fun () ->
      one_diagnostic "type Light =\n  | Off\n  | On\n  derives Default\n" "types.cannot_derive";
      no_diagnostics [ ("app::main", "type Point(x: Int64, y: Int64)\n  derives Default\n") ]);
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
            \  fn monotonic(self) -> Duration { todo }\n\
            \  fn sleep(self, duration: Duration) {}\n\
             }\n" );
        ]);
  test "a capability's impl method may repeat its impl's uses" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "type FixedClock(time: Instant)\n\n\
             impl Clock for FixedClock\n\
            \  uses Random\n\
             {\n\
            \  fn now(self) -> Instant\n\
            \    uses Random\n\
            \  {\n\
            \    todo\n\
            \  }\n\
            \  fn monotonic(self) -> Duration { todo }\n\
            \  fn sleep(self, duration: Duration) {}\n\
             }\n" );
        ]);
  test "a capability's impl method cannot add uses of its own" (fun () ->
      one_diagnostic
        "type FixedClock(time: Instant)\n\n\
         impl Clock for FixedClock {\n\
        \  fn now(self) -> Instant\n\
        \    uses Random\n\
        \  {\n\
        \    todo\n\
        \  }\n\
        \  fn monotonic(self) -> Duration { todo }\n\
        \  fn sleep(self, duration: Duration) {}\n\
         }\n"
        "types.impl_uses");
  test "an impl's method names its generic parameters its own way" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "trait Filler {\n\
            \  fn fill[count: USize](self) -> Array[Int64, count]\n\n\
            \  fn run[capability Used](self, action: (fn() uses Used))\n\
            \    uses Used\n\
             }\n\n\
             type Thing()\n\n\
             impl Filler for Thing {\n\
            \  fn fill[size: USize](self) -> Array[Int64, size] { todo }\n\n\
            \  fn run[capability Given](self, action: (fn() uses Given))\n\
            \    uses Given\n\
            \  {\n\
            \    todo\n\
            \  }\n\
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
        "types.redeclared_method");
  test "a trait may add a version of a method of a trait it requires" (fun () ->
      no_diagnostics
        [
          ( "app::main",
            "trait Changeable: Iterable {\n  fn each(mut self) yields mut Self.Element\n}\n" );
        ])

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
    "type Tree =\n  | Leaf\n  | indirect Node(left: Tree, right: Tree)\n"
    (fun _ -> Types.named (app "Tree") [])
    Interface.Impls.plain;
  property "a recursive type is still Copyable" true
    "type Tree =\n  | Leaf\n  | indirect Node(left: Tree, right: Tree)\n"
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
let chain = "type Chain[Value] =\n  | End\n  | indirect Link(value: Value, rest: Chain[Value])\n"

let kept =
  "trait Shown {\n\
  \  type Part\n\
   }\n\n\
   type Numbers(items: List[Int64])\n\n\
   impl Shown for Numbers {\n\
  \  type Part = Slice[Int64]\n\
   }\n\n\
   type Counted(count: Int64)\n\n\
   impl Shown for Counted {\n\
  \  type Part = Int64\n\
   }\n\n\
   type Kept[Source: Shown](part: Source.Part)\n"

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
    "type Nest[Value] =\n  | Leaf(value: Value)\n  | indirect More(inner: Nest[Slice[Value]])\n"
    (fun _ -> Types.named (app "Nest") [ int64 ])
    Interface.Impls.is_view;
  property "types that hold each other are Copyable when nothing in them says otherwise" true
    "type Even =\n  | Zero\n  | indirect After(odd: Odd)\n\ntype Odd(even: Even, count: Int64)\n"
    (fun _ -> Types.named (app "Even") [])
    Interface.Impls.copyable;
  property "types that hold each other are not Copyable when one holds what is not" false
    "public opaque type Token(code: Int64)\n\n\
     type Even =\n\
    \  | Zero\n\
    \  | indirect After(odd: Odd)\n\n\
     type Odd(even: Even, token: Token)\n"
    (fun _ -> Types.named (app "Even") [])
    Interface.Impls.copyable;
  property "a type that holds an associated type is a view when that type is one" true kept
    (fun _ -> Types.named (app "Kept") [ Types.named (app "Numbers") [] ])
    Interface.Impls.is_view;
  property "a type that holds an associated type is not a view when that type is not" false kept
    (fun _ -> Types.named (app "Kept") [ Types.named (app "Counted") [] ])
    Interface.Impls.is_view;
  property "a type that holds an associated type is Plain when that type is" true kept
    (fun _ -> Types.named (app "Kept") [ Types.named (app "Counted") [] ])
    Interface.Impls.plain;
  property "a type that holds a type holding an associated type is a view when that type is one"
    true
    (kept ^ "\ntype Outer(kept: Kept[Numbers])\n")
    (fun _ -> Types.named (app "Outer") [])
    Interface.Impls.is_view;
  let through_itself =
    kept
    ^ "\n\
       type Marker()\n\n\
       impl Shown for Marker {\n\
      \  type Part = Tree\n\
       }\n\n\
       type Tree =\n\
      \  | Leaf\n\
      \  | indirect Branch(kept: Kept[Marker])\n"
  in
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
  let text =
    "trait Described {\n\
    \  fn describe(self) -> Int64\n\n\
    \  fn beside[Other](self, other: Other) -> Self { todo }\n\
     }\n\n\
     type One()\n\n\
     impl Described for One {\n\
    \  fn describe(self) -> Int64 { todo }\n\
     }\n\n\
     type Both[Value](first: Value, second: Value)\n\n\
     impl Described for Both[Value: Described] {\n\
    \  fn describe(self) -> Int64 { todo }\n\
     }\n\n\
     type FixedClock(time: Instant)\n\n\
     impl Clock for FixedClock\n\
    \  uses Random\n\
     {\n\
    \  fn now(self) -> Instant { todo }\n\
    \  fn monotonic(self) -> Duration { todo }\n\
    \  fn sleep(self, duration: Duration) {}\n\
     }\n"
  in
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
  test "a capability's impl method uses what its impl uses" (fun () ->
      let database = setup [ ("app::main", text) ] in
      let clock : Types.trait_reference =
        { trait = standard [ "capabilities" ] "Clock"; trait_arguments = []; associated = [] }
      in
      let signature = at database (Types.named (app "FixedClock") []) clock "now" in
      match signature.uses with [ Capability _ ] -> () | uses -> fail "%d uses" (List.length uses))

(* Law proofs *)

let () =
  let monoid =
    "trait Joined {\n\
    \  fn join(self, other: Self) -> Self\n\n\
    \  law associative(first: Self, second: Self, third: Self) {\n\
    \    true\n\
    \  }\n\
     }\n\n\
     type Meters(value: Int64)\n\n\
     type Feet(value: Int64)\n\n\
     impl Joined for Meters {\n\
    \  fn join(self, other: Meters) -> Meters { todo }\n\
     }\n\n"
  in
  test "a law's proof is of a law its trait has, kept by a type that implements the trait"
    (fun () ->
      no_diagnostics [ ("app::main", monoid ^ "proof Joined.associative for Meters {\n}\n") ];
      one_diagnostic (monoid ^ "proof Joined.commutative for Meters {\n}\n") "types.unknown_member";
      one_diagnostic (monoid ^ "proof Joined.associative for Feet {\n}\n") "types.no_impl")

(* Real implementations *)

let () =
  test "a capability's real implementation is the one standard::system holds" (fun () ->
      let database = setup [] in
      match Interface.Impls.real_implementation database (standard [ "capabilities" ] "Clock") with
      | Some (Impl { module_ = { package = "standard"; modules = "system" :: _ }; _ }) -> ()
      | Some impl -> fail "found %s" (Path.show impl)
      | None -> fail "none found");
  test "a trait that is no capability has no real implementation" (fun () ->
      let database = setup [] in
      if Option.is_some (Interface.Impls.real_implementation database (standard [ "core" ] "Equal"))
      then fail "found one")

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
        Query.query ~name:"asker" ~phase:Bodies
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
        (Interface.Impls.copyable database
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
          (Interface.Impls.copyable database
             ~bounds:(fun _ -> [])
             (Types.named (app "Box") [ int64 ]))
      then fail "not Copyable");
  test "only some traits can be derived" (fun () ->
      one_diagnostic "type P()\n  derives Iterable\n" "types.not_derivable");
  test "a capability's impl must give every method" (fun () ->
      one_diagnostic
        "capability Journal {\n\
        \  fn write(text: StringSlice)\n\
        \  fn flush()\n\
         }\n\n\
         type Silent()\n\n\
         impl Journal for Silent {\n\
        \  fn write(self, text: StringSlice) {}\n\
         }\n"
        "types.missing_member");
  test "a capability's impl takes self or mut self" (fun () ->
      one_diagnostic
        "type Fixed()\n\n\
         impl Clock for Fixed {\n\
        \  fn now(own self) -> Instant { todo }\n\
        \  fn monotonic(self) -> Duration { todo }\n\
        \  fn sleep(self, duration: Duration) {}\n\
         }\n"
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

(* Every error type carries its report: these once lowered to an error with
   no report. *)

let () =
  test "`Self.Item` outside a trait and an impl of one is an error" (fun () ->
      one_diagnostic "type Box(value: Int64)\n\nfn Box.get(self) -> Self.Item {\n  todo\n}\n"
        "types.unknown_associated_type");
  test "a generic parameter is not a bound" (fun () ->
      one_diagnostic "fn f[First, Second: First](value: own Second) -> Second {\n  value\n}\n"
        "types.not_a_trait");
  test "`Self` in a capability is an error" (fun () ->
      one_diagnostic "capability Logger {\n  fn log(message: Self)\n}\n" "types.misplaced_self_type");
  test "`Self` in a function that is not a method is an error" (fun () ->
      one_diagnostic "fn f(value: Self) {}\n" "types.misplaced_self_type");
  test "a trait is not the head of a method" (fun () ->
      one_diagnostic "fn Ordered.twice(self) -> Bool {\n  true\n}\n" "types.not_a_type");
  test "a capability parameter is not a type" (fun () ->
      one_diagnostic "fn f[capability Granted](value: Granted) {}\n" "types.not_a_type");
  test "a method of an unknown type keeps its head's generic parameters" (fun () ->
      one_diagnostic "fn Missing[Element].first(self) -> Element {\n  todo\n}\n"
        "resolve.unknown_name")

let () = finish ()
