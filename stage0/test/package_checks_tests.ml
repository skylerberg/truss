module Package_checks = Type_checker.For_testing.Package_checks

(* The tests of the checks across a package. *)

open Harness
open Support

let check database module_ =
  Resolve.diagnostics database module_
  @ Interface.diagnostics database module_
  @ Package_checks.diagnostics database module_

let one_diagnostic = one_diagnostic ~check
let fine text = no_diagnostics ~check [ ("app::main", text) ]

let () =
  test "an impl must live with its trait, its type, or a type its trait names" (fun () ->
      one_diagnostic "impl Display for Int64 {\n  fn display(self, output: mut TextBuilder) {}\n}\n"
        "package.impl_location");
  test "only the built-in integer types implement the integer traits" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "type Count(value: Int64)\n\n\
               impl SignedInteger for Count {\n\
              \  type Unsigned = UInt64\n\
               }\n" );
          ]
      in
      let found = codes (check database (module_of "app::main")) in
      if not (List.mem "package.sealed_trait_impl" found) then
        fail "found [%s]" (String.concat "; " found));
  test "an impl may live with a type its trait's arguments name" (fun () ->
      fine
        "type UserId(number: Int64)\n\n\
         impl From[UserId] for Int64 {\n\
        \  fn from(value: own UserId) -> Int64 { todo }\n\
         }\n");
  test "two impls of a trait for one type constructor overlap when their arguments unify" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "type Vector[Element](first: Element)\n\n\
               impl Add[Element] for Vector[Element] {\n\
              \  type Output = Vector[Element]\n\
              \  fn add_is_defined(self, right: Element) -> Bool { true }\n\
              \  fn add(self, right: Element) -> Vector[Element] { todo }\n\
               }\n\n\
               impl Add[Int64] for Vector[Element] {\n\
              \  type Output = Vector[Element]\n\
              \  fn add_is_defined(self, right: Int64) -> Bool { true }\n\
              \  fn add(self, right: Int64) -> Vector[Element] { todo }\n\
               }\n" );
          ]
      in
      if not (List.mem "package.overlapping_impls" (codes (check database (module_of "app::main"))))
      then fail "no overlap");
  test "a type's own method cannot share a name with a trait's" (fun () ->
      one_diagnostic
        "type Point(x: Int64)\n\n\
         fn Point.equal(self, other: Point) -> Bool { todo }\n\n\
         impl Equal for Point {\n\
        \  fn equal(self, other: Point) -> Bool { todo }\n\
         }\n"
        "package.method_name_clash");
  test "a type's own method may be another version of a trait's" (fun () ->
      fine
        "type Bag(items: List[Int64])\n\n\
         impl Iterable for Bag {\n\
        \  type Element = Int64\n\
        \  fn each(self) yields Int64 { todo }\n\
         }\n\n\
         fn Bag.each(mut self) yields mut Int64 { todo }\n\n\
         fn Bag.each(own self) yields own Int64 { todo }\n");
  test "an impl that writes a method may make it another version of the type's own" (fun () ->
      fine
        "trait Labelled {\n\
        \  fn label(self) -> Int64\n\
        \    cost time O(1)\n\
        \  {\n\
        \    0\n\
        \  }\n\
         }\n\n\
         type Counter(count: Int64)\n\n\
         fn Counter.label(own self) -> Int64 { todo }\n\n\
         impl Labelled for Counter {\n\
        \  fn label(self) -> Int64\n\
        \    cost time O(1)\n\
        \  {\n\
        \    0\n\
        \  }\n\
         }\n");
  test "a method an impl leaves to its trait cannot be a version of the type's own" (fun () ->
      one_diagnostic
        "trait Labelled {\n\
        \  fn label(self) -> Int64\n\
        \    cost time O(1)\n\
        \  {\n\
        \    0\n\
        \  }\n\
         }\n\n\
         type Counter(count: Int64)\n\n\
         fn Counter.label(own self) -> Int64 { todo }\n\n\
         impl Labelled for Counter {}\n"
        "package.method_name_clash");
  test "a type's constant cannot share a name with a trait's method" (fun () ->
      one_diagnostic
        "trait Bounded {\n\
        \  fn largest() -> Self\n\
         }\n\n\
         type Level(value: Int64)\n\n\
         let Level.largest: Level = Level(9)\n\n\
         impl Bounded for Level {\n\
        \  fn largest() -> Level { todo }\n\
         }\n"
        "package.method_name_clash");
  test "a type that contains itself in place needs indirect, with a fix that adds it" (fun () ->
      one_diagnostic "type Tree =\n  | Leaf\n  | Node(left: Tree, right: Tree)\n"
        "package.needs_indirect"
        ~fixed:"type Tree =\n  | Leaf\n  | indirect Node(left: Tree, right: Tree)\n");
  test "a type that contains itself through a collection needs no indirect" (fun () ->
      fine "type Expression =\n  | Number(value: Int64)\n  | Call(arguments: List[Expression])\n");
  test "a record cannot contain itself through an Option" (fun () ->
      one_diagnostic "type Node(next: Option[Node])\n" "package.needs_indirect");
  test "a type that contains itself with growing arguments is an error" (fun () ->
      one_diagnostic
        "type Nested[Element] =\n\
        \  | Leaf(value: Element)\n\
        \  | indirect Node(inner: Nested[List[Element]])\n"
        "package.growing_type");
  test "generic code that instantiates itself with growing arguments is an error" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "fn grow[Element](value: own Element) -> Int64 {\n  grow(Some(own value))\n}\n" );
          ]
      in
      if
        not
          (List.mem "package.instantiation_cycle" (codes (check database (module_of "app::main"))))
      then fail "no cycle");
  test "two tests of a package cannot share a name" (fun () ->
      let database =
        setup [ ("app::main", "test \"adds\" {\n}\n"); ("app::other", "test \"adds\" {\n}\n") ]
      in
      match codes (check database (module_of "app::other")) with
      | [ "package.duplicate_test" ] -> ()
      | actual -> fail "found [%s]" (String.concat "; " actual))

(* Recursive types, at scale *)

let () =
  test "a long chain of types that hold each other is fine" (fun () ->
      fine
        (String.concat ""
           (List.init 20 (fun index ->
                if index = 19 then "type T19(value: Int64)\n"
                else Printf.sprintf "type T%d(inner: T%d)\n\n" index (index + 1)))));
  test "nested instances of a generic type are not growing" (fun () ->
      fine
        "type Couple[First, Second](first: First, second: Second)\n\n\
         type Nest(value: Couple[Couple[Int64, String], Couple[String, Int64]])\n");
  test "many types that each hold the next several times are checked quickly" (fun () ->
      let text =
        String.concat ""
          (List.init 16 (fun index ->
               if index = 15 then "type D15(value: Int64)\n"
               else
                 Printf.sprintf "type D%d(a: D%d, b: D%d, c: D%d, d: D%d)\n\n" index (index + 1)
                   (index + 1) (index + 1) (index + 1)))
      in
      let started = Sys.time () in
      fine text;
      if Sys.time () -. started > 5.0 then fail "took %.1f seconds" (Sys.time () -. started));
  test "a type held in place through a generic type's argument needs indirect" (fun () ->
      one_diagnostic
        "type Couple[First, Second](first: First, second: Second)\n\n\
         type Tree =\n\
        \  | Leaf\n\
        \  | Node(children: Couple[Tree, Int64])\n"
        "package.needs_indirect");
  test "a type held in place through an associated type needs indirect" (fun () ->
      one_diagnostic
        "trait Shown {\n\
        \  type Part\n\
         }\n\n\
         type Marker()\n\n\
         impl Shown for Marker {\n\
        \  type Part = Tree\n\
         }\n\n\
         type Kept[Source: Shown](part: Source.Part)\n\n\
         type Tree(held: Kept[Marker], count: Int64)\n"
        "package.needs_indirect");
  test "a type held through a generic type's collection needs no indirect" (fun () ->
      fine
        "type Wrapper[Element](items: List[Element])\n\n\
         type Tree =\n\
        \  | Leaf\n\
        \  | Node(children: Wrapper[Tree])\n");
  test "generic types whose arguments grow through each other are both growing" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "type Outer[Element] =\n\
              \  | Empty\n\
              \  | indirect More(inner: Inner[List[Element]])\n\n\
               type Inner[Element](outer: Outer[Element])\n" );
          ]
      in
      match codes (check database (module_of "app::main")) with
      | [ "package.growing_type"; "package.growing_type" ] -> ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
  test "a generic type that swaps its arguments is not growing" (fun () ->
      fine "type Swap[First, Second] =\n  | Stop\n  | indirect Next(next: Swap[Second, First])\n")

(* Strict positivity *)

let shown = "trait Shown {\n  type Part\n}\n\ntype Marker()\n\n"
let holder = "type Kept[Source: Shown](part: Source.Part)\n\n"

let () =
  let actual text = codes (check (setup [ ("app::main", text) ]) (module_of "app::main")) in
  let expect expected text =
    match actual text with
    | actual when actual = expected -> ()
    | actual -> fail "found [%s]" (String.concat "; " actual)
  in
  test "a type cannot occur in the input of a function type that has a time clause" (fun () ->
      one_diagnostic "type Knot(run: (fn(Knot) -> Bool cost time finite))\n"
        "package.not_strictly_positive");
  test "a type may occur in the input of a function type that has no time clause" (fun () ->
      fine "type Button(label: String, on_click: fn(Button))\n");
  test "a type may occur in the output of a function type that has a time clause" (fun () ->
      fine "type Lazy(next: (fn() -> Lazy cost time finite))\n");
  test "a type cannot occur in such an input inside a collection" (fun () ->
      one_diagnostic "type Knot(runs: List[(fn(Knot) -> Bool cost time finite)])\n"
        "package.not_strictly_positive");
  test "a type cannot occur in such an input inside a type without fields" (fun () ->
      one_diagnostic
        "type Pending[Element] = todo\n\n\
         type Knot(runs: Pending[(fn(Knot) -> Bool cost time finite)])\n"
        "package.not_strictly_positive");
  test "a type cannot occur in such an input inside another function type's output" (fun () ->
      one_diagnostic "type Knot(make: fn() -> (fn(Knot) -> Bool cost time finite))\n"
        "package.not_strictly_positive");
  test "a type cannot occur in the input of a function type in such an input" (fun () ->
      one_diagnostic "type Knot(run: (fn(fn(Knot) -> Bool) -> Bool cost time finite))\n"
        "package.not_strictly_positive");
  test "a type cannot occur in such an input of an any type's associated type" (fun () ->
      one_diagnostic
        "trait Shown {\n\
        \  type Part\n\
         }\n\n\
         type Knot(shown: any Shown[Part = (fn(Knot) -> Bool cost time finite)])\n"
        "package.not_strictly_positive");
  test "a type cannot be the argument that a generic type puts in such an input" (fun () ->
      one_diagnostic
        "type Callback[Input](run: (fn(Input) -> Bool cost time finite))\n\n\
         type Wrap(next: Callback[Wrap])\n"
        "package.not_strictly_positive");
  test "a generic type may put another type's argument in such an input" (fun () ->
      fine
        "type Callback[Input](run: (fn(Input) -> Bool cost time finite))\n\n\
         type Wrap(next: Callback[Int64], rest: List[Wrap])\n");
  test "each type of a cycle through such an input is an error" (fun () ->
      expect
        [ "package.not_strictly_positive"; "package.not_strictly_positive" ]
        "type Left =\n\
        \  | Stop\n\
        \  | Go(right: List[Right])\n\n\
         type Right(run: (fn(Int64, Left) -> Bool cost time O(1)))\n");
  test "a type cannot occur in such an input through an associated type" (fun () ->
      one_diagnostic
        (shown ^ "impl Shown for Marker {\n  type Part = (fn(Knot) -> Bool cost time finite)\n}\n\n"
       ^ holder ^ "type Knot(held: Kept[Marker])\n")
        "package.not_strictly_positive");
  test "an associated type cannot put a type in such an input of itself" (fun () ->
      one_diagnostic
        (shown
       ^ "impl Shown for Marker {\n  type Part = (fn(Kept[Marker]) -> Bool cost time finite)\n}\n\n"
       ^ holder)
        "package.not_strictly_positive");
  test "an associated type cannot make a type contain itself in place" (fun () ->
      one_diagnostic
        (shown ^ "impl Shown for Marker {\n  type Part = Kept[Marker]\n}\n\n" ^ holder)
        "package.needs_indirect");
  test "an associated type may make a type contain itself in a collection" (fun () ->
      fine (shown ^ "impl Shown for Marker {\n  type Part = List[Kept[Marker]]\n}\n\n" ^ holder));
  test "only the impl that makes a type contain itself is an error" (fun () ->
      one_diagnostic
        (shown
       ^ "impl Shown for Marker {\n  type Part = (fn(Kept[Marker]) -> Bool cost time finite)\n}\n\n"
       ^ holder
       ^ "type Outer(inner: Kept[Marker])\n\n\
          type Other()\n\n\
          impl Shown for Other {\n\
         \  type Part = List[Kept[Marker]]\n\
          }\n")
        "package.not_strictly_positive");
  test "an associated type may put the associated type of its impl's parameter in such an input"
    (fun () ->
      fine
        (shown ^ holder
       ^ "type Box[Inner](inner: Inner)\n\n\
          impl Shown for Box[Inner: Shown] {\n\
         \  type Part = (fn(Kept[Inner]) -> Bool cost time finite)\n\
          }\n\n\
          impl Shown for Marker {\n\
         \  type Part = Int64\n\
          }\n\n\
          type Holder(held: Kept[Box[Box[Marker]]])\n"));
  test "an associated type cannot make a type contain itself through another impl's type" (fun () ->
      one_diagnostic
        (shown ^ holder
       ^ "type Box[Inner](inner: Inner)\n\n\
          impl Shown for Box[Inner: Shown] {\n\
         \  type Part = Kept[Inner]\n\
          }\n\n\
          impl Shown for Marker {\n\
         \  type Part = (fn(Kept[Box[Marker]]) -> Bool cost time finite)\n\
          }\n")
        "package.not_strictly_positive");
  test "the arguments of an impl's type are generic parameters, as the recursive type check assumes"
    (fun () ->
      one_diagnostic
        (shown ^ holder
       ^ "type Box[Inner](inner: Inner)\n\nimpl Shown for Box[Marker] {\n  type Part = Int64\n}\n")
        "resolve.hides_name");
  test "an associated type cannot make a type contain itself through another impl's definition"
    (fun () ->
      one_diagnostic
        (shown ^ holder
       ^ "type Box[Inner](inner: Inner)\n\n\
          impl Shown for Box[Inner: Shown] {\n\
         \  type Part = Inner.Part\n\
          }\n\n\
          impl Shown for Marker {\n\
         \  type Part = (fn(Kept[Box[Marker]]) -> Bool cost time finite)\n\
          }\n")
        "package.not_strictly_positive")

(* Across packages *)

let () =
  test "an impl overlaps an impl in a package it depends on" (fun () ->
      let database = Engine.context (Engine.create ()) in
      Database.load_standard (Engine.of_context database);
      Database.load_package (Engine.of_context database) ~name:{ owner = None; name = "lib" }
        ~dependencies:[]
        [
          ( module_of "lib::vector",
            "public type Vector[Element](items: List[Element])\n\n\
             impl Add[Element] for Vector[Element] {\n\
            \  type Output = Vector[Element]\n\
            \  fn add_is_defined(self, right: Element) -> Bool { true }\n\
            \  fn add(self, right: Element) -> Vector[Element] { todo }\n\
             }\n" );
        ];
      Database.load_package (Engine.of_context database) ~name:{ owner = None; name = "app" }
        ~dependencies:[ { package = { owner = None; name = "lib" }; capabilities = [] } ]
        [
          ( module_of "app::main",
            "use lib::vector\n\n\
             public type Meters(value: Int64)\n\n\
             impl Add[Meters] for vector::Vector[Element] {\n\
            \  type Output = vector::Vector[Element]\n\
            \  fn add_is_defined(self, right: Meters) -> Bool { true }\n\
            \  fn add(self, right: Meters) -> vector::Vector[Element] { todo }\n\
             }\n" );
        ];
      match codes (Package_checks.diagnostics database (module_of "app::main")) with
      | [ "package.overlapping_impls" ] -> ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
  test "an impl in another package cannot give a type another version of its method" (fun () ->
      let database = Engine.context (Engine.create ()) in
      Database.load_standard (Engine.of_context database);
      Database.load_package (Engine.of_context database) ~name:{ owner = None; name = "lib" }
        ~dependencies:[]
        [
          ( module_of "lib::counter",
            "public type Counter(count: Int64)\n\npublic fn Counter.label(self) -> Int64 { todo }\n"
          );
        ];
      Database.load_package (Engine.of_context database) ~name:{ owner = None; name = "app" }
        ~dependencies:[ { package = { owner = None; name = "lib" }; capabilities = [] } ]
        [
          ( module_of "app::main",
            "use lib::counter\n\n\
             trait Cleared {\n\
            \  fn label(mut self) -> Int64\n\
             }\n\n\
             impl Cleared for counter::Counter {\n\
            \  fn label(mut self) -> Int64 { todo }\n\
             }\n" );
        ];
      match codes (Package_checks.diagnostics database (module_of "app::main")) with
      | [ "package.method_name_clash" ] -> ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
  test "impls whose heads unify only through an infinite type do not overlap" (fun () ->
      fine
        "type Box[Element](value: Element)\n\n\
         trait Mark[Other] {}\n\n\
         impl Mark[Box[Element]] for Box[Element] {}\n\n\
         impl Mark[Element] for Box[Element] {}\n")
