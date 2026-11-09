(* The tests of the checks across a package. See TYPECHECKER.md, "Traits
   and impls across a package" and "Recursive types". *)

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
              \  fn add(self, right: Element) -> Vector[Element] { todo }\n\
               }\n\n\
               impl Add[Int64] for Vector[Element] {\n\
              \  type Output = Vector[Element]\n\
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
              "fn grow[Element](value: own Element) -> Int64 {\n  grow(Some(value))\n}\n" );
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
      | found -> fail "found [%s]" (String.concat "; " found))

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
      | found -> fail "found [%s]" (String.concat "; " found));
  test "a generic type that swaps its arguments is not growing" (fun () ->
      fine "type Swap[First, Second] =\n  | Stop\n  | indirect Next(next: Swap[Second, First])\n")

(* Across packages *)

let () =
  test "an impl overlaps an impl in a package it depends on" (fun () ->
      let database = Engine.context (Engine.create ()) in
      Database.load_standard (Engine.of_context database);
      Database.load_package (Engine.of_context database) ~name:"lib" ~dependencies:[]
        [
          ( module_of "lib::vector",
            "public type Vector[Element](items: List[Element])\n\n\
             impl Add[Element] for Vector[Element] {\n\
            \  type Output = Vector[Element]\n\
            \  fn add(self, right: Element) -> Vector[Element] { todo }\n\
             }\n" );
        ];
      Database.load_package (Engine.of_context database) ~name:"app"
        ~dependencies:[ { package = "lib"; capabilities = [] } ]
        [
          ( module_of "app::main",
            "use lib::vector\n\n\
             public type Meters(value: Int64)\n\n\
             impl Add[Meters] for vector::Vector[Element] {\n\
            \  type Output = vector::Vector[Element]\n\
            \  fn add(self, right: Meters) -> vector::Vector[Element] { todo }\n\
             }\n" );
        ];
      match codes (Package_checks.diagnostics database (module_of "app::main")) with
      | [ "package.overlapping_impls" ] -> ()
      | found -> fail "found [%s]" (String.concat "; " found));
  test "impls whose heads unify only through an infinite type do not overlap" (fun () ->
      fine
        "type Box[Element](value: Element)\n\n\
         trait Mark[Other] {}\n\n\
         impl Mark[Box[Element]] for Box[Element] {}\n\n\
         impl Mark[Element] for Box[Element] {}\n")

let () = finish ()
