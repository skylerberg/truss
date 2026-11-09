(* The tests of the checks across a package. See TYPECHECKER.md, "Traits
   and impls across a package" and "Recursive types". *)

open Harness
open Support

let check database module_ =
  Resolve.diagnostics database module_
  @ Interface.diagnostics database module_
  @ Package_checks.file_diagnostics database module_

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

let () = finish ()
