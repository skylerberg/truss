module Compatibility = Cli.Compatibility

let changes ?(modules = []) before after =
  let package : Path.package = { owner = None; name = "lib" } in
  let state text = Support.database (Support.setup (("lib::shapes", text) :: modules)) in
  Compatibility.compare ~before:(state before) ~after:(state after) package

let show actual =
  List.map
    (fun ({ path; change } : Compatibility.public_change) ->
      match change with
      | Breaks reason -> Printf.sprintf "breaks: %s %s" (Path.show path) reason
      | Grows addition -> Printf.sprintf "grows: %s %s" (Path.show path) addition)
    actual

let expect ?modules before after expected =
  let actual = show (changes ?modules before after) in
  if actual <> expected then
    Harness.fail "found [%s], expected [%s]" (String.concat "; " actual)
      (String.concat "; " expected)

let area body = Printf.sprintf "public fn area(side: Int64) -> Int64\n%s{\n  side\n}\n" body

let () =
  Harness.test "a body that changes is no change" (fun () ->
      expect Fixtures.Compatibility.sides Fixtures.Compatibility.sides_returning_two_plus_two []);
  Harness.test "a private or internal definition that changes is no change" (fun () ->
      expect Fixtures.Compatibility.private_sides_and_internal_corners
        Fixtures.Compatibility.private_sides_taking_a_count []);
  Harness.test "a public definition that is added grows the package" (fun () ->
      expect "" Fixtures.Compatibility.sides [ "grows: lib::shapes::sides is new" ]);
  Harness.test "a public definition that is removed, or made private, breaks" (fun () ->
      let sides = Fixtures.Compatibility.sides in
      expect sides "" [ "breaks: lib::shapes::sides was removed or is no longer public" ];
      expect sides Fixtures.Compatibility.private_sides
        [ "breaks: lib::shapes::sides was removed or is no longer public" ]);
  Harness.test "a changed parameter type, parameter name, or result breaks" (fun () ->
      let was = area "" in
      List.iter
        (fun now ->
          expect was now [ "breaks: lib::shapes::area changed its parameters or its result" ])
        [
          Fixtures.Compatibility.area_taking_an_int32_side;
          Fixtures.Compatibility.area_taking_an_edge;
          Fixtures.Compatibility.area_returning_int32;
          Fixtures.Compatibility.area_taking_a_side_and_a_depth;
        ]);
  Harness.test "a parameter that gains a default grows, and one that loses it breaks" (fun () ->
      let with_default = Fixtures.Compatibility.area_with_a_default_side in
      expect (area "") with_default [ "grows: lib::shapes::area gained a default" ];
      expect with_default (area "")
        [ "breaks: lib::shapes::area changed its parameters or its result" ]);
  Harness.test "an added capability in uses breaks, and a removed one grows" (fun () ->
      let pure = Fixtures.Compatibility.stamp_using_nothing
      and timed = Fixtures.Compatibility.stamp_using_clock in
      expect pure timed [ "breaks: lib::shapes::stamp now uses `standard::capabilities::Clock`" ];
      expect timed pure [ "grows: lib::shapes::stamp uses fewer capabilities" ]);
  Harness.test "a requires that is added breaks, and one that is dropped grows" (fun () ->
      let guarded = area "  requires side > 0\n" in
      expect (area "") guarded
        [ "breaks: lib::shapes::area has a `requires` clause it did not have" ];
      expect guarded (area "") [ "grows: lib::shapes::area has fewer `requires` clauses" ]);
  Harness.test "an ensures that is added grows, and one that is dropped breaks" (fun () ->
      let promised = area "  ensures result == side\n" in
      expect (area "") promised [ "grows: lib::shapes::area has more `ensures` clauses" ];
      expect promised (area "") [ "breaks: lib::shapes::area lost an `ensures` clause" ]);
  Harness.test "a cost that is added grows, and one that is dropped breaks" (fun () ->
      let bounded = area "  cost time O(1)\n" in
      expect (area "") bounded
        [
          "grows: lib::shapes::area promises to terminate";
          "grows: lib::shapes::area has more `cost` clauses";
        ];
      expect bounded (area "")
        [
          "breaks: lib::shapes::area no longer promises to terminate";
          "breaks: lib::shapes::area lost a `cost` clause";
        ]);
  Harness.test "a type that made its fields visible keeps them" (fun () ->
      let square = "public type Square(side: Int64)\n" in
      expect square "public type Square(side: Int64, depth: Int64)\n"
        [ "breaks: lib::shapes::Square changed its fields or variants" ];
      expect square "public type Square(side: Int32)\n"
        [ "breaks: lib::shapes::Square changed its fields or variants" ];
      expect "public type Shape = Round | Flat\n" "public type Shape = Round | Flat | Bent\n"
        [ "breaks: lib::shapes::Shape changed its fields or variants" ]);
  Harness.test "an opaque type may change everything inside it" (fun () ->
      expect "public opaque type Square(side: Int64)\n"
        "public opaque type Square(width: Int32, height: Int32)\n" []);
  Harness.test "a type that hid its fields breaks, and one that shows them grows" (fun () ->
      let shown = "public type Square(side: Int64)\n"
      and hidden = "public opaque type Square(side: Int64)\n" in
      expect shown hidden [ "breaks: lib::shapes::Square hid its fields" ];
      expect hidden shown [ "grows: lib::shapes::Square made its fields visible" ]);
  Harness.test "a changed invariant breaks" (fun () ->
      expect "public type Square(side: Int64)\n  invariant side > 0\n"
        "public type Square(side: Int64)\n  invariant side >= 0\n"
        [ "breaks: lib::shapes::Square changed its invariant" ]);
  Harness.test "invariants written in another order are no change" (fun () ->
      expect "public type Square(side: Int64)\n  invariant side > 0\n  invariant side < 100\n"
        "public type Square(side: Int64)\n  invariant side < 100\n  invariant side > 0\n" []);
  Harness.test "a derived trait that is dropped breaks, and one that is added grows" (fun () ->
      let plain = "public type Square(side: Int64)\n"
      and equal = "public type Square(side: Int64)\n  derives Equal\n" in
      expect equal plain [ "breaks: lib::shapes::Square no longer derives a trait" ];
      expect plain equal [ "grows: lib::shapes::Square derives another trait" ]);
  Harness.test "a trait gains only methods that have bodies" (fun () ->
      let was = Fixtures.Compatibility.sided_trait_with_only_sides in
      expect was Fixtures.Compatibility.sided_trait_with_default_corners
        [ "grows: lib::shapes::Sided gained the method `corners`" ];
      expect was Fixtures.Compatibility.sided_trait_with_required_sides_and_corners
        [
          "breaks: lib::shapes::Sided gained the method `corners` without a default body, which \
           every `impl` must then define";
        ];
      expect was Fixtures.Compatibility.sided_trait_with_only_corners
        [
          "breaks: lib::shapes::Sided no longer has the method `sides`";
          "breaks: lib::shapes::Sided gained the method `corners` without a default body, which \
           every `impl` must then define";
        ]);
  Harness.test "a capability's method that changes breaks" (fun () ->
      expect Fixtures.Compatibility.ledger_recording_int64
        Fixtures.Compatibility.ledger_recording_int32
        [ "breaks: lib::shapes::Ledger its method `record` changed its parameters or its result" ]);
  Harness.test "a constant keeps its type and its value" (fun () ->
      let sides = "public let sides: Int64 = 4\n" in
      expect sides "public let sides: Int64 = 5\n"
        [ "breaks: lib::shapes::sides changed its value" ];
      expect sides "public let sides: Int32 = 4\n" [ "breaks: lib::shapes::sides changed its type" ];
      expect sides "public let sides: Int64 = 2 + 2\n" []);
  Harness.test "an impl that is removed breaks, and one that is added grows" (fun () ->
      let square = "public type Square(side: Int64)\n" in
      let with_impl = square ^ Fixtures.Compatibility.default_impl_for_square in
      (match show (changes with_impl square) with
      | [ actual ] when Substring.contains actual "was removed: the `impl` of" -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
      match show (changes square with_impl) with
      | [ actual ] when Substring.contains actual "is new: the `impl` of" -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "an impl whose associated capability set gains a capability breaks" (fun () ->
      let feed uses =
        Printf.sprintf
          "public trait Feed {\n\
          \  capability Uses\n\
          \  fn pull(self) -> Int64\n\
          \    uses Self.Uses\n\
           }\n\n\
           public type Gauge(last: Int64)\n\n\
           impl Feed for Gauge {\n\
           %s  fn pull(self) -> Int64 {\n\
          \    self.last\n\
          \  }\n\
           }\n"
          uses
      in
      let gains = show (changes (feed "") (feed "  capability Uses = Clock\n")) in
      (match gains with
      | [ actual ]
        when Substring.For_testing.find actual "breaks:" = Some 0
             && Substring.contains actual "added `Clock` to its `Uses`" ->
          ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
      (match show (changes (feed "  capability Uses = Clock\n") (feed "")) with
      | [ actual ]
        when Substring.For_testing.find actual "grows:" = Some 0
             && Substring.contains actual "removed capabilities from its `Uses`" ->
          ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
      expect (feed "  capability Uses = Clock\n") (feed "  capability Uses = Clock\n") []);
  Harness.test "a trait that loses an associated capability set breaks" (fun () ->
      let feed member =
        Printf.sprintf "public trait Feed {\n%s  fn pull(self) -> Int64\n}\n" member
      in
      expect (feed "  capability Uses\n") (feed "")
        [ "breaks: lib::shapes::Feed lost an associated capability set" ];
      expect (feed "") (feed "  capability Uses\n")
        [ "grows: lib::shapes::Feed gained an associated capability set" ])

let sized law =
  Printf.sprintf
    "public trait Sized {\n\
    \  fn size(self) -> Int64\n\
    \    cost time finite\n\n\
    \  law bounded(value: Self) {\n\
     %s  }\n\
     }\n"
    law

let () =
  Harness.test "a requires that only gains parentheses is no change" (fun () ->
      expect (area "  requires side > 0\n") (area "  requires (side > 0)\n") []);
  Harness.test "a dropped requires leaves the ensures after it unchanged" (fun () ->
      expect
        (area "  requires side > 0\n  ensures result == side\n")
        (area "  ensures result == side\n")
        [ "grows: lib::shapes::area has fewer `requires` clauses" ]);
  Harness.test "a requires whose name another use makes refer elsewhere breaks" (fun () ->
      let modules =
        [
          ("lib::one::limits", "public let bound: Int64 = 10\n");
          ("lib::two::limits", "public let bound: Int64 = 20\n");
        ]
      in
      let guarded imported =
        Printf.sprintf "use lib::%s::limits\n\n%s" imported
          (area "  requires side < limits::bound\n")
      in
      expect ~modules (guarded "one") (guarded "two")
        [ "breaks: lib::shapes::area has a `requires` clause it did not have" ]);
  Harness.test "a law whose body changes breaks" (fun () ->
      expect (sized "    value.size() >= 0\n") (sized "    value.size() >= 1\n")
        [ "breaks: lib::shapes::Sized changed its laws" ]);
  Harness.test "a law that renames a binder of its body is no change" (fun () ->
      expect
        (sized "    let measured = value.size()\n    measured >= 0\n")
        (sized "    let counted = value.size()\n    counted >= 0\n")
        []);
  Harness.test "a constant the evaluator cannot compute keeps its written value" (fun () ->
      let name = "public let name: String = \"square\"\n" in
      expect name "public let name: String = \"cube\"\n"
        [ "breaks: lib::shapes::name changed its value" ];
      expect name "public let name: String = (\"square\")\n" [])

let () =
  Harness.test "an impl moved to another module of its package is no change" (fun () ->
      let package : Path.package = { owner = None; name = "lib" } in
      let square = "public type Square(side: Int64)\n" in
      let moved =
        "use lib::shapes\n\n\
         impl Default for shapes::Square {\n\
        \  fn default() -> shapes::Square {\n\
        \    shapes::Square(1)\n\
        \  }\n\
         }\n"
      in
      let state files = Support.database (Support.setup files) in
      match
        show
          (Compatibility.compare
             ~before:
               (state
                  [
                    ("lib::shapes", square ^ Fixtures.Compatibility.default_impl_for_square);
                    ("lib::extra", "");
                  ])
             ~after:(state [ ("lib::shapes", square); ("lib::extra", moved) ])
             package)
      with
      | [] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual))
