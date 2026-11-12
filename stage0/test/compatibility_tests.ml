module Compatibility = Cli.Compatibility

(* Each test gives a module before and after a release, and states the
   compatibility changes. *)

open Harness
open Support

let changes ?(usize_bits = (32, 32)) before after =
  let state text bits =
    let database = setup [] in
    Database.load_package ~usize_bits:bits (Engine.of_context database)
      ~name:{ owner = None; name = "lib" } ~dependencies:[]
      [ (module_of "lib::shapes", text) ];
    database
  in
  Compatibility.compare
    ~before:(state before (fst usize_bits))
    ~after:(state after (snd usize_bits))
    { owner = None; name = "lib" }

let show (actual, _) =
  List.map
    (fun ({ path; change } : Compatibility.public_change) ->
      match change with
      | Breaks what -> Printf.sprintf "breaks: %s %s" (Path.show path) what
      | Grows what -> Printf.sprintf "grows: %s %s" (Path.show path) what)
    actual

let expect before after expected =
  let actual = show (changes before after) in
  if actual <> expected then
    fail "found [%s], expected [%s]" (String.concat "; " actual) (String.concat "; " expected)

let area body = Printf.sprintf "public fn area(side: Int64) -> Int64\n%s{\n  side\n}\n" body

let () =
  test "a body that changes is no change" (fun () ->
      expect "public fn sides() -> Int64 {\n  4\n}\n" "public fn sides() -> Int64 {\n  2 + 2\n}\n"
        []);
  test "a transparent function's body that changes breaks" (fun () ->
      let sides body =
        Printf.sprintf "public transparent fn sides() -> Int64\n  cost time O(1)\n{\n  %s\n}\n" body
      in
      expect (sides "4") (sides "2 + 2")
        [ "breaks: lib::shapes::sides changed its body, which callers' proofs read" ];
      expect (sides "4") (sides "4") []);
  test "a function that stops being transparent breaks, and one that starts grows" (fun () ->
      let sides modifier =
        Printf.sprintf "public%s fn sides() -> Int64\n  cost time O(1)\n{\n  4\n}\n" modifier
      in
      expect (sides " transparent") (sides "")
        [
          "breaks: lib::shapes::sides is no longer `transparent`, so callers' proofs cannot read \
           its body";
        ];
      expect (sides "") (sides " transparent") [ "grows: lib::shapes::sides is `transparent`" ]);
  test "a private or internal definition that changes is no change" (fun () ->
      expect "fn sides() -> Int64 {\n  4\n}\n\ninternal fn corners() -> Int64 {\n  4\n}\n"
        "fn sides(of: Int64) -> Int64 {\n  of\n}\n" []);
  test "a public definition that is added grows the package" (fun () ->
      expect "" "public fn sides() -> Int64 {\n  4\n}\n" [ "grows: lib::shapes::sides is new" ]);
  test "a public definition that is removed, or made private, breaks" (fun () ->
      let sides = "public fn sides() -> Int64 {\n  4\n}\n" in
      expect sides "" [ "breaks: lib::shapes::sides was removed or is no longer public" ];
      expect sides "fn sides() -> Int64 {\n  4\n}\n"
        [ "breaks: lib::shapes::sides was removed or is no longer public" ]);
  test "a changed parameter type, parameter name, or result breaks" (fun () ->
      let was = area "" in
      List.iter
        (fun now ->
          expect was now [ "breaks: lib::shapes::area changed its parameters or its result" ])
        [
          "public fn area(side: Int32) -> Int64 {\n  1\n}\n";
          "public fn area(edge: Int64) -> Int64 {\n  edge\n}\n";
          "public fn area(side: Int64) -> Int32 {\n  1\n}\n";
          "public fn area(side: Int64, depth: Int64) -> Int64 {\n  side\n}\n";
        ]);
  test "a parameter that gains a default grows, and one that loses it breaks" (fun () ->
      let with_default = "public fn area(side: Int64 = 1) -> Int64 {\n  side\n}\n" in
      expect (area "") with_default [ "grows: lib::shapes::area gained a default" ];
      expect with_default (area "")
        [ "breaks: lib::shapes::area changed its parameters or its result" ]);
  test "an added capability in uses breaks, and a removed one grows" (fun () ->
      let pure = "public fn stamp() -> Int64 {\n  1\n}\n"
      and timed = "public fn stamp() -> Int64\n  uses Clock\n{\n  1\n}\n" in
      expect pure timed [ "breaks: lib::shapes::stamp now uses `standard::capabilities::Clock`" ];
      expect timed pure [ "grows: lib::shapes::stamp uses fewer capabilities" ]);
  test "a requires that is added breaks, and one that is dropped grows" (fun () ->
      let guarded = area "  requires side > 0\n" in
      expect (area "") guarded
        [ "breaks: lib::shapes::area has a `requires` clause it did not have" ];
      expect guarded (area "") [ "grows: lib::shapes::area has fewer `requires` clauses" ]);
  test "an ensures that is added grows, and one that is dropped breaks" (fun () ->
      let promised = area "  ensures result == side\n" in
      expect (area "") promised [ "grows: lib::shapes::area has more `ensures` clauses" ];
      expect promised (area "") [ "breaks: lib::shapes::area lost an `ensures` clause" ]);
  test "a cost that is added grows, and one that is dropped breaks" (fun () ->
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
  test "a yielding method that could be pulled and no longer can breaks" (fun () ->
      let tree each =
        "public type Tree =\n\
        \  | Leaf\n\
        \  | indirect Node(left: Tree, value: Int64, right: Tree)\n\n\
         public fn Tree.each(self) yields Int64 {\n\
        \  match self {\n\
        \    Leaf => {}\n\
        \    Node(left, value, right) => {\n" ^ each ^ "    }\n  }\n}\n"
      in
      let own = tree "      yield value\n"
      and through =
        tree "      for item in left.each() {\n        yield item\n      }\n      yield value\n"
      in
      expect own through
        [ "breaks: lib::shapes::Tree.each can be pulled as a cursor in fewer cases" ];
      expect through own [ "grows: lib::shapes::Tree.each can be pulled as a cursor in more cases" ]);
  test "a type that made its fields visible keeps them" (fun () ->
      let square = "public type Square(side: Int64)\n" in
      expect square "public type Square(side: Int64, depth: Int64)\n"
        [ "breaks: lib::shapes::Square changed its fields or variants" ];
      expect square "public type Square(side: Int32)\n"
        [ "breaks: lib::shapes::Square changed its fields or variants" ];
      expect "public type Shape = Round | Flat\n" "public type Shape = Round | Flat | Bent\n"
        [ "breaks: lib::shapes::Shape changed its fields or variants" ]);
  test "an opaque type may change everything inside it" (fun () ->
      expect "public opaque type Square(side: Int64)\n"
        "public opaque type Square(width: Int32, height: Int32)\n" []);
  test "a type that hid its fields breaks, and one that shows them grows" (fun () ->
      let shown = "public type Square(side: Int64)\n"
      and hidden = "public opaque type Square(side: Int64)\n" in
      expect shown hidden [ "breaks: lib::shapes::Square hid its fields" ];
      expect hidden shown [ "grows: lib::shapes::Square made its fields visible" ]);
  test "a changed invariant breaks" (fun () ->
      expect "public type Square(side: Int64)\n  invariant side > 0\n"
        "public type Square(side: Int64)\n  invariant side >= 0\n"
        [ "breaks: lib::shapes::Square changed its invariant" ]);
  test "a derived trait that is dropped breaks, and one that is added grows" (fun () ->
      let plain = "public type Square(side: Int64)\n"
      and equal = "public type Square(side: Int64)\n  derives Equal\n" in
      expect equal plain [ "breaks: lib::shapes::Square no longer derives a trait" ];
      expect plain equal [ "grows: lib::shapes::Square derives another trait" ]);
  test "a trait gains only methods that have bodies" (fun () ->
      let was = "public trait Sided {\n  fn sides(self) -> Int64\n}\n" in
      expect was
        "public trait Sided {\n\
        \  fn sides(self) -> Int64\n\n\
        \  fn corners(self) -> Int64 {\n\
        \    self.sides()\n\
        \  }\n\
         }\n"
        [ "grows: lib::shapes::Sided gained the method `corners`" ];
      expect was "public trait Sided {\n  fn sides(self) -> Int64\n  fn corners(self) -> Int64\n}\n"
        [
          "breaks: lib::shapes::Sided gained the method `corners` without a default body, which \
           every `impl` must then define";
        ];
      expect was "public trait Sided {\n  fn corners(self) -> Int64\n}\n"
        [
          "breaks: lib::shapes::Sided no longer has the method `sides`";
          "breaks: lib::shapes::Sided gained the method `corners` without a default body, which \
           every `impl` must then define";
        ]);
  test "a capability's method that changes breaks" (fun () ->
      expect "public capability Ledger {\n  fn record(amount: Int64)\n}\n"
        "public capability Ledger {\n  fn record(amount: Int32)\n}\n"
        [ "breaks: lib::shapes::Ledger its method `record` changed its parameters or its result" ]);
  test "a constant keeps its type and its value" (fun () ->
      let sides = "public let sides: Int64 = 4\n" in
      expect sides "public let sides: Int64 = 5\n"
        [ "breaks: lib::shapes::sides changed its value" ];
      expect sides "public let sides: Int32 = 4\n" [ "breaks: lib::shapes::sides changed its type" ];
      expect sides "public let sides: Int64 = 2 + 2\n" []);
  test "an impl that is removed breaks, and one that is added grows" (fun () ->
      let square = "public type Square(side: Int64)\n" in
      let with_impl =
        square ^ "\nimpl Default for Square {\n  fn default() -> Square {\n    Square(1)\n  }\n}\n"
      in
      (match show (changes with_impl square) with
      | [ actual ] when Substring.contains actual "was removed: the `impl` of" -> ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
      match show (changes square with_impl) with
      | [ actual ] when Substring.contains actual "is new: the `impl` of" -> ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
  test "an impl whose associated capability set gains a capability breaks" (fun () ->
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
        when Substring.find actual "breaks:" = Some 0
             && Substring.contains actual "added `Clock` to its `Uses`" ->
          ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
      (match show (changes (feed "  capability Uses = Clock\n") (feed "")) with
      | [ actual ]
        when Substring.find actual "grows:" = Some 0
             && Substring.contains actual "removed capabilities from its `Uses`" ->
          ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
      expect (feed "  capability Uses = Clock\n") (feed "  capability Uses = Clock\n") []);
  test "a trait that loses an associated capability set breaks" (fun () ->
      let feed member =
        Printf.sprintf "public trait Feed {\n%s  fn pull(self) -> Int64\n}\n" member
      in
      expect (feed "  capability Uses\n") (feed "")
        [ "breaks: lib::shapes::Feed lost an associated capability set" ];
      expect (feed "") (feed "  capability Uses\n")
        [ "grows: lib::shapes::Feed gained an associated capability set" ]);
  test "a package that ran on every target and now runs only on 64-bit ones is told" (fun () ->
      if not (snd (changes ~usize_bits:(32, 64) "" "")) then fail "not told";
      if snd (changes ~usize_bits:(64, 64) "" "") || snd (changes ~usize_bits:(64, 32) "" "") then
        fail "told of a package that does not narrow")
