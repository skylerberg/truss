(* The tests of whether a release keeps what the one before it offered.
   Each gives a module as it was and as it is, and states what changed. *)

open Harness
open Support

let changes ?(usize_bits = (32, 32)) before after =
  let state text bits =
    let database = setup [] in
    Database.load_package ~usize_bits:bits (Engine.of_context database) ~name:"lib" ~dependencies:[]
      [ (module_of "lib::shapes", text) ];
    database
  in
  Compatibility.compare
    ~before:(state before (fst usize_bits))
    ~after:(state after (snd usize_bits))
    "lib"

let show (found, _) =
  List.map
    (fun ({ path; change } : Compatibility.found) ->
      match change with
      | Breaks what -> Printf.sprintf "breaks: %s %s" (Path.show path) what
      | Grows what -> Printf.sprintf "grows: %s %s" (Path.show path) what)
    found

let expect before after expected =
  let found = show (changes before after) in
  if found <> expected then
    fail "found [%s], expected [%s]" (String.concat "; " found) (String.concat "; " expected)

let area body = Printf.sprintf "public fn area(side: Int64) -> Int64\n%s{\n  side\n}\n" body

let () =
  test "a body that changes is no change" (fun () ->
      expect "public fn sides() -> Int64 {\n  4\n}\n" "public fn sides() -> Int64 {\n  2 + 2\n}\n"
        []);
  test "a private or internal definition that changes is no change" (fun () ->
      expect "fn sides() -> Int64 {\n  4\n}\n\ninternal fn corners() -> Int64 {\n  4\n}\n"
        "fn sides(of: Int64) -> Int64 {\n  of\n}\n" []);
  test "a public definition that is added grows the package" (fun () ->
      expect "" "public fn sides() -> Int64 {\n  4\n}\n" [ "grows: lib::shapes::sides is new" ]);
  test "a public definition that is taken away, or made private, breaks" (fun () ->
      let sides = "public fn sides() -> Int64 {\n  4\n}\n" in
      expect sides "" [ "breaks: lib::shapes::sides is gone, or is no longer public" ];
      expect sides "fn sides() -> Int64 {\n  4\n}\n"
        [ "breaks: lib::shapes::sides is gone, or is no longer public" ]);
  test "another parameter type, parameter name, or result breaks" (fun () ->
      let was = area "" in
      List.iter
        (fun now ->
          expect was now [ "breaks: lib::shapes::area has other parameters or another result" ])
        [
          "public fn area(side: Int32) -> Int64 {\n  1\n}\n";
          "public fn area(edge: Int64) -> Int64 {\n  edge\n}\n";
          "public fn area(side: Int64) -> Int32 {\n  1\n}\n";
          "public fn area(side: Int64, depth: Int64) -> Int64 {\n  side\n}\n";
        ]);
  test "a parameter that gains a default grows, and one that loses it breaks" (fun () ->
      let with_default = "public fn area(side: Int64 = 1) -> Int64 {\n  side\n}\n" in
      expect (area "") with_default [ "grows: lib::shapes::area has a default it did not" ];
      expect with_default (area "")
        [ "breaks: lib::shapes::area has other parameters or another result" ]);
  test "a capability more in uses breaks, and one fewer grows" (fun () ->
      let pure = "public fn stamp() -> Int64 {\n  1\n}\n"
      and timed = "public fn stamp() -> Int64\n  uses Clock\n{\n  1\n}\n" in
      expect pure timed
        [ "breaks: lib::shapes::stamp uses `standard::capabilities::Clock`, which it did not" ];
      expect timed pure [ "grows: lib::shapes::stamp uses fewer capabilities" ]);
  test "a requires that is added breaks, and one that is dropped grows" (fun () ->
      let guarded = area "  requires side > 0\n" in
      expect (area "") guarded [ "breaks: lib::shapes::area requires what it did not" ];
      expect guarded (area "") [ "grows: lib::shapes::area requires less" ]);
  test "an ensures that is added grows, and one that is dropped breaks" (fun () ->
      let promised = area "  ensures result == side\n" in
      expect (area "") promised [ "grows: lib::shapes::area ensures more" ];
      expect promised (area "") [ "breaks: lib::shapes::area no longer ensures what it did" ]);
  test "a cost that is added grows, and one that is dropped breaks" (fun () ->
      let bounded = area "  cost time O(1)\n" in
      expect (area "") bounded
        [
          "grows: lib::shapes::area promises to end";
          "grows: lib::shapes::area promises a cost more";
        ];
      expect bounded (area "")
        [
          "breaks: lib::shapes::area no longer promises to end";
          "breaks: lib::shapes::area no longer promises a cost it did";
        ]);
  test "a type that shows its fields keeps them" (fun () ->
      let square = "public type Square(side: Int64)\n" in
      expect square "public type Square(side: Int64, depth: Int64)\n"
        [ "breaks: lib::shapes::Square has other fields or variants" ];
      expect square "public type Square(side: Int32)\n"
        [ "breaks: lib::shapes::Square has other fields or variants" ];
      expect "public type Shape = Round | Flat\n" "public type Shape = Round | Flat | Bent\n"
        [ "breaks: lib::shapes::Shape has other fields or variants" ]);
  test "an opaque type may change everything inside it" (fun () ->
      expect "public opaque type Square(side: Int64)\n"
        "public opaque type Square(width: Int32, height: Int32)\n" []);
  test "a type that hides fields it showed breaks, and one that shows them grows" (fun () ->
      let shown = "public type Square(side: Int64)\n"
      and hidden = "public opaque type Square(side: Int64)\n" in
      expect shown hidden [ "breaks: lib::shapes::Square hides fields it showed" ];
      expect hidden shown [ "grows: lib::shapes::Square shows its fields" ]);
  test "another invariant breaks" (fun () ->
      expect "public type Square(side: Int64)\n  invariant side > 0\n"
        "public type Square(side: Int64)\n  invariant side >= 0\n"
        [ "breaks: lib::shapes::Square has another invariant" ]);
  test "a derived trait that is dropped breaks, and one that is added grows" (fun () ->
      let plain = "public type Square(side: Int64)\n"
      and equal = "public type Square(side: Int64)\n  derives Equal\n" in
      expect equal plain [ "breaks: lib::shapes::Square no longer derives a trait it did" ];
      expect plain equal [ "grows: lib::shapes::Square derives a trait more" ]);
  test "a trait gains only methods that have bodies" (fun () ->
      let was = "public trait Sided {\n  fn sides(self) -> Int64\n}\n" in
      expect was
        "public trait Sided {\n\
        \  fn sides(self) -> Int64\n\n\
        \  fn corners(self) -> Int64 {\n\
        \    self.sides()\n\
        \  }\n\
         }\n"
        [ "grows: lib::shapes::Sided has the method `corners`" ];
      expect was "public trait Sided {\n  fn sides(self) -> Int64\n  fn corners(self) -> Int64\n}\n"
        [
          "breaks: lib::shapes::Sided has the method `corners` without a body, which every `impl` \
           of it would have to add";
        ];
      expect was "public trait Sided {\n  fn corners(self) -> Int64\n}\n"
        [
          "breaks: lib::shapes::Sided no longer has the method `sides`";
          "breaks: lib::shapes::Sided has the method `corners` without a body, which every `impl` \
           of it would have to add";
        ]);
  test "a capability's method that changes breaks" (fun () ->
      expect "public capability Ledger {\n  fn record(amount: Int64)\n}\n"
        "public capability Ledger {\n  fn record(amount: Int32)\n}\n"
        [ "breaks: lib::shapes::Ledger its method `record` has other parameters or another result" ]);
  test "a constant keeps its type and its value" (fun () ->
      let sides = "public let sides: Int64 = 4\n" in
      expect sides "public let sides: Int64 = 5\n"
        [ "breaks: lib::shapes::sides has another value" ];
      expect sides "public let sides: Int32 = 4\n" [ "breaks: lib::shapes::sides has another type" ];
      expect sides "public let sides: Int64 = 2 + 2\n" []);
  test "an impl that is taken away breaks, and one that is added grows" (fun () ->
      let square = "public type Square(side: Int64)\n" in
      let with_impl =
        square ^ "\nimpl Default for Square {\n  fn default() -> Square {\n    Square(1)\n  }\n}\n"
      in
      (match show (changes with_impl square) with
      | [ found ] when Documents.find found "is gone: the `impl` of" ~occurrence:1 >= 0 -> ()
      | found -> fail "found [%s]" (String.concat "; " found));
      match show (changes square with_impl) with
      | [ found ] when Documents.find found "is new: the `impl` of" ~occurrence:1 >= 0 -> ()
      | found -> fail "found [%s]" (String.concat "; " found));
  test "a package that ran on every target and now runs only on 64-bit ones is told" (fun () ->
      if not (snd (changes ~usize_bits:(32, 64) "" "")) then fail "not told";
      if snd (changes ~usize_bits:(64, 64) "" "") || snd (changes ~usize_bits:(64, 32) "" "") then
        fail "told of a package that does not narrow")

let () = finish ()
