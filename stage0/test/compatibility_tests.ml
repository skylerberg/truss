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
      | Breaks reason -> Printf.sprintf "breaks: %s %s" (Path.show path) reason
      | Grows addition -> Printf.sprintf "grows: %s %s" (Path.show path) addition)
    actual

let expect before after expected =
  let actual = show (changes before after) in
  if actual <> expected then
    fail "found [%s], expected [%s]" (String.concat "; " actual) (String.concat "; " expected)

let area body = Printf.sprintf "public fn area(side: Int64) -> Int64\n%s{\n  side\n}\n" body

let () =
  test "a body that changes is no change" (fun () ->
      expect Fixtures.Compatibility.body_that_changes_is_no_change
        Fixtures.Compatibility.body_that_changes_is_no_change_2 []);
  test "a transparent function's body that changes breaks" (fun () ->
      let sides body =
        Printf.sprintf "public transparent fn sides() -> Int64\n  cost time O(1)\n{\n  %s\n}\n" body
      in
      expect (sides "4") (sides "2 + 2")
        [ "breaks: lib::shapes::sides has another body, which callers' proofs read" ];
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
      expect Fixtures.Compatibility.private_or_internal_definition_that_changes_is_no
        Fixtures.Compatibility.private_or_internal_definition_that_changes_is_no_2 []);
  test "a public definition that is added grows the package" (fun () ->
      expect "" Fixtures.Compatibility.public_definition_that_is_added_grows_the_package
        [ "grows: lib::shapes::sides is new" ]);
  test "a public definition that is taken away, or made private, breaks" (fun () ->
      let sides = Fixtures.Compatibility.sides in
      expect sides "" [ "breaks: lib::shapes::sides is gone, or is no longer public" ];
      expect sides Fixtures.Compatibility.public_definition_that_is_taken_away_or_made
        [ "breaks: lib::shapes::sides is gone, or is no longer public" ]);
  test "another parameter type, parameter name, or result breaks" (fun () ->
      let was = area "" in
      List.iter
        (fun now ->
          expect was now [ "breaks: lib::shapes::area has other parameters or another result" ])
        [
          Fixtures.Compatibility.another_parameter_type_parameter_name_or_result;
          Fixtures.Compatibility.another_parameter_type_parameter_name_or_result_2;
          Fixtures.Compatibility.another_parameter_type_parameter_name_or_result_3;
          Fixtures.Compatibility.another_parameter_type_parameter_name_or_result_4;
        ]);
  test "a parameter that gains a default grows, and one that loses it breaks" (fun () ->
      let with_default = Fixtures.Compatibility.with_default in
      expect (area "") with_default [ "grows: lib::shapes::area has a default it did not" ];
      expect with_default (area "")
        [ "breaks: lib::shapes::area has other parameters or another result" ]);
  test "a capability more in uses breaks, and one fewer grows" (fun () ->
      let pure = Fixtures.Compatibility.pure
      and timed = Fixtures.Compatibility.capability_more_in_uses_breaks_and_one_fewer_grows in
      expect pure timed
        [ "breaks: lib::shapes::stamp uses `standard::capabilities::Clock`, which it did not" ];
      expect timed pure [ "grows: lib::shapes::stamp uses fewer capabilities" ]);
  test "a requires that is added breaks, and one that is dropped grows" (fun () ->
      let guarded = area "  requires side > 0\n" in
      expect (area "") guarded [ "breaks: lib::shapes::area requires more" ];
      expect guarded (area "") [ "grows: lib::shapes::area requires less" ]);
  test "an ensures that is added grows, and one that is dropped breaks" (fun () ->
      let promised = area "  ensures result == side\n" in
      expect (area "") promised [ "grows: lib::shapes::area ensures more" ];
      expect promised (area "") [ "breaks: lib::shapes::area ensures less" ]);
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
      expect own through [ "breaks: lib::shapes::Tree.each can no longer be pulled as it could" ];
      expect through own [ "grows: lib::shapes::Tree.each can be pulled where it could not" ]);
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
      let was = Fixtures.Compatibility.was in
      expect was Fixtures.Compatibility.trait_gains_only_methods_that_have_bodies
        [ "grows: lib::shapes::Sided has the method `corners`" ];
      expect was Fixtures.Compatibility.trait_gains_only_methods_that_have_bodies_2
        [
          "breaks: lib::shapes::Sided has the method `corners` without a body, which every `impl` \
           of it would have to add";
        ];
      expect was Fixtures.Compatibility.trait_gains_only_methods_that_have_bodies_3
        [
          "breaks: lib::shapes::Sided no longer has the method `sides`";
          "breaks: lib::shapes::Sided has the method `corners` without a body, which every `impl` \
           of it would have to add";
        ]);
  test "a capability's method that changes breaks" (fun () ->
      expect Fixtures.Compatibility.capabilitys_method_that_changes_breaks
        Fixtures.Compatibility.capabilitys_method_that_changes_breaks_2
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
        square ^ Fixtures.Compatibility.impl_that_is_taken_away_breaks_and_one_that_is
      in
      (match show (changes with_impl square) with
      | [ actual ] when Substring.contains actual "is gone: the `impl` of" -> ()
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
             && Substring.contains actual "has `Clock` in its `Uses`, which it did not" ->
          ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
      (match show (changes (feed "  capability Uses = Clock\n") (feed "")) with
      | [ actual ]
        when Substring.find actual "grows:" = Some 0
             && Substring.contains actual "has fewer capabilities in its `Uses`" ->
          ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
      expect (feed "  capability Uses = Clock\n") (feed "  capability Uses = Clock\n") []);
  test "a trait that loses an associated capability set breaks" (fun () ->
      let feed member =
        Printf.sprintf "public trait Feed {\n%s  fn pull(self) -> Int64\n}\n" member
      in
      expect (feed "  capability Uses\n") (feed "")
        [ "breaks: lib::shapes::Feed no longer has an associated capability set it did" ];
      expect (feed "") (feed "  capability Uses\n")
        [ "grows: lib::shapes::Feed has an associated capability set more" ]);
  test "a package that ran on every target and now runs only on 64-bit ones is told" (fun () ->
      if not (snd (changes ~usize_bits:(32, 64) "" "")) then fail "not told";
      if snd (changes ~usize_bits:(64, 64) "" "") || snd (changes ~usize_bits:(64, 32) "" "") then
        fail "told of a package that does not narrow")
