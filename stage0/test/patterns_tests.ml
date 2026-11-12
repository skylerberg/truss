module Patterns = Type_checker.For_testing.Patterns

(* The tests of exhaustiveness and reachability. *)

open Harness
open Support

let check database module_ =
  Resolve.diagnostics database module_
  @ Interface.diagnostics database module_
  @ Infer.diagnostics database module_
  @ Patterns.diagnostics database module_

let one_diagnostic = one_diagnostic ~check
let fine text = no_diagnostics ~check [ ("app::main", text) ]
let priority = "type Priority =\n  | Low\n  | Normal\n  | Urgent(deadline: Instant)\n\n"

let message text =
  let database = setup [ ("app::main", text) ] in
  match check database (module_of "app::main") with
  | [ diagnostic ] -> diagnostic.message
  | found -> failwith (Printf.sprintf "%d diagnostics" (List.length found))

let () =
  test "a missing case is named" (fun () ->
      let text =
        priority
        ^ "fn f(found: Option[Priority]) -> Int64 {\n\
          \  match found {\n\
          \    Some(Low) => 1\n\
          \    Some(Normal) => 2\n\
          \    None => 3\n\
          \  }\n\
           }\n"
      in
      let found = message text in
      let expected = "`Some(Urgent(_))` is not covered" in
      if not (Substring.contains found expected) then fail "message %S" found);
  test "a missing case's fix adds an arm with todo" (fun () ->
      one_diagnostic "fn f(ready: Bool) -> Int64 {\n  match ready {\n    true => 1\n  }\n}\n"
        "patterns.not_covered"
        ~fixed:
          "fn f(ready: Bool) -> Int64 {\n\
          \  match ready {\n\
          \    true => 1\n\
          \    false => todo\n\
          \  }\n\
           }\n");
  test "an arm earlier arms cover is an error with a fix that deletes it" (fun () ->
      one_diagnostic
        "fn f(found: Option[Int64]) -> Int64 {\n\
        \  match found {\n\
        \    Some(value) => value\n\
        \    None => 0\n\
        \    _ => 1\n\
        \  }\n\
         }\n"
        "patterns.unreachable_arm"
        ~fixed:
          "fn f(found: Option[Int64]) -> Int64 {\n\
          \  match found {\n\
          \    Some(value) => value\n\
          \    None => 0\n\
          \  }\n\
           }\n");
  test "an alternative the alternatives before it cover is an error" (fun () ->
      one_diagnostic
        "fn f(found: Option[Int64]) -> Int64 {\n\
        \  match found {\n\
        \    None | None => 0\n\
        \    Some(value) => value\n\
        \  }\n\
         }\n"
        "patterns.unreachable_alternative");
  test "an arm with a guard does not cover its pattern" (fun () ->
      one_diagnostic
        "fn f(count: Int64) -> Int64 {\n  match count {\n    value if value > 0 => 1\n  }\n}\n"
        "patterns.not_covered");
  test "integer ranges that cover the type are exhaustive" (fun () ->
      fine
        "fn f(byte: UInt8) -> Int64 {\n\
        \  match byte {\n\
        \    0..=127 => 1\n\
        \    128..=255 => 2\n\
        \  }\n\
         }\n");
  test "integer ranges that leave a gap name it" (fun () ->
      let found =
        message
          "fn f(byte: UInt8) -> Int64 {\n\
          \  match byte {\n\
          \    0..=99 => 1\n\
          \    101..=255 => 2\n\
          \  }\n\
           }\n"
      in
      if not (Substring.contains found "`100`") then fail "message %S" found);
  test "a match on a string needs a pattern that matches everything" (fun () ->
      one_diagnostic "fn f(text: String) -> Int64 {\n  match text {\n    \"a\" => 1\n  }\n}\n"
        "patterns.not_covered");
  test "a match over several values is checked as one" (fun () ->
      fine
        "type State = Idle | Running\n\n\
         type Event = Start | Stop\n\n\
         fn f(state: State, event: Event) -> Int64 {\n\
        \  match state, event {\n\
        \    Idle, Start => 1\n\
        \    Running, Stop => 2\n\
        \    _, _ => 3\n\
        \  }\n\
         }\n");
  test "a match over several values misses a combination" (fun () ->
      one_diagnostic
        "type State = Idle | Running\n\n\
         type Event = Start | Stop\n\n\
         fn f(state: State, event: Event) -> Int64 {\n\
        \  match state, event {\n\
        \    Idle, Start => 1\n\
        \    Running, _ => 2\n\
        \  }\n\
         }\n"
        "patterns.not_covered");
  test "a pattern that can fail cannot be a let's" (fun () ->
      one_diagnostic
        "fn f(found: Option[Int64]) -> Int64 {\n  let Some(value) = found\n  value\n}\n"
        "patterns.refutable");
  test "a record pattern cannot fail" (fun () ->
      fine
        "type Pair2(first: Int64, second: Int64)\n\n\
         fn f(pair: Pair2) -> Int64 {\n\
        \  let (first, second) = pair\n\
        \  first + second\n\
         }\n");
  test "a constant in a pattern is its value" (fun () ->
      fine
        "let limit: Int64 = 10\n\n\
         fn f(count: Int64) -> Bool {\n\
        \  match count {\n\
        \    limit => true\n\
        \    _ => false\n\
        \  }\n\
         }\n");
  test "a match whose guards are covered by unreachable is marked for the prover" (fun () ->
      let text =
        "fn f(count: Int64) -> Int64 {\n\
        \  match count {\n\
        \    value if value > 0 => 1\n\
        \    value if value <= 0 => 2\n\
        \    _ => unreachable\n\
        \  }\n\
         }\n"
      in
      if
        not
          (List.exists
             (fun (node : Core.expression) ->
               match node.kind with
               | Match { guards_exhaustive; _ } -> guards_exhaustive
               | _ -> false)
             (first_core_nodes text).expressions)
      then fail "the match is not marked for the prover")

(* Constants in patterns *)

let () =
  let codes_of text =
    let database = setup [ ("app::main", text) ] in
    (match parse_errors database (module_of "app::main") with
    | [] -> ()
    | errors -> fail "the test input does not parse: %s" (String.concat " " errors));
    codes (check database (module_of "app::main"))
  in
  let expect text expected =
    match codes_of text with
    | found when found = expected -> ()
    | found -> fail "found [%s]" (String.concat "; " found)
  in
  test "a qualified constant covers only its value" (fun () ->
      expect
        "type Code(number: Int64)\n\n\
         public let Code.teapot: Int64 = 418\n\n\
         fn f(n: Int64) -> Int64 {\n\
        \  match n {\n\
        \    Code.teapot => 1\n\
        \    5 => 2\n\
        \  }\n\
         }\n"
        [ "patterns.not_covered" ]);
  test "a range with a constant end covers only up to it" (fun () ->
      expect
        "let limit: Int64 = 10\n\n\
         fn f(n: Int64) -> Int64 {\n\
        \  match n {\n\
        \    limit..=20 => 1\n\
        \    5 | 15 => 2\n\
        \    _ => 3\n\
        \  }\n\
         }\n"
        [ "patterns.unreachable_alternative" ]);
  test "a range with a constant end is not a wildcard" (fun () ->
      expect
        "let limit: Int64 = 10\n\n\
         fn f(n: Int64) -> Int64 {\n\
        \  match n {\n\
        \    limit..=20 => 1\n\
        \  }\n\
         }\n"
        [ "patterns.not_covered" ]);
  test "a Bool constant covers its value" (fun () ->
      expect
        "let on: Bool = true\n\n\
         fn f(b: Bool) -> Int64 {\n\
        \  match b {\n\
        \    on => 1\n\
        \    false => 2\n\
        \  }\n\
         }\n"
        []);
  test "a variant constant covers its variant" (fun () ->
      expect
        "type Color =\n\
        \  | Red\n\
        \  | Green\n\
        \  derives Equal\n\n\
         let favorite: Color = Color.Red\n\n\
         fn f(color: Color) -> Int64 {\n\
        \  match color {\n\
        \    favorite => 1\n\
        \    Green => 2\n\
        \  }\n\
         }\n"
        []);
  test "a constant whose value is not evaluated at compile time covers only itself" (fun () ->
      expect
        "let made: Int64 = 3 << 0\n\n\
         fn f(n: Int64) -> Int64 {\n\
        \  match n {\n\
        \    made => 1\n\
        \    3 => 2\n\
        \    _ => 3\n\
        \  }\n\
         }\n"
        [])

(* Errors reported once *)

let () =
  let codes_of text = codes (check (setup [ ("app::main", text) ]) (module_of "app::main")) in
  test "a generic parameter that is a value covers nothing else" (fun () ->
      one_diagnostic
        "fn f[limit: USize](count: USize) -> Bool {\n  match count {\n    limit => true\n  }\n}\n"
        "patterns.not_covered");
  test "a record constant covers the record it is" (fun () ->
      one_diagnostic
        "type Point(x: Int64, y: Bool)\n\
        \  derives Equal\n\n\
         let origin: Point = Point(x: 0, y: false)\n\n\
         fn f(point: Point) -> Bool {\n\
        \  match point {\n\
        \    origin => true\n\
        \    (x: 0, y: false) => false\n\
        \    _ => false\n\
        \  }\n\
         }\n"
        "patterns.unreachable_arm");
  test "a match on a type that failed to parse reports nothing more" (fun () ->
      match
        codes_of
          "type Broken =\n\
          \  | A\n\
          \  | B(x: )\n\n\
           fn f(e: Broken) -> Int64 {\n\
          \  match e {\n\
          \    A => 1\n\
          \    B(..) => 2\n\
          \  }\n\
           }\n"
      with
      | found when List.mem "patterns.not_covered" found ->
          fail "found [%s]" (String.concat "; " found)
      | _ -> ());
  test "code that builds a type that failed to parse reports nothing more" (fun () ->
      (* The definition that builds the value has no error of its own. It
         must still have no core form, or building one stops the compiler. *)
      List.iter
        (fun argument ->
          match
            codes_of
              ("type Entry = {\n\
               \  name: String\n\
                }\n\n\
                fn made(name: String) -> Entry {\n\
               \  Entry(name: " ^ argument ^ ")\n}\n")
          with
          | [] -> ()
          | found -> fail "found [%s]" (String.concat "; " found))
        [ "own name"; "\"${name}\"" ]);
  test "a sub-pattern that failed to type makes no arm unreachable" (fun () ->
      match
        codes_of
          "type Tree =\n\
          \  | Leaf\n\
          \  | indirect Node(left: Tree)\n\n\
           fn f(tree: Tree) -> Int64 {\n\
          \  match tree {\n\
          \    Node(Lef) => 1\n\
          \    Leaf => 2\n\
          \    _ => 3\n\
          \  }\n\
           }\n"
      with
      | found when List.exists (fun code -> String.starts_with ~prefix:"patterns." code) found ->
          fail "found [%s]" (String.concat "; " found)
      | _ -> ())

(* Alternatives *)

let () =
  test "an alternative that an earlier arm covers is unreachable, even the first" (fun () ->
      one_diagnostic
        "type Color =\n\
        \  | Red\n\
        \  | Green\n\
        \  | Blue\n\n\
         fn f(color: Color) -> Int64 {\n\
        \  match color {\n\
        \    Red => 1\n\
        \    Red | Green => 2\n\
        \    Blue => 3\n\
        \  }\n\
         }\n"
        "patterns.unreachable_alternative"
        ~fixed:
          "type Color =\n\
          \  | Red\n\
          \  | Green\n\
          \  | Blue\n\n\
           fn f(color: Color) -> Int64 {\n\
          \  match color {\n\
          \    Red => 1\n\
          \    Green => 2\n\
          \    Blue => 3\n\
          \  }\n\
           }\n");
  test "a nested alternative that the one before covers is unreachable" (fun () ->
      one_diagnostic
        "type Color =\n\
        \  | Red\n\
        \  | Green\n\n\
         fn f(color: Option[Color]) -> Int64 {\n\
        \  match color {\n\
        \    Some(Red | Red) => 1\n\
        \    _ => 2\n\
        \  }\n\
         }\n"
        "patterns.unreachable_alternative")

let () =
  test "character literals and ranges cover their values" (fun () ->
      one_diagnostic
        "fn f(letter: Character) -> Int64 {\n\
        \  match letter {\n\
        \    Character\"a\"..=Character\"z\" => 1\n\
        \    Character\"m\" => 2\n\
        \    _ => 3\n\
        \  }\n\
         }\n"
        "patterns.unreachable_arm")

let () = finish ()
