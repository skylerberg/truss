(* The tests of exhaustiveness and reachability. See TYPECHECKER.md,
   "Exhaustiveness and reachability". *)

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
      if not (Documents.find found expected ~occurrence:1 >= 0) then fail "message %S" found);
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
      if Documents.find found "`100`" ~occurrence:1 < 0 then fail "message %S" found);
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
  test "guards covered by unreachable record an obligation" (fun () ->
      let text =
        "fn f(count: Int64) -> Int64 {\n\
        \  match count {\n\
        \    value if value > 0 => 1\n\
        \    value if value <= 0 => 2\n\
        \    _ => unreachable\n\
        \  }\n\
         }\n"
      in
      let database = setup [ ("app::main", text) ] in
      let key =
        Resolve.Names.key_of
          (List.hd (Query.demand database Resolve.Names.declarations (module_of "app::main")))
      in
      match Query.demand database Infer.checked key with
      | Some { checked = { obligations = [ Guards_cover _ ]; _ }; _ } -> ()
      | _ -> fail "no obligation")

let () = finish ()
