(* The tests of checking bodies. Each gives a small definition and states
   one fact: a diagnostic with its fix, or one fact about the checked form.
   See TYPECHECKER.md, "Checking bodies" and "Testing". *)

open Harness
open Support

let check database module_ =
  Resolve.diagnostics database module_
  @ Interface.diagnostics database module_
  @ Infer.diagnostics database module_

let one_diagnostic = one_diagnostic ~check
let no_diagnostics = no_diagnostics ~check
let fine text = no_diagnostics [ ("app::main", text) ]

(* The checked form of the definition that holds the [occurrence]th
   appearance of [written], and the innermost expression that starts there. *)
let expression_at text written occurrence =
  let database = setup [ ("app::main", text) ] in
  let module_ = module_of "app::main" in
  let offset = Documents.find text written ~occurrence in
  let found =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        match
          ( Query.demand database Resolve.Names.definition key,
            Query.demand database Resolve.Names.base key,
            Query.demand database Infer.checked key )
        with
        | Some definition, Some (_, base), Some result ->
            (* The expression whose span is exactly the text, or else the
               innermost one that starts there. *)
            let best = ref None in
            let exact (value : Syntax.expression) =
              value.span.stop - value.span.start = String.length written
            in
            let rec visit (value : Syntax.expression) =
              (if base + value.span.start = offset then
                 match !best with
                 | Some (other : Syntax.expression)
                   when exact other
                        || (not (exact value))
                           && other.span.stop - other.span.start
                              <= value.span.stop - value.span.start ->
                     ()
                 | _ -> best := Some value);
              Syntax_walk.children visit value
            in
            Syntax_walk.definition visit definition;
            Option.map (fun value -> (value, result.checked)) !best
        | _ -> None)
      (Query.demand database Resolve.Names.declarations module_)
  in
  match found with
  | Some found -> found
  | None -> failwith (Printf.sprintf "no expression at %S" written)

let has_type text written ?(occurrence = 1) expected =
  let value, checked = expression_at text written occurrence in
  match checked.types.(value.id) with
  | Some type_ ->
      if Types.show type_ <> expected then
        fail "`%s` has type %s, not %s" written (Types.show type_) expected
  | None -> fail "`%s` has no type" written

(* Literals *)

let () =
  test "a literal takes the type of the other operand" (fun () ->
      has_type "fn f(count: UInt8) -> UInt8 {\n  count + 1\n}\n" "1" "UInt8");
  test "a literal nothing decides is an Int64" (fun () ->
      has_type "fn f() -> Int64 {\n  var best = 0\n  best\n}\n" "0" "Int64");
  test "a literal takes the expected type" (fun () ->
      has_type "fn f() {\n  let small: UInt8 = 3\n}\n" "3" "UInt8");
  test "a literal multiplied by a type that is not an integer is an Int64" (fun () ->
      fine
        "type Duration2(nanoseconds: Int64)\n\n\
         impl Multiply[Int64] for Duration2 {\n\
        \  type Output = Duration2\n\
        \  fn multiply(self, right: Int64) -> Duration2 { todo }\n\
         }\n\n\
         fn f(duration: Duration2) -> Duration2 {\n\
        \  duration * 2\n\
         }\n");
  test "an expression of literals waits for the same decision" (fun () ->
      has_type "fn f(count: UInt16) -> UInt16 {\n  count + (60 * 60)\n}\n" "60" "UInt16");
  test "a literal that does not fit its type is an error" (fun () ->
      one_diagnostic "fn f() {\n  let small: UInt8 = 300\n}\n" "types.literal_out_of_range");
  test "a negated literal is checked after the negation" (fun () ->
      fine "fn f() {\n  let small: Int8 = -128\n}\n");
  test "an integer literal where a float is expected is an error with a fix" (fun () ->
      one_diagnostic "fn f() {\n  let ratio: Float64 = 1\n}\n" "types.integer_for_float"
        ~fixed:"fn f() {\n  let ratio: Float64 = 1.0\n}\n");
  test "a literal shift amount is a USize" (fun () ->
      has_type "fn f(flags: UInt32) -> UInt32 {\n  flags << 3\n}\n" "3" ~occurrence:3 "USize")

(* Operators *)

let () =
  test "comparing integer types that differ is an error with a fix that converts" (fun () ->
      one_diagnostic "fn f(count: UInt32, length: UInt64) -> Bool {\n  length == count\n}\n"
        "types.mismatched_integers"
        ~fixed:"fn f(count: UInt32, length: UInt64) -> Bool {\n  length == UInt64.from(count)\n}\n");
  test "+ on strings is an error with a fix to interpolation" (fun () ->
      one_diagnostic "fn f(name: String) -> String {\n  name + \"!\"\n}\n" "types.string_addition"
        ~fixed:"fn f(name: String) -> String {\n  \"${name}!\"\n}\n");
  test "an operator chooses the impl by both operands" (fun () ->
      let text = "fn f(left: Int64, right: Int64) -> Int64 {\n  left + right\n}\n" in
      let value, checked = expression_at text "left + right" 1 in
      match checked.calls.(value.id) with
      | Some { callee = Trait_method { evidence = Impl _; name = "add"; _ }; _ } -> ()
      | _ -> fail "no impl recorded");
  test "a type without the operator's trait is an error" (fun () ->
      one_diagnostic "type Point(x: Int64)\n\nfn f(point: Point) -> Point {\n  point + point\n}\n"
        "types.no_impl")

(* Calls and arguments *)

let () =
  let functions = "fn copy_file(source: Int64, destination: Int64) {}\n\n" in
  test "an argument after the first needs a label, with a fix that adds it" (fun () ->
      one_diagnostic
        (functions ^ "fn f(original: Int64, backup: Int64) {\n  copy_file(original, backup)\n}\n")
        "types.missing_label"
        ~fixed:
          (functions
         ^ "fn f(original: Int64, backup: Int64) {\n  copy_file(original, destination: backup)\n}\n"
          ));
  test "a variable with the parameter's name needs no label" (fun () ->
      fine
        (functions
       ^ "fn f(source: Int64, destination: Int64) {\n  copy_file(source, destination)\n}\n"));
  test "arguments out of order are an error with a fix that reorders them" (fun () ->
      one_diagnostic
        (functions
       ^ "fn f(source: Int64, destination: Int64) {\n  copy_file(destination, source)\n}\n")
        "types.out_of_order"
        ~fixed:
          (functions
         ^ "fn f(source: Int64, destination: Int64) {\n  copy_file(source, destination)\n}\n"));
  test "a missing argument is an error" (fun () ->
      one_diagnostic (functions ^ "fn f() {\n  copy_file(1)\n}\n") "types.missing_argument");
  test "a parameter with a default may be left out" (fun () ->
      let text = "fn connect(host: Int64, port: UInt16 = 443) {}\n\nfn f() {\n  connect(1)\n}\n" in
      let value, checked = expression_at text "connect(1)" 1 in
      match checked.calls.(value.id) with
      | Some { defaults_left_out = [ "port" ]; _ } -> ()
      | _ -> fail "the default left out is not recorded");
  test "a String passed where a StringSlice is expected is viewed" (fun () ->
      let text = "fn greet(text: StringSlice) {}\n\nfn f(name: String) {\n  greet(name)\n}\n" in
      let value, checked = expression_at text "greet(name)" 1 in
      match checked.calls.(value.id) with
      | Some { arguments = [ { conversion = Some Owned_to_view; _ } ]; _ } -> ()
      | _ -> fail "no conversion recorded");
  test "a capability's method views a String argument too" (fun () ->
      let text = "fn f(name: String)\n  uses Console\n{\n  Console.print_line(name)\n}\n" in
      let value, checked = expression_at text "Console.print_line(name)" 1 in
      match checked.calls.(value.id) with
      | Some { arguments = [ { conversion = Some Owned_to_view; _ } ]; _ } -> ()
      | _ -> fail "no conversion recorded");
  test "a string literal is a String, viewed where a StringSlice is expected" (fun () ->
      let text = "fn f()\n  uses Console\n{\n  Console.print_line(\"hello\")\n}\n" in
      has_type text "\"hello\"" "String";
      let value, checked = expression_at text "Console.print_line(\"hello\")" 1 in
      match checked.calls.(value.id) with
      | Some { arguments = [ { conversion = Some Owned_to_view; _ } ]; _ } -> ()
      | _ -> fail "no conversion recorded");
  test "a cursor's next is the Cursor trait's, built in" (fun () ->
      let text =
        "fn count_to(limit: Int64) yields Int64 {\n\
        \  yield limit\n\
         }\n\n\
         fn f() {\n\
        \  var first = count_to(3)\n\
        \  while mut first.next() is Some(left) {\n\
        \    let _ = left\n\
        \  }\n\
         }\n"
      in
      fine text;
      has_type text "count_to(3)" "the cursor of app::main::count_to";
      let value, checked = expression_at text "first.next()" 1 in
      match checked.calls.(value.id) with
      | Some
          {
            callee =
              Trait_method
                {
                  name = "next";
                  receiver = Mut;
                  self_type = Cursor _;
                  evidence = Built_in;
                  trait;
                  _;
                };
            result;
            _;
          }
        when Path.show trait.trait = "standard::core::Cursor" && Types.show result = "Option[Int64]"
        ->
          ()
      | _ -> fail "not the built-in Cursor's next");
  test "an unknown label is an error with a fix to the closest" (fun () ->
      one_diagnostic
        (functions ^ "fn f() {\n  copy_file(1, destinaton: 2)\n}\n")
        "types.unknown_label"
        ~fixed:(functions ^ "fn f() {\n  copy_file(1, destination: 2)\n}\n"));
  test "a record is built with labels in any order" (fun () ->
      fine "type Point(x: Int64, y: Int64)\n\nfn f() -> Point {\n  Point(y: 1, x: 0)\n}\n");
  test "a record with one field takes a bare value" (fun () ->
      fine "type UserId(number: UInt64)\n\nfn f() -> UserId {\n  UserId(42)\n}\n");
  test "a generic function's type arguments are solved from its arguments" (fun () ->
      has_type
        "fn wrap[Value](value: own Value) -> Option[Value] { Some(value) }\n\n\
         fn f() -> Option[Int64] {\n\
        \  wrap(5)\n\
         }\n"
        "wrap(5)" "Option[Int64]")

(* Modes *)

let () =
  test "a mut parameter needs mut at the call, with a fix that adds it" (fun () ->
      one_diagnostic "fn bump(count: mut Int64) {}\n\nfn f() {\n  var count = 0\n  bump(count)\n}\n"
        "types.missing_mark"
        ~fixed:"fn bump(count: mut Int64) {}\n\nfn f() {\n  var count = 0\n  bump(mut count)\n}\n");
  test "an own parameter needs own for a place that does not copy implicitly" (fun () ->
      one_diagnostic
        "fn keep(items: own List[Int64]) {}\n\nfn f(items: own List[Int64]) {\n  keep(items)\n}\n"
        "types.missing_mark"
        ~fixed:
          "fn keep(items: own List[Int64]) {}\n\n\
           fn f(items: own List[Int64]) {\n\
          \  keep(own items)\n\
           }\n");
  test "own on a place that copies implicitly is redundant" (fun () ->
      one_diagnostic "fn keep(count: own Int64) {}\n\nfn f(count: Int64) {\n  keep(own count)\n}\n"
        "types.redundant_mark"
        ~fixed:"fn keep(count: own Int64) {}\n\nfn f(count: Int64) {\n  keep(count)\n}\n");
  test "a mut receiver chooses the method's mut version" (fun () ->
      fine "fn f() {\n  var items: List[Int64] = []\n  mut items.push(1)\n}\n");
  test "a place calling a method that takes mut self needs the mark, with a fix that adds it"
    (fun () ->
      one_diagnostic "fn f() {\n  var items: List[Int64] = []\n  items.push(1)\n}\n"
        "types.missing_mark"
        ~fixed:"fn f() {\n  var items: List[Int64] = []\n  mut items.push(1)\n}\n")

(* Statements *)

let () =
  test "a statement's value must be used, with a fix that discards it" (fun () ->
      one_diagnostic "fn f(items: List[Int64]) {\n  items.length()\n}\n" "types.unused_value"
        ~fixed:"fn f(items: List[Int64]) {\n  let _ = items.length()\n}\n");
  test "a let cannot be assigned" (fun () ->
      one_diagnostic "fn f() {\n  let count = 0\n  count = 1\n}\n" "types.not_assignable");
  test "a var can be assigned" (fun () ->
      fine "fn f() {\n  var count = 0\n  count = 1\n  let _ = count\n}\n");
  test "an empty list with nothing to decide its elements is an error" (fun () ->
      one_diagnostic "fn f() {\n  var names = []\n}\n" "types.cannot_infer");
  test "an empty list takes its elements' type from the annotation" (fun () ->
      fine "fn f() {\n  var names: List[String] = []\n}\n");
  test "a body's value must have the result type" (fun () ->
      one_diagnostic "fn f() -> Int64 {\n  true\n}\n" "types.mismatch");
  test "an arm of type Never is left out of the match's type" (fun () ->
      fine
        "fn f(found: Option[Int64]) -> Int64 {\n\
        \  match found {\n\
        \    Some(value) => value\n\
        \    None => return 0\n\
        \  }\n\
         }\n");
  test "? needs the function's error type" (fun () ->
      one_diagnostic
        "fn parse() -> Result[Int64, Bool] { todo }\n\n\
         fn f() -> Result[Int64, String] {\n\
        \  let value = parse()?\n\
        \  Ok(value)\n\
         }\n"
        "types.wrong_try");
  test "? on a matching Result gives its value" (fun () ->
      has_type
        "fn parse() -> Result[Int64, Bool] { todo }\n\n\
         fn f() -> Result[Int64, Bool] {\n\
        \  let value = parse()?\n\
        \  Ok(value)\n\
         }\n"
        "parse()?" "Int64");
  test "if without else has type Unit" (fun () ->
      has_type "fn f(ready: Bool) {\n  let value = if ready { }\n  let _ = value\n}\n"
        "if ready { }" "Unit")

(* Members *)

let () =
  test "an unknown field is an error with a fix to the closest" (fun () ->
      one_diagnostic
        "type Point(x: Int64, y: Int64)\n\nfn f(point: Point) -> Int64 {\n  point.z\n}\n"
        "types.unknown_member");
  test "a method from a trait needs no import" (fun () ->
      fine "fn f(items: List[Int64]) -> List[Int64] {\n  items.copy()\n}\n");
  test "a variant is looked up under its type" (fun () ->
      fine
        "type Shape =\n\
        \  | Circle(radius: Float64)\n\
        \  | Empty\n\n\
         fn f() -> Shape {\n\
        \  Shape.Circle(radius: 1.0)\n\
         }\n");
  test "a constant under a type is read by name" (fun () ->
      has_type "fn f() -> UInt8 {\n  UInt8.maximum\n}\n" "UInt8.maximum" "UInt8");
  test "a trait method through a type chooses the impl by the argument" (fun () ->
      fine "fn f(count: Int32) -> Int64 {\n  Int64.from(count)\n}\n")

(* Patterns *)

let () =
  test "an unknown variant in a pattern is an error" (fun () ->
      one_diagnostic
        "fn f(found: Option[Int64]) -> Int64 {\n\
        \  match found {\n\
        \    Sone(value) => value\n\
        \    _ => 0\n\
        \  }\n\
         }\n"
        "types.unknown_variant");
  test "a bare name in a record pattern binds the field it names" (fun () ->
      fine
        "type Pair2(first: Int64, second: Int64)\n\n\
         fn f(pair: Pair2) -> Int64 {\n\
        \  let (first, second) = pair\n\
        \  first + second\n\
         }\n");
  test "a bare name that names no field of a record with several is an error" (fun () ->
      one_diagnostic
        "type Pair2(first: Int64, second: Int64)\n\n\
         fn f(pair: Pair2) -> Int64 {\n\
        \  let (a, second) = pair\n\
        \  a + second\n\
         }\n"
        "types.unknown_member")

(* Lambdas *)

let () =
  test "a lambda with nothing to give its parameter types is an error" (fun () ->
      one_diagnostic "fn f() {\n  let length = fn(text) { text }\n}\n" "types.lambda_needs_type");
  test "a lambda takes its parameter types from the function type it is passed as" (fun () ->
      has_type "fn f(items: List[Int64]) -> List[Int64] {\n  items.map(fn(item) { item + 1 })\n}\n"
        "item + 1" "Int64");
  test "a lambda's captures are the outer locals it reads" (fun () ->
      let text =
        "fn f(items: List[Int64], step: Int64) -> List[Int64] {\n\
        \  items.map(fn(item) { item + step })\n\
         }\n"
      in
      let value, checked = expression_at text "fn(item)" 1 in
      match checked.captures.(value.id) with
      | Some [ _ ] -> ()
      | Some found -> fail "%d captures" (List.length found)
      | None -> fail "none recorded")

(* Strings and collections *)

let () =
  test "an interpolated value must implement Display" (fun () ->
      one_diagnostic "type Point(x: Int64)\n\nfn f(point: Point) -> String {\n  \"${point}\"\n}\n"
        "types.no_impl");
  test "an array literal must have its type's length" (fun () ->
      one_diagnostic "fn f() {\n  let digest: Array[UInt8, 2] = [1, 2, 3]\n}\n" "types.mismatch");
  test "a list literal is a set where a set is expected" (fun () ->
      fine "fn f() {\n  let colors: Set[String] = [\"red\", \"green\"]\n}\n")

(* Specifications *)

let () =
  test "integer arithmetic in a specification is exact" (fun () ->
      has_type "fn f(a: Int64, b: Int64) -> Int64\n  ensures result == a + b\n{\n  todo\n}\n"
        "a + b" "Integer");
  test "comparisons in a specification may mix integer types" (fun () ->
      fine "fn f(count: UInt32, items: List[Int64])\n  requires count <= items.length()\n{\n}\n")

(* Loops *)

let () =
  test "a for loop over a range of integers is a counted loop" (fun () ->
      let text = "fn f(count: USize) {\n  for i in 0..count {\n    let _ = i\n  }\n}\n" in
      let database = setup [ ("app::main", text) ] in
      let key =
        Resolve.Names.key_of
          (List.hd (Query.demand database Resolve.Names.declarations (module_of "app::main")))
      in
      match Query.demand database Infer.checked key with
      | Some result ->
          if
            not
              (Array.exists
                 (function Some (Checked.Integer_range _) -> true | _ -> false)
                 result.checked.loops)
          then fail "no counted loop"
      | None -> fail "not checked");
  test "a for loop over a list drives its each" (fun () ->
      fine
        "fn f(items: List[Int64]) -> Int64 {\n\
        \  var total = 0\n\
        \  for item in items {\n\
        \    total += item\n\
        \  }\n\
        \  total\n\
         }\n")

(* Incremental work and determinism *)

let () =
  test "editing a function's body re-checks no caller" (fun () ->
      let text body =
        "fn callee() -> Int64 { " ^ body ^ " }\n\nfn caller() -> Int64 {\n  callee()\n}\n"
      in
      let database = setup [ ("app::main", text "1") ] in
      let module_ = module_of "app::main" in
      ignore (Infer.diagnostics database module_);
      Query.set database Workspace.file_text module_ (text "2");
      Query.clear_log database;
      ignore (Infer.diagnostics database module_);
      if List.mem "checked(app::main::caller)" (Query.executed database) then
        fail "the caller was checked again");
  test "checking twice gives the same checked form" (fun () ->
      let text =
        "fn f(items: List[Int64]) -> Int64 {\n\
        \  var total = 0\n\
        \  for item in items {\n\
        \    total += item\n\
        \  }\n\
        \  total\n\
         }\n"
      in
      let checked () =
        let database = setup [ ("app::main", text) ] in
        let key =
          Resolve.Names.key_of
            (List.hd (Query.demand database Resolve.Names.declarations (module_of "app::main")))
        in
        Query.demand database Infer.checked key
      in
      if checked () <> checked () then fail "different")

let () =
  test "no checked form of the standard library holds an unsolved type" (fun () ->
      let database = setup [] in
      let rec unsolved = function
        | Types.Variable _ | Types.Literal _ | Types.Hole -> true
        | Types.Named { arguments; _ } | Types.Cursor { arguments; _ } ->
            List.exists (function Types.Type type_ -> unsolved type_ | _ -> false) arguments
        | Types.Function { inputs; output; _ } -> (
            List.exists (fun (_, type_) -> unsolved type_) inputs
            ||
            match output with
            | Returns type_ | Yields (_, type_) | Lends (_, type_) -> unsolved type_)
        | _ -> false
      in
      let arguments =
        List.exists (function
          | Types.Type type_ -> unsolved type_
          | Types.Value (Value_variable _) -> true
          | _ -> false)
      in
      List.iter
        (fun ((module_ : Path.module_), _) ->
          List.iter
            (fun (declaration : Resolve.Names.declaration) ->
              match Query.demand database Infer.checked (Resolve.Names.key_of declaration) with
              | Some { checked; _ } ->
                  Array.iter
                    (function
                      | Some type_ when unsolved type_ ->
                          fail "%s: an unsolved type" (Path.show declaration.path)
                      | _ -> ())
                    checked.types;
                  Array.iter
                    (function
                      | Some
                          ({
                             callee =
                               Intrinsic { type_arguments; _ } | Function { type_arguments; _ };
                             _;
                           } :
                            Checked.call)
                        when arguments type_arguments ->
                          fail "%s: a call with unsolved type arguments"
                            (Path.show declaration.path)
                      | _ -> ())
                    checked.calls
              | None -> ())
            (Query.demand database Resolve.Names.declarations module_))
        Standard_library.modules)

(* What the review of body checking found *)

let point = "type Point(x: Int64)\n\n"

let () =
  test "a call's type arguments must meet their bounds" (fun () ->
      one_diagnostic
        (point
       ^ "fn need[Value: Ordered](value: Value) {}\n\nfn f(point: Point) {\n  need(point)\n}\n")
        "types.unsatisfied_bound");
  test "a type written in a body must meet its bounds" (fun () ->
      let database =
        setup [ ("app::main", point ^ "fn f() {\n  let points: Set[Point] = []\n}\n") ]
      in
      match codes (check database (module_of "app::main")) with
      | [ "types.unsatisfied_bound"; "types.unsatisfied_bound" ] -> ()
      | found -> fail "found [%s]" (String.concat "; " found));
  test "a type written in a body that is not a type is an error" (fun () ->
      one_diagnostic "fn f() {\n  let value: Display = 3\n}\n" "types.not_a_type");
  test "an operator's result must be the type expected of it" (fun () ->
      one_diagnostic
        "type Span2(length: Int64)\n\n\
         impl Multiply[Int64] for Span2 {\n\
        \  type Output = Span2\n\
        \  fn multiply(self, right: Int64) -> Span2 { todo }\n\
         }\n\n\
         fn f(span: Span2) -> Int64 {\n\
        \  span * 3\n\
         }\n"
        "types.mismatch");
  test "an array length nothing decides is an error" (fun () ->
      one_diagnostic
        "fn zeros[count: USize]() -> Array[Int64, count] { todo }\n\n\
         fn f() {\n\
        \  let _ = zeros()\n\
         }\n"
        "types.cannot_infer");
  test "a qualified constant in a pattern must have the matched type" (fun () ->
      one_diagnostic
        "fn f(count: Int64) -> Int64 {\n\
        \  match count {\n\
        \    ExitCode.success => 1\n\
        \    _ => 0\n\
        \  }\n\
         }\n"
        "types.mismatch");
  test "the alternatives of a pattern bind each name with one type" (fun () ->
      one_diagnostic
        "type Either2 =\n\
        \  | Number(value: Int64)\n\
        \  | Text(value: String)\n\n\
         fn f(either: Either2) -> Int64 {\n\
        \  match either {\n\
        \    Number(value) | Text(value) => 1\n\
        \  }\n\
         }\n"
        "types.mismatch");
  test "a pattern must match every field or write .." (fun () ->
      one_diagnostic
        "type Pair2(first: Int64, second: Int64)\n\n\
         fn f(pair: Pair2) -> Int64 {\n\
        \  let (first) = pair\n\
        \  first\n\
         }\n"
        "types.missing_argument");
  test "an opaque type cannot be matched outside its package" (fun () ->
      one_diagnostic "fn f(items: List[Int64]) {\n  let (storage) = items\n}\n"
        "types.private_field");
  test "a bitwise compound assignment works on integers only" (fun () ->
      one_diagnostic "fn f() {\n  var text = \"a\"\n  text ^= \"b\"\n}\n" "types.no_impl");
  test "a method written in full takes its receiver's mark" (fun () ->
      one_diagnostic "fn f() {\n  var items: List[Int64] = []\n  List.push(items, item: 1)\n}\n"
        "types.wrong_receiver");
  test "an associated type of an argument is normalized" (fun () ->
      fine
        "fn has_key[Collection: Index](collection: Collection, key: Collection.Key) {}\n\n\
         fn f(items: List[Int64]) {\n\
        \  has_key(items, key: 0)\n\
         }\n");
  test "a literal receiver has its default type" (fun () ->
      has_type "fn f() -> Int64 {\n  5.wrapping_add(3)\n}\n" "5.wrapping_add(3)" "Int64");
  test "a for loop over characters counts" (fun () ->
      fine
        "fn f(first: Character, last: Character) {\n\
        \  for letter in first..last {\n\
        \    let _ = letter\n\
        \  }\n\
         }\n");
  test "an operation on a hole is a hole" (fun () ->
      fine "fn f() {\n  let body = todo\n  let _ = body + 1\n}\n");
  test "a loop variable's type comes from the loop's header" (fun () ->
      one_diagnostic "fn f() {\n  for i in 0..10 {\n    let small: UInt8 = i\n  }\n}\n"
        "types.mismatch");
  test "a mistake is not reported again as a type that cannot be worked out" (fun () ->
      let database =
        setup
          [ ("app::main", "fn f(items: List[Int64]) {\n  let _ = items.map(undefined_thing)\n}\n") ]
      in
      if List.mem "types.cannot_infer" (codes (check database (module_of "app::main"))) then
        fail "cascaded");
  test "a Float32 literal too large is an error" (fun () ->
      one_diagnostic "fn f() {\n  let large: Float32 = 3.5e38\n}\n" "types.literal_out_of_range");
  test "a Float32 literal is rounded once, from its decimal" (fun () ->
      let value, checked =
        expression_at "fn f() {\n  let value: Float32 = 1.0000000596046447754\n}\n"
          "1.0000000596046447754" 1
      in
      match checked.literals.(value.id) with
      | Some (Float_value rounded) ->
          if rounded <> Float.of_string "0x1.000002p+0" then fail "rounded to %h" rounded
      | _ -> fail "no value");
  test "each end of a range pattern records its own value" (fun () ->
      let value, checked =
        expression_at "fn f(n: Int64) -> Int64 {\n  match n {\n    1..=5 => 1\n    _ => 2\n  }\n}\n"
          "match" 1
      in
      match value.kind with
      | Match
          {
            arms = { patterns = [ { kind = Pattern_range { start; stop; _ }; id; _ } ]; _ } :: _;
            _;
          } -> (
          match
            (checked.literals.(start.id), checked.literals.(stop.id), checked.literals.(id))
          with
          | Some (Integer_value low), Some (Integer_value high), None
            when Z.equal low (Z.of_int 1) && Z.equal high (Z.of_int 5) ->
              ()
          | _ -> fail "the ends are not recorded each by its own id")
      | _ -> fail "not a match on a range");
  test "a range pattern on a type that is not an integer or Character is an error" (fun () ->
      one_diagnostic
        "fn f(ready: Bool) -> Int64 {\n  match ready {\n    true..=false => 1\n    _ => 2\n  }\n}\n"
        "types.mismatch");
  test "an integer range on a type that is not ordered is one error" (fun () ->
      one_diagnostic
        "fn f(ready: Bool) -> Int64 {\n  match ready {\n    1..=2 => 1\n    _ => 2\n  }\n}\n"
        "types.mismatch");
  test "a range pattern on Character is fine" (fun () ->
      fine
        "fn f(letter: Character) -> Int64 {\n\
        \  match letter {\n\
        \    Character\"a\"..=Character\"z\" => 1\n\
        \    _ => 2\n\
        \  }\n\
         }\n");
  test "a Character literal is a tagged string holding its scalar value" (fun () ->
      has_type "fn f() -> Character {\n  Character\"é\"\n}\n" "Character\"é\"" "Character";
      let value, checked =
        expression_at "fn f() -> Character {\n  Character\"é\"\n}\n" "Character\"é\"" 1
      in
      match checked.literals.(value.id) with
      | Some (Integer_value scalar) when Z.equal scalar (Z.of_int 0xE9) -> ()
      | _ -> fail "no value");
  test "a UInt8 literal holds its ASCII character's value" (fun () ->
      let value, checked = expression_at "fn f() -> UInt8 {\n  UInt8\"\\n\"\n}\n" "UInt8" 2 in
      match checked.literals.(value.id) with
      | Some (Integer_value byte) when Z.equal byte (Z.of_int 10) -> ()
      | _ -> fail "no value");
  test "a Character literal of two scalar values is an error" (fun () ->
      one_diagnostic "fn f() -> Character {\n  Character\"ab\"\n}\n" "types.bad_character");
  test "a UInt8 literal of a character that is not ASCII is an error" (fun () ->
      one_diagnostic "fn f() -> UInt8 {\n  UInt8\"é\"\n}\n" "types.bad_character");
  test "a negated literal of an unsigned type is one error" (fun () ->
      one_diagnostic "fn f() {\n  let value: UInt8 = -1\n}\n" "types.negated_unsigned");
  test "explicit type arguments give exactly the function's own" (fun () ->
      one_diagnostic
        "fn pick[First, Second](first: First) -> Second { todo }\n\n\
         fn f() -> Int64 {\n\
        \  pick[Int64](3)\n\
         }\n"
        "types.arity");
  test "a missing label has no fix when which one is meant is not known" (fun () ->
      let database =
        setup
          [ ("app::main", "fn g(a: Int64, b: Int64, c: Int64) {}\n\nfn f() {\n  g(1, 2, 3)\n}\n") ]
      in
      List.iter
        (fun (diagnostic : Diagnostic.t) -> if diagnostic.fixes <> [] then fail "offered a fix")
        (check database (module_of "app::main")));
  test "the string + fix keeps escapes" (fun () ->
      one_diagnostic "fn f(name: String) -> String {\n  \"a\\\"b\" + name\n}\n"
        "types.string_addition" ~fixed:"fn f(name: String) -> String {\n  \"a\\\"b${name}\"\n}\n");
  test "a lambda cannot change what it captures" (fun () ->
      one_diagnostic
        "fn f(items: List[Int64]) {\n\
        \  var count = 0\n\
        \  let _ = items.map(fn(item) { count = item })\n\
        \  let _ = count\n\
         }\n"
        "types.not_assignable")

(* Specifications on loops and on function-typed parameters *)

let () =
  test "a function-typed parameter's requires is a Bool over its inputs" (fun () ->
      fine
        "fn apply_all(limit: USize, visit: (fn(index: USize) requires index < limit)) {\n\
        \  todo\n\
         }\n");
  test "a function-typed parameter's requires must be a Bool" (fun () ->
      one_diagnostic
        "fn apply_all(limit: USize, visit: (fn(index: USize) requires index + limit)) {\n\
        \  todo\n\
         }\n"
        "types.mismatch");
  test "a trait method without a body has its clauses checked" (fun () ->
      one_diagnostic "trait Measured {\n  fn measure(self) -> Int64\n    ensures result + true\n}\n"
        "types.no_impl");
  test "a loop's cost bound is checked" (fun () ->
      one_diagnostic
        "fn f(count: USize) {\n\
        \  for i in 0..count\n\
        \    cost time O(missing)\n\
        \  {\n\
        \    let _ = i\n\
        \  }\n\
         }\n"
        "resolve.unknown_name")

let () = finish ()
