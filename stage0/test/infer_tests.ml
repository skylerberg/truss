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
      one_diagnostic "fn f() {\n  let ratio: Float64 = 1\n}\n" "types.mismatch"
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
  test "a method without the version a receiver asks for is an error" (fun () ->
      one_diagnostic "fn f(items: List[Int64]) {\n  items.push(1)\n}\n" "types.wrong_receiver")

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

let () = finish ()
