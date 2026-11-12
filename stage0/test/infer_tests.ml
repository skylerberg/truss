(* The tests of checking bodies. Each gives a small definition and states
   one fact: a diagnostic with its fix, or one fact about the tables or the
   core form. *)

open Harness
open Support

let check database module_ =
  Resolve.diagnostics database module_
  @ Interface.diagnostics database module_
  @ Infer.diagnostics database module_

let one_diagnostic = one_diagnostic ~check
let no_diagnostics = no_diagnostics ~check
let fine text = no_diagnostics [ ("app::main", text) ]

(* The type check result of the definition that holds the [occurrence]th
   appearance of [written], and the innermost expression that starts there. *)
let expression_at text written occurrence =
  let database = setup [ ("app::main", text) ] in
  let module_ = module_of "app::main" in
  let offset = Option.get (Substring.find ~occurrence text written) in
  let found =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        match
          ( Query.demand database Resolve.Names.definition key,
            Query.demand database Resolve.Names.base key,
            Query.demand database Infer.type_check_result key )
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
            Option.map (fun value -> (value, result)) !best
        | _ -> None)
      (Query.demand database Resolve.Names.declarations module_)
  in
  match found with
  | Some found -> found
  | None -> failwith (Printf.sprintf "no expression at %S" written)

(* Whether the core form of the first definition has an integer literal
   with this value. *)
let has_integer text value =
  List.exists
    (fun (node : Core.expression) ->
      match node.kind with Integer found -> Z.equal found (Z.of_int value) | _ -> false)
    (first_core_nodes text).expressions

(* The core nodes built from the [occurrence]th appearance of [written]. *)
let core_at text written occurrence =
  let value, (result : Infer.type_check_result) = expression_at text written occurrence in
  match result.core with
  | None -> failwith (Printf.sprintf "no core form holds %S" written)
  | Some form ->
      let nodes = ref [] in
      Core_walk.definition
        {
          Core_walk.ignore_all with
          expression =
            (fun (node : Core.expression) -> if node.origin = value.id then nodes := node :: !nodes);
        }
        form.definition;
      List.rev !nodes

(* The call built from the [occurrence]th appearance of [written], with its
   type. *)
let core_call_at text written occurrence =
  match
    List.find_map
      (fun (node : Core.expression) ->
        match node.kind with Call call -> Some (call, node.type_) | _ -> None)
      (core_at text written occurrence)
  with
  | Some call -> call
  | None -> failwith (Printf.sprintf "%S is not a call" written)

(* Whether an argument is the view of an owned collection: a call of its
   [slice]. *)
let is_view : Core.argument -> bool = function
  | Passed
      {
        value =
          Value
            { kind = Call { callee = Function { path = Method { name = "slice"; _ }; _ }; _ }; _ };
        _;
      } ->
      true
  | _ -> false

let has_type text written ?(occurrence = 1) expected =
  let value, (result : Infer.type_check_result) = expression_at text written occurrence in
  match result.tables.types.(value.id) with
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
        \  fn multiply_is_defined(self, right: Int64) -> Bool { true }\n\
        \  fn multiply(self, right: Int64) -> Duration2 { todo }\n\
         }\n\n\
         fn f(duration: Duration2) -> Duration2 {\n\
        \  duration * 2\n\
         }\n");
  test "an expression of literals waits for the same decision" (fun () ->
      has_type "fn f(count: UInt16) -> UInt16 {\n  count + (60 * 60)\n}\n" "60" "UInt16");
  test "a literal that does not fit its type is an error" (fun () ->
      one_diagnostic "fn f() {\n  let small: UInt8 = 300\n}\n" "types.literal_out_of_range");
  test "a USize literal must fit in 32 bits, so that the code holds on every target" (fun () ->
      one_diagnostic "fn f() {\n  let size: USize = 5_000_000_000\n}\n" "types.literal_out_of_range");
  test "a package that runs only on 64-bit targets may use 64-bit USize literals" (fun () ->
      let engine = Engine.create ~bases:[ Lazy.force Support.standard ] () in
      Database.load_package ~usize_bits:64 engine ~name:{ owner = None; name = "app" }
        ~dependencies:[]
        [ (module_of "app::main", "fn f() {\n  let size: USize = 5_000_000_000\n}\n") ];
      match check (Engine.context engine) (module_of "app::main") with
      | [] -> ()
      | found -> fail "%s" (String.concat "; " (codes found)));
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
      let text =
        "type Meters(value: Int64)\n\n\
         impl Add[Meters] for Meters {\n\
        \  type Output = Meters\n\
        \  fn add_is_defined(self, right: Meters) -> Bool { true }\n\
        \  fn add(self, right: Meters) -> Meters { todo }\n\
         }\n\n\
         impl Add[Int64] for Meters {\n\
        \  type Output = Meters\n\
        \  fn add_is_defined(self, right: Int64) -> Bool { true }\n\
        \  fn add(self, right: Int64) -> Meters { todo }\n\
         }\n\n\
         fn f(length: Meters, extra: Int64) -> Meters {\n\
        \  length + extra\n\
         }\n"
      in
      match core_call_at text "length + extra" 1 with
      | { callee = Trait_method { evidence = Impl { impl; _ }; name = "add"; _ }; _ }, _ ->
          let shown = Path.show impl in
          if not (Substring.contains shown "Add[Int64]") then fail "the impl chosen is %s" shown
      | _ -> fail "no impl recorded");
  test "an ordering on Self in a trait's law is its compare" (fun () ->
      let text =
        "trait Ranked: Ordered {\n\
        \  law transitive(first: Self, second: Self, third: Self)\n\
        \    requires first < second\n\
        \    requires second < third\n\
        \  {\n\
        \    first < third\n\
        \  }\n\
         }\n"
      in
      List.iter
        (fun written ->
          match core_call_at text written 1 with
          | { callee = Trait_method { name = "compare"; evidence = Bound; _ }; _ }, result ->
              if Types.show result <> "Ordering" then
                fail "`%s` calls a `compare` that gives `%s`" written (Types.show result)
          | _ -> fail "`%s` is another call" written)
        [ "first < second"; "second < third"; "first < third" ]);
  test "an operand can be the result of an operator's method" (fun () ->
      fine "fn f(left: Int64, right: Int64) -> Int64 {\n  left + right.multiply(2)\n}\n");
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
  test "an argument for a parameter with a default can be omitted" (fun () ->
      let text = "fn connect(host: Int64, port: UInt16 = 443) {}\n\nfn f() {\n  connect(1)\n}\n" in
      match core_call_at text "connect(1)" 1 with
      | { arguments = [ Passed _; Default ]; _ }, _ -> ()
      | _ -> fail "the omitted default is not recorded");
  test "a String passed where a StringSlice is expected is viewed" (fun () ->
      let text = "fn greet(text: StringSlice) {}\n\nfn f(name: String) {\n  greet(name)\n}\n" in
      match core_call_at text "greet(name)" 1 with
      | { arguments = [ argument ]; _ }, _ when is_view argument -> ()
      | _ -> fail "no conversion recorded");
  test "a capability's method views a String argument too" (fun () ->
      let text = "fn f(name: String)\n  uses Console\n{\n  Console.print_line(name)\n}\n" in
      match core_call_at text "Console.print_line(name)" 1 with
      | { arguments = [ argument ]; _ }, _ when is_view argument -> ()
      | _ -> fail "no conversion recorded");
  test "a string literal is a String, viewed where a StringSlice is expected" (fun () ->
      let text = "fn f()\n  uses Console\n{\n  Console.print_line(\"hello\")\n}\n" in
      has_type text "\"hello\"" "String";
      match core_call_at text "Console.print_line(\"hello\")" 1 with
      | { arguments = [ argument ]; _ }, _ when is_view argument -> ()
      | _ -> fail "no conversion recorded");
  test "a cursor's next is the Cursor trait's, by the cursor's own impl" (fun () ->
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
      match core_at text "first.next()" 1 with
      | [ { kind = Cursor_next _; type_; _ } ] when Types.show type_ = "Option[Int64]" -> ()
      | _ -> fail "not the `next` of the cursor's own impl");
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
  test "the default of a parameter of a view type can be an owned value" (fun () ->
      fine
        "fn greet(name: StringSlice = \"world\", tags: Slice[Int64] = [1, 2]) -> USize {\n\
        \  name.length() + tags.length()\n\
         }\n\n\
         fn f() -> USize {\n\
        \  greet() + greet(\"you\")\n\
         }\n");
  test "`time` of a method that no bound of the type parameter declares is an error" (fun () ->
      one_diagnostic
        "fn f[Element: Equal](item: Element)\n  cost time O(time(Element.compare))\n{\n}\n"
        "types.unknown_member");
  test "a let cannot be assigned" (fun () ->
      one_diagnostic "fn f() {\n  let count = 0\n  count = 1\n}\n" "types.not_assignable");
  List.iter
    (fun (what, text) ->
      test (what ^ " cannot be marked `mut`") (fun () -> one_diagnostic text "types.wrong_mark"))
    [
      ("a read-only parameter", "fn f(items: List[Int64]) {\n  mut items.push(2)\n}\n");
      ("an `own` parameter", "fn f(items: own List[Int64]) {\n  mut items.push(2)\n}\n");
      ("a `let`", "fn f() {\n  let items: List[Int64] = [1]\n  mut items.push(2)\n}\n");
      ( "a field of a `let`",
        "type Config(ports: List[Int64])\n\n\
         fn f() {\n\
        \  let config = Config(ports: [1])\n\
        \  mut config.ports.push(2)\n\
         }\n" );
      ( "an element of a read-only parameter",
        "fn f(rows: List[List[Int64]]) {\n  mut rows[0].push(2)\n}\n" );
      ("a constant", "let names: List[Int64] = [1, 2]\n\nfn f() {\n  mut names.push(3)\n}\n");
      ( "a read-only argument",
        "fn change(items: mut List[Int64]) {}\n\n\
         fn f(items: List[Int64]) {\n\
        \  change(mut items)\n\
         }\n" );
      ( "the collection of a `for` loop that is a read-only parameter",
        "fn f(items: List[Int64]) {\n  for item in mut items {\n    item = 0\n  }\n}\n" );
      ( "`self` in a method that takes `self` read-only",
        "type Counter(counts: List[Int64])\n\n\
         fn Counter.add(self) {\n\
        \  mut self.counts.push(1)\n\
         }\n" );
      ( "`self` inside a lambda",
        "type Counter(counts: List[Int64])\n\n\
         fn Counter.add_all(mut self, items: List[Int64]) {\n\
        \  let _ = items.map(fn(item) {\n\
        \    mut self.counts.push(item)\n\
        \    item\n\
        \  })\n\
         }\n" );
      ( "a local that a lambda captures",
        "fn f(items: List[Int64]) {\n\
        \  var seen: List[Int64] = []\n\
        \  let _ = items.map(fn(item) {\n\
        \    mut seen.push(item)\n\
        \    item\n\
        \  })\n\
        \  let _ = seen\n\
         }\n" );
    ];
  test "a `var`, a `mut` parameter, `mut self`, and a `mut` loop variable can be marked `mut`"
    (fun () ->
      fine
        "type Counter(counts: List[Int64])\n\n\
         fn Counter.add(mut self) {\n\
        \  mut self.counts.push(1)\n\
         }\n\n\
         fn f(rows: mut List[List[Int64]]) {\n\
        \  var items: List[Int64] = [1]\n\
        \  mut items.push(2)\n\
        \  mut rows[0].push(3)\n\
        \  for row in mut rows {\n\
        \    mut row.push(4)\n\
        \  }\n\
         }\n");
  test "the variable of a loop over a call that yields `mut` can be marked `mut`" (fun () ->
      fine
        "trait Rows {\n\
        \  fn rows(mut self) yields mut List[Int64]\n\
         }\n\n\
         type Grid(cells: List[List[Int64]])\n\n\
         impl Rows for Grid {\n\
        \  fn rows(mut self) yields mut List[Int64] {\n\
        \    for row in mut self.cells {\n\
        \      yield mut row\n\
        \    }\n\
        \  }\n\
         }\n\n\
         fn f[Source: Rows](grid: mut Grid, source: mut Source) {\n\
        \  for row in mut grid.rows() {\n\
        \    mut row.push(1)\n\
        \  }\n\
        \  for row in mut source.rows() {\n\
        \    mut row.push(2)\n\
        \  }\n\
         }\n");
  test "a var can be assigned" (fun () ->
      fine "fn f() {\n  var count = 0\n  count = 1\n  let _ = count\n}\n");
  test "an empty list with nothing to decide its elements is an error" (fun () ->
      one_diagnostic "fn f() {\n  var names = []\n}\n" "types.cannot_infer");
  test "an empty list takes its elements' type from the annotation" (fun () ->
      fine "fn f() {\n  var names: List[String] = []\n}\n");
  test "a body's value must have the result type" (fun () ->
      one_diagnostic "fn f() -> Int64 {\n  true\n}\n" "types.mismatch");
  test "an arm of type Never does not contribute to the type of the match" (fun () ->
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
  test "a law's proof names the law's parameters, which have the proof's type for Self" (fun () ->
      fine
        "type Pair(first: UInt8, second: UInt8)\n\
        \  derives Equal\n\n\
         fn same(first: Pair, second: Pair) -> Bool {\n\
        \  first == second\n\
         }\n\n\
         impl Ordered for Pair {\n\
        \  fn compare(self, other: Pair) -> Ordering {\n\
        \    self.first.compare(other.first)\n\
        \  }\n\
         }\n\n\
         proof Ordered.agrees_with_equal for Pair {\n\
        \  let _ = same(first, second: second)\n\
         }\n");
  test "a law's proof for a generic impl is checked under its own generic parameters" (fun () ->
      fine
        "type Box[Item](item: Item)\n\n\
         fn smaller[Item: Ordered](first: Box[Item], second: Box[Item]) -> Bool {\n\
        \  first.item < second.item\n\
         }\n\n\
         impl Equal for Box[Item: Equal] {\n\
        \  fn equal(self, other: Box[Item]) -> Bool {\n\
        \    self.item == other.item\n\
        \  }\n\
         }\n\n\
         impl Ordered for Box[Item: Ordered] {\n\
        \  fn compare(self, other: Box[Item]) -> Ordering {\n\
        \    self.item.compare(other.item)\n\
        \  }\n\
         }\n\n\
         proof Ordered.transitive for Box[Element: Ordered] {\n\
        \  let _ = smaller(first, second: second)\n\
        \  let _ = first.item < third.item\n\
         }\n");
  test "a law's proof names no parameter of another law" (fun () ->
      one_diagnostic
        "type Pair(first: UInt8, second: UInt8)\n\
        \  derives Equal\n\n\
         impl Ordered for Pair {\n\
        \  fn compare(self, other: Pair) -> Ordering {\n\
        \    self.first.compare(other.first)\n\
        \  }\n\
         }\n\n\
         proof Ordered.agrees_with_equal for Pair {\n\
        \  let _ = third\n\
         }\n"
        "resolve.unknown_name");
  test "a law's proof cannot assign to a parameter of the law" (fun () ->
      one_diagnostic
        "type Pair(first: UInt8, second: UInt8)\n\
        \  derives Equal\n\n\
         impl Ordered for Pair {\n\
        \  fn compare(self, other: Pair) -> Ordering {\n\
        \    self.first.compare(other.first)\n\
        \  }\n\
         }\n\n\
         proof Ordered.agrees_with_equal for Pair {\n\
        \  first = second\n\
         }\n"
        "types.not_assignable");
  test "a variant with one field is a function" (fun () ->
      fine
        "type Shape =\n\
        \  | Circle(radius: Int64)\n\
        \  | Rectangle(width: Int64, height: Int64)\n\n\
         fn f(make: fn(own Int64) -> Shape) {}\n\n\
         fn g() {\n\
        \  f(Shape.Circle)\n\
         }\n");
  test "a variant with several fields is not a function, because fields have no order" (fun () ->
      one_diagnostic
        "type Shape =\n\
        \  | Circle(radius: Int64)\n\
        \  | Rectangle(width: Int64, height: Int64)\n\n\
         fn f(make: fn(own Int64, own Int64) -> Shape) {}\n\n\
         fn g() {\n\
        \  f(Shape.Rectangle)\n\
         }\n"
        "types.not_a_value");
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
  test "concurrent code needs `Tasks`, in a block and in a loop" (fun () ->
      one_diagnostic "fn g() {}\n\nfn f() {\n  concurrent {\n    g()\n    g()\n  }\n}\n"
        "capabilities.not_available";
      one_diagnostic
        "fn g(item: Int64) {}\n\n\
         fn f(items: List[Int64]) {\n\
        \  concurrent for item in items {\n\
        \    g(item)\n\
        \  }\n\
         }\n"
        "capabilities.not_available");
  test "a branch of a concurrent block uses the capabilities around the block" (fun () ->
      fine
        "fn tick()\n\
        \  uses Clock\n\
         {\n\
         }\n\n\
         fn f(items: List[Int64])\n\
        \  uses Tasks, Clock\n\
         {\n\
        \  concurrent {\n\
        \    tick()\n\
        \    tick()\n\
        \  }\n\
        \  concurrent for item in items {\n\
        \    let _ = item\n\
        \    tick()\n\
        \  }\n\
         }\n");
  (let sessions =
     "capability Sessions {\n\
     \  fn touch(session: USize)\n\
     \  fn each(visit: (fn(USize) uses Clock))\n\
      }\n\n\
      type Table(sessions: List[USize])\n\n\
      impl Sessions for Table {\n\
     \  fn touch(mut self, session: USize) {\n\
     \    mut self.sessions.push(session)\n\
     \  }\n\n\
     \  fn each(mut self, visit: (fn(USize) uses Clock)) {\n\
     \  }\n\
      }\n\n\
      fn serve(session: USize)\n\
     \  uses Sessions\n\
      {\n\
     \  Sessions.touch(session)\n\
      }\n\n"
   in
   test "a capability implemented by a monitor has no method with a callback that uses a capability"
     (fun () ->
       one_diagnostic
         (sessions
        ^ "fn f()\n\
          \  uses Tasks\n\
           {\n\
          \  var table = Table(sessions: [])\n\
          \  provide mut table {\n\
          \    concurrent {\n\
          \      serve(1)\n\
          \      serve(2)\n\
          \    }\n\
          \  }\n\
           }\n")
         "capabilities.callback_may_deadlock");
   test "an implementation is not a monitor if the body of its `provide` cannot use `Tasks`"
     (fun () ->
       fine
         (sessions
        ^ "fn f() {\n\
          \  var table = Table(sessions: [])\n\
          \  provide mut table {\n\
          \    serve(1)\n\
          \    serve(2)\n\
          \  }\n\
           }\n"));
   let tally =
     "capability Counter {\n\
     \  fn bump()\n\
      }\n\n\
      type Tally(count: USize)\n\n\
      impl Counter for Tally {\n\
     \  fn bump(mut self) {\n\
     \    self.count = 1\n\
     \  }\n\
      }\n\n\
      type Scheduler(turn: UInt64)\n\n\
      impl Tasks for Scheduler {\n\
     \  fn open(self) -> UInt64 {\n\
     \    0\n\
     \  }\n\n\
     \  fn spawn(self, task_group: UInt64, work: own fn(UInt64), item: UInt64) -> Bool {\n\
     \    false\n\
     \  }\n\n\
     \  fn join(self, task_group: UInt64) {}\n\n\
     \  fn cancel(self, task_group: UInt64) -> Bool {\n\
     \    false\n\
     \  }\n\n\
     \  fn cancelled(self) -> Bool {\n\
     \    false\n\
     \  }\n\n\
     \  fn watch(self, key: UInt64) -> UInt64 {\n\
     \    0\n\
     \  }\n\n\
     \  fn wait(self, key: UInt64, ticket: UInt64, reason: StringSlice) {}\n\n\
     \  fn wake(self, key: UInt64) {}\n\n\
     \  fn lock(self, mutex: UInt64) {}\n\n\
     \  fn unlock(self, mutex: UInt64) {}\n\n\
     \  fn yield_now(self) {}\n\
      }\n\n\
      fn count_once()\n\
     \  uses Counter\n\
      {\n\
     \  Counter.bump()\n\
      }\n\n"
   in
   test "a monitor needs `Tasks` at its `provide`, not only in a nested one" (fun () ->
       one_diagnostic
         (tally
        ^ "fn f() {\n\
          \  var tally = Tally(count: 0)\n\
          \  let scheduler = Scheduler(turn: 0)\n\
          \  provide mut tally {\n\
          \    provide scheduler {\n\
          \      concurrent {\n\
          \        count_once()\n\
          \        count_once()\n\
          \      }\n\
          \    }\n\
          \  }\n\
           }\n")
         "capabilities.monitor_needs_tasks");
   test
     "a monitor can lock through `Tasks` of its `provide`, an enclosing one, or a capability \
      parameter" (fun () ->
       fine
         (tally
        ^ "fn same() {\n\
          \  var tally = Tally(count: 0)\n\
          \  let scheduler = Scheduler(turn: 0)\n\
          \  provide mut tally, scheduler {\n\
          \    concurrent {\n\
          \      count_once()\n\
          \      count_once()\n\
          \    }\n\
          \  }\n\
           }\n\n\
           fn enclosing() {\n\
          \  var tally = Tally(count: 0)\n\
          \  let scheduler = Scheduler(turn: 0)\n\
          \  provide scheduler {\n\
          \    provide mut tally {\n\
          \      concurrent {\n\
          \        count_once()\n\
          \        count_once()\n\
          \      }\n\
          \    }\n\
          \  }\n\
           }\n\n\
           fn through_parameter[capability Granted](run: (fn() uses Granted))\n\
          \  uses Granted\n\
           {\n\
          \  var tally = Tally(count: 0)\n\
          \  provide mut tally {\n\
          \    run()\n\
          \  }\n\
           }\n")));
  test "an assignment through an index of a map takes the key as an owned value" (fun () ->
      fine
        "fn f(name: own String) -> USize {\n\
        \  var ports: Map[String, Int64] = [\"http\": 80]\n\
        \  ports[\"ftp\"] = 21\n\
        \  ports[own name] = 8080\n\
        \  ports.length()\n\
         }\n";
      one_diagnostic
        "fn f(name: String) {\n\
        \  var ports: Map[String, Int64] = [\"http\": 80]\n\
        \  ports[name] = 8080\n\
         }\n"
        "types.missing_mark";
      one_diagnostic "fn f(ports: Map[String, Int64]) {\n  ports[\"ftp\"] = 21\n}\n"
        "types.not_assignable");
  (let keep =
     "type Labeled(view: Slice[Int64], name: String)\n\n\
      type Boxed[Value](value: Value)\n\n\
      fn keep[Value: Storable](value: own Value) {}\n\n\
      fn double(value: Int64) -> Int64 {\n\
     \  value\n\
      }\n\n\
      trait Job: Storable {\n\
     \  fn run(self) -> Int64\n\
      }\n\n\
      trait Task {\n\
     \  fn run(self) -> Int64\n\
      }\n\n\
      type Count(value: Int64)\n\n\
      impl Job for Count {\n\
     \  fn run(self) -> Int64 {\n\
     \    self.value\n\
     \  }\n\
      }\n\n\
      impl Task for Count {\n\
     \  fn run(self) -> Int64 {\n\
     \    self.value\n\
     \  }\n\
      }\n\n"
   in
   test "a type that holds no view is Storable" (fun () ->
       fine
         (keep
        ^ "fn f[Element: Storable](names: own List[String], element: own Element) {\n\
          \  keep(5)\n\
          \  keep(own names)\n\
          \  keep(Boxed(value: \"a\".copy()))\n\
          \  keep(own element)\n\
           }\n"));
   test "an any type is Storable when its trait requires Storable" (fun () ->
       fine (keep ^ "fn f() {\n  let job: any Job = any Count(value: 1)\n  keep(own job)\n}\n"));
   test "a trait that requires Storable cannot be implemented for a view type" (fun () ->
       one_diagnostic
         (keep ^ "impl Job for Labeled {\n  fn run(self) -> Int64 {\n    0\n  }\n}\n")
         "types.missing_required_impl");
   List.iter
     (fun (name, body) ->
       test name (fun () -> one_diagnostic (keep ^ body) "types.unsatisfied_bound"))
     [
       ("a slice is not Storable", "fn f(items: List[Int64]) {\n  keep(items[..])\n}\n");
       ( "a record that holds a slice is not Storable",
         "fn f(items: List[Int64]) {\n  keep(Labeled(view: items[..], name: \"a\".copy()))\n}\n" );
       ( "a generic type is not Storable where its argument is not",
         "fn f(items: List[Int64]) {\n  keep(Boxed(value: items[..]))\n}\n" );
       ("a function type is not Storable", "fn f() {\n  keep(double)\n}\n");
       ( "an any type is not Storable when its trait does not require it",
         "fn f() {\n  let task: any Task = any Count(value: 1)\n  keep(own task)\n}\n" );
       ( "a type parameter is Storable only when it is bounded",
         "fn f[Element](element: own Element) {\n  keep(own element)\n}\n" );
     ];
   test "no impl of Storable can be written" (fun () ->
       one_diagnostic (keep ^ "impl Storable for Labeled {}\n") "types.implements_built_in"));
  test "the body of a concurrent block gets its types" (fun () ->
      has_type
        "fn g(count: UInt16) {}\n\n\
         fn f(count: UInt16) {\n\
        \  concurrent {\n\
        \    g(count + 2)\n\
        \  }\n\
         }\n"
        "2" "UInt16");
  test "a lambda's captures are the outer locals it reads" (fun () ->
      let text =
        "fn f(items: List[Int64], step: Int64) -> List[Int64] {\n\
        \  items.map(fn(item) { item + step })\n\
         }\n"
      in
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match node.kind with Lambda { captures; _ } -> Some captures | _ -> None)
          (first_core_nodes text).expressions
      with
      | [ [ _ ] ] -> ()
      | [ found ] -> fail "%d captures" (List.length found)
      | found -> fail "%d lambdas" (List.length found))

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
      fine "fn f(count: UInt32, items: List[Int64])\n  requires count <= items.length()\n{\n}\n");
  test "a lambda in a specification may give a built-in integer for an Integer" (fun () ->
      fine
        "fn f(rows: List[List[Int64]])\n\
        \  requires rows.model().sum(fn(cells) { cells.length() }) > 0\n\
         {\n\
         }\n")

(* Loops *)

let () =
  test "a for loop over a range of integers is a counted loop" (fun () ->
      let text = "fn f(count: USize) {\n  for i in 0..count {\n    let _ = i\n  }\n}\n" in
      if
        not
          (List.exists
             (fun (node : Core.statement) ->
               match node.kind with For { iteration = Integer_range _; _ } -> true | _ -> false)
             (first_core_nodes text).statements)
      then fail "no counted loop");
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
      let engine = Engine.of_context database in
      let module_ = module_of "app::main" in
      expect_not_recomputed engine
        ~first:(fun () -> ignore (Infer.diagnostics database module_))
        ~again:(fun () ->
          Database.Testing.set_text engine module_ (text "2");
          ignore (Infer.diagnostics database module_))
        Infer.type_check_result
        [ top_key "app::main" "caller" ]);
  test "checking twice gives the same result" (fun () ->
      let text =
        "fn f(items: List[Int64]) -> Int64 {\n\
        \  var total = 0\n\
        \  for item in items {\n\
        \    total += item\n\
        \  }\n\
        \  total\n\
         }\n"
      in
      let type_check_result () =
        let database = setup [ ("app::main", text) ] in
        let key =
          Resolve.Names.key_of
            (List.hd (Query.demand database Resolve.Names.declarations (module_of "app::main")))
        in
        Query.demand database Infer.type_check_result key
      in
      if type_check_result () <> type_check_result () then fail "different")

let () =
  test "no table of the standard library holds a type inference left unsolved" (fun () ->
      let database = setup [] in
      let rec unsolved = function
        | Types.Variable _ | Types.Literal _ -> true
        | Types.Named { arguments; _ } | Types.Cursor { arguments; _ } ->
            List.exists (function Types.Type type_ -> unsolved type_ | _ -> false) arguments
        | Types.Function { inputs; output; _ } -> (
            List.exists (fun (_, type_) -> unsolved type_) inputs
            ||
            match output with
            | Returns type_ | Yields (_, type_) | Lends (_, type_) -> unsolved type_)
        | _ -> false
      in
      List.iter
        (fun ((module_ : Path.module_), _) ->
          List.iter
            (fun (declaration : Resolve.Names.declaration) ->
              match
                Query.demand database Infer.type_check_result (Resolve.Names.key_of declaration)
              with
              | Some { tables; _ } ->
                  List.iter
                    (Array.iter (function
                      | Some type_ when unsolved type_ ->
                          fail "%s: an unsolved type" (Path.show declaration.path)
                      | _ -> ()))
                    [ tables.types; tables.local_types ]
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
        \  fn multiply_is_defined(self, right: Int64) -> Bool { true }\n\
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
  test "a for loop takes each version from the type or from a trait" (fun () ->
      fine
        "type Bag(items: List[Int64])\n\n\
         impl Iterable for Bag {\n\
        \  type Element = Int64\n\
        \  fn each(self) yields Int64 { todo }\n\
         }\n\n\
         fn Bag.each(mut self) yields mut Int64 { todo }\n\n\
         fn f(bag: mut Bag) -> Int64 {\n\
        \  for item in mut bag {\n\
        \    item = 0\n\
        \  }\n\
        \  var last: Int64 = 0\n\
        \  for item in bag {\n\
        \    last = item\n\
        \  }\n\
        \  last\n\
         }\n");
  test "a call picks a version among a type's own and its family of traits'" (fun () ->
      fine
        "trait Shown {\n\
        \  fn label(self) -> Int64\n\
         }\n\n\
         trait Cleared: Shown {\n\
        \  fn label(mut self) -> Int64\n\
         }\n\n\
         type Counter(count: Int64)\n\n\
         impl Shown for Counter {\n\
        \  fn label(self) -> Int64 { todo }\n\
         }\n\n\
         impl Cleared for Counter {\n\
        \  fn label(mut self) -> Int64 { todo }\n\
         }\n\n\
         fn Counter.label(own self) -> Int64 { todo }\n\n\
         fn f(counter: mut Counter) -> Int64 {\n\
        \  let read = counter.label()\n\
        \  let cleared = mut counter.label()\n\
        \  let made = Counter(count: 3).label()\n\
        \  let in_full = Counter.label(mut counter)\n\
        \  let through_trait = Shown.label(counter)\n\
        \  read.max(cleared).max(made).max(in_full).max(through_trait)\n\
         }\n");
  test "two traits that give one version of a name are ambiguous at the call" (fun () ->
      one_diagnostic
        "trait First {\n\
        \  fn label(self) -> Int64\n\
         }\n\n\
         trait Second {\n\
        \  fn label(self) -> Int64\n\
         }\n\n\
         type Counter(count: Int64)\n\n\
         impl First for Counter {\n\
        \  fn label(self) -> Int64 { todo }\n\
         }\n\n\
         impl Second for Counter {\n\
        \  fn label(self) -> Int64 { todo }\n\
         }\n\n\
         fn f(counter: Counter) -> Int64 {\n\
        \  counter.label()\n\
         }\n"
        "types.ambiguous_method"
        ~fixed:
          "trait First {\n\
          \  fn label(self) -> Int64\n\
           }\n\n\
           trait Second {\n\
          \  fn label(self) -> Int64\n\
           }\n\n\
           type Counter(count: Int64)\n\n\
           impl First for Counter {\n\
          \  fn label(self) -> Int64 { todo }\n\
           }\n\n\
           impl Second for Counter {\n\
          \  fn label(self) -> Int64 { todo }\n\
           }\n\n\
           fn f(counter: Counter) -> Int64 {\n\
          \  First.label(counter)\n\
           }\n");
  test "two unrelated traits that share a name are ambiguous however each takes self" (fun () ->
      one_diagnostic
        "trait First {\n\
        \  fn label(self) -> Int64\n\
         }\n\n\
         trait Second {\n\
        \  fn label(own self) -> Int64\n\
         }\n\n\
         type Counter(count: Int64)\n\n\
         impl First for Counter {\n\
        \  fn label(self) -> Int64 { todo }\n\
         }\n\n\
         impl Second for Counter {\n\
        \  fn label(own self) -> Int64 { todo }\n\
         }\n\n\
         fn f() -> Int64 {\n\
        \  Counter(count: 3).label()\n\
         }\n"
        "types.ambiguous_method");
  test "two bounds that give one version of a name are ambiguous through the type" (fun () ->
      one_diagnostic
        "trait First {\n\
        \  fn make() -> Self\n\
         }\n\n\
         trait Second {\n\
        \  fn make() -> Self\n\
         }\n\n\
         fn f[Value: First + Second]() -> Value {\n\
        \  Value.make()\n\
         }\n"
        "types.ambiguous_method");
  test "two unrelated bounds that share a name are ambiguous however each takes self" (fun () ->
      one_diagnostic
        "trait First {\n\
        \  fn label(self) -> Int64\n\
         }\n\n\
         trait Second {\n\
        \  fn label(mut self) -> Int64\n\
         }\n\n\
         fn f[Value: First + Second](value: Value) -> Int64 {\n\
        \  value.label()\n\
         }\n"
        "types.ambiguous_method");
  test "a bound's method is picked from its family by how the call takes self" (fun () ->
      fine
        "trait Shown {\n\
        \  fn label(self) -> Int64\n\
         }\n\n\
         trait Cleared: Shown {\n\
        \  fn label(mut self) -> Int64\n\
         }\n\n\
         fn f[Value: Cleared](value: mut Value) -> Int64 {\n\
        \  let read = value.label()\n\
        \  let cleared = mut value.label()\n\
        \  let in_full = Value.label(mut value)\n\
        \  read.max(cleared).max(in_full)\n\
         }\n");
  test "a trait's method written in full has no version for a mark it lacks" (fun () ->
      one_diagnostic
        "trait Shown {\n\
        \  fn label(self) -> Int64\n\
         }\n\n\
         fn f[Value: Shown](value: mut Value) -> Int64 {\n\
        \  Shown.label(mut value)\n\
         }\n"
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
  test "a mistake is not reported again as a type that cannot be inferred" (fun () ->
      let database =
        setup
          [ ("app::main", "fn f(items: List[Int64]) {\n  let _ = items.map(undefined_thing)\n}\n") ]
      in
      if List.mem "types.cannot_infer" (codes (check database (module_of "app::main"))) then
        fail "cascaded");
  test "a Float32 literal too large is an error" (fun () ->
      one_diagnostic "fn f() {\n  let large: Float32 = 3.5e38\n}\n" "types.literal_out_of_range");
  test "a Float32 literal is rounded once, from its decimal" (fun () ->
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match node.kind with Float rounded -> Some rounded | _ -> None)
          (first_core_nodes "fn f() {\n  let value: Float32 = 1.0000000596046447754\n}\n")
            .expressions
      with
      | [ rounded ] ->
          if rounded <> Float.of_string "0x1.000002p+0" then fail "rounded to %h" rounded
      | _ -> fail "no value");
  test "a range pattern has the values of its two bounds" (fun () ->
      match
        List.filter_map
          (fun (node : Core.pattern) ->
            match node.kind with
            | Range { start = { kind = Integer low; _ }; stop = { kind = Integer high; _ }; _ } ->
                Some (Z.to_int low, Z.to_int high)
            | _ -> None)
          (first_core_nodes
             "fn f(n: Int64) -> Int64 {\n  match n {\n    1..=5 => 1\n    _ => 2\n  }\n}\n")
            .patterns
      with
      | [ (1, 5) ] -> ()
      | _ -> fail "the range pattern does not have the bounds 1 and 5");
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
      if not (has_integer "fn f() -> Character {\n  Character\"é\"\n}\n" 0xE9) then fail "no value");
  test "a UInt8 literal holds its ASCII character's value" (fun () ->
      if not (has_integer "fn f() -> UInt8 {\n  UInt8\"\\n\"\n}\n" 10) then fail "no value");
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
  test "a lambda cannot mutate a captured variable" (fun () ->
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
  test "==> in a compiled body" (fun () ->
      one_diagnostic "fn f(a: Bool, b: Bool) -> Bool {\n  a ==> b\n}\n" "types.specification_only");
  test "a quantifier over a type in a compiled body" (fun () ->
      one_diagnostic "fn f() -> Bool {\n  forall value: Int64 => value == value\n}\n"
        "types.specification_only");
  test "a function for specifications only has a specification for a body" (fun () ->
      fine
        "fn holds(limit: Integer) -> Bool {\n\
        \  forall value: Int64 => value > 0 ==> value + limit > limit\n\
         }\n");
  test "a constant in a pattern needs structural equality" (fun () ->
      one_diagnostic
        "type Point(x: Float64)\n\
        \  derives Equal\n\n\
         let origin: Point = Point(x: 0.0)\n\n\
         fn f(point: Point) -> Bool {\n\
        \  match point {\n\
        \    origin => true\n\
        \    _ => false\n\
        \  }\n\
         }\n"
        "types.not_structural");
  test "a constant of a derived type of integers in a pattern" (fun () ->
      fine
        "type Point(x: Int64)\n\
        \  derives Equal\n\n\
         let origin: Point = Point(x: 0)\n\n\
         fn f(point: Point) -> Bool {\n\
        \  match point {\n\
        \    origin => true\n\
        \    _ => false\n\
        \  }\n\
         }\n");
  test "a provided method without a time clause cannot be replaced" (fun () ->
      Support.one_diagnostic ~check:Type_checker.diagnostics
        "trait Doubling {\n\
        \  fn doubled(self) -> Bool {\n\
        \    true\n\
        \  }\n\
         }\n\n\
         type Amount(cents: Int64)\n\n\
         impl Doubling for Amount {\n\
        \  fn doubled(self) -> Bool {\n\
        \    false\n\
        \  }\n\
         }\n"
        "types.not_replaceable");
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

(* Every error type carries its report, so nothing is accepted of code that
   reported nothing: what was once an error with no report is reported. *)

let identity = "fn identity[Value](value: own Value) -> Value {\n  value\n}\n\n"

let () =
  test "type arguments after a parenthesized name are read as after the name" (fun () ->
      fine (identity ^ "fn f() -> Int64 {\n  (identity)[Int64](5)\n}\n");
      one_diagnostic (identity ^ "fn f() -> String {\n  (identity)[Int64](5)\n}\n") "types.mismatch");
  test "a parenthesized name with type arguments is a value of that function" (fun () ->
      fine (identity ^ "fn f() -> Int64 {\n  let same = (identity)[Int64]\n  same(5)\n}\n"));
  test "a trait's written arguments are the ones its call uses" (fun () ->
      let database = setup [ ("app::main", "fn f() -> Int64 {\n  Add[String].add(1, 2)\n}\n") ] in
      if not (List.mem "types.no_impl" (codes (check database (module_of "app::main")))) then
        fail "the written argument was ignored");
  test "a literal is the receiver of a trait method written in full" (fun () ->
      fine "fn f() -> Int64 {\n  Add[Int64].add(1, 2)\n}\n");
  test "a generic parameter takes no type arguments" (fun () ->
      one_diagnostic "fn f[Element: Default]() -> Element {\n  Element[Int64].default()\n}\n"
        "types.arity");
  test "a member of a generic parameter that it does not have is an error" (fun () ->
      one_diagnostic "fn f[Element](value: Element) -> Int64 {\n  Element.anything\n}\n"
        "types.unknown_member");
  test "a type with no fields is not its own value" (fun () ->
      one_diagnostic "type Marker()\n\nfn f() -> Marker {\n  Marker\n}\n" "types.not_a_value");
  test "`self` outside a method is an error" (fun () ->
      one_diagnostic "fn f() -> Int64 {\n  self.anything\n}\n" "types.not_a_value");
  test "`old` without what it is about is an error" (fun () ->
      one_diagnostic "fn f(value: Int64) -> Int64\n  ensures old == 3\n{\n  value\n}\n"
        "types.not_a_value");
  test "a type argument that nothing decides is an error at its call" (fun () ->
      one_diagnostic "fn make[Value]() -> Int64 {\n  1\n}\n\nfn f() -> Int64 {\n  make()\n}\n"
        "types.cannot_infer");
  test "a trait is not called" (fun () ->
      one_diagnostic "fn f() -> Int64 {\n  Ordered[Int64](1)\n}\n" "types.not_callable");
  test "a generic function given type arguments, as a value, must meet its bounds" (fun () ->
      one_diagnostic
        (point
       ^ "fn need[Value: Ordered](value: Value) -> Bool {\n\
         \  true\n\
          }\n\n\
          fn f() {\n\
         \  let check = need[Point]\n\
         \  let _ = check\n\
          }\n")
        "types.unsatisfied_bound");
  test "the scrutinee of an `is` is inferred before its pattern is checked" (fun () ->
      fine
        "type Span(ticks: Int64)\n\n\
         impl Divide[Int64] for Span {\n\
        \  type Output = Option[Span]\n\n\
        \  fn divide_is_defined(self, right: Int64) -> Bool { true }\n\n\
        \  fn divide(self, right: Int64) -> Option[Span] {\n\
        \    todo\n\
        \  }\n\
         }\n\n\
         fn f(span: Span) -> Bool {\n\
        \  span / 0 is None\n\
         }\n");
  test "a `for` over a call of `each` binds the yielded elements" (fun () ->
      fine
        "fn total(items: List[Int64]) -> Int64 {\n\
        \  var sum = 0\n\
        \  for item in items.each() {\n\
        \    sum += item\n\
        \  }\n\
        \  sum\n\
         }\n");
  test "`Self` in the body of a method without `self` is the method's type" (fun () ->
      fine
        "type Box(value: Int64)\n\n\
         fn Box.made() -> Box {\n\
        \  let made: Self = Box(value: 1)\n\
        \  made\n\
         }\n");
  test "a pattern that does not fit its type still gives its bindings a type" (fun () ->
      one_diagnostic
        "fn f(value: Int64) -> Int64 {\n\
        \  match value {\n\
        \    Some(inner) => inner\n\
        \    _ => 0\n\
        \  }\n\
         }\n"
        "types.unknown_variant");
  test "a `todo` that nothing decides keeps the hole type in the tables" (fun () ->
      has_type "fn f() {\n  let later = todo\n  let _ = later\n}\n" "todo" "an undecided type")

(* Bounds wherever generic parameters are filled in *)

let shape =
  "trait Shape {\n\
  \  fn area(self) -> Int64\n\
   }\n\n\
   type Square(side: Int64)\n\n\
   impl Shape for Square {\n\
  \  fn area(self) -> Int64 {\n\
  \    self.side\n\
  \  }\n\
   }\n\n\
   type Holder[Value: Shape](value: Value)\n\n\
   fn Holder[Value: Shape].area(self) -> Int64 {\n\
  \  self.value.area()\n\
   }\n\n"

let source =
  "trait Source {\n\
  \  type Item\n\
  \  fn first(self) -> Self.Item\n\
   }\n\n\
   type Numbers(items: List[Int64])\n\n\
   impl Source for Numbers {\n\
  \  type Item = Int64\n\n\
  \  fn first(self) -> Int64 {\n\
  \    self.items[0]\n\
  \  }\n\
   }\n\n"

let () =
  test "a value built of a generic type must meet the type's bounds" (fun () ->
      one_diagnostic (shape ^ "fn f() {\n  let _ = Holder(5)\n}\n") "types.unsatisfied_bound");
  test "a value built of a generic type that meets its bounds is fine" (fun () ->
      fine (shape ^ "fn f() {\n  let _ = Holder(Square(2))\n}\n"));
  test "a value built inside another must meet its type's bounds" (fun () ->
      one_diagnostic (shape ^ "fn f() {\n  let _ = Some(Holder(5))\n}\n") "types.unsatisfied_bound");
  test "a variant built of a generic type must meet the type's bounds" (fun () ->
      one_diagnostic
        (shape
       ^ "type Slot[Value: Shape] =\n\
         \  | Empty\n\
         \  | Full(value: Value)\n\n\
          fn f() {\n\
         \  let _ = Slot.Full(5)\n\
          }\n")
        "types.unsatisfied_bound");
  test "a generic type named in an expression must meet its bounds" (fun () ->
      one_diagnostic
        (shape
       ^ "type Slot[Value: Shape] =\n\
         \  | Empty\n\
         \  | Full(value: Value)\n\n\
          fn f() {\n\
         \  let _ = Slot[Int64].Empty\n\
          }\n")
        "types.unsatisfied_bound");
  test "a statement reports a bound once, however many of its parts need it" (fun () ->
      one_diagnostic
        (shape ^ "fn f() -> Int64 {\n  Holder[Int64].area(Holder(5))\n}\n")
        "types.unsatisfied_bound");
  test "a method used as a value must meet its bounds" (fun () ->
      one_diagnostic
        (shape
       ^ "fn Square.fits[Other: Shape](self, other: Other) -> Bool {\n\
         \  true\n\
          }\n\n\
          fn f() {\n\
         \  let fits: fn(Square, Int64) -> Bool = Square.fits\n\
         \  let _ = fits\n\
          }\n")
        "types.unsatisfied_bound");
  test "function types that count the calls of different capabilities are different types"
    (fun () ->
      let lists counted =
        "fn take(runs: List[(fn() uses Clock, Console cost calls(Console) <= 1)]) {}\n\n\
         fn f(runs: List[(fn() uses Clock, Console cost calls(" ^ counted
        ^ ") <= 1)]) {\n  take(runs)\n}\n"
      in
      fine (lists "Console");
      one_diagnostic (lists "Clock") "types.mismatch";
      one_diagnostic (lists "Console.print_line") "types.mismatch");
  test "the target of `calls` in a function type is a capability or one of its methods" (fun () ->
      one_diagnostic "type Point(x: Int64)\n\nfn f(run: (fn() cost calls(Point) <= 1)) {}\n"
        "types.not_a_capability";
      one_diagnostic "fn f(run: (fn() uses Clock cost calls(Clock.later) <= 1)) {}\n"
        "types.unknown_member";
      one_diagnostic "fn f(visit: fn(), run: (fn() cost calls(visit) <= 1)) {}\n"
        "types.not_a_capability");
  test
    "the target of `calls` in a clause is a function parameter, a capability, or a capability's \
     method" (fun () ->
      let clause counted =
        "type Point(x: Int64)\n\n\
         fn f(count: Int64, visit: (fn() cost time finite))\n\
        \  uses Clock\n\
        \  cost calls(" ^ counted ^ ") <= 1\n{\n  todo\n}\n"
      in
      fine (clause "visit");
      fine (clause "Clock");
      fine (clause "Clock.now");
      one_diagnostic (clause "count") "types.not_callable";
      one_diagnostic (clause "Point") "types.not_a_capability";
      one_diagnostic (clause "Clock.later") "types.unknown_member");
  test "a method with generic parameters is not object-safe" (fun () ->
      one_diagnostic
        "trait Visitor {\n\
        \  fn visit[Other](self, other: Other) -> Int64\n\
         }\n\n\
         fn f(visitor: any Visitor) -> Int64 {\n\
        \  visitor.visit(3)\n\
         }\n"
        "types.not_callable");
  test "a method that takes or returns Self cannot be called through any" (fun () ->
      one_diagnostic
        "trait Joined {\n\
        \  fn join(self, other: Self) -> Int64\n\
         }\n\n\
         fn f(first: any Joined, second: any Joined) -> Int64 {\n\
        \  first.join(second)\n\
         }\n"
        "types.not_callable");
  test "a method whose result holds Self cannot be called through any" (fun () ->
      one_diagnostic
        "fn f(items: List[Int64]) -> USize {\n\
        \  var boxed: any Cursor[Element = Int64] = any items.each()\n\
        \  let _ = own boxed.skip(1)\n\
        \  0\n\
         }\n"
        "types.not_callable");
  test "a cursor's own step and its counting can be called through any" (fun () ->
      fine
        "fn f(items: List[Int64]) -> USize {\n\
        \  var boxed: any Cursor[Element = Int64] = any items.each()\n\
        \  let _ = mut boxed.next()\n\
        \  own boxed.count()\n\
         }\n");
  test "a method that names an associated type can be called through any" (fun () ->
      fine
        (source
       ^ "fn f(numbers: own Numbers) -> Int64 {\n\
         \  let source: any Source[Item = Int64] = any numbers\n\
         \  source.first()\n\
          }\n"));
  test "`any value` must give the associated types its type fixes" (fun () ->
      one_diagnostic
        (source
       ^ "fn f(numbers: own Numbers) -> String {\n\
         \  let source: any Source[Item = String] = any numbers\n\
         \  source.first()\n\
          }\n")
        "types.no_impl");
  test "`any value` that gives the associated types its type fixes is fine" (fun () ->
      fine
        (source
       ^ "fn f(numbers: own Numbers) -> Int64 {\n\
         \  let source: any Source[Item = Int64] = any numbers\n\
         \  source.first()\n\
          }\n"));
  test "`any value` of a generic parameter needs a bound that fixes the associated types" (fun () ->
      one_diagnostic
        (source
       ^ "fn f[Input: Source](input: own Input) -> Int64 {\n\
         \  let source: any Source[Item = Int64] = any input\n\
         \  source.first()\n\
          }\n")
        "types.no_impl");
  test "`any value` of a generic parameter whose bound fixes the associated types is fine"
    (fun () ->
      fine
        (source
       ^ "fn f[Input: Source[Item = Int64]](input: own Input) -> Int64 {\n\
         \  let source: any Source[Item = Int64] = any input\n\
         \  source.first()\n\
          }\n"));
  test "an associated type a bound fixes works out a type argument" (fun () ->
      fine
        (source
       ^ "fn first_of[Input: Source[Item = Output], Output](input: Input) -> Output {\n\
         \  input.first()\n\
          }\n\n\
          fn f(numbers: Numbers) -> Int64 {\n\
         \  let first = first_of(numbers)\n\
         \  first\n\
          }\n"));
  test "an associated type a bound fixes must be the one the impl gives" (fun () ->
      one_diagnostic
        (source
       ^ "fn text_of[Input: Source[Item = String]](input: Input) -> String {\n\
         \  input.first()\n\
          }\n\n\
          fn f(numbers: Numbers) -> String {\n\
         \  text_of(numbers)\n\
          }\n")
        "types.unsatisfied_bound")

(* Constant expressions *)

let point = "type Point(x: Int64, y: Int64)\n\n"

let () =
  test "a constant is built from literals, operators on numbers, and other constants" (fun () ->
      fine
        "let small: UInt8 = 200 + 55\n\n\
         let lowest: Int8 = -128\n\n\
         let is_small: Bool = small < 10 && !(small == 4)\n");
  test "a constant builds records, variants, and collections of constants" (fun () ->
      fine
        (point
       ^ "let origin: Point = Point(x: 1, y: 2 * 3)\n\n\
          let points: List[Point] = [origin, Point(x: 0, y: 0)]\n\n\
          let no_point: Option[Point] = None\n\n\
          let wrapped: Option[Int64] = Some(4)\n\n\
          let first: Int64 = origin.x\n\n\
          let epoch: Instant = Instant.epoch\n"));
  test "a constant cannot call a function" (fun () ->
      one_diagnostic "fn compute() -> Int64 {\n  1\n}\n\nlet computed: Int64 = compute()\n"
        "types.not_constant");
  test "a constant cannot call a capability" (fun () ->
      one_diagnostic "let started: Instant = Clock.now()\n" "types.not_constant");
  test "a constant cannot call a method" (fun () ->
      one_diagnostic "let length: USize = \"four\".length()\n" "types.not_constant");
  test "a constant cannot index a collection" (fun () ->
      one_diagnostic "let numbers: List[Int64] = [1, 2]\n\nlet first: Int64 = numbers[0]\n"
        "types.not_constant");
  test "a constant cannot branch" (fun () ->
      one_diagnostic "let chosen: Int64 = if true { 1 } else { 2 }\n" "types.not_constant");
  test "a constant cannot use an operator that a type defines" (fun () ->
      one_diagnostic "let greeting: String = \"a\"\n\nlet same: Bool = greeting == greeting\n"
        "types.not_constant");
  test "a constant's arithmetic must stay within its type" (fun () ->
      one_diagnostic "let size: USize = 0 - 1\n" "types.constant_overflow");
  test "each step of a constant's arithmetic must stay within its type" (fun () ->
      one_diagnostic "let small: UInt8 = 200 + 100 - 100\n" "types.constant_overflow");
  test "a constant's arithmetic through another constant must stay within its type" (fun () ->
      one_diagnostic "let most: UInt8 = 255\n\nlet more: UInt8 = most + 1\n"
        "types.constant_overflow");
  test "negating a constant's least value overflows" (fun () ->
      one_diagnostic "let flipped: Int8 = -(-128)\n" "types.constant_overflow");
  test "a constant cannot divide by zero" (fun () ->
      one_diagnostic "let nothing: Int64 = 5 / 0\n" "types.constant_overflow");
  test "a default must be a constant expression" (fun () ->
      one_diagnostic "fn compute() -> Int64 {\n  1\n}\n\nfn f(count: Int64 = compute()) {}\n"
        "types.default_not_constant");
  test "a default cannot name a parameter" (fun () ->
      one_diagnostic "fn f(count: Int64, twice: Int64 = count * 2) {}\n"
        "types.default_not_constant");
  test "a method's default must be a constant expression" (fun () ->
      one_diagnostic
        (point
       ^ "fn compute() -> Int64 {\n\
         \  1\n\
          }\n\n\
          fn Point.moved(self, by: Int64 = compute()) -> Int64 {\n\
         \  self.x + by\n\
          }\n")
        "types.default_not_constant");
  test "a field's default must be a constant expression" (fun () ->
      one_diagnostic "fn compute() -> Int64 {\n  1\n}\n\ntype Settings(limit: Int64 = compute())\n"
        "types.default_not_constant");
  test "a field's default's arithmetic must stay within its type" (fun () ->
      one_diagnostic "type Settings(retries: UInt8 = 250 + 10)\n" "types.constant_overflow")

(* The body of a transparent function *)

let () =
  let transparent body =
    Printf.sprintf
      "public transparent fn shown(value: Int64) -> Int64\n  cost time O(1)\n{\n  %s\n}\n" body
  in
  let helper visibility =
    Printf.sprintf "%sfn half(value: Int64) -> Int64\n  cost time O(1)\n{\n  value - 1\n}\n\n"
      visibility
  in
  test "a transparent body calls only functions that other packages can call" (fun () ->
      one_diagnostic (helper "internal " ^ transparent "half(value)") "types.private_in_public";
      one_diagnostic (helper "" ^ transparent "half(value)") "types.private_in_public";
      fine (helper "public " ^ transparent "half(value)");
      fine (helper "public transparent " ^ transparent "half(value) + value"));
  test "a transparent body names only constants that other packages can name" (fun () ->
      one_diagnostic
        ("internal let limit: Int64 = 10\n\n" ^ transparent "value + limit")
        "types.private_in_public";
      fine ("public let limit: Int64 = 10\n\n" ^ transparent "value + limit"));
  test "a transparent body calls only public methods, and can read a hidden field" (fun () ->
      let meter visibility =
        Printf.sprintf
          "public opaque type Meter(reading: Int64)\n\n\
          \           %sfn Meter.raw(self) -> Int64\n\
          \            cost time O(1)\n\
          \           {\n\
          \            self.reading\n\
          \           }\n\n\
          \           public transparent fn Meter.shown(self) -> Int64\n\
          \            cost time O(1)\n\
          \           {\n\
          \            self.raw() + self.reading\n\
          \           }\n"
          visibility
      in
      one_diagnostic (meter "internal ") "types.private_in_public";
      fine (meter "public "));
  test "a public contract names only functions that other packages can call" (fun () ->
      let sorted visibility =
        Printf.sprintf
          "%sfn in_order(items: Slice[Int64]) -> Bool\n\
          \  cost time O(1)\n\
           {\n\
          \  items.length() < 2\n\
           }\n\n"
          visibility
      in
      let sort visibility clause =
        Printf.sprintf "%sfn sort(items: mut Slice[Int64])\n  %s\n{\n  todo\n}\n" visibility clause
      in
      one_diagnostic
        (sorted "internal " ^ sort "public " "ensures in_order(items)")
        "types.private_in_public";
      one_diagnostic
        (sorted "" ^ sort "public " "requires in_order(items)")
        "types.private_in_public";
      fine (sorted "public " ^ sort "public " "ensures in_order(items)");
      fine (sorted "internal " ^ sort "internal " "ensures in_order(items)");
      fine (sorted "" ^ sort "" "ensures in_order(items)"));
  test "a public contract names only constants that other packages can name" (fun () ->
      let capped visibility =
        Printf.sprintf
          "%slet limit: Int64 = 10\n\n\
           public fn capped(value: Int64) -> Int64\n\
          \  ensures result <= limit\n\
           {\n\
          \  todo\n\
           }\n"
          visibility
      in
      one_diagnostic (capped "internal ") "types.private_in_public";
      fine (capped "public "));
  test
    "the contract of a public trait's method and of its impl's method names only public functions"
    (fun () ->
      let helper =
        "internal fn small(value: Int64) -> Bool\n  cost time O(1)\n{\n  value < 10\n}\n\n"
      in
      one_diagnostic
        (helper ^ "public trait Sized {\n  fn size(self) -> Int64\n    ensures small(result)\n}\n")
        "types.private_in_public";
      fine (helper ^ "trait Sized {\n  fn size(self) -> Int64\n    ensures small(result)\n}\n");
      let implemented visibility =
        helper
        ^ Printf.sprintf
            "public trait Sized {\n\
            \  fn size(self) -> Int64\n\
             }\n\n\
             %stype Box(side: Int64)\n\n\
             impl Sized for Box {\n\
            \  fn size(self) -> Int64\n\
            \    ensures small(result)\n\
            \  {\n\
            \    todo\n\
            \  }\n\
             }\n"
            visibility
      in
      one_diagnostic (implemented "public ") "types.private_in_public";
      fine (implemented "internal "));
  test "a function that is not transparent can call a function that other packages cannot"
    (fun () ->
      fine
        (helper "internal "
       ^ "public fn hidden(value: Int64) -> Int64\n  cost time O(1)\n{\n  half(value)\n}\n"))
