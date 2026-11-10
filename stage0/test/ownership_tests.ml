(* The tests of moves, loans, and views. *)

open Harness
open Support

let check database module_ =
  Resolve.diagnostics database module_
  @ Interface.diagnostics database module_
  @ Infer.diagnostics database module_
  @ Patterns.diagnostics database module_
  @ Usage.diagnostics database module_
  @ Ownership.diagnostics database module_

let one_diagnostic = one_diagnostic ~check
let fine text = no_diagnostics ~check [ ("app::main", text) ]
let keep = "fn keep(items: own List[Int64]) {}\n\nfn look(items: List[Int64]) {}\n\n"

(* Writing through a slice *)

let () =
  let bump =
    "fn bump(items: mut Slice[Int64])\n  requires items.length() > 0\n{\n  items[0] = 9\n}\n\n"
  in
  List.iter
    (fun (what, text) ->
      test (what ^ " cannot be changed through a slice") (fun () ->
          one_diagnostic (bump ^ text) "ownership.read_only_view"))
    [
      ( "a read-only parameter",
        "fn f(items: List[Int64]) -> USize {\n\
        \  var part = items.slice()\n\
        \  bump(mut part)\n\
        \  items.length()\n\
         }\n" );
      ( "a constant",
        "let primes: List[Int64] = [2, 3, 5]\n\n\
         fn f() -> USize {\n\
        \  var part = primes.slice()\n\
        \  bump(mut part)\n\
        \  primes.length()\n\
         }\n" );
      ( "a `let`",
        "fn f() -> USize {\n\
        \  let items: List[Int64] = [3, 1, 2]\n\
        \  var part = items.slice()\n\
        \  part[0] = 7\n\
        \  items.length()\n\
         }\n" );
      ( "what a slice in a field views",
        "type Window(rest: Slice[Int64])\n\n\
         fn f(window: mut Window) {\n\
        \  bump(mut window.rest)\n\
         }\n" );
    ];
  test "a `var` and a `mut` parameter can be changed through a slice" (fun () ->
      fine
        (bump
       ^ "type Window(rest: Slice[Int64])\n\n\
          fn narrow(window: mut Window, count: USize) {\n\
         \  window.rest = window.rest[..count]\n\
          }\n\n\
          fn f(given: mut List[Int64]) -> USize {\n\
         \  var items: List[Int64] = [3, 1, 2]\n\
         \  var part = items.slice()\n\
         \  bump(mut part)\n\
         \  part[1] = 4\n\
         \  var other = given.slice()\n\
         \  bump(mut other)\n\
         \  items.length()\n\
          }\n"))

(* The operands of one operation *)

let () =
  let functions =
    "fn take(items: mut List[Int64], view: Slice[Int64]) {}\n\n\
     fn give(view: Slice[Int64], items: mut List[Int64]) {}\n\n\
     fn measure(items: mut List[Int64], count: USize) {}\n\n\
     fn show(item: Int64, count: USize) {}\n\n\
     fn change(item: mut Int64, count: USize) {}\n\n\
     fn count_of(view: Slice[Int64], count: USize) {}\n\n\
     fn grow(items: mut List[Int64]) -> USize {\n\
    \  mut items.push(1)\n\
    \  items.length()\n\
     }\n\n"
  in
  let rejected name body code =
    test name (fun () ->
        one_diagnostic (functions ^ "fn f(items: mut List[Int64]) {\n" ^ body ^ "}\n") code)
  in
  rejected "a view cannot be passed after a `mut` borrow of what it views"
    "  var part = items.slice()\n  take(mut items, view: part)\n" "ownership.conflicting_loan";
  rejected "a view cannot be passed before a `mut` borrow of what it views"
    "  var part = items.slice()\n  give(part, items: mut items)\n" "ownership.conflicting_loan";
  rejected "a slice of a place cannot be passed with a `mut` borrow of the place"
    "  take(mut items, view: items[..1])\n" "ownership.conflicting_loan";
  test "a view of another place, and a value read from the place, can be passed with it" (fun () ->
      fine
        (functions
       ^ "fn f(items: mut List[Int64], others: List[Int64]) {\n\
         \  var part = others.slice()\n\
         \  take(mut items, view: part)\n\
         \  measure(mut items, count: items.length())\n\
          }\n"));
  rejected "a later argument cannot change a place that an earlier argument borrows"
    "  show(items[0], count: grow(mut items))\n" "ownership.changed_while_viewed";
  rejected "a later argument cannot change a place that an earlier argument borrows `mut`"
    "  change(mut items[0], count: grow(mut items))\n" "ownership.changed_while_viewed";
  rejected "a later argument cannot change what an earlier argument views"
    "  count_of(items[..1], count: grow(mut items))\n" "ownership.changed_while_viewed";
  rejected "a later argument cannot change what a view passed earlier views"
    "  var part = items.slice()\n  count_of(part, count: grow(mut items))\n"
    "ownership.changed_while_viewed";
  rejected "an index key cannot change the collection that is indexed"
    "  let _ = items[grow(mut items)]\n" "ownership.changed_while_viewed";
  rejected "a bound of a slice cannot change the collection that is sliced"
    "  let _ = items[..grow(mut items)]\n" "ownership.changed_while_viewed";
  test "a later field cannot change what an earlier field views" (fun () ->
      one_diagnostic
        (functions
       ^ "type Counted(view: Slice[Int64], count: USize)\n\n\
          fn f(items: mut List[Int64]) {\n\
         \  let _ = Counted(view: items[..1], count: grow(mut items))\n\
          }\n")
        "ownership.changed_while_viewed");
  test "an operand that is a copy does not lend its place" (fun () ->
      fine
        (functions
       ^ "fn sum(first: own USize, second: USize) {}\n\n\
          fn bump(count: mut USize) -> USize {\n\
         \  count = 1\n\
         \  count\n\
          }\n\n\
          fn f(count: mut USize) {\n\
         \  sum(count, second: bump(mut count))\n\
          }\n"))

(* A yielded constructor that lends places *)

let () =
  let shelf =
    "type Shelf(books: List[String])\n\n\
     type First(title: String, rest: Slice[String])\n\n\
     type Numbered(index: USize, title: String)\n\n\
     type Tagged(tag: String, book: String)\n\n\
     type Both(first: List[String], second: List[String])\n\n"
  in
  let lends name signature body = shelf ^ "fn Shelf." ^ name ^ signature ^ " {\n" ^ body ^ "}\n" in
  test "a yielded constructor lends a place without a mark" (fun () ->
      fine
        (lends "get" "(self, index: USize) lends Option[String]"
           "  if index < self.books.length() {\n\
           \    yield Some(self.books[index])\n\
           \  } else {\n\
           \    yield None\n\
           \  }\n"
        ^ "\n\
           fn title_length(shelf: Shelf) -> USize {\n\
          \  match shelf.get(0) {\n\
          \    Some(title) => title.length()\n\
          \    None => 0\n\
          \  }\n\
           }\n"));
  test "a constructor nested in a yielded constructor lends places too" (fun () ->
      fine
        (lends "first" "(self) lends Option[First]"
           "  yield Some(First(title: self.books[0], rest: self.books[1..]))\n"));
  test "a yielded constructor that lends no place owns its fields" (fun () ->
      fine
        (lends "copied" "(self) lends Tagged"
           "  yield Tagged(tag: \"new\".copy(), book: self.books[0].copy())\n"));
  test "a `Plain` place in a yielded constructor is copied, so it lends nothing" (fun () ->
      fine
        (lends "numbered" "(self, index: USize) lends Numbered"
           "  yield Numbered(index: index, title: self.books[index].copy())\n"));
  test "a local is a place that a yielded constructor lends" (fun () ->
      fine
        (lends "tagged" "(self) lends Tagged"
           "  let tag = \"new\".copy()\n  yield Tagged(tag: tag, book: self.books[0])\n"));
  test "a yielded constructor that lends a place takes no owned value" (fun () ->
      one_diagnostic
        (lends "tagged" "(self) lends Tagged"
           "  yield Tagged(tag: \"new\".copy(), book: self.books[0])\n")
        "ownership.owned_beside_lent");
  test "a constructor yielded `mut` lends the places marked `mut`" (fun () ->
      fine
        (lends "numbered" "(mut self) yields mut Numbered"
           "  var index: USize = 0\n\
           \  while index < self.books.length() {\n\
           \    yield Numbered(index: index, title: mut self.books[index])\n\
           \    index = index + 1\n\
           \  }\n"
        ^ "\n\
           fn clear(shelf: mut Shelf) {\n\
          \  for numbered in mut shelf.numbered() {\n\
          \    numbered.title = \"\".copy()\n\
          \  }\n\
           }\n"));
  test "a place in a constructor yielded `mut` needs the `mut` mark" (fun () ->
      one_diagnostic
        (lends "numbered" "(mut self) lends mut Numbered"
           "  yield Numbered(index: 0, title: self.books[0])\n")
        "types.missing_mark");
  test "a place in a constructor yielded read-only takes no `mut` mark" (fun () ->
      one_diagnostic
        (lends "numbered" "(self) lends Numbered"
           "  yield Numbered(index: 0, title: mut self.books[0])\n")
        "types.redundant_mark");
  test "a yielded constructor is not lent one place `mut` twice" (fun () ->
      one_diagnostic
        (lends "both" "(mut self) lends mut Both"
           "  yield Both(first: mut self.books, second: mut self.books)\n")
        "ownership.conflicting_loan");
  test "a method that yields a constructor that lends places is not pulled" (fun () ->
      one_diagnostic
        (lends "numbered" "(self) yields Numbered"
           "  var index: USize = 0\n\
           \  while index < self.books.length() {\n\
           \    yield Numbered(index: index, title: self.books[index])\n\
           \    index = index + 1\n\
           \  }\n"
        ^ "\n\
           fn f(shelf: Shelf) {\n\
          \  var cursor = shelf.numbered()\n\
          \  let _ = mut cursor.next()\n\
           }\n")
        "ownership.not_pullable")

(* Lambdas that capture *)

let () =
  let helpers =
    "type Handlers(first: fn(Int64) -> Int64)\n\n\
     fn take(handler: own fn(Int64) -> Int64) {}\n\n\
     fn apply(handler: fn(Int64) -> Int64, to: Int64) -> Int64 {\n\
    \  handler(to)\n\
     }\n\n\
     fn double(value: Int64) -> Int64 {\n\
    \  value\n\
     }\n\n"
  in
  let rejected name body code = test name (fun () -> one_diagnostic (helpers ^ body) code) in
  let accepted name body = test name (fun () -> fine (helpers ^ body)) in
  rejected "a lambda that captures a parameter cannot be returned"
    "fn adder(amount: Int64) -> fn(Int64) -> Int64 {\n  fn(value) { value + amount }\n}\n"
    "ownership.view_escapes";
  rejected "a lambda that captures a local cannot be returned"
    "fn adder(amount: Int64) -> fn(Int64) -> Int64 {\n\
    \  let extra = amount\n\
    \  fn(value) { value + extra }\n\
     }\n"
    "ownership.view_escapes";
  rejected "a lambda that captures cannot be returned through a name"
    "fn adder(amount: Int64) -> fn(Int64) -> Int64 {\n\
    \  let add: fn(Int64) -> Int64 = fn(value) { value + amount }\n\
    \  add\n\
     }\n"
    "ownership.view_escapes";
  rejected "a record that holds a lambda that captures cannot be returned"
    "fn build(amount: Int64) -> Handlers {\n  Handlers(first: fn(value) { value + amount })\n}\n"
    "ownership.view_escapes";
  rejected "a lambda that captures cannot be put in what the caller keeps"
    "fn keep(handlers: mut Handlers, amount: Int64) {\n\
    \  handlers.first = fn(value) { value + amount }\n\
     }\n"
    "ownership.view_escapes";
  rejected "a lambda that captures cannot be given to an `own` parameter"
    "fn give(amount: Int64) {\n  take(fn(value) { value + amount })\n}\n" "ownership.view_escapes";
  rejected "a function value that is not owned cannot be given to an `own` parameter"
    "fn relay(handler: fn(Int64) -> Int64) {\n  take(handler)\n}\n" "ownership.view_escapes";
  (* A generic [own] parameter is not declared with a function type, so the
     view rules track a capturing lambda that is passed to one. *)
  accepted
    "a capturing lambda can be stored in a local list and passed to a generic `own` parameter"
    "fn same[Value](value: own Value) -> Value {\n\
    \  value\n\
     }\n\n\
     fn local(amount: Int64) -> Int64 {\n\
    \  let add: fn(Int64) -> Int64 = fn(value) { value + amount }\n\
    \  var handlers = [add]\n\
    \  mut handlers.push(add)\n\
    \  let again = same(add)\n\
    \  let first = handlers[0]\n\
    \  again(first(amount))\n\
     }\n";
  rejected "a list that stores a capturing lambda cannot be returned"
    "fn escape(amount: Int64) -> List[fn(Int64) -> Int64] {\n\
    \  let add: fn(Int64) -> Int64 = fn(value) { value + amount }\n\
    \  [add]\n\
     }\n"
    "ownership.view_escapes";
  rejected "a capturing lambda returned through a generic `own` parameter cannot be returned"
    "fn same[Value](value: own Value) -> Value {\n\
    \  value\n\
     }\n\n\
     fn escape(amount: Int64) -> fn(Int64) -> Int64 {\n\
    \  let add: fn(Int64) -> Int64 = fn(value) { value + amount }\n\
    \  same(add)\n\
     }\n"
    "ownership.view_escapes";
  accepted "a function that captures nothing can be returned, kept, and given up"
    "fn plain() -> fn(Int64) -> Int64 {\n\
    \  fn(value) { double(value) }\n\
     }\n\n\
     fn named() -> fn(Int64) -> Int64 {\n\
    \  double\n\
     }\n\n\
     fn keep(handlers: mut Handlers) {\n\
    \  handlers.first = double\n\
     }\n\n\
     fn give() {\n\
    \  take(double)\n\
    \  take(fn(value) { double(value) })\n\
     }\n\n\
     fn relay(handler: own fn(Int64) -> Int64) {\n\
    \  take(handler)\n\
     }\n";
  accepted "a lambda that captures can be passed down and held in a local record"
    "fn f(amount: Int64) -> Int64 {\n\
    \  let handlers = Handlers(first: fn(value) { value + amount })\n\
    \  apply(handlers.first, to: 1) + apply(fn(value) { value + amount }, to: 2)\n\
     }\n"

(* Values that refer to a place, and values taken out of one *)

let () =
  let types =
    "type Labeled(view: Slice[Int64], name: String)\n\n\
     trait Runner {\n\
    \  fn run(self) -> USize\n\
     }\n\n\
     type Window(view: Slice[Int64])\n\n\
     impl Runner for Window {\n\
    \  fn run(self) -> USize {\n\
    \    self.view.length()\n\
    \  }\n\
     }\n\n\
     type Owner(items: List[Int64])\n\n\
     impl Runner for Owner {\n\
    \  fn run(self) -> USize {\n\
    \    self.items.length()\n\
    \  }\n\
     }\n\n"
  in
  let rejected name body code = test name (fun () -> one_diagnostic (types ^ body) code) in
  let accepted name body = test name (fun () -> fine (types ^ body)) in
  rejected "a borrow of a value that owns data and holds a view views the value"
    "fn f(items: List[Int64]) -> USize {\n\
    \  var labeled = Labeled(view: items[..], name: \"a\".copy())\n\
    \  let borrowed = labeled\n\
    \  labeled = Labeled(view: items[..], name: \"b\".copy())\n\
    \  borrowed.name.length()\n\
     }\n"
    "ownership.changed_while_viewed";
  rejected "a slice of a part of a value that owns data and holds a view views the value"
    "fn f(items: List[Int64]) -> USize {\n\
    \  var labeled = Labeled(view: items[..], name: \"a\".copy())\n\
    \  let name = labeled.name.slice()\n\
    \  labeled = Labeled(view: items[..], name: \"b\".copy())\n\
    \  name.length()\n\
     }\n"
    "ownership.changed_while_viewed";
  rejected "a reference into a parameter that the function owns cannot be returned"
    "fn f(labeled: own Labeled) -> StringSlice {\n  labeled.name.slice()\n}\n"
    "ownership.view_escapes";
  accepted "a view taken out of a parameter that the function owns can be returned"
    "fn f(labeled: own Labeled) -> Slice[Int64] {\n  labeled.view\n}\n";
  rejected "an `any` that holds a view of a local cannot be returned"
    "fn f() -> any Runner {\n\
    \  let items: List[Int64] = [1, 2, 3]\n\
    \  any Window(view: items[..])\n\
     }\n"
    "ownership.view_escapes";
  rejected "what an `any` views cannot change while the `any` is in use"
    "fn f(items: mut List[Int64]) -> USize {\n\
    \  let runner: any Runner = any Window(view: items[..])\n\
    \  mut items.push(4)\n\
    \  runner.run()\n\
     }\n"
    "ownership.changed_while_viewed";
  accepted "an `any` made from owned data can be returned"
    "fn f() -> any Runner {\n  any Owner(items: [1, 2, 3])\n}\n";
  rejected "a lambda that captures cannot be returned as a wider function type"
    "fn adder(amount: Int64) -> (fn(Int64) -> Int64 uses Clock) {\n\
    \  let add: fn(Int64) -> Int64 = fn(value) { value + amount }\n\
    \  add\n\
     }\n"
    "ownership.view_escapes";
  rejected "the value of an `if` views what its branches' values view"
    "fn f(items: mut List[Int64], first: Bool) -> USize {\n\
    \  let part = if first { items[..1] } else { items[1..] }\n\
    \  mut items.push(1)\n\
    \  part.length()\n\
     }\n"
    "ownership.changed_while_viewed";
  rejected "the value of a `match` views what its arms' values view"
    "fn f(items: mut List[Int64], pick: Option[USize]) -> USize {\n\
    \  let part = match pick {\n\
    \    Some(count) => items[..count]\n\
    \    None => items[..]\n\
    \  }\n\
    \  mut items.push(1)\n\
    \  part.length()\n\
     }\n"
    "ownership.changed_while_viewed";
  rejected "the value of a block views what its last expression views"
    "fn f(items: mut List[Int64]) -> USize {\n\
    \  let part = {\n\
    \    let all = items[..]\n\
    \    all\n\
    \  }\n\
    \  mut items.push(1)\n\
    \  part.length()\n\
     }\n"
    "ownership.changed_while_viewed";
  rejected "a view of a local cannot be returned through an `if` and a name"
    "fn f(first: Bool) -> Slice[Int64] {\n\
    \  let items: List[Int64] = [1, 2, 3]\n\
    \  let part = if first { items[..1] } else { items[1..] }\n\
    \  part\n\
     }\n"
    "ownership.view_escapes";
  rejected "a copy of a view views what the view does"
    "fn f(items: mut List[Int64]) -> USize {\n\
    \  let all = items[..]\n\
    \  let part = all.copy()\n\
    \  mut items.push(1)\n\
    \  part.length()\n\
     }\n"
    "ownership.changed_while_viewed";
  rejected "a record made by `with` views what the new fields view"
    "type Sized(view: Slice[Int64], count: USize)\n\n\
     fn f(items: mut List[Int64], other: List[Int64]) -> USize {\n\
    \  let sized = Sized(view: other[..], count: 0)\n\
    \  let changed = sized with (view: items[..])\n\
    \  mut items.push(1)\n\
    \  changed.view.length()\n\
     }\n"
    "ownership.changed_while_viewed";
  rejected "a view copied out of a loop variable views what the loop goes over"
    "fn f(data: mut List[Int64], other: List[Int64]) -> USize {\n\
    \  var parts: List[Slice[Int64]] = []\n\
    \  mut parts.push(data[..])\n\
    \  var kept: Slice[Int64] = other[..]\n\
    \  for part in parts {\n\
    \    kept = part\n\
    \  }\n\
    \  mut data.push(1)\n\
    \  kept.length()\n\
     }\n"
    "ownership.changed_while_viewed";
  accepted "a `Plain` loop variable is a copy, so what the loop went over can change after it"
    "fn f(data: List[Int64], other: List[Int64]) -> USize {\n\
    \  var parts: List[Slice[Int64]] = []\n\
    \  mut parts.push(data[..])\n\
    \  var kept: Slice[Int64] = other[..]\n\
    \  for part in parts {\n\
    \    kept = part\n\
    \  }\n\
    \  mut parts.clear()\n\
    \  kept.length()\n\
     }\n";
  rejected "a place cannot change while a name that a `match` on it binds is in use"
    "fn f() -> USize {\n\
    \  var slot: Option[String] = Some(\"a\".copy())\n\
    \  match slot {\n\
    \    Some(inner) => {\n\
    \      slot = None\n\
    \      inner.length()\n\
    \    }\n\
    \    None => 0\n\
    \  }\n\
     }\n"
    "ownership.changed_while_viewed";
  accepted "a place can change in an arm once the names the `match` binds are not used"
    "fn f() -> USize {\n\
    \  var slot: Option[String] = Some(\"a\".copy())\n\
    \  match slot {\n\
    \    Some(inner) => {\n\
    \      let length = inner.length()\n\
    \      slot = None\n\
    \      length\n\
    \    }\n\
    \    None => 0\n\
    \  }\n\
     }\n"

(* Views that a method yields *)

let () =
  let reader = "type Reader(buffer: List[Int64])\n\n" in
  let rejected name body code = test name (fun () -> one_diagnostic (reader ^ body) code) in
  let accepted name body = test name (fun () -> fine (reader ^ body)) in
  rejected "a yielding method cannot yield a view of its local"
    "fn Reader.chunks(self) yields Slice[Int64] {\n\
    \  let scratch: List[Int64] = [1, 2, 3]\n\
    \  yield scratch[..]\n\
     }\n"
    "ownership.view_escapes";
  rejected "a lending method cannot lend a view of its local"
    "fn Reader.window(self) lends Slice[Int64] {\n\
    \  let scratch: List[Int64] = [1, 2, 3]\n\
    \  yield scratch[..]\n\
     }\n"
    "ownership.view_escapes";
  accepted "a method can yield a view of `self`, and lend a local itself"
    "fn Reader.windows(self) yields Slice[Int64] {\n\
    \  yield self.buffer[..1]\n\
    \  yield self.buffer[1..]\n\
     }\n\n\
     fn Reader.scratch(self) lends List[Int64] {\n\
    \  let scratch: List[Int64] = [1, 2, 3]\n\
    \  yield scratch\n\
     }\n";
  (let chunks =
     "fn Reader.chunks(mut self) yields Slice[Int64] {\n\
     \  yield self.buffer[..]\n\
     \  mut self.buffer.push(4)\n\
     \  yield self.buffer[..]\n\
      }\n\n"
   in
   rejected "a view from one step of a loop that is lent `mut` is not used in a later step"
     (chunks
    ^ "fn f(reader: mut Reader, other: List[Int64]) -> USize {\n\
      \  var kept: Slice[Int64] = other[..]\n\
      \  for chunk in mut reader.chunks() {\n\
      \    kept = chunk\n\
      \  }\n\
      \  kept.length()\n\
       }\n")
     "ownership.changed_while_viewed";
   accepted "a view from a step of a loop that is lent `mut` can be used in that step"
     (chunks
    ^ "fn f(reader: mut Reader) -> USize {\n\
      \  var total: USize = 0\n\
      \  for chunk in mut reader.chunks() {\n\
      \    let current = chunk\n\
      \    total = total + current.length()\n\
      \  }\n\
      \  total\n\
       }\n"));
  accepted "a view from a loop over a read-only source can be kept after the loop"
    "fn Reader.windows(self) yields Slice[Int64] {\n\
    \  yield self.buffer[..1]\n\
    \  yield self.buffer[1..]\n\
     }\n\n\
     fn f(reader: Reader, other: List[Int64]) -> USize {\n\
    \  var kept: Slice[Int64] = other[..]\n\
    \  for window in reader.windows() {\n\
    \    kept = window\n\
    \  }\n\
    \  kept.length()\n\
     }\n"

(* A place given to a [provide] block *)

let () =
  let counter =
    "capability Counter {\n\
    \  fn next() -> USize\n\
     }\n\n\
     type Tally(counts: List[USize])\n\n\
     impl Counter for Tally {\n\
    \  fn next(mut self) -> USize {\n\
    \    mut self.counts.push(1)\n\
    \    self.counts.length()\n\
    \  }\n\
     }\n\n\
     type Fixed(value: USize)\n\n\
     impl Counter for Fixed {\n\
    \  fn next(self) -> USize {\n\
    \    self.value\n\
    \  }\n\
     }\n\n\
     fn count() -> USize\n\
    \  uses Counter\n\
     {\n\
    \  Counter.next()\n\
     }\n\n"
  in
  test "the body of a `provide` cannot use a place that the block is given `mut`" (fun () ->
      one_diagnostic
        (counter
       ^ "fn f() -> USize {\n\
         \  var tally = Tally(counts: [])\n\
         \  provide mut tally {\n\
         \    let before = tally.counts.length()\n\
         \    count() + before\n\
         \  }\n\
          }\n")
        "ownership.conflicting_loan");
  test "the body of a `provide` cannot change a place that the block is given" (fun () ->
      one_diagnostic
        (counter
       ^ "fn f() -> USize {\n\
         \  var fixed = Fixed(value: 1)\n\
         \  provide fixed {\n\
         \    fixed = Fixed(value: 2)\n\
         \    count()\n\
         \  }\n\
          }\n")
        "ownership.changed_while_viewed");
  test "the body of a `provide` can read a place that the block is given read-only" (fun () ->
      fine
        (counter
       ^ "fn f() -> USize {\n\
         \  let fixed = Fixed(value: 1)\n\
         \  provide fixed {\n\
         \    count() + fixed.value\n\
         \  }\n\
          }\n"));
  test "a place given to a `provide` block is free again after the block" (fun () ->
      fine
        (counter
       ^ "fn f() -> USize {\n\
         \  var tally = Tally(counts: [])\n\
         \  let first = provide mut tally {\n\
         \    count()\n\
         \  }\n\
         \  first + tally.counts.length()\n\
          }\n"))

(* Views in the branches of a [parallel] block *)

let () =
  test "one branch of a `parallel` block cannot change what another branch's view views" (fun () ->
      one_diagnostic
        "fn f(items: mut List[Int64]) -> USize {\n\
        \  let part = items[..]\n\
        \  parallel {\n\
        \    let length = part.length()\n\
        \    mut items.push(1)\n\
        \  }\n\
        \  length\n\
         }\n"
        "ownership.data_race");
  test "two branches of a `parallel` block can read through views of one place" (fun () ->
      fine
        "fn f(items: List[Int64]) -> USize {\n\
        \  let part = items[..]\n\
        \  parallel {\n\
        \    let first = part.length()\n\
        \    let second = items.length()\n\
        \  }\n\
        \  first + second\n\
         }\n")

(* Views of a temporary through a copy and a record update *)

let () =
  let make = "fn make() -> List[Int64] {\n  [1, 2, 3]\n}\n\n" in
  test "a copy of a view of a temporary cannot be kept" (fun () ->
      one_diagnostic
        (make ^ "fn f() -> USize {\n  let part = make().slice().copy()\n  part.length()\n}\n")
        "ownership.views_temporary");
  test "a record made by `with` cannot keep a view of a temporary" (fun () ->
      one_diagnostic
        (make
       ^ "type Sized(view: Slice[Int64], count: USize)\n\n\
          fn f(other: List[Int64]) -> USize {\n\
         \  let sized = Sized(view: other[..], count: 0)\n\
         \  let changed = sized with (view: make().slice())\n\
         \  changed.view.length()\n\
          }\n")
        "ownership.views_temporary")

(* Quantifiers in code that runs *)

let () =
  let grow = "fn grow(items: mut List[Int64]) -> Bool {\n  mut items.push(1)\n  true\n}\n\n" in
  test "the body of a quantifier in code cannot change what the quantifier goes over" (fun () ->
      one_diagnostic
        (grow
       ^ "fn f(items: mut List[Int64]) -> Bool {\n\
         \  exists item in items => grow(mut items) && item < 0\n\
          }\n")
        "ownership.changed_while_viewed");
  test "a quantifier in code reads what it goes over" (fun () ->
      fine
        "fn f(items: List[Int64]) -> Bool {\n\
        \  (forall i in 0..items.length() => items[i] > 0) && (exists item in items => item < 0)\n\
         }\n")

(* What a place given [mut] is taken to keep *)

let () =
  let reader =
    "type Reader(bytes: Slice[UInt8], position: USize)\n\n\
     fn Reader.read(mut self, buffer: mut List[UInt8], limit: USize) -> USize {\n\
    \  mut buffer.push(self.bytes[self.position])\n\
    \  self.position = self.position + limit\n\
    \  limit\n\
     }\n\n"
  in
  test "a view given `mut` beside a place that is only lent does not come to view the place"
    (fun () ->
      fine
        (reader
       ^ "fn f(bytes: List[UInt8]) -> USize {\n\
         \  var reader = Reader(bytes: bytes[..], position: 0)\n\
         \  var buffer: List[UInt8] = []\n\
         \  let first = mut reader.read(mut buffer, limit: 1)\n\
         \  let second = mut reader.read(mut buffer, limit: 1)\n\
         \  first + second + buffer.length()\n\
          }\n"))

(* Cursors that a yielding method makes *)

let () =
  test "the `Cursor` trait's own methods are called on a yielding method's cursor" (fun () ->
      fine
        "fn f(items: List[Int64], text: String) -> USize {\n\
        \  var cursor = items.each()\n\
        \  let _ = mut cursor.find(fn(item) { item > 3 })\n\
        \  let _ = items.each().fold(0, combine: fn(total, item) { total + item })\n\
        \  let skipped = items.each().skip(1).count()\n\
        \  let taken = items.each().take(1).count()\n\
        \  skipped + taken + text.characters().skip(1).count()\n\
         }\n");
  test "a cursor that would copy its elements cannot be given to generic code" (fun () ->
      one_diagnostic
        "fn f(names: List[String]) -> List[String] {\n  List.collect(names.each())\n}\n"
        "ownership.not_pullable");
  test "a cursor that would copy its elements cannot be used through the trait's methods" (fun () ->
      one_diagnostic "fn f(names: List[String]) -> List[String] {\n  names.each().to_list()\n}\n"
        "ownership.not_pullable");
  test "a cursor over `Plain` elements can be given to generic code" (fun () ->
      fine "fn f(items: List[Int64]) -> List[Int64] {\n  List.collect(items.each())\n}\n")

(* Views and a capability's implementation *)

let () =
  let journal =
    "capability Journal {\n  fn write(text: StringSlice)\n  fn last() -> StringSlice\n}\n\n"
  in
  let rejected name body code = test name (fun () -> one_diagnostic (journal ^ body) code) in
  rejected "a capability's implementation cannot keep a view that a method is given"
    "type Keeper(kept: StringSlice)\n\n\
     impl Journal for Keeper {\n\
    \  fn write(mut self, text: StringSlice) {\n\
    \    self.kept = text\n\
    \  }\n\n\
    \  fn last(self) -> StringSlice {\n\
    \    self.kept\n\
    \  }\n\
     }\n"
    "ownership.view_crosses_capability";
  rejected "a capability's method cannot return a view of the implementation's own parts"
    "type Lines(text: String)\n\n\
     impl Journal for Lines {\n\
    \  fn write(mut self, text: StringSlice) {\n\
    \    self.text = text.to_string()\n\
    \  }\n\n\
    \  fn last(self) -> StringSlice {\n\
    \    self.text.slice()\n\
    \  }\n\
     }\n"
    "ownership.view_crosses_capability";
  test "an implementation can keep a copy and return a view that it was built with" (fun () ->
      fine
        (journal
       ^ "type Labelled(text: String, label: StringSlice)\n\n\
          impl Journal for Labelled {\n\
         \  fn write(mut self, text: StringSlice) {\n\
         \    self.text = text.to_string()\n\
         \  }\n\n\
         \  fn last(self) -> StringSlice {\n\
         \    self.label\n\
         \  }\n\
          }\n"));
  test "a method that is not a capability's can keep a view and return a view of its parts"
    (fun () ->
      fine
        "type Keeper(kept: StringSlice, text: String)\n\n\
         fn Keeper.keep(mut self, text: StringSlice) {\n\
        \  self.kept = text\n\
         }\n\n\
         fn Keeper.all(self) -> StringSlice {\n\
        \  self.text.slice()\n\
         }\n")

(* Views of a name that refers to a part of a parameter *)

let () =
  let url = "type Url(scheme: String, user: Option[String])\n\n" in
  let accepted name body = test name (fun () -> fine (url ^ body)) in
  accepted "a view of what a `match` on a parameter binds can be returned"
    "fn Url.user(self) -> Option[StringSlice] {\n\
    \  match self.user {\n\
    \    Some(found) => Some(found.slice())\n\
    \    None => None\n\
    \  }\n\
     }\n";
  accepted "a view of what an `is` test on a parameter binds can be returned"
    "fn Url.user(self) -> Option[StringSlice] {\n\
    \  if self.user is Some(found) {\n\
    \    Some(found.slice())\n\
    \  } else {\n\
    \    None\n\
    \  }\n\
     }\n";
  accepted "a view of a name that a `let` binds to a part of a parameter can be returned"
    "fn Url.scheme(self) -> StringSlice {\n  let scheme = self.scheme\n  scheme.slice()\n}\n";
  accepted "a view of a loop's element of a parameter can be returned"
    "fn first(names: List[String]) -> Option[StringSlice] {\n\
    \  for name in names {\n\
    \    return Some(name.slice())\n\
    \  }\n\
    \  None\n\
     }\n";
  test "a view of what a `match` on a local binds cannot be returned" (fun () ->
      one_diagnostic
        "fn f() -> Option[StringSlice] {\n\
        \  let user: Option[String] = Some(\"a\".copy())\n\
        \  match user {\n\
        \    Some(found) => Some(found.slice())\n\
        \    None => None\n\
        \  }\n\
         }\n"
        "ownership.view_escapes");
  test "a place cannot change while a view of what a `match` on it binds is in use" (fun () ->
      one_diagnostic
        "fn f() -> USize {\n\
        \  var user: Option[String] = Some(\"a\".copy())\n\
        \  match user {\n\
        \    Some(found) => {\n\
        \      let name = found.slice()\n\
        \      user = None\n\
        \      name.length()\n\
        \    }\n\
        \    None => 0\n\
        \  }\n\
         }\n"
        "ownership.changed_while_viewed")

(* Concurrent code *)

let () =
  let helpers =
    "type Holder(items: List[Int64], count: USize)\n\n\
     fn wait(count: USize) -> Result[USize, USize]\n\
    \  uses Clock\n\
     {\n\
    \  Ok(count)\n\
     }\n\n\
     fn keep(items: own List[Int64]) {}\n\n"
  in
  let rejected ?says name body code =
    test name (fun () -> one_diagnostic ?says (helpers ^ body) code)
  in
  let accepted name body = test name (fun () -> fine (helpers ^ body)) in
  rejected "one branch of a `concurrent` block cannot change a place that another uses"
    ~says:"`concurrent` block"
    "fn f(items: mut List[Int64]) -> USize\n\
    \  uses Tasks\n\
     {\n\
    \  concurrent {\n\
    \    let length = items.length()\n\
    \    mut items.push(1)\n\
    \  }\n\
    \  length\n\
     }\n"
    "ownership.data_race";
  rejected "an iteration of a `concurrent for` changes only its own element and locals"
    ~says:"`concurrent for`"
    "fn f(items: List[Int64], total: mut Int64)\n\
    \  uses Tasks\n\
     {\n\
    \  concurrent for item in items {\n\
    \    total = item\n\
    \  }\n\
     }\n"
    "ownership.data_race";
  rejected "a branch puts back what it takes out of a place that is lent `mut`"
    "fn f(holder: mut Holder) -> Result[USize, USize]\n\
    \  uses Tasks, Clock\n\
     {\n\
    \  concurrent {\n\
    \    let taken = own holder.items\n\
    \    let waited = wait(1)?\n\
    \  }\n\
    \  holder.items = own taken\n\
    \  Ok(waited)\n\
     }\n"
    "ownership.not_reinitialized";
  accepted "a branch may take a value out of a place that is lent `mut` and put one back"
    "fn f(holder: mut Holder) -> Result[USize, USize]\n\
    \  uses Tasks, Clock\n\
     {\n\
    \  concurrent {\n\
    \    {\n\
    \      keep(own holder.items)\n\
    \      holder.items = []\n\
    \    }\n\
    \    let waited = wait(1)?\n\
    \  }\n\
    \  Ok(waited)\n\
     }\n";
  rejected "what is moved out before a `concurrent` block must be back where a branch returns"
    "fn f(holder: mut Holder) -> Result[USize, USize]\n\
    \  uses Tasks, Clock\n\
     {\n\
    \  let taken = own holder.items\n\
    \  concurrent {\n\
    \    let first = wait(1)?\n\
    \    let second = wait(2)?\n\
    \  }\n\
    \  holder.items = own taken\n\
    \  Ok(first + second)\n\
     }\n"
    "ownership.not_reinitialized";
  (* A [concurrent for] over a yielding method that does not yield by
     position: its body is not a single loop over a range. *)
  let pair =
    "type Pair(first: List[Int64], second: List[Int64], text: String)\n\n\
     fn look[Value](value: Value) {}\n\n"
  in
  let rejected_loop name ~says method_ loop =
    test name (fun () ->
        one_diagnostic ~says
          (pair ^ method_ ^ "\nfn f(pair: mut Pair)\n  uses Tasks\n{\n" ^ loop ^ "}\n")
          "ownership.task_outlives_yield")
  in
  rejected_loop "a `concurrent for` cannot iterate over a method that yields `mut` borrows"
    ~says:"`mut` borrows"
    "fn Pair.each(mut self) yields mut List[Int64] {\n\
    \  yield mut self.first\n\
    \  yield mut self.second\n\
     }\n"
    "  concurrent for list in mut pair.each() {\n    look(list)\n  }\n";
  rejected_loop "a task cannot borrow a place inside a `mut` parameter of the yielding method"
    ~says:"`self.first`"
    "fn Pair.each(mut self) yields List[Int64] {\n\
    \  yield self.first\n\
    \  mut self.first.clear()\n\
    \  yield self.second\n\
     }\n"
    "  concurrent for list in mut pair.each() {\n    look(list)\n  }\n";
  rejected_loop "a task cannot borrow a local of the yielding method" ~says:"`local`"
    "fn Pair.each(self) yields List[Int64] {\n\
    \  let local: List[Int64] = [1]\n\
    \  yield local\n\
    \  yield self.second\n\
     }\n"
    "  concurrent for list in pair.each() {\n    look(list)\n  }\n";
  rejected_loop "a task cannot keep a view of a place inside a `mut` parameter" ~says:"`self.text`"
    "fn Pair.words(mut self) yields own StringSlice {\n\
    \  yield self.text.slice()\n\
    \  mut self.text.clear()\n\
     }\n"
    "  concurrent for word in mut pair.words() {\n    look(word)\n  }\n";
  test "a task can borrow and view places inside a read-only parameter" (fun () ->
      fine
        (pair
       ^ "fn Pair.each(self) yields List[Int64] {\n\
         \  yield self.first\n\
         \  yield self.second\n\
          }\n\n\
          fn Pair.words(self) yields own StringSlice {\n\
         \  yield self.text.slice()\n\
          }\n\n\
          fn f(pair: Pair, names: List[String], parts: List[Slice[Int64]])\n\
         \  uses Tasks\n\
          {\n\
         \  concurrent for list in pair.each() {\n\
         \    look(list)\n\
         \  }\n\
         \  concurrent for word in pair.words() {\n\
         \    look(word)\n\
         \  }\n\
         \  concurrent for name in names {\n\
         \    look(name)\n\
         \  }\n\
         \  concurrent for part in parts {\n\
         \    look(part)\n\
         \  }\n\
          }\n"));
  test "a `concurrent for` cannot iterate over a cursor of views" (fun () ->
      one_diagnostic ~says:"`Slice[Int64]` is a view"
        (pair
       ^ "fn f(parts: List[Slice[Int64]])\n\
         \  uses Tasks\n\
          {\n\
         \  var cursor = parts.each()\n\
         \  concurrent for part in cursor {\n\
         \    look(part)\n\
         \  }\n\
          }\n")
        "ownership.task_outlives_yield");
  test "a `concurrent for` can iterate over owned values and Plain copies" (fun () ->
      fine
        (pair
       ^ "fn Pair.lengths(self) yields own USize {\n\
         \  yield self.first.length()\n\
         \  yield self.second.length()\n\
          }\n\n\
          fn f(pair: Pair, numbers: List[Int64])\n\
         \  uses Tasks\n\
          {\n\
         \  concurrent for length in pair.lengths() {\n\
         \    look(length)\n\
         \  }\n\
         \  concurrent for number in numbers {\n\
         \    look(number)\n\
         \  }\n\
          }\n"));
  test "a `concurrent for` can iterate over a method that yields by position" (fun () ->
      fine
        (pair
       ^ "fn f(rows: mut List[List[Int64]])\n\
         \  uses Tasks\n\
          {\n\
         \  concurrent for row in mut rows {\n\
         \    look(row)\n\
         \  }\n\
          }\n"))

(* Guards *)

let () =
  let bump = "fn bump(count: mut Int64) -> Bool {\n  count = 1\n  false\n}\n\n" in
  test "a guard cannot change what the `match` matches" (fun () ->
      one_diagnostic
        (bump
       ^ "fn f() -> Int64 {\n\
         \  var n: Int64 = 0\n\
         \  match n {\n\
         \    0 if bump(mut n) => 1\n\
         \    0 => 2\n\
         \    _ => 3\n\
         \  }\n\
          }\n")
        "ownership.changed_while_viewed");
  test "a guard can change another place, and an arm's body can change what was matched" (fun () ->
      fine
        (bump
       ^ "fn f() -> Int64 {\n\
         \  var n: Int64 = 0\n\
         \  var other: Int64 = 0\n\
         \  match n {\n\
         \    0 if bump(mut other) => 1\n\
         \    0 => {\n\
         \      n = 5\n\
         \      n + other\n\
         \    }\n\
         \    _ => 3\n\
         \  }\n\
          }\n"))

(* Constants *)

let () =
  let names = "let names: List[Int64] = [1, 2]\n\n" in
  let config =
    "type Config(items: List[Int64])\n\n\
     let config: Config = Config(items: [1])\n\n\
     let Config.ports: List[Int64] = [1]\n\n"
  in
  List.iter
    (fun (what, text, code) -> test (what ^ " is an error") (fun () -> one_diagnostic text code))
    [
      ( "giving up a constant with `own`",
        keep ^ names ^ "fn f() {\n  keep(own names)\n}\n",
        "ownership.not_owned" );
      ( "giving up a field of a constant with `own`",
        keep ^ config ^ "fn f() {\n  keep(own config.items)\n}\n",
        "ownership.not_owned" );
      ( "passing a constant to an `own` parameter",
        keep ^ names ^ "fn f() {\n  keep(names)\n}\n",
        "types.missing_mark" );
      ( "passing a type's constant to an `own` parameter",
        keep ^ config ^ "fn f() {\n  keep(Config.ports)\n}\n",
        "types.missing_mark" );
      ( "binding a constant with `var`",
        names ^ "fn f() {\n  var mine = names\n  mut mine.push(1)\n}\n",
        "ownership.needs_owned" );
      ( "binding a type's constant with `var`",
        config ^ "fn f() {\n  var mine = Config.ports\n  mut mine.push(1)\n}\n",
        "ownership.needs_owned" );
      ( "returning a constant",
        names ^ "fn f() -> List[Int64] {\n  names\n}\n",
        "ownership.needs_owned" );
    ];
  test "an owned value from a constant is a copy, with a fix" (fun () ->
      one_diagnostic
        (names ^ "fn f() -> List[Int64] {\n  names\n}\n")
        "ownership.needs_owned"
        ~fixed:(names ^ "fn f() -> List[Int64] {\n  names.copy()\n}\n"));
  test "a constant can be read, viewed, copied, and returned as a view" (fun () ->
      fine
        (keep ^ names
       ^ "let limit: Int64 = 10\n\n\
          fn first() -> Slice[Int64] {\n\
         \  names[0..1]\n\
          }\n\n\
          fn f() -> Int64 {\n\
         \  look(names)\n\
         \  keep(names.copy())\n\
         \  let view = names\n\
         \  look(view)\n\
         \  var count = limit\n\
         \  count += 1\n\
         \  count\n\
          }\n"))

let () =
  test "the default of a parameter of a view type views a value that lasts for the call" (fun () ->
      fine
        "fn greet(name: StringSlice = \"world\", tags: Slice[Int64] = [1, 2]) -> USize {\n\
        \  name.length() + tags.length()\n\
         }\n\n\
         fn f() -> USize {\n\
        \  greet() + greet(\"you\")\n\
         }\n");
  test "a moved place cannot be used, with a fix that copies at the move" (fun () ->
      one_diagnostic
        (keep ^ "fn f(items: own List[Int64]) {\n  keep(own items)\n  look(items)\n}\n")
        "ownership.use_after_move"
        ~fixed:(keep ^ "fn f(items: own List[Int64]) {\n  keep(items.copy())\n  look(items)\n}\n"));
  test "a tagged string takes its parts, and a plain one reads them" (fun () ->
      let shout =
        "type Shout(text: String)\n\n\
         impl FromTemplate for Shout {\n\
        \  type Part = String\n\n\
        \  fn from_template(template: Template[String]) -> Shout { todo }\n\
         }\n\n"
      in
      one_diagnostic
        (shout ^ "fn f(name: String) -> Shout {\n  Shout\"hey ${name}\"\n}\n")
        "ownership.needs_owned";
      fine (shout ^ "fn f(name: String) -> Shout {\n  Shout\"hey ${name.copy()}\"\n}\n");
      fine (shout ^ "fn f(name: own String) -> Shout {\n  Shout\"hey ${own name}\"\n}\n");
      fine "fn f(name: String) -> String {\n  \"hey ${name}\"\n}\n");
  test "a place that copies implicitly is copied, not moved" (fun () ->
      fine "fn take(count: own Int64) {}\n\nfn f(count: Int64) {\n  take(count)\n  take(count)\n}\n");
  test "a place moved on one path cannot be used after the paths meet" (fun () ->
      one_diagnostic
        (keep
       ^ "fn f(items: own List[Int64], ready: Bool) {\n\
         \  if ready {\n\
         \    keep(own items)\n\
         \  }\n\
         \  look(items)\n\
          }\n")
        "ownership.use_after_move");
  test "a place moved in a loop is moved in the loop's next iteration" (fun () ->
      one_diagnostic
        (keep
       ^ "fn f(items: own List[Int64], count: USize) {\n\
         \  for i in 0..count {\n\
         \    let _ = i\n\
         \    keep(own items)\n\
         \  }\n\
          }\n")
        "ownership.use_after_move");
  test "a place is usable again once it is assigned" (fun () ->
      fine
        (keep
       ^ "fn f(items: own List[Int64]) {\n\
         \  var current = own items\n\
         \  keep(own current)\n\
         \  current = []\n\
         \  look(current)\n\
          }\n"));
  test "a field can be moved out on its own" (fun () ->
      fine
        "type Config(name: String, port: UInt16)\n\n\
         fn take(name: own String) {}\n\n\
         fn f(config: own Config) -> UInt16 {\n\
        \  take(own config.name)\n\
        \  config.port\n\
         }\n");
  test "a read-only parameter cannot be moved" (fun () ->
      one_diagnostic
        (keep ^ "fn f(items: List[Int64]) {\n  keep(own items)\n}\n")
        "ownership.not_owned");
  test "a mut parameter's field moved out must be put back" (fun () ->
      one_diagnostic
        "type Config(name: String, port: UInt16)\n\n\
         fn take(name: own String) {}\n\n\
         fn f(config: mut Config) {\n\
        \  take(own config.name)\n\
         }\n"
        "ownership.not_reinitialized");
  test "a name that a value is moved into does not view the place it came from" (fun () ->
      fine
        "fn f(first: own List[Int64]) -> List[Int64] {\n\
        \  var items = own first\n\
        \  let taken = own items\n\
        \  items = [1]\n\
        \  mut items.push(2)\n\
        \  taken\n\
         }\n");
  (let holder = "type Holder(items: List[Int64], count: USize)\n\n" in
   let accepted name body = test name (fun () -> fine (holder ^ body)) in
   let rejected name body code = test name (fun () -> one_diagnostic (holder ^ body) code) in
   accepted "a field of a place lent `mut` can be moved out and put back"
     "fn Holder.take_items(mut self) -> List[Int64] {\n\
     \  let taken = own self.items\n\
     \  self.items = []\n\
     \  taken\n\
      }\n";
   rejected "a field moved out of `mut self` must be put back"
     "fn Holder.take_items(mut self) -> List[Int64] {\n  let taken = own self.items\n  taken\n}\n"
     "ownership.not_reinitialized";
   accepted "a place lent `mut` can be moved out whole and put back"
     "fn take[Value](slot: mut Option[Value]) -> Option[Value] {\n\
     \  let taken = own slot\n\
     \  slot = None\n\
     \  taken\n\
      }\n\n\
      fn replace[Value](slot: mut Option[Value], value: own Value) -> Option[Value] {\n\
     \  let previous = own slot\n\
     \  slot = Some(own value)\n\
     \  previous\n\
      }\n";
   rejected "a place lent `mut` that is moved out whole must be put back"
     "fn f(holder: mut Holder) -> Holder {\n  let taken = own holder\n  taken\n}\n"
     "ownership.not_reinitialized";
   rejected "a place lent `mut` must be put back on every path"
     "fn f(holder: mut Holder, keep: Bool) -> List[Int64] {\n\
     \  let taken = own holder.items\n\
     \  if keep {\n\
     \    holder.items = []\n\
     \  }\n\
     \  taken\n\
      }\n"
     "ownership.not_reinitialized";
   rejected "a place lent `mut` cannot be used while it is moved out"
     "fn f(holder: mut Holder) -> USize {\n\
     \  let taken = own holder\n\
     \  let count = holder.count\n\
     \  holder = own taken\n\
     \  count\n\
      }\n"
     "ownership.use_after_move";
   accepted "a `mut` loop variable can be moved out and put back in the iteration"
     "fn f(holders: mut List[Holder]) {\n\
     \  for holder in mut holders {\n\
     \    let items = own holder.items\n\
     \    holder.items = own items\n\
     \  }\n\
      }\n";
   rejected "what is moved out of a `mut` loop variable must be put back in the iteration"
     "fn f(holders: mut List[Holder]) -> USize {\n\
     \  var total: USize = 0\n\
     \  for holder in mut holders {\n\
     \    let items = own holder.items\n\
     \    total = total + items.length()\n\
     \  }\n\
     \  total\n\
      }\n"
     "ownership.not_reinitialized";
   rejected "what is moved out of a `mut` binding of a `match` must be put back in the arm"
     "fn f(slot: mut Option[Holder]) -> USize {\n\
     \  match mut slot {\n\
     \    Some(holder) => {\n\
     \      let items = own holder.items\n\
     \      items.length()\n\
     \    }\n\
     \    None => 0\n\
     \  }\n\
      }\n"
     "ownership.not_reinitialized";
   rejected "a yielding method cannot yield while a place of its caller is moved out"
     "fn Holder.each_item(mut self) yields mut Int64 {\n\
     \  var items = own self.items\n\
     \  for item in mut items {\n\
     \    yield mut item\n\
     \  }\n\
     \  self.items = own items\n\
      }\n"
     "ownership.not_reinitialized";
   accepted "a lending method can yield while a place of its caller is moved out"
     "fn Holder.lend_items(mut self) lends mut List[Int64] {\n\
     \  var items = own self.items\n\
     \  yield mut items\n\
     \  self.items = own items\n\
      }\n");
  test "one place cannot be lent mut twice to one call" (fun () ->
      one_diagnostic
        "fn swap(first: mut Int64, second: mut Int64) {}\n\n\
         fn f() {\n\
        \  var first = 1\n\
        \  swap(mut first, second: mut first)\n\
         }\n"
        "ownership.conflicting_loan");
  test "a place cannot change while a view of it is in use" (fun () ->
      one_diagnostic
        "fn f() -> USize {\n\
        \  var items: List[Int64] = [1, 2, 3, 4, 5]\n\
        \  let middle = items[1..4]\n\
        \  mut items.push(9)\n\
        \  middle.length()\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a place can change once the view of it is no longer used" (fun () ->
      fine
        "fn f() -> USize {\n\
        \  var items: List[Int64] = [1, 2, 3, 4, 5]\n\
        \  let middle = items[1..4]\n\
        \  let total = middle.length()\n\
        \  mut items.push(9)\n\
        \  total\n\
         }\n");
  test "a function cannot return a view of its own local" (fun () ->
      one_diagnostic
        "fn f() -> Slice[Int64] {\n  let items: List[Int64] = [1, 2, 3]\n  items[0..2]\n}\n"
        "ownership.view_escapes");
  test "a function cannot return a view of its local nested in a type nested in itself" (fun () ->
      one_diagnostic
        "type Holder[Value](value: Value)\n\n\
         fn f() -> Holder[Holder[Slice[Int64]]] {\n\
        \  let items: List[Int64] = [1, 2, 3]\n\
        \  Holder(Holder(items[0..2]))\n\
         }\n"
        "ownership.view_escapes");
  test "a function cannot return a view of its local kept as an associated type" (fun () ->
      one_diagnostic
        "trait Shown {\n\
        \  type Part\n\
        \  fn part(self) -> Self.Part\n\
         }\n\n\
         type Numbers(items: List[Int64])\n\n\
         impl Shown for Numbers {\n\
        \  type Part = Slice[Int64]\n\n\
        \  fn part(self) -> Slice[Int64] {\n\
        \    self.items[0..2]\n\
        \  }\n\
         }\n\n\
         type Kept[Source: Shown](part: Source.Part)\n\n\
         fn f() -> Kept[Numbers] {\n\
        \  let numbers = Numbers([1, 2, 3])\n\
        \  Kept(numbers.part())\n\
         }\n"
        "ownership.view_escapes");
  test "a function can return a view of its parameter" (fun () ->
      fine "fn f(items: List[Int64]) -> Slice[Int64] {\n  items[0..2]\n}\n");
  test "a var needs an owned value, with fixes that give up or copy the place" (fun () ->
      one_diagnostic "fn f(items: own List[Int64]) {\n  var copy = items\n  mut copy.push(1)\n}\n"
        "ownership.needs_owned"
        ~fixed:"fn f(items: own List[Int64]) {\n  var copy = own items\n  mut copy.push(1)\n}\n");
  test "an assigned value must be owned" (fun () ->
      one_diagnostic
        "fn f(items: own List[Int64]) {\n\
        \  var held: List[Int64] = []\n\
        \  held = items\n\
        \  let _ = held\n\
         }\n"
        "ownership.needs_owned"
        ~fixed:
          "fn f(items: own List[Int64]) {\n\
          \  var held: List[Int64] = []\n\
          \  held = own items\n\
          \  let _ = held\n\
           }\n");
  test "a map literal's keys and values must be owned" (fun () ->
      one_diagnostic "fn f(name: own String) -> Map[String, Int64] {\n  [name: 1]\n}\n"
        "ownership.needs_owned");
  test "a constant's value and a default may hold a constant without a copy" (fun () ->
      fine
        "let first: List[Int64] = [1, 2]\n\n\
         let both: List[List[Int64]] = [first, first]\n\n\
         fn f(rows: List[List[Int64]] = [first]) -> USize {\n\
        \  rows.length() + both.length()\n\
         }\n");
  test "a list element needs an owned value" (fun () ->
      one_diagnostic "fn f(name: String) -> List[String] {\n  [name]\n}\n" "ownership.needs_owned");
  test "a lending method yields on every path" (fun () ->
      one_diagnostic
        "type Grid(cells: List[Int64])\n\n\
         fn Grid.cell(self, ready: Bool) lends Int64 {\n\
        \  if ready {\n\
        \    yield self.cells[0]\n\
        \  }\n\
         }\n"
        "ownership.lends_count");
  (let grid = "type Grid(cells: List[Int64], count: USize)\n\n" in
   test "a lending method can yield in one branch of a `parallel` block" (fun () ->
       fine
         (grid
        ^ "fn Grid.cell(self) lends Int64 {\n\
          \  parallel {\n\
          \    yield self.cells[0]\n\
          \    let _ = self.count\n\
          \  }\n\
           }\n"));
   test "a lending method cannot yield in two branches of a `parallel` block" (fun () ->
       one_diagnostic
         (grid
        ^ "fn Grid.cell(self) lends Int64 {\n\
          \  parallel {\n\
          \    yield self.cells[0]\n\
          \    yield self.cells[1]\n\
          \  }\n\
           }\n")
         "ownership.lends_count"));
  test "a yielding method that yields through recursion cannot be pulled" (fun () ->
      one_diagnostic
        "type Tree =\n\
        \  | Leaf\n\
        \  | indirect Node(left: Tree, value: Int64, right: Tree)\n\n\
         fn Tree.each(self) yields Int64 {\n\
        \  match self {\n\
        \    Leaf => {}\n\
        \    Node(left, value, right) => {\n\
        \      for item in left.each() {\n\
        \        yield item\n\
        \      }\n\
        \      yield value\n\
        \      for item in right.each() {\n\
        \        yield item\n\
        \      }\n\
        \    }\n\
        \  }\n\
         }\n\n\
         fn f(tree: Tree) -> Option[Int64] {\n\
        \  var cursor = tree.each()\n\
        \  mut cursor.next()\n\
         }\n"
        "ownership.not_pullable");
  test "a cursor of a method that can be pulled is pulled" (fun () ->
      fine
        "fn f(items: List[Int64]) -> Option[Int64] {\n\
        \  var cursor = items.each()\n\
        \  mut cursor.next()\n\
         }\n");
  test "a parallel branch cannot change what another uses" (fun () ->
      one_diagnostic
        "fn bump(count: mut Int64) {}\n\n\
         fn f() -> Int64 {\n\
        \  var count = 0\n\
        \  parallel {\n\
        \    bump(mut count)\n\
        \    let seen = count\n\
        \  }\n\
        \  seen\n\
         }\n"
        "ownership.data_race")

(* Methods *)

let () =
  let bag = "type Bag(items: List[Int64])\n\n" in
  test "an impl method's read-only parameter may be returned as a view" (fun () ->
      fine
        (bag
       ^ "trait Shower {\n\
         \  fn show(self, items: List[Int64]) -> Slice[Int64]\n\
          }\n\n\
          impl Shower for Bag {\n\
         \  fn show(self, items: List[Int64]) -> Slice[Int64] { items[..] }\n\
          }\n"));
  test "an impl method cannot move a read-only parameter" (fun () ->
      one_diagnostic
        (keep ^ bag
       ^ "trait Eater {\n\
         \  fn eat(self, items: List[Int64])\n\
          }\n\n\
          impl Eater for Bag {\n\
         \  fn eat(self, items: List[Int64]) {\n\
         \    keep(own items)\n\
         \  }\n\
          }\n")
        "ownership.not_owned");
  test "an impl method may move a field of an owned self" (fun () ->
      fine
        (bag
       ^ "trait Taker {\n\
         \  fn take(own self) -> List[Int64]\n\
          }\n\n\
          impl Taker for Bag {\n\
         \  fn take(own self) -> List[Int64] { own self.items }\n\
          }\n"));
  test "a trait's method with a body is checked too" (fun () ->
      one_diagnostic
        (keep ^ "trait Eater {\n  fn eat(self, items: List[Int64]) {\n    keep(own items)\n  }\n}\n")
        "ownership.not_owned")

(* Loans held for a stretch of code *)

let () =
  test "a loop's body cannot change what it goes over, even inside a branch" (fun () ->
      one_diagnostic
        "fn f(ready: Bool) {\n\
        \  var items: List[Int64] = [1, 2]\n\
        \  for _ in items {\n\
        \    if ready {\n\
        \      items = []\n\
        \    }\n\
        \  }\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a loop's body cannot lend mut what it goes over" (fun () ->
      one_diagnostic
        "fn f() {\n\
        \  var items: List[Int64] = [1, 2]\n\
        \  for item in items {\n\
        \    mut items.push(item)\n\
        \  }\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a parallel for cannot lend mut a place from outside it" (fun () ->
      one_diagnostic
        "fn f(items: List[Int64]) {\n\
        \  var total: List[Int64] = []\n\
        \  parallel for item in items {\n\
        \    mut total.push(item)\n\
        \  }\n\
         }\n"
        "ownership.data_race");
  test "a parallel for cannot assign a place from outside it, even inside a branch" (fun () ->
      one_diagnostic
        "fn f(ready: Bool) {\n\
        \  var total = 0\n\
        \  parallel for item in 0..10 {\n\
        \    if ready {\n\
        \      total = item\n\
        \    }\n\
        \  }\n\
         }\n"
        "ownership.data_race");
  test "a parallel for may change its own element and locals" (fun () ->
      fine
        "fn f(items: mut List[Int64]) {\n\
        \  parallel for item in mut items {\n\
        \    var doubled = item * 2\n\
        \    doubled = doubled + 1\n\
        \    item = doubled\n\
        \  }\n\
         }\n");
  test "a call cannot view a place another of its arguments moves" (fun () ->
      one_diagnostic
        "fn both(first: List[Int64], second: own List[Int64]) {}\n\n\
         fn f(items: own List[Int64]) {\n\
        \  both(items, second: own items)\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a Plain place passed own is copied, so the call may use it twice" (fun () ->
      fine
        "fn both(first: Int64, second: own Int64) {}\n\n\
         fn f(count: Int64) {\n\
        \  both(count, second: count)\n\
         }\n")

(* Pulling and lending *)

let () =
  let tree =
    "type Tree =\n  | Leaf\n  | indirect Node(left: Tree, value: Int64, right: Tree)\n\n"
  in
  test "a method that yields through itself inside a branch cannot be pulled" (fun () ->
      one_diagnostic
        (tree
       ^ "fn Tree.odd(self) yields Int64 {\n\
         \  match self {\n\
         \    Leaf => {}\n\
         \    Node(left, ..) => {\n\
         \      for item in left.odd() {\n\
         \        if item > 0 {\n\
         \          yield item\n\
         \        }\n\
         \      }\n\
         \    }\n\
         \  }\n\
          }\n\n\
          fn f(tree: Tree) -> Option[Int64] {\n\
         \  var cursor = tree.odd()\n\
         \  mut cursor.next()\n\
          }\n")
        "ownership.not_pullable");
  test "methods that yield through each other cannot be pulled" (fun () ->
      one_diagnostic
        (tree
       ^ "fn Tree.first(self) yields Int64 {\n\
         \  match self {\n\
         \    Leaf => {}\n\
         \    Node(left, ..) => {\n\
         \      for item in left.second() {\n\
         \        yield item\n\
         \      }\n\
         \    }\n\
         \  }\n\
          }\n\n\
          fn Tree.second(self) yields Int64 {\n\
         \  for item in self.first() {\n\
         \    yield item\n\
         \  }\n\
          }\n\n\
          fn f(tree: Tree) -> Option[Int64] {\n\
         \  var cursor = tree.first()\n\
         \  mut cursor.next()\n\
          }\n")
        "ownership.not_pullable");
  test "a call's result does not view a Plain argument it was given" (fun () ->
      fine
        "fn window(items: List[Int64], start: USize) -> Slice[Int64] {\n\
        \  items[start..]\n\
         }\n\n\
         fn f(items: List[Int64]) -> Slice[Int64] {\n\
        \  let start: USize = 1\n\
        \  window(items, start)\n\
         }\n");
  test "a lending method's path that cannot finish need not yield" (fun () ->
      fine
        "type Grid(cells: List[Int64])\n\n\
         fn Grid.cell(self, ready: Bool) lends Int64 {\n\
        \  if ready {\n\
        \    yield self.cells[0]\n\
        \  } else {\n\
        \    unreachable\n\
        \  }\n\
         }\n")

(* Views of temporaries *)

let () =
  let same = "fn same(prefix: String) yields String {\n  yield prefix.copy()\n}\n\n" in
  test "a cursor cannot view a temporary that the statement drops" (fun () ->
      one_diagnostic
        (same ^ "fn f() -> Option[String] {\n  var each = same(\"a${1}\")\n  mut each.next()\n}\n")
        "ownership.views_temporary");
  test "a cursor may view a named value" (fun () ->
      fine
        (same
       ^ "fn f() -> Option[String] {\n\
         \  let prefix = \"a${1}\"\n\
         \  var each = same(prefix)\n\
         \  mut each.next()\n\
          }\n"));
  test "a cursor may view a string literal, which lives in static memory" (fun () ->
      fine (same ^ "fn f() -> Option[String] {\n  var each = same(\"a\")\n  mut each.next()\n}\n"));
  test "a slice cannot view a temporary list" (fun () ->
      one_diagnostic
        "fn make() -> List[Int64] { [1, 2, 3] }\n\n\
         fn f() -> USize {\n\
        \  let middle = make()[1..2]\n\
        \  middle.length()\n\
         }\n"
        "ownership.views_temporary");
  test "a value computed from a temporary's view is fine" (fun () ->
      fine
        "fn make() -> List[Int64] { [1, 2, 3] }\n\nfn f() -> USize {\n  make()[1..2].length()\n}\n")

(* Pulling views of places *)

let () =
  test "pulling a view of a String element is an error" (fun () ->
      one_diagnostic
        "fn f(names: List[String]) -> Option[String] {\n\
        \  var each = names.each()\n\
        \  mut each.next()\n\
         }\n"
        "ownership.not_pullable");
  test "a for loop over a held cursor of String elements is an error too" (fun () ->
      one_diagnostic
        "fn f(names: List[String]) {\n\
        \  var each = names.each()\n\
        \  for name in mut each {\n\
        \    let _ = name\n\
        \  }\n\
         }\n"
        "ownership.not_pullable");
  test "a method that yields owned values can be pulled whatever its element" (fun () ->
      fine
        "fn greetings() yields String {\n\
        \  yield \"hello\"\n\
        \  yield \"hi\"\n\
         }\n\n\
         fn f() -> Option[String] {\n\
        \  var each = greetings()\n\
        \  mut each.next()\n\
         }\n");
  test "a for loop over a marked call drives the method, not a cursor" (fun () ->
      fine
        "fn f(names: mut List[String]) {\n\
        \  for name in mut names.each() {\n\
        \    let _ = name\n\
        \  }\n\
         }\n");
  test "a recursive mut walk may loop over itself" (fun () ->
      fine
        "type Tree(value: Int64, children: List[Tree])\n\n\
         fn Tree.each(mut self) yields mut Int64 {\n\
        \  yield mut self.value\n\
        \  for child in mut self.children {\n\
        \    for value in mut child.each() {\n\
        \      yield mut value\n\
        \    }\n\
        \  }\n\
         }\n");
  test "looping over a method that yields views of String elements is fine" (fun () ->
      fine
        "fn f(names: List[String]) -> USize {\n\
        \  var count: USize = 0\n\
        \  for name in names {\n\
        \    count = count + name.length()\n\
        \  }\n\
        \  count\n\
         }\n")

let () =
  test "is on a temporary binds its parts as owned, as match does" (fun () ->
      fine
        "fn make() -> Option[String] { todo }\n\n\
         fn keep(text: own String) {}\n\n\
         fn f() {\n\
        \  if make() is Some(text) {\n\
        \    keep(own text)\n\
        \  }\n\
         }\n");
  test "a let of a marked call's result binds it owned" (fun () ->
      fine
        "fn keep(found: own Option[List[Int64]]) {}\n\n\
         fn f(source: mut List[List[Int64]]) {\n\
        \  let last = mut source.pop()\n\
        \  keep(own last)\n\
         }\n");
  test "is on a place binds views of its parts" (fun () ->
      one_diagnostic
        "fn keep(text: own String) {}\n\n\
         fn f(found: Option[String]) {\n\
        \  if found is Some(text) {\n\
        \    keep(own text)\n\
        \  }\n\
         }\n"
        "ownership.not_owned")

let () =
  let make = "fn make() -> Option[String] { todo }\n\nfn keep(text: own String) {}\n\n" in
  test "a binding inside a loop is a new one each time, so it may be moved" (fun () ->
      fine
        (make
       ^ "fn f(ready: Bool) {\n\
         \  while ready {\n\
         \    let found = make()\n\
         \    keep_found(own found)\n\
         \  }\n\
          }\n\n\
          fn keep_found(found: own Option[String]) {}\n"));
  test "a while loop's is binding may be moved each time round" (fun () ->
      fine (make ^ "fn f() {\n  while make() is Some(text) {\n    keep(own text)\n  }\n}\n"));
  test "an is binding in an if inside a loop may be moved" (fun () ->
      fine
        (make
       ^ "fn f(ready: Bool) {\n\
         \  while ready {\n\
         \    if make() is Some(text) {\n\
         \      keep(own text)\n\
         \    }\n\
         \  }\n\
          }\n"));
  test "a let-else binding inside a loop may be moved" (fun () ->
      fine
        (make
       ^ "fn f(ready: Bool) {\n\
         \  while ready {\n\
         \    let Some(text) = make() else {\n\
         \      return\n\
         \    }\n\
         \    keep(own text)\n\
         \  }\n\
          }\n"))

(* The prover's part *)

(* How many [Disjoint] obligations a definition leaves to the prover. *)
let disjoint_obligations text =
  let database = setup [ ("app::main", text) ] in
  let module_ = module_of "app::main" in
  List.fold_left
    (fun total declaration ->
      match Query.demand database Ownership.ownership (Resolve.Names.key_of declaration) with
      | Some result ->
          total
          + List.length
              (List.filter
                 (function Checked.Disjoint _ -> true | _ -> false)
                 result.Ownership.obligations)
      | None -> total)
    0
    (Query.demand database Resolve.Names.declarations module_)

let () =
  test "two slices of one list lent together are left to the prover" (fun () ->
      let found =
        disjoint_obligations
          "fn both(first: mut Slice[Int64], second: mut Slice[Int64]) {}\n\n\
           fn f(items: mut List[Int64], middle: USize) {\n\
          \  both(mut items[..middle], second: mut items[middle..])\n\
           }\n"
      in
      if found <> 1 then fail "%d obligations" found);
  test "parallel branches that change two elements are left to the prover" (fun () ->
      let found =
        disjoint_obligations
          "fn f(items: mut List[Int64], first: USize, second: USize) {\n\
          \  parallel {\n\
          \    items[first] = 1\n\
          \    items[second] = 2\n\
          \  }\n\
           }\n"
      in
      if found <> 1 then fail "%d obligations" found);
  test "a slice lent `mut` beside a slice that is viewed leaves an obligation" (fun () ->
      let found =
        disjoint_obligations
          "fn f(first: mut Slice[Int64], other: Slice[Int64]) {}\n\n\
           fn g(items: mut List[Int64]) {\n\
          \  f(mut items[0..2], other: items[0..2])\n\
           }\n"
      in
      if found <> 1 then fail "%d obligations" found);
  test "an element lent `mut` beside a slice that is viewed leaves an obligation" (fun () ->
      let found =
        disjoint_obligations
          "fn f(first: mut Int64, other: Slice[Int64]) {}\n\n\
           fn g(items: mut List[Int64]) {\n\
          \  f(mut items[0], other: items[1..2])\n\
           }\n"
      in
      if found <> 1 then fail "%d obligations" found)

(* Lending: a call of a lending method is a part, lent for the rest of the
   statement, and the place it is lent from is lent whole for as long. *)

let grid =
  "type Cell(name: String)\n\n\
   type Grid(cells: List[Cell])\n\n\
   fn Cell.visit(mut self) {\n\
  \  self.name = \"seen\"\n\
   }\n\n\
   fn Grid.cell(self, index: USize) lends Cell {\n\
  \  yield self.cells[index]\n\
   }\n\n\
   fn Grid.cell(mut self, index: USize) lends mut Cell {\n\
  \  yield mut self.cells[index]\n\
   }\n\n"

let counter =
  "type Counter(count: Int64)\n\n\
   fn Counter.current(self) lends Int64 {\n\
  \  yield self.count\n\
   }\n\n\
   fn Counter.step(mut self) {\n\
  \  self.count = 3\n\
   }\n\n"

let tally =
  "type Tally(cells: List[Int64])\n\n\
   impl Index for Tally {\n\
  \  type Key = USize\n\
  \  type Output = Int64\n\n\
  \  fn contains_key(self, key: USize) -> Bool {\n\
  \    key < self.cells.length()\n\
  \  }\n\n\
  \  fn at(self, key: USize) lends Int64 {\n\
  \    yield self.cells[key]\n\
  \  }\n\n\
  \  fn at(mut self, key: USize) lends mut Int64 {\n\
  \    yield mut self.cells[key]\n\
  \  }\n\
   }\n\n\
   fn bump(first: mut Int64, second: mut Int64) {\n\
  \  first = 1\n\
  \  second = 2\n\
   }\n\n"

let () =
  test "a part lent `mut` is changed through its `mut self` method, with no mark of its own"
    (fun () -> fine (grid ^ "fn f(grid: mut Grid) {\n  mut grid.cell(0).visit()\n}\n"));
  test "a part lent `mut` is assigned to" (fun () ->
      fine (grid ^ "fn f(grid: mut Grid) {\n  mut grid.cell(0).name = \"new\"\n}\n"));
  test "a part lent read-only is not assigned to" (fun () ->
      one_diagnostic
        (grid ^ "fn f(grid: mut Grid) {\n  grid.cell(0).name = \"new\"\n}\n")
        "types.not_assignable");
  test "a part lent read-only is not passed `mut`" (fun () ->
      one_diagnostic
        (grid
       ^ "fn change(cell: mut Cell) {}\n\nfn f(grid: mut Grid) {\n  change(grid.cell(0))\n}\n")
        "types.wrong_mark");
  test "a part that is lent cannot be given up" (fun () ->
      one_diagnostic
        (grid ^ "fn take(cell: own Cell) {}\n\nfn f(grid: Grid) {\n  take(grid.cell(0))\n}\n")
        "types.missing_mark");
  test "a part that is lent cannot be returned" (fun () ->
      one_diagnostic
        (grid ^ "fn f(grid: Grid) -> Cell {\n  grid.cell(0)\n}\n")
        "ownership.not_owned");
  test "a name cannot keep a part that is lent" (fun () ->
      one_diagnostic
        (grid
       ^ "fn look(cell: Cell) {}\n\n\
          fn f(grid: Grid) {\n\
         \  let kept = grid.cell(0)\n\
         \  look(kept)\n\
          }\n")
        "ownership.keeps_lent_part");
  test "a name copies a `Plain` part that is lent" (fun () ->
      fine (counter ^ "fn f(counter: Counter) -> Int64 {\n  let now = counter.current()\n  now\n}\n"));
  test "matching a part that is lent binds views of it, which cannot be given up" (fun () ->
      one_diagnostic
        (grid
       ^ "fn take(name: own String) {}\n\n\
          fn f(grid: Grid) {\n\
         \  match grid.cell(0) {\n\
         \    (name) => take(own name)\n\
         \  }\n\
          }\n")
        "ownership.not_owned");
  test "a place is lent whole, so two parts of it are not lent `mut` in one statement" (fun () ->
      one_diagnostic
        (grid
       ^ "fn touch(first: mut Cell, second: mut Cell) {}\n\n\
          fn f(grid: mut Grid) {\n\
         \  touch(mut grid.cell(0), second: mut grid.cell(1))\n\
          }\n")
        "ownership.conflicting_loan");
  test "a place and a part it lends `mut` do not go to one call" (fun () ->
      one_diagnostic
        (grid
       ^ "fn both(grid: Grid, cell: mut Cell) {}\n\n\
          fn f(grid: mut Grid) {\n\
         \  both(grid, cell: mut grid.cell(0))\n\
          }\n")
        "ownership.changed_while_viewed");
  test "a place lent read-only is not changed in the same statement" (fun () ->
      one_diagnostic
        (tally ^ "fn f(tally: mut Tally) {\n  tally[0] = tally[1]\n}\n")
        "ownership.changed_while_viewed");
  test "two parts of a place are lent read-only in one statement" (fun () ->
      fine (tally ^ "fn f(tally: Tally) -> Int64 {\n  tally[0] + tally[1]\n}\n"));
  test "a lend ends with its statement" (fun () ->
      fine
        (grid
       ^ "fn f(grid: mut Grid) -> USize {\n  mut grid.cell(0).visit()\n  grid.cells.length()\n}\n"));
  test "what a `while` loop's test lends goes back before its body" (fun () ->
      fine
        (counter
       ^ "fn f(counter: mut Counter) {\n\
         \  while counter.current() < 3 {\n\
         \    mut counter.step()\n\
         \  }\n\
          }\n"));
  test "two indexes of a user's collection are not lent `mut` together" (fun () ->
      one_diagnostic
        (tally ^ "fn f(tally: mut Tally) {\n  bump(mut tally[0], second: mut tally[1])\n}\n")
        "ownership.conflicting_loan");
  test "two indexes of a list are lent `mut` together, for the prover to show apart" (fun () ->
      fine
        "fn bump(first: mut Int64, second: mut Int64) {\n\
        \  first = 1\n\
        \  second = 2\n\
         }\n\n\
         fn f(items: mut List[Int64]) {\n\
        \  bump(mut items[0], second: mut items[1])\n\
         }\n")

(* What comes to hold a view *)

let window = "type Window(view: Slice[Int64])\n\n"

let () =
  test "a list given mut views what was passed to the call" (fun () ->
      one_diagnostic
        "fn f() -> USize {\n\
        \  var data: List[Int64] = [1, 2, 3]\n\
        \  var views: List[Slice[Int64]] = []\n\
        \  mut views.push(data[0..2])\n\
        \  mut data.push(4)\n\
        \  views.length()\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a list given mut no longer views what was passed once it is not used" (fun () ->
      fine
        "fn f() -> USize {\n\
        \  var data: List[Int64] = [1, 2, 3]\n\
        \  var views: List[Slice[Int64]] = []\n\
        \  mut views.push(data[0..2])\n\
        \  let count = views.length()\n\
        \  mut data.push(4)\n\
        \  count\n\
         }\n");
  test "a place given mut to a function views what the function was lent" (fun () ->
      one_diagnostic
        "fn keep(kept: mut List[Slice[Int64]], view: Slice[Int64]) {\n\
        \  mut kept.push(view)\n\
         }\n\n\
         fn f() -> USize {\n\
        \  var data: List[Int64] = [1, 2, 3]\n\
        \  var views: List[Slice[Int64]] = []\n\
        \  keep(mut views, view: data[0..2])\n\
        \  mut data.push(4)\n\
        \  views.length()\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a view put in a place inside a branch is still held after it" (fun () ->
      one_diagnostic
        "fn f(often: Bool) -> USize {\n\
        \  var data: List[Int64] = [1, 2, 3]\n\
        \  var views: List[Slice[Int64]] = []\n\
        \  if often {\n\
        \    mut views.push(data[0..2])\n\
        \  }\n\
        \  mut data.push(4)\n\
        \  views.length()\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a field assigned a view makes its record view what the value does" (fun () ->
      one_diagnostic
        (window
       ^ "fn f() -> USize {\n\
         \  var data: List[Int64] = [1, 2, 3]\n\
         \  var other: List[Int64] = [7]\n\
         \  var window = Window(other[0..1])\n\
         \  window.view = data[0..2]\n\
         \  mut data.push(4)\n\
         \  window.view.length()\n\
          }\n")
        "ownership.changed_while_viewed");
  test "a place given mut cannot keep a view of a temporary" (fun () ->
      one_diagnostic
        "fn make() -> List[Int64] {\n\
        \  [1, 2, 3]\n\
         }\n\n\
         fn f() -> USize {\n\
        \  var views: List[Slice[Int64]] = []\n\
        \  mut views.push(make()[0..2])\n\
        \  views.length()\n\
         }\n"
        "ownership.views_temporary");
  test "a mut parameter cannot be given a view of a local" (fun () ->
      one_diagnostic
        "fn f(kept: mut List[Slice[Int64]]) {\n\
        \  let local: List[Int64] = [1, 2, 3]\n\
        \  mut kept.push(local[0..2])\n\
         }\n"
        "ownership.view_escapes");
  test "a mut parameter can be given a view that the function was given" (fun () ->
      fine
        "fn f(kept: mut List[Slice[Int64]], source: Slice[Int64]) {\n\
        \  mut kept.push(source[0..2])\n\
         }\n");
  test "a mut parameter cannot be given a view of a parameter that is only lent" (fun () ->
      one_diagnostic
        "fn f(kept: mut List[Slice[Int64]], source: List[Int64]) {\n\
        \  mut kept.push(source[0..2])\n\
         }\n"
        "ownership.view_escapes");
  test "what a mut parameter views cannot be changed in the rest of the function" (fun () ->
      one_diagnostic
        "fn f(kept: mut List[Slice[Int64]], source: mut Slice[Int64]) {\n\
        \  mut kept.push(source[0..2])\n\
        \  source = source[1..]\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a mut self method cannot put a view of a local in self" (fun () ->
      one_diagnostic
        (window
       ^ "fn Window.narrow(mut self) {\n\
         \  let local: List[Int64] = [1, 2, 3]\n\
         \  self.view = local[0..1]\n\
          }\n")
        "ownership.view_escapes");
  test "a mut self method can put a view that it was given in self" (fun () ->
      fine
        (window ^ "fn Window.widen(mut self, data: Slice[Int64]) {\n  self.view = data[0..2]\n}\n"));
  test "a mut self method cannot put a view of a parameter that is only lent in self" (fun () ->
      one_diagnostic
        (window ^ "fn Window.widen(mut self, data: List[Int64]) {\n  self.view = data[0..2]\n}\n")
        "ownership.view_escapes");
  test "a mut self method cannot put a view of a part of self in self" (fun () ->
      one_diagnostic
        "type Cached(items: List[Int64], recent: Slice[Int64])\n\n\
         fn Cached.refresh(mut self) {\n\
        \  self.recent = self.items[0..1]\n\
         }\n"
        "ownership.self_referential");
  test "a view that a mut self method was given is viewed by what it was called on" (fun () ->
      one_diagnostic
        (window
       ^ "fn Window.widen(mut self, data: Slice[Int64]) {\n\
         \  self.view = data[0..2]\n\
          }\n\n\
          fn f() -> USize {\n\
         \  var data: List[Int64] = [1, 2, 3]\n\
         \  var other: List[Int64] = [7]\n\
         \  var window = Window(other[0..1])\n\
         \  mut window.widen(data)\n\
         \  mut data.push(4)\n\
         \  window.view.length()\n\
          }\n")
        "ownership.changed_while_viewed");
  test "a result views what was lent mut to its call" (fun () ->
      one_diagnostic
        "fn first(data: mut List[Int64]) -> Slice[Int64] {\n\
        \  data[0..1]\n\
         }\n\n\
         fn f() -> USize {\n\
        \  var numbers: List[Int64] = [1, 2]\n\
        \  let view = first(mut numbers)\n\
        \  mut numbers.push(3)\n\
        \  view.length()\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a function cannot return a view of a parameter it owns" (fun () ->
      one_diagnostic "fn f(data: own List[Int64]) -> Slice[Int64] {\n  data[0..1]\n}\n"
        "ownership.view_escapes");
  test "a function can return a view it was given to own" (fun () ->
      fine "fn f(view: own Slice[Int64]) -> Slice[Int64] {\n  view\n}\n");
  test "a function can return a local that views its parameter" (fun () ->
      fine
        "fn f(items: List[Int64]) -> Slice[Int64] {\n\
        \  let part = items[0..2]\n\
        \  let again = part\n\
        \  again\n\
         }\n");
  test "a function can return a record that views its parameter" (fun () ->
      fine
        (window
       ^ "fn f(items: List[Int64]) -> Window {\n  let made = Window(items[0..2])\n  made\n}\n"));
  test "a function cannot return a local that views its local" (fun () ->
      one_diagnostic
        "fn f() -> Slice[Int64] {\n\
        \  let items: List[Int64] = [1, 2, 3]\n\
        \  let part = items[0..2]\n\
        \  part\n\
         }\n"
        "ownership.view_escapes")

let () = finish ()
