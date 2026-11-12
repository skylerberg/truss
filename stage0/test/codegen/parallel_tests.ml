(* [parallel] blocks and loops in whole programs, whose branches run on the
   runtime's threads, and in a test, where they run in order. *)

open Codegen_support

(* A program's output with a number of threads, which changes nothing a
   program does. More threads than cores makes them cross more often. *)
let output_with ~workers text =
  Unix.putenv "TRUSS_WORKERS" (string_of_int workers);
  let status, output, errors = run_main text in
  if status <> 0 then fail "ended with status %d: %s" status errors;
  output

let same_with_any_workers text ~expected =
  List.iter (fun workers -> expect_string ~expected (output_with ~workers text)) worker_counts

let () =
  test "branches give results through lets, change their own parts, and call a lambda" (fun () ->
      same_with_any_workers ~expected:"2500050000 2500000000 2 n100000 300000\n"
        {|type Totals(evens: Int64, odds: Int64, names: List[String])

fn sum_to(limit: Int64, step: Int64, from: Int64) -> Int64 {
  var total: Int64 = 0
  var next = from
  while next <= limit {
    total = total.wrapping_add(next)
    next = next.wrapping_add(step)
  }
  total
}

fn label(count: Int64) -> String {
  "n${count}"
}

fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  var totals = Totals(evens: 0, odds: 0, names: [])
  let limit: Int64 = 100000
  parallel {
    totals.evens = sum_to(limit, step: 2, from: 0)
    totals.odds = sum_to(limit, step: 2, from: 1)
    {
      mut totals.names.push(label(1))
      mut totals.names.push(label(2))
    }
    let built = label(limit)
    let scaled = [1, 2, 3].map(fn(item) { item.wrapping_multiply(limit) })
  }
  Console.print_line("${totals.evens} ${totals.odds} ${totals.names.length()} ${built} ${scaled[2]}")
  ExitCode.success
}
|});
  test "a branch forks again at every depth of a recursion" (fun () ->
      same_with_any_workers ~expected:"832040\n"
        {|fn fib(n: UInt64) -> UInt64 {
  if n < 2 {
    return n
  }
  parallel {
    let left = fib(n - 1)
    let right = fib(n - 2)
  }
  left.wrapping_add(right)
}

fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  Console.print_line("${fib(30)}")
  ExitCode.success
}
|});
  test "a branch takes a value out of its own part, and another gives its part a new one" (fun () ->
      same_with_any_workers ~expected:"first taken second!\n"
        {|type Pair(first: String, second: String)

fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  var pair = Pair(first: "first", second: "second")
  parallel {
    let moved = own pair.first
    {
      mut pair.second.push("!")
    }
  }
  pair.first = "taken"
  Console.print_line("${moved} ${pair.first} ${pair.second}")
  ExitCode.success
}
|})

let board =
  {|type Board(cells: List[Int64])

fn Board.each(mut self) yields mut Int64 {
  for index in 0..self.cells.length() {
    yield mut self.cells[index]
  }
}

fn collatz(start: Int64) -> Int64 {
  var value = start
  var steps: Int64 = 0
  while value > 1 {
    if value % 2 == 0 {
      value = value / 2
    } else {
      value = value.wrapping_multiply(3).wrapping_add(1)
    }
    steps = steps.wrapping_add(1)
  }
  steps
}

fn filled(count: Int64) -> List[Int64] {
  var cells: List[Int64] = []
  var next: Int64 = 1
  while next <= count {
    mut cells.push(next)
    next = next.wrapping_add(1)
  }
  cells
}
|}

let () =
  test "a parallel for over a method that yields by position changes each element once" (fun () ->
      same_with_any_workers ~expected:"7905322 same\n"
        (board
       ^ {|
fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  var board = Board(cells: filled(100000))
  var expected = filled(100000)
  for cell in mut expected {
    if cell % 7 != 0 {
      cell = collatz(cell)
    }
  }
  parallel for cell in mut board {
    if cell % 7 == 0 {
      continue
    }
    cell = collatz(cell)
  }
  var same = true
  for index in 0..expected.length() {
    if expected[index] != board.cells[index] {
      same = false
    }
  }
  var total: Int64 = 0
  for steps in board.cells {
    if steps % 7 != 0 || steps < 7 {
      total = total.wrapping_add(steps)
    }
  }
  Console.print_line("${total} ${if same { "same" } else { "different" }}")
  ExitCode.success
}
|}
        ));
  test "a region reads a parameter that the function is passed by pointer" (fun () ->
      same_with_any_workers ~expected:"2 4 6 8\n"
        {|fn doubled(items: mut List[Int64]) {
  parallel for item in mut items {
    item = item * 2
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  var numbers: List[Int64] = [1, 2, 3, 4]
  doubled(mut numbers)
  Console.print_line("${numbers[0]} ${numbers[1]} ${numbers[2]} ${numbers[3]}")
  ExitCode.success
}
|});
  test "a parallel for over a list, whose each keeps a count between yields, runs in order"
    (fun () ->
      same_with_any_workers ~expected:"5050\n"
        {|fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  var items: List[Int64] = []
  var next: Int64 = 1
  while next <= 100 {
    mut items.push(0)
    next = next.wrapping_add(1)
  }
  var position: Int64 = 0
  for item in mut items {
    position = position.wrapping_add(1)
    item = position
  }
  parallel for item in mut items {
    item = item.wrapping_multiply(1)
  }
  var total: Int64 = 0
  for item in items {
    total = total.wrapping_add(item)
  }
  Console.print_line("${total}")
  ExitCode.success
}
|});
  test "a panic in an iteration of a parallel for over a range ends the program" (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        run_main
          {|fn main(arguments: List[String]) -> ExitCode
  uses Panic
{
  parallel for index in 0..=20 {
    if index == 20 {
      Panic.crash("the last one ran")
    }
  }
  ExitCode.success
}
|}
      in
      expect_int ~expected:101 status;
      if not (contains errors "the last one ran") then fail "reported %s" errors);
  test "an empty range and a range of one run their bodies no times and once" (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        run_main
          {|fn main(arguments: List[String]) -> ExitCode
  uses Panic
{
  let none: Int64 = 0
  parallel for _ in 5..none {
    Panic.crash("an empty range ran")
  }
  parallel for index in -3..-2 {
    if index == -3 {
      Panic.crash("minus three ran")
    }
  }
  ExitCode.success
}
|}
      in
      expect_int ~expected:101 status;
      if not (contains errors "minus three ran") then fail "reported %s" errors)

let () =
  test "a parallel for over a range of characters steps over the surrogates" (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        run_main
          {|fn main(arguments: List[String]) -> ExitCode
  uses Panic
{
  parallel for letter in Character"\u{D700}"..=Character"\u{E001}" {
    if letter > Character"\u{D7FF}" && letter < Character"\u{E000}" {
      Panic.crash("a surrogate")
    }
    if letter == Character"\u{E001}" {
      Panic.crash("the last character ran")
    }
  }
  ExitCode.success
}
|}
      in
      expect_int ~expected:101 status;
      if not (contains errors "the last character ran") then fail "reported %s" errors)

let () =
  passes "a test runs the branches of a parallel block and of a parallel for, in order"
    (board
   ^ {|
test "parallel in a test" {
  var board = Board(cells: filled(50))
  parallel {
    let first = collatz(27)
    let second = collatz(97)
  }
  assert first == 111
  assert second == 118
  parallel for cell in mut board {
    cell = cell.wrapping_multiply(2)
  }
  assert board.cells[0] == 2
  assert board.cells[49] == 100
}
|}
    )

(* Outlining *)

let outlined (instance : Lir.t) =
  Lir.to_string (Lir.canonical_instance (Outline.instance (shape_env ()) instance))

let () =
  test "a region's own local goes with it, and a shared one is reached through the environment"
    (fun () ->
      let int = Lir.Value int32 in
      let add a b = Lir.Binary (Add, copy a, copy b) in
      let actual =
        outlined
          (instance "entry"
             (function_ ~parameters:[ 0 ] ~result:int
                [ local int; local int; local int; local int ]
                [
                  block
                    [
                      Region { fork = 0; region = Branch };
                      Assign (at 3, add 0 0);
                      Assign (at 1, add 3 0);
                      Region { fork = 0; region = Branch };
                      Assign (at 2, Use (copy 0));
                      Regions_end { fork = 0 };
                      Assign (at 1, add 1 2);
                    ]
                    (Return (Some (copy 1)));
                ]))
      in
      expect_string
        ~expected:
          (String.concat "\n"
             [
               "test::entry fn(_0: Int32) -> Int32";
               "b0: _1.capture0 = &mut _0; _1.capture1 = &mut _2; _3.capture0 = &mut _0; \
                _3.capture1 = &mut _4; fork nested 0(&_1), nested 1(&_3); goto b1";
               "b1: _2 = _2 + _4; return _2";
               "nested 0 fn(_0: raw nullable)";
               "b0: _1 = _0; goto b1";
               "b1: _2 = **_1.capture0 + **_1.capture0; **_1.capture1 = _2 + **_1.capture0; goto b2";
               "b2: return";
               "nested 1 fn(_0: raw nullable)";
               "b0: _1 = _0; goto b1";
               "b1: **_1.capture1 = **_1.capture0; goto b2";
               "b2: return";
             ])
        actual)

(* Coroutines *)

let () =
  test "a coroutine runs when resumed, switches back when it suspends, and ends when it returns"
    (fun () ->
      (* The coroutine adds its item to a count, suspends, and adds 10. The
         entry reads the count after each resume, and the result of each
         resume. *)
      let work : Ground.function_type =
        { parameters = [ (Read, named "UInt64") ]; result = Returns (named "Unit"); uses = [] }
      in
      let environment = [ ("count", Lir.Pointer { target = value int32; writable = true }) ] in
      let count = at ~projections:[ Deref; Field "count"; Deref ] 2 in
      let add amount = Lir.Assign (count, Binary (Add, Copy count, amount)) in
      let coroutine =
        function_ ~parameters:[ 0; 1 ] ~environment
          [
            local ~name:"environment" (Raw (Nullable_pointer Opaque));
            local ~name:"item" (value (named "UInt64"));
            local (Pointer { target = Environment 0; writable = false });
            local (value int32);
          ]
          [
            block
              [
                Assign (at 2, Use (copy 0));
                Assign (at 3, Convert (copy 1, Integer Int32));
                add (copy 3);
                Call { target = Intrinsic Coroutine_suspend; arguments = []; result = Discarded };
                add (constant_int32 10);
              ]
              (Return None);
          ]
      in
      let resume into : Lir.statement =
        Call
          {
            target = Intrinsic Coroutine_resume;
            arguments = [ copy 3 ];
            result = Returned (at into);
          }
      in
      let plus amount = Lir.Assign (at 6, Binary (Add, copy 6, amount)) in
      expect_status 112
        [
          entry ~nested:[ coroutine ]
            [
              local ~name:"count" (value int32);
              local (Environment 0);
              local (value (Function work));
              local (value usize);
              local (Raw Bool);
              local (Raw Bool);
              local (value int32);
              local (value int32);
              local (value int32);
            ]
            [
              block
                [
                  Assign (at 0, Use (constant_int32 0));
                  Assign
                    ( at ~projections:[ Field "count" ] 1,
                      Use (Address { place = at 0; writable = true }) );
                  Assign
                    ( at 2,
                      Function_value
                        {
                          code = Nested 0;
                          environment = Some (Address { place = at 1; writable = false });
                        } );
                  Call
                    {
                      target = Intrinsic Coroutine_start;
                      arguments = [ copy 2; Constant (Integer (UInt64, Z.one)) ];
                      result = Returned (at 3);
                    };
                  resume 4;
                  Assign (at 6, Use (copy 0));
                  resume 5;
                  Assign (at 7, Convert (copy 4, Integer Int32));
                  Assign (at 8, Convert (copy 5, Integer Int32));
                  Assign (at 7, Binary (Multiply, copy 7, constant_int32 100));
                  Assign (at 8, Binary (Multiply, copy 8, constant_int32 50));
                  plus (copy 0);
                  plus (copy 7);
                  plus (copy 8);
                ]
                (Return (Some (copy 6)));
            ];
        ])
