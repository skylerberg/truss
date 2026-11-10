(* [intrinsic::Shared] and its operations. Only the standard library can
   name the intrinsic module, so the tests' source is one more module of the
   [standard] package, checked and compiled with the library. *)

open Codegen_support

let probe : Path.module_ = { package = Standard_library.package; modules = [ "shared_probe" ] }

let source =
  {|use standard::intrinsic

type Counter(count: Int64, label: String)

type Nothing()

type InOrder(opened: UInt64, cancelled: List[UInt64])

fn InOrder.is_cancelled(self, task_group: UInt64) -> Bool {
  for other in self.cancelled {
    if other == task_group {
      return true
    }
  }
  false
}

impl Tasks for InOrder {
  fn open(mut self) -> UInt64 {
    self.opened += 1
    self.opened
  }

  fn spawn(self, task_group: UInt64, work: own fn(UInt64), item: UInt64) -> Bool {
    if self.is_cancelled(task_group) {
      return false
    }
    work(item)
    true
  }

  fn join(self, task_group: UInt64) {}

  fn cancel(mut self, task_group: UInt64) -> Bool {
    if self.is_cancelled(task_group) {
      return false
    }
    mut self.cancelled.push(task_group)
    true
  }

  fn cancelled(self) -> Bool {
    false
  }

  fn watch(self, key: UInt64) -> UInt64 {
    0
  }

  fn wait(self, key: UInt64, ticket: UInt64, reason: StringSlice) {}

  fn wake(self, key: UInt64) {}

  fn lock(self, mutex: UInt64) {}

  fn unlock(self, mutex: UInt64) {}

  fn yield_now(self) {}
}

fn add(counter: intrinsic::Shared[Counter], amount: Int64) -> Int64
  uses Tasks
{
  intrinsic::shared_update(counter, input: amount, change: fn(value, by) {
    value.count += by
    value.count
  })
}

fn push(texts: intrinsic::Shared[List[String]], text: own String) -> USize
  uses Tasks
{
  intrinsic::shared_update(texts, input: own text, change: fn(list, added) {
    mut list.push(own added)
    list.length()
  })
}

fn pop(texts: intrinsic::Shared[List[String]]) -> Option[String]
  uses Tasks
{
  intrinsic::shared_update(texts, input: 0, change: fn(list, _) {
    mut list.pop()
  })
}

test "a copy refers to the same value" {
  var tasks = InOrder(opened: 0, cancelled: [])
  provide mut tasks {
    let counter = intrinsic::shared_new(Counter(count: 1, label: "a ${1}"))
    let other = counter.copy()
    assert add(counter, amount: 2) == 3
    assert add(other, amount: 4) == 7
    assert add(counter, amount: 0) == 7
  }
}

test "an update moves its input into the value and a value out of it" {
  var tasks = InOrder(opened: 0, cancelled: [])
  provide mut tasks {
    let texts: intrinsic::Shared[List[String]] = intrinsic::shared_new([])
    let other = texts.copy()
    assert push(texts, text: "first ${1}") == 1
    assert push(other, text: "second ${2}") == 2
    assert pop(texts) == Some("second 2")
    assert push(other, text: "third ${3}") == 2
  }
}

test "every copy has the same key, and another shared value has another" {
  var tasks = InOrder(opened: 0, cancelled: [])
  provide mut tasks {
    let first = intrinsic::shared_new(Counter(count: 0, label: "first"))
    let second = intrinsic::shared_new(Counter(count: 0, label: "second"))
    let copy = first.copy()
    assert intrinsic::shared_key(first) == intrinsic::shared_key(copy)
    assert intrinsic::shared_key(first) != intrinsic::shared_key(second)
  }
}

test "tasks update one value through their own references" {
  var tasks = InOrder(opened: 0, cancelled: [])
  provide mut tasks {
    let counter = intrinsic::shared_new(Counter(count: 0, label: "tasks"))
    concurrent for index in 1..=4 {
      let _ = add(counter, amount: index)
    }
    concurrent {
      let _ = add(counter, amount: 100)
      let _ = add(counter.copy(), amount: 1000)
    }
    assert add(counter, amount: 0) == 1110
  }
}

test "a shared value of no size" {
  var tasks = InOrder(opened: 0, cancelled: [])
  provide mut tasks {
    let nothing = intrinsic::shared_new(Nothing())
    let other = nothing.copy()
    assert intrinsic::shared_key(nothing) == intrinsic::shared_key(other)
  }
}

fn release(reference: own intrinsic::Shared[Counter]) {}

fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  let counter = intrinsic::shared_new(Counter(count: 0, label: "threads ${1}"))
  parallel for index in 0..20000 {
    if index % 2 == 0 {
      release(counter.copy())
    }
  }
  Console.print_line("released")
  ExitCode.success
}
|}

(* The standard library with the probe module, checked, and a compiler for
   it. *)
let loaded =
  lazy
    (let engine = Engine.create () in
     Database.load_package ~usize_bits:64 engine ~name:Standard_library.package ~dependencies:[]
       (Standard_library.modules @ [ (probe, source) ]);
     let database = Engine.context engine in
     let text = (Query.demand database Workspace.file probe).source in
     (match Type_checker.diagnostics database probe with
     | [] -> ()
     | diagnostics ->
         fail "the source has diagnostics:\n%s"
           (String.concat "" (List.map (Diagnostic.render text) diagnostics)));
     ( database,
       Compile.create ~want:(Database.want_in engine) database target_64 (Lazy.force compiler)
         (Lazy.force cache) settings ))

let () =
  test "shared values are updated, copied, and dropped without a leak" (fun () ->
      let database, compile = Lazy.force loaded in
      match Compile.run_tests compile ~time_limit:2000 (tests_in database probe) with
      | Ok records ->
          expect_string
            ~expected:(String.concat "" (List.init 5 (Printf.sprintf "test %d passed\n")))
            (render_records records)
      | Error message -> failwith message)

let () =
  test "on threads, references to one shared value are copied and dropped" (fun () ->
      let _, compile = Lazy.force loaded in
      List.iter
        (fun workers ->
          Unix.putenv "TRUSS_WORKERS" (string_of_int workers);
          match
            Compile.run_program compile ~main:(Top { module_ = probe; name = "main" }) ~arguments:[]
          with
          | Ok (0, output, _) -> expect_string ~expected:"released\n" output
          | Ok (status, _, errors) -> fail "ended with status %d: %s" status errors
          | Error message -> failwith message)
        worker_counts)

(* Where the capability check allows [shared_update] and [shared_key],
   which require [Tasks], and the [Storable] bound on [Shared]'s value. *)
let checks : Path.module_ = { package = Standard_library.package; modules = [ "shared_checks" ] }

let checks_source =
  {|use standard::intrinsic

capability Ticker {
  fn next() -> Int64
}

type Clockwork(ticks: intrinsic::Shared[Int64])

impl Ticker for Clockwork {
  fn next(self) -> Int64 {
    intrinsic::shared_update(self.ticks, input: 1, change: fn(ticks, by) {
      ticks += by
      ticks
    })
  }
}

type Flag(raised: intrinsic::Shared[Bool])

impl Tasks for Flag {
  fn open(self) -> UInt64 {
    intrinsic::shared_key(self.raised)
  }

  fn spawn(self, task_group: UInt64, work: own fn(UInt64), item: UInt64) -> Bool {
    work(item)
    true
  }

  fn join(self, task_group: UInt64) {}

  fn cancel(self, task_group: UInt64) -> Bool {
    intrinsic::shared_update(self.raised, input: true, change: fn(raised, now) {
      let first = !raised
      raised = now
      first
    })
  }

  fn cancelled(self) -> Bool {
    false
  }

  fn watch(self, key: UInt64) -> UInt64 {
    0
  }

  fn wait(self, key: UInt64, ticket: UInt64, reason: StringSlice) {}

  fn wake(self, key: UInt64) {}

  fn lock(self, mutex: UInt64) {}

  fn unlock(self, mutex: UInt64) {}

  fn yield_now(self) {}
}

fn with_tasks(ticks: intrinsic::Shared[Int64]) -> UInt64
  uses Tasks
{
  intrinsic::shared_key(ticks)
}

fn without_tasks(ticks: intrinsic::Shared[Int64]) -> UInt64 {
  intrinsic::shared_key(ticks)
}

fn of_a_view(numbers: intrinsic::Shared[Slice[Int64]]) -> UInt64
  uses Tasks
{
  intrinsic::shared_key(numbers)
}
|}

let () =
  test "Shared's operations require Tasks outside an impl, and its value must be Storable"
    (fun () ->
      let engine = Engine.create () in
      Database.load_package ~usize_bits:64 engine ~name:Standard_library.package ~dependencies:[]
        (Standard_library.modules @ [ (checks, checks_source) ]);
      let database = Engine.context engine in
      let text = (Query.demand database Workspace.file checks).source in
      expect_string
        ~expected:
          "standard/shared_checks.truss:66:3: error[capabilities.not_available]: This call uses \
           `Tasks`, which is not available here. Declare it with `uses Tasks`, or `provide` an \
           implementation.\n\
          \  |   intrinsic::shared_key(ticks)\n\
          \  |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n\
           standard/shared_checks.truss:69:23: error[types.unsatisfied_bound]: \
           `Shared[Slice[Int64]]` needs `Slice[Int64]: Storable`, which does not hold here.\n\
          \  | fn of_a_view(numbers: intrinsic::Shared[Slice[Int64]]) -> UInt64\n\
          \  |                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n\
           standard/shared_checks.truss:72:3: error[types.unsatisfied_bound]: This needs \
           `Slice[Int64]: Storable`, which does not hold.\n\
          \  |   intrinsic::shared_key(numbers)\n\
          \  |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
        (String.concat ""
           (List.map (Diagnostic.render text) (Type_checker.diagnostics database checks))))

let () = Harness.finish ()
