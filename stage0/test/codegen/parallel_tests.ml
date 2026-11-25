let expect_same_with_any_workers text ~expected =
  let program = Codegen_support.build_main text in
  List.iter
    (fun workers ->
      Unix.putenv "TRUSS_WORKERS" (string_of_int workers);
      let status, output, errors = Process.run program [] in
      if status <> 0 then Codegen_support.fail "ended with status %d: %s" status errors;
      Codegen_support.expect_string ~expected output)
    (Codegen_support.list_worker_counts ())

let () =
  Codegen_support.test
    "branches give results through lets, mutate their own parts, and call a lambda" (fun () ->
      expect_same_with_any_workers ~expected:"2500050000 2500000000 2 n100000 300000\n"
        Fixtures.Parallel.parallel_branches_with_totals);
  Codegen_support.test "a branch forks again at every depth of a recursion" (fun () ->
      expect_same_with_any_workers ~expected:"832040\n" Fixtures.Parallel.parallel_fib);
  Codegen_support.test
    "one branch moves a field out and another changes a second field, and the first is \
     reinitialized after" (fun () ->
      expect_same_with_any_workers ~expected:"first taken second!\n"
        Fixtures.Parallel.parallel_branches_moving_and_changing_a_pair)

let board = Fixtures.Parallel.board

let () =
  Codegen_support.test "a parallel for over a list mutates each element once" (fun () ->
      expect_same_with_any_workers ~expected:"7905322 same\n"
        (board ^ Fixtures.Parallel.parallel_for_mutating_a_list));
  Codegen_support.test "a region reads a parameter that the function is passed by pointer"
    (fun () ->
      expect_same_with_any_workers ~expected:"2 4 6 8\n"
        Fixtures.Parallel.doubled_through_a_pointer_parameter);
  Codegen_support.test "a parallel for over a list leaves each element at its position" (fun () ->
      expect_same_with_any_workers ~expected:"5050\n"
        Fixtures.Parallel.parallel_for_over_a_list_by_position);
  Codegen_support.test "a panic in an iteration of a parallel for over a range ends the program"
    (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        Codegen_support.run_main Fixtures.Parallel.parallel_for_with_a_panic
      in
      Codegen_support.expect_int ~expected:101 status;
      if not (String.includes ~affix:"the last one ran" errors) then
        Codegen_support.fail "reported %s" errors);
  Codegen_support.test "an empty range and a range of one run their bodies no times and once"
    (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        Codegen_support.run_main Fixtures.Parallel.parallel_for_over_empty_and_single_ranges
      in
      Codegen_support.expect_int ~expected:101 status;
      if not (String.includes ~affix:"minus three ran" errors) then
        Codegen_support.fail "reported %s" errors)

let () =
  Codegen_support.test "a parallel for over a range of characters steps over the surrogates"
    (fun () ->
      Unix.putenv "TRUSS_WORKERS" "8";
      let status, _, errors =
        Codegen_support.run_main
          Fixtures.Parallel.parallel_for_over_characters_around_the_surrogates
      in
      Codegen_support.expect_int ~expected:101 status;
      if not (String.includes ~affix:"the last character ran" errors) then
        Codegen_support.fail "reported %s" errors)

let () =
  Codegen_support.test
    "a test runs the branches of a parallel block and of a parallel for, in order" (fun () ->
      Codegen_support.expect_output
        (board ^ Fixtures.Parallel.parallel_board_test)
        "test 0 passed\n")

let lowered_int32 = Lowered.Value Codegen_support.int32
let add left right = Lowered.Binary (Add, Codegen_support.copy left, Codegen_support.copy right)
let take_address holder = Lowered.Address { place = Codegen_support.at holder; writable = false }

let expect_c_includes c texts =
  List.iter
    (fun text ->
      if not (String.includes ~affix:text c) then Codegen_support.fail "no %s in:\n%s" text c)
    texts

let () =
  Codegen_support.test
    "an outlined function's own local goes with it, a shared local it only reads arrives by value, \
     and one it writes arrives as a restrict pointer" (fun () ->
      let env = Codegen_support.make_shape_env () in
      let builder = Emit_c.Ir_builder.create env ~item:(Codegen_support.code_item "entry") in
      let parameter = Emit_c.Ir_builder.allocate_local builder lowered_int32 in
      let sum = Emit_c.Ir_builder.allocate_local builder lowered_int32 in
      let other = Emit_c.Ir_builder.allocate_local builder lowered_int32 in
      Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
      Emit_c.Ir_builder.emit builder
        (Assign (Codegen_support.at parameter, Use (Codegen_support.constant_int32 5)));
      let first =
        Emit_c.Ir_builder.outline builder ~index:0 ~parts:[] (fun () ->
            let own = Emit_c.Ir_builder.allocate_local builder ~name:"own" lowered_int32 in
            Emit_c.Ir_builder.emit builder
              (Assign (Codegen_support.at own, add parameter parameter));
            Emit_c.Ir_builder.emit builder (Assign (Codegen_support.at sum, add own parameter));
            Emit_c.Ir_builder.finish builder (Return None))
      in
      let second =
        Emit_c.Ir_builder.outline builder ~index:1 ~parts:[] (fun () ->
            Emit_c.Ir_builder.emit builder
              (Assign (Codegen_support.at other, Use (Codegen_support.copy parameter)));
            Emit_c.Ir_builder.finish builder (Return None))
      in
      Emit_c.Ir_builder.emit builder
        (Fork { branches = [ (0, take_address first); (1, take_address second) ] });
      Emit_c.Ir_builder.emit builder (Assign (Codegen_support.at sum, add sum other));
      Emit_c.Ir_builder.finish builder (Return (Some (Codegen_support.copy sum)));
      let fragment =
        Emit_c.Ir_builder.build builder
          { parameters = []; result = Some lowered_int32; returns = true }
      in
      let c = Emit_c.For_testing.render_c fragment in
      expect_c_includes c
        [
          "_Nested_0_body(int32_t l0, int32_t *restrict l1_address)";
          "_Nested_0_body(*(*l5).f_capture0, (*l5).f_capture1);";
          "_Nested_1_body(int32_t l0, int32_t *restrict l2_address)";
          "int32_t l6_own;";
        ];
      if String.includes ~affix:"f_capture2" c then
        Codegen_support.fail "a function reaches three locals:\n%s" c;
      Codegen_support.expect_status 20 [ Codegen_support.make_program_fragment fragment ])

let () =
  Codegen_support.test
    "a region nested in another reaches the enclosing function's locals through it, by address \
     where the inner region writes them and by value where it only reads them" (fun () ->
      let env = Codegen_support.make_shape_env () in
      let builder = Emit_c.Ir_builder.create env ~item:(Codegen_support.code_item "entry") in
      let written = Emit_c.Ir_builder.allocate_local builder ~name:"written" lowered_int32 in
      let read = Emit_c.Ir_builder.allocate_local builder ~name:"read" lowered_int32 in
      let target = Emit_c.Ir_builder.allocate_local builder ~name:"target" lowered_int32 in
      let pointer =
        Emit_c.Ir_builder.allocate_local builder ~name:"pointer"
          (Pointer { target = lowered_int32; writable = true })
      in
      let pointee = Codegen_support.at ~projections:[ Deref ] pointer in
      Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
      Emit_c.Ir_builder.emit builder
        (Assign (Codegen_support.at written, Use (Codegen_support.constant_int32 1)));
      Emit_c.Ir_builder.emit builder
        (Assign (Codegen_support.at read, Use (Codegen_support.constant_int32 3)));
      Emit_c.Ir_builder.emit builder
        (Assign (Codegen_support.at target, Use (Codegen_support.constant_int32 10)));
      Emit_c.Ir_builder.emit builder
        (Assign
           ( Codegen_support.at pointer,
             Use (Address { place = Codegen_support.at target; writable = true }) ));
      let outer =
        Emit_c.Ir_builder.outline builder ~index:0 ~parts:[] (fun () ->
            Emit_c.Ir_builder.emit builder
              (Assign (pointee, Binary (Add, Copy pointee, Codegen_support.constant_int32 6)));
            let inner =
              Emit_c.Ir_builder.outline builder ~index:1 ~parts:[] (fun () ->
                  Emit_c.Ir_builder.emit builder
                    (Assign
                       ( Codegen_support.at written,
                         Binary (Add, Codegen_support.copy read, Codegen_support.constant_int32 4)
                       ));
                  Emit_c.Ir_builder.finish builder (Return None))
            in
            Emit_c.Ir_builder.emit builder (Fork { branches = [ (1, take_address inner) ] });
            Emit_c.Ir_builder.finish builder (Return None))
      in
      Emit_c.Ir_builder.emit builder (Fork { branches = [ (0, take_address outer) ] });
      Emit_c.Ir_builder.emit builder (Assign (Codegen_support.at written, add written target));
      Emit_c.Ir_builder.finish builder (Return (Some (Codegen_support.copy written)));
      let fragment =
        Emit_c.Ir_builder.build builder
          { parameters = []; result = Some lowered_int32; returns = true }
      in
      expect_c_includes
        (Emit_c.For_testing.render_c fragment)
        [
          "_Nested_0_body(int32_t *restrict l0_written_address, int32_t l1_read, int32_t *restrict \
           l3_pointer)";
          "_Nested_1_body(int32_t *restrict l0_written_address, int32_t l1_read)";
        ];
      Codegen_support.expect_status 23 [ Codegen_support.make_program_fragment fragment ])

let () =
  Codegen_support.test
    "a shared record that a region only reads arrives as a restrict pointer, not as a copy"
    (fun () ->
      let point_shape =
        ( "Point",
          Memory_layout.Record
            [
              Codegen_support.field "x" Codegen_support.int32;
              Codegen_support.field "y" Codegen_support.int32;
            ] )
      in
      let env = Codegen_support.make_shape_env ~extra:[ point_shape ] () in
      let builder = Emit_c.Ir_builder.create env ~item:(Codegen_support.code_item "entry") in
      let point =
        Emit_c.Ir_builder.allocate_local builder ~name:"point"
          (Codegen_support.value (Codegen_support.named "Point"))
      in
      let sum = Emit_c.Ir_builder.allocate_local builder ~name:"sum" lowered_int32 in
      let field name = Codegen_support.at ~projections:[ Field name ] point in
      Emit_c.Ir_builder.start builder (Emit_c.Ir_builder.allocate_block builder);
      Emit_c.Ir_builder.emit builder (Assign (field "x", Use (Codegen_support.constant_int32 3)));
      Emit_c.Ir_builder.emit builder (Assign (field "y", Use (Codegen_support.constant_int32 4)));
      let region =
        Emit_c.Ir_builder.outline builder ~index:0 ~parts:[] (fun () ->
            Emit_c.Ir_builder.emit builder
              (Assign (Codegen_support.at sum, Binary (Add, Copy (field "x"), Copy (field "y"))));
            Emit_c.Ir_builder.finish builder (Return None))
      in
      Emit_c.Ir_builder.emit builder (Fork { branches = [ (0, take_address region) ] });
      Emit_c.Ir_builder.finish builder (Return (Some (Codegen_support.copy sum)));
      let fragment =
        Emit_c.Ir_builder.build builder
          { parameters = []; result = Some lowered_int32; returns = true }
      in
      let c = Emit_c.For_testing.render_c fragment in
      expect_c_includes c [ " *restrict l0_point_address, int32_t *restrict l1_sum_address)" ];
      Codegen_support.expect_status ~extra:[ point_shape ] 7
        [ Codegen_support.make_program_fragment fragment ])

let () =
  Codegen_support.test
    "a coroutine runs when resumed, switches back when it suspends, and ends when it returns"
    (fun () ->
      let work : Ground.function_type =
        {
          parameters = [ (Read, Codegen_support.uint64) ];
          result = Codegen_support.unit;
          lends = None;
          uses = [];
        }
      in
      let environment =
        [
          ( "count",
            Lowered.Pointer
              { target = Codegen_support.value Codegen_support.int32; writable = true } );
        ]
      in
      let count = Codegen_support.at ~projections:[ Deref; Field "count"; Deref ] 2 in
      let add amount = Lowered.Assign (count, Binary (Add, Copy count, amount)) in
      let coroutine =
        Codegen_support.function_ ~parameters:[ 0; 1; 4 ] ~environment
          [
            Codegen_support.local ~name:"environment" (Raw (Nullable_pointer Opaque));
            Codegen_support.local ~name:"item" (Codegen_support.value Codegen_support.uint64);
            Codegen_support.local (Pointer { target = Environment 0; writable = false });
            Codegen_support.local (Codegen_support.value Codegen_support.int32);
            Codegen_support.local ~name:"capabilities" Convention.capabilities;
          ]
          [
            Codegen_support.block
              [
                Assign (Codegen_support.at 2, Use (Codegen_support.copy 0));
                Assign (Codegen_support.at 3, Convert (Codegen_support.copy 1, Integer Int32));
                add (Codegen_support.copy 3);
                Call { target = Intrinsic Coroutine_suspend; arguments = []; result = Discarded };
                add (Codegen_support.constant_int32 10);
              ]
              (Return None);
          ]
      in
      let resume into : Lowered.statement =
        Call
          {
            target = Intrinsic Coroutine_resume;
            arguments = [ Codegen_support.copy 3 ];
            result = Returned (Codegen_support.at into);
          }
      in
      let add_amount amount =
        Lowered.Assign (Codegen_support.at 6, Binary (Add, Codegen_support.copy 6, amount))
      in
      Codegen_support.expect_status 112
        [
          Codegen_support.entry ~nested:[ coroutine ]
            [
              Codegen_support.local ~name:"count" (Codegen_support.value Codegen_support.int32);
              Codegen_support.local (Environment 0);
              Codegen_support.local (Codegen_support.value (Function work));
              Codegen_support.local (Codegen_support.value Codegen_support.uint64);
              Codegen_support.local (Raw Bool);
              Codegen_support.local (Raw Bool);
              Codegen_support.local (Codegen_support.value Codegen_support.int32);
              Codegen_support.local (Codegen_support.value Codegen_support.int32);
              Codegen_support.local (Codegen_support.value Codegen_support.int32);
            ]
            [
              Codegen_support.block
                [
                  Assign (Codegen_support.at 0, Use (Codegen_support.constant_int32 0));
                  Assign
                    ( Codegen_support.at ~projections:[ Field "count" ] 1,
                      Use (Address { place = Codegen_support.at 0; writable = true }) );
                  Assign
                    ( Codegen_support.at 2,
                      Function_value
                        {
                          code = Nested 0;
                          environment =
                            Some (Address { place = Codegen_support.at 1; writable = false });
                        } );
                  Call
                    {
                      target = Intrinsic Coroutine_start;
                      arguments =
                        [
                          Copy (Builtin_records.Function_value.project_code (Codegen_support.at 2));
                          Copy
                            (Builtin_records.Function_value.project_environment
                               (Codegen_support.at 2));
                          Constant (Integer (UInt64, Z.one));
                        ];
                      result = Returned (Codegen_support.at 3);
                    };
                  resume 4;
                  Assign (Codegen_support.at 6, Use (Codegen_support.copy 0));
                  resume 5;
                  Assign (Codegen_support.at 7, Convert (Codegen_support.copy 4, Integer Int32));
                  Assign (Codegen_support.at 8, Convert (Codegen_support.copy 5, Integer Int32));
                  Assign
                    ( Codegen_support.at 7,
                      Binary (Multiply, Codegen_support.copy 7, Codegen_support.constant_int32 100)
                    );
                  Assign
                    ( Codegen_support.at 8,
                      Binary (Multiply, Codegen_support.copy 8, Codegen_support.constant_int32 50)
                    );
                  add_amount (Codegen_support.copy 0);
                  add_amount (Codegen_support.copy 7);
                  add_amount (Codegen_support.copy 8);
                ]
                (Return (Some (Codegen_support.copy 6)));
            ];
        ])

let runtime_declarations =
  {|#define _GNU_SOURCE
#include <stddef.h>
#include <stdint.h>
#include <stdatomic.h>
#include <time.h>

struct truss_branch {
  void (*run)(void *environment);
  void *environment;
};

void truss_runtime_main(void (*code)(void *environment, uint64_t item, void *capabilities),
                        void *environment, uint32_t requested_workers);
void truss_runtime_parallel(const struct truss_branch *branches, uint64_t count);
void truss_runtime_parallel_range(void (*body)(void *environment, uint64_t first, uint64_t last),
                                  void *environment, uint64_t first, uint64_t last);
|}

let spinning =
  {|
static atomic_int timed_out;

static int spin_until(atomic_int *flag, long milliseconds) {
  struct timespec start, now;
  clock_gettime(CLOCK_MONOTONIC, &start);
  while (!atomic_load(flag)) {
    clock_gettime(CLOCK_MONOTONIC, &now);
    long elapsed = (now.tv_sec - start.tv_sec) * 1000 + (now.tv_nsec - start.tv_nsec) / 1000000;
    if (elapsed > milliseconds) return 0;
  }
  return 1;
}

static void wait_or_time_out(atomic_int *flag) {
  if (!spin_until(flag, 2000)) atomic_store(&timed_out, 1);
}
|}

let expect_runtime_status expected program =
  let output = Codegen_support.make_scratch_path "runtime" in
  match
    C_compiler.build_executable
      (Lazy.force Codegen_support.c_compiler)
      Development
      ~sources:
        [
          C_compiler.make_source ~name:"the runtime" (Startup.render_runtime ~tests:false);
          C_compiler.make_source ~name:"the program" (runtime_declarations ^ program);
        ]
      ~output
  with
  | Ok () ->
      let status, _, errors = Process.run output [] in
      if status <> expected then
        Codegen_support.fail "expected status %d, got %d (%s)" expected status errors
  | Error message -> failwith message

let () =
  Codegen_support.test
    "a parallel block of 40 branches starts its last branch while its first still runs" (fun () ->
      expect_runtime_status 0
        (spinning
       ^ {|
static atomic_int last_ran;

static void wait_for_last(void *environment) { wait_or_time_out(&last_ran); }
static void mark_last(void *environment) { atomic_store(&last_ran, 1); }
static void do_nothing(void *environment) {}

static void run(void *environment, uint64_t item, void *capabilities) {
  struct truss_branch branches[40];
  branches[0] = (struct truss_branch){wait_for_last, NULL};
  for (int index = 1; index < 39; index++) branches[index] = (struct truss_branch){do_nothing, NULL};
  branches[39] = (struct truss_branch){mark_last, NULL};
  truss_runtime_parallel(branches, 40);
}

int main(void) {
  truss_runtime_main(run, NULL, 2);
  return atomic_load(&timed_out);
}
|}
        ));
  Codegen_support.test
    "a thread that waits for a stolen branch runs only work forked inside that branch" (fun () ->
      expect_runtime_status 0
        (spinning
       ^ {|
static atomic_int outer_started, inner_started, inner_done, unrelated_ran_early;

static void fork_two(void (*first)(void *environment), void (*second)(void *environment)) {
  struct truss_branch branches[2] = {{first, NULL}, {second, NULL}};
  truss_runtime_parallel(branches, 2);
}

static void wait_for_inner(void *environment) { wait_or_time_out(&inner_done); }

static void unrelated(void *environment) {
  if (!atomic_load(&inner_done)) atomic_store(&unrelated_ran_early, 1);
}

static void outer(void *environment) {
  atomic_store(&outer_started, 1);
  wait_or_time_out(&inner_started);
  fork_two(wait_for_inner, unrelated);
}

static void wait_for_inner_start(void *environment) { wait_or_time_out(&inner_started); }

static void inner(void *environment) {
  atomic_store(&inner_started, 1);
  spin_until(&unrelated_ran_early, 50);
  atomic_store(&inner_done, 1);
}

static void waiting(void *environment) {
  wait_or_time_out(&outer_started);
  fork_two(wait_for_inner_start, inner);
}

static void run(void *environment, uint64_t item, void *capabilities) { fork_two(waiting, outer); }

int main(void) {
  truss_runtime_main(run, NULL, 3);
  if (atomic_load(&timed_out)) return 2;
  return atomic_load(&unrelated_ran_early);
}
|}
        ));
  Codegen_support.test "one worker runs a parallel range as one call to its body" (fun () ->
      expect_runtime_status 0
        {|
static atomic_int calls, wrong_bounds;

static void count_call(void *environment, uint64_t first, uint64_t last) {
  atomic_fetch_add(&calls, 1);
  if (first != 0 || last != 999) atomic_store(&wrong_bounds, 1);
}

static void run(void *environment, uint64_t item, void *capabilities) {
  truss_runtime_parallel_range(count_call, NULL, 0, 999);
}

int main(void) {
  truss_runtime_main(run, NULL, 1);
  return atomic_load(&calls) != 1 || atomic_load(&wrong_bounds);
}
|});
  Codegen_support.test "eight workers run every index of a parallel range once" (fun () ->
      expect_runtime_status 0
        {|
#define COUNT 100003

static atomic_uchar visits[COUNT];
static atomic_int wrong_bounds;

static void visit(void *environment, uint64_t first, uint64_t last) {
  if (first > last || last >= COUNT) {
    atomic_store(&wrong_bounds, 1);
    return;
  }
  for (uint64_t index = first; index <= last; index++) atomic_fetch_add(&visits[index], 1);
}

static void run(void *environment, uint64_t item, void *capabilities) {
  truss_runtime_parallel_range(visit, NULL, 0, 0);
  truss_runtime_parallel_range(visit, NULL, 1, 2);
  truss_runtime_parallel_range(visit, NULL, 3, COUNT - 1);
}

int main(void) {
  truss_runtime_main(run, NULL, 8);
  if (atomic_load(&wrong_bounds)) return 2;
  for (uint64_t index = 0; index < COUNT; index++)
    if (atomic_load(&visits[index]) != 1) return 1;
  return 0;
}
|})
