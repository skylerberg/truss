(* [intrinsic::Shared] and its operations. Only the standard library can
   name the intrinsic module, so the tests' source is one more module of the
   [standard] package, checked and compiled with the library. *)

open Codegen_support

let probe : Path.file =
  { module_ = { package = Path.standard_package; modules = [ "shared_probe" ] }; name = "probe" }

let source = Fixtures.Shared.shared_probe

(* The standard library with the probe module, checked, and a compiler for
   it. *)
let loaded =
  lazy
    (let engine = Engine.create () in
     Database.load_package ~usize_bits:64 engine ~name:Path.standard_package ~dependencies:[]
       (Standard_library.files @ [ (probe, source) ]);
     let database = Engine.context engine in
     let text = (Query.demand database Workspace.file probe).source in
     (match Checks.diagnostics database probe with
     | [] -> ()
     | diagnostics ->
         fail "the source has diagnostics:\n%s"
           (String.concat "" (List.map (Diagnostic.render text) diagnostics)));
     ( database,
       Compile.create
         ~want:(fun lowering wanted ->
           Engine.set engine Compile.roots lowering
             (Compile.add_roots (Engine.context engine) lowering wanted))
         database target_64 (Lazy.force compiler) (Lazy.force cache) settings ))

let () =
  test "shared values are updated, copied, and dropped without a leak" (fun () ->
      let database, compile = Lazy.force loaded in
      match Compile.run_tests compile ~time_limit:2000 (tests_in database probe.module_) with
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
            Compile.For_testing.run_program compile
              ~main:(Top { module_ = probe.module_; name = "main" })
              ~arguments:[]
          with
          | Ok (0, output, _) -> expect_string ~expected:"released\n" output
          | Ok (status, _, errors) -> fail "ended with status %d: %s" status errors
          | Error message -> failwith message)
        worker_counts)

(* Where the capability check allows [shared_update] and [shared_key],
   which require [Tasks], and the [Storable] bound on [Shared]'s value. *)
let checks : Path.file =
  { module_ = { package = Path.standard_package; modules = [ "shared_checks" ] }; name = "checks" }

let checks_source = Fixtures.Shared.checks_source

let () =
  test "Shared's operations require Tasks outside an impl, and its value must be Storable"
    (fun () ->
      let engine = Engine.create () in
      Database.load_package ~usize_bits:64 engine ~name:Path.standard_package ~dependencies:[]
        (Standard_library.files @ [ (checks, checks_source) ]);
      let database = Engine.context engine in
      let text = Source.text (Query.demand database Workspace.file checks).source in
      let actual =
        List.map
          (fun (diagnostic : Diagnostic.t) ->
            ( Diagnostic.Code.name diagnostic.code,
              String.sub text diagnostic.span.start (diagnostic.span.stop - diagnostic.span.start)
            ))
          (Checks.diagnostics database checks)
      in
      let expected =
        [
          ("capabilities.not_available", "intrinsic::shared_key(ticks)");
          ("types.unsatisfied_bound", "intrinsic::Shared[Slice[Int64]]");
          ("types.unsatisfied_bound", "intrinsic::shared_key(numbers)");
        ]
      in
      let show = List.map (fun (code, excerpt) -> code ^ " at " ^ excerpt) in
      if actual <> expected then
        fail "expected [%s], got [%s]"
          (String.concat "; " (show expected))
          (String.concat "; " (show actual)))
