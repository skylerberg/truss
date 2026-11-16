open Codegen_support

let probe : Path.file =
  { module_ = { package = Path.standard_package; modules = [ "shared_probe" ] }; name = "probe" }

let source = Fixtures.Shared.shared_probe

let loaded =
  lazy
    (let database =
       Database.create
         [
           {
             name = Path.standard_package;
             dependencies = [];
             files = Standard_library.files @ [ (probe, source) ];
           };
         ]
     in
     Database.For_testing.root database
       (Generated (Program_main (Top { module_ = probe.module_; name = "main" })));
     let text = Source.create ~path:(Path.show_file probe) source in
     (match diagnostics database probe with
     | [] -> ()
     | diagnostics ->
         fail "the source has diagnostics:\n%s"
           (String.concat "" (List.map (Diagnostic.render text) diagnostics)));
     ( database,
       Compile.create
         (Database.make_lowering_requests database [ Path.standard_package ])
         (Lazy.force compiler) (Lazy.force cache) (Lazy.force settings) ))

let () =
  test "shared values are updated, copied, and dropped without a leak" (fun () ->
      let database, compile = Lazy.force loaded in
      match Compile.run_tests compile ~time_limit_ms:2000 (tests_in database probe.module_) with
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

let checks : Path.file =
  { module_ = { package = Path.standard_package; modules = [ "shared_checks" ] }; name = "checks" }

let checks_source = Fixtures.Shared.checks_source

let () =
  test
    "Shared's operations need Tasks except directly in a method of a capability's impl, and its \
     value must be Storable" (fun () ->
      let database =
        Database.create
          [
            {
              name = Path.standard_package;
              dependencies = [];
              files = Standard_library.files @ [ (checks, checks_source) ];
            };
          ]
      in
      let text = checks_source in
      let actual =
        List.map
          (fun (diagnostic : Diagnostic.t) ->
            ( Diagnostic.Code.name diagnostic.code,
              String.sub text diagnostic.span.start (diagnostic.span.stop - diagnostic.span.start)
            ))
          (diagnostics database checks)
      in
      let expected =
        [
          ("capabilities.lambda_uses", "fn() { intrinsic::shared_key(self.ticks) }");
          ("capabilities.not_available", "intrinsic::shared_key(self.ticks)");
          ("capabilities.not_available", "intrinsic::shared_key(ticks)");
          ("types.unsatisfied_bound", "intrinsic::Shared[Slice[Int64]]");
        ]
      in
      let show = List.map (fun (code, excerpt) -> code ^ " at " ^ excerpt) in
      if actual <> expected then
        fail "expected [%s], got [%s]"
          (String.concat "; " (show expected))
          (String.concat "; " (show actual)))
