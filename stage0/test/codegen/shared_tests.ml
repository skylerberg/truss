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
     Database.For_testing.add_root database
       (Generated (Program_main (Top { module_ = probe.module_; name = "main" })));
     let text = Source.create ~path:(Path.show_file probe) source in
     (match Codegen_support.list_diagnostics database probe with
     | [] -> ()
     | diagnostics ->
         Codegen_support.fail "the source has diagnostics:\n%s"
           (String.concat "" (List.map (Diagnostic.render text) diagnostics)));
     ( database,
       Backend.create
         (match Database.find_lowered_lookups database [ Path.standard_package ] with
         | Ok lookups -> lookups
         | Error message -> failwith message)
         (Lazy.force Codegen_support.c_compiler)
         Development ))

let () =
  Codegen_support.test "shared values are updated, copied, and dropped without a leak" (fun () ->
      let database, backend = Lazy.force loaded in
      match
        Backend.run_tests backend ~time_limit_ms:2000
          (Codegen_support.list_tests_in database probe.module_)
      with
      | Ok records ->
          Codegen_support.expect_string
            ~expected:(String.concat "" (List.init 5 (Printf.sprintf "test %d passed\n")))
            (Codegen_support.render_records records)
      | Error message -> failwith message)

let () =
  Codegen_support.test "on threads, references to one shared value are copied and dropped"
    (fun () ->
      let _, backend = Lazy.force loaded in
      List.iter
        (fun workers ->
          Unix.putenv "TRUSS_WORKERS" (string_of_int workers);
          match
            Backend.For_testing.run_program backend
              ~main:(Top { module_ = probe.module_; name = "main" })
              ~arguments:[]
          with
          | Ok (0, output, _) -> Codegen_support.expect_string ~expected:"released\n" output
          | Ok (status, _, errors) -> Codegen_support.fail "ended with status %d: %s" status errors
          | Error message -> failwith message)
        Codegen_support.worker_counts)

let checks : Path.file =
  { module_ = { package = Path.standard_package; modules = [ "shared_checks" ] }; name = "checks" }

let checks_source = Fixtures.Shared.checks_source

let () =
  Codegen_support.test
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
          (Codegen_support.list_diagnostics database checks)
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
        Codegen_support.fail "expected [%s], got [%s]"
          (String.concat "; " (show expected))
          (String.concat "; " (show actual)))
