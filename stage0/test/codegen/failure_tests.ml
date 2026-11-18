let expect_bug ~saying work =
  match work () with
  | () -> Codegen_support.fail "expected a compiler bug saying %S" saying
  | exception Compiler_bug.Bug bug ->
      let text = Compiler_bug.to_string bug in
      if not (String.includes ~affix:saying text) then
        Codegen_support.fail "expected %S in %S" saying text

let env = Codegen_support.make_shape_env ()
let emit env make_instance = ignore (Emit_c.make_fragment env (Code (make_instance env)))

let make_caller arguments =
  Codegen_support.entry
    [ Codegen_support.local (Codegen_support.value Codegen_support.int32) ]
    [
      Codegen_support.block
        [
          Codegen_support.call "callee"
            ~parameters:[ Codegen_support.value Codegen_support.int32 ]
            arguments
            (Some (Codegen_support.at 0));
        ]
        (Return (Some (Codegen_support.copy 0)));
    ]

let () =
  Codegen_support.test "a call that passes fewer arguments than its target takes is a bug"
    (fun () ->
      expect_bug ~saying:"passes 0 arguments to a target that takes 1" (fun () ->
          emit env (make_caller [])));
  Codegen_support.test "a return of nothing from a function with a result is a bug" (fun () ->
      expect_bug ~saying:"a return of nothing from a function with a result" (fun () ->
          emit env (Codegen_support.entry [] [ Codegen_support.block [] (Return None) ])));
  Codegen_support.test "a value built with a field its type does not have is a bug" (fun () ->
      expect_bug ~saying:"built with a field third, which it does not have" (fun () ->
          emit
            (Codegen_support.make_shape_env ~extra:Codegen_support.drop_shapes ())
            (Codegen_support.entry
               [ Codegen_support.local (Codegen_support.value Codegen_support.pair) ]
               [
                 Codegen_support.block
                   [
                     Assign
                       ( Codegen_support.at 0,
                         Build
                           {
                             ty = Codegen_support.pair;
                             variant = None;
                             fields = [ ("third", Codegen_support.constant_int32 1) ];
                           } );
                   ]
                   (Return (Some (Codegen_support.constant_int32 0)));
               ])));
  Codegen_support.test "a call that writes its result to a place it is also given is a bug"
    (fun () ->
      let quad = Codegen_support.named "Quad" in
      let pointer writable = Lowered.Pointer { target = Codegen_support.value quad; writable } in
      let swapped : Lowered.statement =
        Call
          {
            target =
              Direct
                {
                  function_ = Instance (Codegen_support.key "swapped");
                  signature =
                    { parameters = [ pointer true; pointer false ]; result = None; returns = true };
                };
            arguments = [ Address { place = Codegen_support.at 0; writable = false } ];
            result = Written (Codegen_support.at 0);
          }
      in
      let four =
        Memory_layout.Record
          (List.map
             (fun name -> Codegen_support.field name Codegen_support.int64)
             [ "a"; "b"; "c"; "d" ])
      in
      expect_bug ~saying:"writes its result to a place it is also given" (fun () ->
          emit
            (Codegen_support.make_shape_env ~extra:[ ("Quad", four) ] ())
            (Codegen_support.entry
               [ Codegen_support.local (Codegen_support.value quad) ]
               [
                 Codegen_support.block [ swapped ]
                   (Return (Some (Codegen_support.constant_int32 0)));
               ])));
  Codegen_support.test "a move out of a constant's static data is a bug" (fun () ->
      let constant : Lowered.place =
        {
          root =
            Static
              { key = Constant (Codegen_support.definition "words"); ty = Codegen_support.text };
          projections = [];
        }
      in
      expect_bug ~saying:"a move out of test::words, which is static data" (fun () ->
          emit
            (Codegen_support.make_shape_env ~extra:Codegen_support.drop_shapes ())
            (Codegen_support.entry
               [ Codegen_support.local (Codegen_support.value Codegen_support.text) ]
               [
                 Codegen_support.block
                   [ Assign (Codegen_support.at 0, Use (Move constant)) ]
                   (Return (Some (Codegen_support.constant_int32 0)));
               ])));
  Codegen_support.test "an instance whose calls fit their targets passes" (fun () ->
      emit env (make_caller [ Codegen_support.constant_int32 1 ]))

let () =
  Codegen_support.test "a compiler bug says which instance was being lowered" (fun () ->
      let not_code =
        Instance.Code
          {
            path = Top { module_ = Codegen_support.example; name = "Point" };
            instantiation = Ground.no_instantiation;
          }
      in
      expect_bug ~saying:"while lowering example::Point" (fun () ->
          ignore (Codegen_support.load ~roots:[ not_code ] "type Point(x: Int64)\n")))
