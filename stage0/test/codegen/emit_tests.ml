let render_c_file env program =
  Emit_c.render_file env Development
    (List.map (fun (program_fragment, linkage) -> (program_fragment env, linkage)) program)

let () =
  Codegen_support.test "a function that returns a constant runs and exits with it" (fun () ->
      Codegen_support.expect_status 7
        [
          Codegen_support.entry []
            [ Codegen_support.block [] (Return (Some (Codegen_support.constant_int32 7))) ];
        ]);
  Codegen_support.test "a counted loop over blocks sums its range" (fun () ->
      Codegen_support.expect_status 55
        [
          Codegen_support.entry
            [
              Codegen_support.local ~name:"total" (Codegen_support.value Codegen_support.int32);
              Codegen_support.local ~name:"i" (Codegen_support.value Codegen_support.int32);
              Codegen_support.local (Raw Bool);
            ]
            [
              Codegen_support.block
                [
                  Assign (Codegen_support.at 0, Use (Codegen_support.constant_int32 0));
                  Assign (Codegen_support.at 1, Use (Codegen_support.constant_int32 1));
                ]
                (Goto 1);
              Codegen_support.block
                [
                  Assign
                    ( Codegen_support.at 2,
                      Binary (Less_equal, Codegen_support.copy 1, Codegen_support.constant_int32 10)
                    );
                ]
                (Switch { value = Codegen_support.copy 2; cases = [ (Z.one, 2) ]; default = 3 });
              Codegen_support.block
                [
                  Assign
                    ( Codegen_support.at 0,
                      Binary (Add, Codegen_support.copy 0, Codegen_support.copy 1) );
                  Assign
                    ( Codegen_support.at 1,
                      Binary (Add, Codegen_support.copy 1, Codegen_support.constant_int32 1) );
                ]
                (Goto 1);
              Codegen_support.block [] (Return (Some (Codegen_support.copy 0)));
            ];
        ]);
  let point = Codegen_support.named "Point" in
  let point_shape =
    ( "Point",
      Memory_layout.Record
        [
          Codegen_support.field "x" Codegen_support.int32;
          Codegen_support.field "y" Codegen_support.int32;
        ] )
  in
  Codegen_support.test "a record is built and its fields read" (fun () ->
      Codegen_support.expect_status ~extra:[ point_shape ] 5
        [
          Codegen_support.entry
            [
              Codegen_support.local (Codegen_support.value point);
              Codegen_support.local (Codegen_support.value Codegen_support.int32);
            ]
            [
              Codegen_support.block
                [
                  Assign
                    ( Codegen_support.at 0,
                      Build
                        {
                          ty = point;
                          variant = None;
                          fields =
                            [
                              ("x", Codegen_support.constant_int32 2);
                              ("y", Codegen_support.constant_int32 3);
                            ];
                        } );
                  Assign
                    ( Codegen_support.at 1,
                      Binary
                        ( Add,
                          Codegen_support.copy ~projections:[ Field "x" ] 0,
                          Codegen_support.copy ~projections:[ Field "y" ] 0 ) );
                ]
                (Return (Some (Codegen_support.copy 1)));
            ];
        ]);
  let shape = Codegen_support.named "Shape" in
  let shape_shape =
    ( "Shape",
      Memory_layout.Sum
        [
          Codegen_support.variant "Circle" [ Codegen_support.field "radius" Codegen_support.int32 ];
          Codegen_support.variant "Square"
            [
              Codegen_support.field "side" Codegen_support.int32;
              Codegen_support.field "corner" Codegen_support.int32;
            ];
          Codegen_support.variant "Empty" [];
        ] )
  in
  Codegen_support.test "a tagged sum is built and switched on, and its variant's fields read"
    (fun () ->
      Codegen_support.expect_status ~extra:[ shape_shape ] 9
        [
          Codegen_support.entry
            [ Codegen_support.local (Codegen_support.value shape) ]
            [
              Codegen_support.block
                [
                  Assign
                    ( Codegen_support.at 0,
                      Build
                        {
                          ty = shape;
                          variant = Some "Square";
                          fields =
                            [
                              ("side", Codegen_support.constant_int32 9);
                              ("corner", Codegen_support.constant_int32 1);
                            ];
                        } );
                ]
                (Switch_variant
                   {
                     place = Codegen_support.at 0;
                     cases = [ ("Circle", 1); ("Square", 2) ];
                     default = Some 3;
                   });
              Codegen_support.block [] (Return (Some (Codegen_support.constant_int32 1)));
              Codegen_support.block []
                (Return
                   (Some
                      (Codegen_support.copy
                         ~projections:[ Variant_field { variant = "Square"; field = "side" } ]
                         0)));
              Codegen_support.block [] (Return (Some (Codegen_support.constant_int32 3)));
            ];
        ]);
  let return_bool locals statements =
    Codegen_support.entry
      (locals @ [ Codegen_support.local (Codegen_support.value Codegen_support.int32) ])
      [
        Codegen_support.block
          (statements
          @ [
              Lowered.Assign
                ( Codegen_support.at (List.length locals),
                  Convert (Codegen_support.copy (List.length locals - 1), Integer Int32) );
            ])
          (Return (Some (Codegen_support.copy (List.length locals))));
      ]
  in
  Codegen_support.test "a niche-encoded None is told apart from Some" (fun () ->
      let maybe = Codegen_support.option Codegen_support.bool in
      Codegen_support.expect_status 1
        [
          return_bool
            [
              Codegen_support.local (Codegen_support.value maybe); Codegen_support.local (Raw Bool);
            ]
            [
              Assign (Codegen_support.at 0, Build { ty = maybe; variant = Some "None"; fields = [] });
              Assign (Codegen_support.at 1, Is_variant (Codegen_support.at 0, "None"));
            ];
        ]);
  Codegen_support.test "a niche-encoded Some is not None" (fun () ->
      let maybe = Codegen_support.option Codegen_support.bool in
      Codegen_support.expect_status 0
        [
          return_bool
            [
              Codegen_support.local (Codegen_support.value maybe); Codegen_support.local (Raw Bool);
            ]
            [
              Assign
                ( Codegen_support.at 0,
                  Build
                    {
                      ty = maybe;
                      variant = Some "Some";
                      fields = [ ("value", Constant (Bool false)) ];
                    } );
              Assign (Codegen_support.at 1, Is_variant (Codegen_support.at 0, "None"));
            ];
        ]);
  let tree = Codegen_support.named "Tree" in
  let tree_shape =
    ( "Tree",
      Memory_layout.Sum
        [
          Codegen_support.variant "Leaf" [];
          Codegen_support.variant ~indirect:true "Node"
            [
              Codegen_support.field "left" tree;
              Codegen_support.field "value" Codegen_support.int32;
              Codegen_support.field "right" tree;
            ];
        ] )
  in
  Codegen_support.test "an indirect variant is built in its block and read through it" (fun () ->
      let leaf = Lowered.Build { ty = tree; variant = Some "Leaf"; fields = [] } in
      Codegen_support.expect_status ~extra:[ tree_shape ] 42
        [
          Codegen_support.entry
            [
              Codegen_support.local (Codegen_support.value tree);
              Codegen_support.local (Codegen_support.value tree);
              Codegen_support.local (Codegen_support.value tree);
            ]
            [
              Codegen_support.block
                [
                  Assign (Codegen_support.at 0, leaf);
                  Assign (Codegen_support.at 1, leaf);
                  Assign
                    ( Codegen_support.at 2,
                      Build
                        {
                          ty = tree;
                          variant = Some "Node";
                          fields =
                            [
                              ("left", Move (Codegen_support.at 0));
                              ("value", Codegen_support.constant_int32 42);
                              ("right", Move (Codegen_support.at 1));
                            ];
                        } );
                ]
                (Switch_variant
                   { place = Codegen_support.at 2; cases = [ ("Node", 1) ]; default = Some 2 });
              Codegen_support.block []
                (Return
                   (Some
                      (Codegen_support.copy
                         ~projections:[ Variant_field { variant = "Node"; field = "value" } ]
                         2)));
              Codegen_support.block [] (Return (Some (Codegen_support.constant_int32 0)));
            ];
        ]);
  let bump =
    Codegen_support.define_function "bump"
      (Codegen_support.function_ ~parameters:[ 0 ]
         [
           Codegen_support.local ~name:"count"
             (Pointer { target = Codegen_support.value Codegen_support.int32; writable = true });
         ]
         [
           Codegen_support.block
             [
               Assign
                 ( Codegen_support.at ~projections:[ Deref ] 0,
                   Binary
                     ( Add,
                       Codegen_support.copy ~projections:[ Deref ] 0,
                       Codegen_support.constant_int32 1 ) );
             ]
             (Return None);
         ])
  in
  let bump_signature =
    [ Lowered.Pointer { target = Codegen_support.value Codegen_support.int32; writable = true } ]
  in
  Codegen_support.test "a mut parameter is a pointer the callee writes through" (fun () ->
      Codegen_support.expect_status 4
        [
          bump;
          Codegen_support.entry
            [ Codegen_support.local (Codegen_support.value Codegen_support.int32) ]
            [
              Codegen_support.block
                [
                  Assign (Codegen_support.at 0, Use (Codegen_support.constant_int32 3));
                  Codegen_support.call "bump" ~result:None ~parameters:bump_signature
                    [ Address { place = Codegen_support.at 0; writable = true } ]
                    None;
                ]
                (Return (Some (Codegen_support.copy 0)));
            ];
        ]);
  Codegen_support.test "a mut parameter is a restrict pointer in C" (fun () ->
      let c_file = render_c_file (Codegen_support.make_shape_env ()) [ (bump, External) ] in
      let expected = "void t_test__bump(int32_t *restrict l0_count)" in
      if not (String.includes ~affix:expected c_file) then
        Codegen_support.fail "no %S in:\n%s" expected c_file);
  let callback =
    ({ parameters = [ (Read, Codegen_support.int32) ]; result = Codegen_support.int32; uses = [] }
      : Ground.function_type)
  in
  Codegen_support.test "a lambda reads a local of its caller through its environment" (fun () ->
      let environment =
        [
          ( "offset",
            Lowered.Pointer
              { target = Codegen_support.value Codegen_support.int32; writable = false } );
        ]
      in
      let lambda =
        Codegen_support.function_ ~parameters:[ 0; 1 ]
          ~result:(Codegen_support.value Codegen_support.int32)
          ~environment
          [
            Codegen_support.local ~name:"environment" (Raw (Nullable_pointer Opaque));
            Codegen_support.local ~name:"argument" (Codegen_support.value Codegen_support.int32);
            Codegen_support.local (Pointer { target = Environment 0; writable = false });
            Codegen_support.local (Codegen_support.value Codegen_support.int32);
          ]
          [
            Codegen_support.block
              [
                Assign (Codegen_support.at 2, Use (Codegen_support.copy 0));
                Assign
                  ( Codegen_support.at 3,
                    Binary
                      ( Add,
                        Codegen_support.copy 1,
                        Copy (Codegen_support.at ~projections:[ Deref; Field "offset"; Deref ] 2) )
                  );
              ]
              (Return (Some (Codegen_support.copy 3)));
          ]
      in
      let signature =
        Convention.make_function_value_signature (Codegen_support.make_shape_env ()) callback
      in
      Codegen_support.expect_status 6
        [
          Codegen_support.entry ~nested:[ lambda ]
            [
              Codegen_support.local ~name:"offset" (Codegen_support.value Codegen_support.int32);
              Codegen_support.local (Environment 0);
              Codegen_support.local (Codegen_support.value (Function callback));
              Codegen_support.local (Codegen_support.value Codegen_support.int32);
            ]
            [
              Codegen_support.block
                [
                  Assign (Codegen_support.at 0, Use (Codegen_support.constant_int32 5));
                  Assign
                    ( Codegen_support.at ~projections:[ Field "offset" ] 1,
                      Use (Address { place = Codegen_support.at 0; writable = false }) );
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
                      target = Indirect { value = Codegen_support.copy 2; signature };
                      arguments = [ Codegen_support.constant_int32 1 ];
                      result = Returned (Codegen_support.at 3);
                    };
                ]
                (Return (Some (Codegen_support.copy 3)));
            ];
        ]);
  let float64_constant value = Lowered.Constant (Float64 (Int64.bits_of_float value)) in
  Codegen_support.test "float equality treats every NaN as equal" (fun () ->
      Codegen_support.expect_status 1
        [
          return_bool
            [ Codegen_support.local (Raw Bool) ]
            [
              Assign
                ( Codegen_support.at 0,
                  Binary (Equal, float64_constant Float.nan, float64_constant Float.nan) );
            ];
        ]);
  Codegen_support.test "IEEE float equality does not" (fun () ->
      Codegen_support.expect_status 0
        [
          return_bool
            [ Codegen_support.local (Raw Bool) ]
            [
              Assign
                ( Codegen_support.at 0,
                  Binary (Ieee_equal, float64_constant Float.nan, float64_constant Float.nan) );
            ];
        ]);
  Codegen_support.test "NaN is ordered after every number" (fun () ->
      Codegen_support.expect_status 1
        [
          return_bool
            [ Codegen_support.local (Raw Bool) ]
            [
              Assign
                ( Codegen_support.at 0,
                  Binary (Less, float64_constant Float.infinity, float64_constant Float.nan) );
            ];
        ]);
  Codegen_support.test "negative zero equals zero" (fun () ->
      Codegen_support.expect_status 1
        [
          return_bool
            [ Codegen_support.local (Raw Bool) ]
            [
              Assign
                (Codegen_support.at 0, Binary (Equal, float64_constant (-0.0), float64_constant 0.0));
            ];
        ]);
  Codegen_support.test "a shift amount is masked to the width of the value" (fun () ->
      Codegen_support.expect_status 2
        [
          Codegen_support.entry
            [
              Codegen_support.local (Codegen_support.value Codegen_support.int64);
              Codegen_support.local (Codegen_support.value Codegen_support.int32);
            ]
            [
              Codegen_support.block
                [
                  Assign
                    ( Codegen_support.at 0,
                      Binary
                        ( Shift_left,
                          Codegen_support.constant_int64 1,
                          Lowered.Constant (Integer (UInt64, Z.of_int 65)) ) );
                  Assign (Codegen_support.at 1, Convert (Codegen_support.copy 0, Integer Int32));
                ]
                (Return (Some (Codegen_support.copy 1)));
            ];
        ]);
  Codegen_support.test "an overflowing add reports the overflow" (fun () ->
      Codegen_support.expect_status 1
        [
          return_bool
            [
              Codegen_support.local (Codegen_support.value Codegen_support.int32);
              Codegen_support.local (Raw Bool);
            ]
            [
              Call
                {
                  target = Intrinsic Add_overflow;
                  arguments =
                    [
                      Lowered.Constant (Integer (Int32, Z.of_string "2147483647"));
                      Codegen_support.constant_int32 1;
                      Address { place = Codegen_support.at 0; writable = true };
                    ];
                  result = Returned (Codegen_support.at 1);
                };
            ];
        ]);
  Codegen_support.test "a panic writes its message and position and exits with 101" (fun () ->
      let status, _, errors =
        Codegen_support.run_program
          [
            Codegen_support.entry []
              [
                Codegen_support.block []
                  (Fail
                     {
                       failure = Panic;
                       message = Constant (Bytes "boom");
                       length = Constant (Integer (UInt64, Z.of_int 4));
                       site = { definition = Codegen_support.definition "entry"; offset = 4 };
                       reported = None;
                       trace = None;
                     });
              ];
          ]
      in
      Codegen_support.expect_int ~expected:101 status;
      Codegen_support.expect_string ~expected:"panic: boom\n  at test.truss:1:5\n" errors);
  Codegen_support.test "a copy of a callee is a static inline function, declared before its caller"
    (fun () ->
      let callee =
        Codegen_support.define_function "callee"
          (Codegen_support.function_ ~parameters:[ 0 ]
             ~result:(Codegen_support.value Codegen_support.int32)
             [ Codegen_support.local (Codegen_support.value Codegen_support.int32) ]
             [ Codegen_support.block [] (Return (Some (Codegen_support.copy 0))) ])
      in
      let caller =
        Codegen_support.entry
          [ Codegen_support.local (Codegen_support.value Codegen_support.int32) ]
          [
            Codegen_support.block
              [
                Codegen_support.call "callee"
                  ~parameters:[ Codegen_support.value Codegen_support.int32 ]
                  [ Codegen_support.constant_int32 7 ]
                  (Some (Codegen_support.at 0));
              ]
              (Return (Some (Codegen_support.copy 0)));
          ]
      in
      let c_file =
        render_c_file (Codegen_support.make_shape_env ()) [ (caller, External); (callee, Internal) ]
      in
      let copy = "static inline int32_t t_test__callee(int32_t l0) {" in
      if not (String.includes ~affix:copy c_file) then
        Codegen_support.fail "no %S in:\n%s" copy c_file;
      if String.includes ~affix:"\nint32_t t_test__callee(int32_t);" c_file then
        Codegen_support.fail "the callee is also declared as another file's:\n%s" c_file);
  Codegen_support.test "the C checks each type's size and alignment against its layout" (fun () ->
      let pair_shape =
        ( "Pair",
          Memory_layout.Record
            [
              Codegen_support.field "first" Codegen_support.int32;
              Codegen_support.field "second" Codegen_support.int64;
            ] )
      in
      let holder =
        Codegen_support.define_function "holder"
          (Codegen_support.function_
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
                           fields =
                             [
                               ("first", Codegen_support.constant_int32 1);
                               ("second", Constant (Integer (Int64, Z.of_int 2)));
                             ];
                         } );
                 ]
                 (Return None);
             ])
      in
      let c_file =
        render_c_file
          (Codegen_support.make_shape_env ~extra:[ pair_shape ] ())
          [ (holder, External) ]
      in
      let expected =
        "_Static_assert(sizeof(t_test__Pair) == 16 && _Alignof(t_test__Pair) == 8, \"layout\");"
      in
      if not (String.includes ~affix:expected c_file) then
        Codegen_support.fail "no %S in:\n%s" expected c_file);
  Codegen_support.test "emitting the same program twice gives the same C" (fun () ->
      let program = [ (bump, Emit_c.External) ] in
      Codegen_support.expect_string
        ~expected:(render_c_file (Codegen_support.make_shape_env ()) program)
        (render_c_file (Codegen_support.make_shape_env ()) program));
  Codegen_support.test "the C has the blocks the entry reaches and the locals their code names"
    (fun () ->
      let entry =
        Codegen_support.define_function "entry"
          (Codegen_support.function_
             ~result:(Codegen_support.value Codegen_support.int32)
             [
               Codegen_support.local ~name:"unused" (Codegen_support.value Codegen_support.int32);
               Codegen_support.local ~name:"late" (Codegen_support.value Codegen_support.int32);
               Codegen_support.local ~name:"early" (Codegen_support.value Codegen_support.int32);
               Codegen_support.local ~name:"dead" (Codegen_support.value Codegen_support.int32);
             ]
             [
               Codegen_support.block
                 [ Assign (Codegen_support.at 2, Use (Codegen_support.constant_int32 1)) ]
                 (Goto 2);
               Codegen_support.block [] (Return (Some (Codegen_support.copy 1)));
               Codegen_support.block
                 [ Assign (Codegen_support.at 1, Use (Codegen_support.copy 2)) ]
                 (Goto 1);
               Codegen_support.block
                 [ Assign (Codegen_support.at 3, Use (Codegen_support.copy 2)) ]
                 (Goto 1);
             ])
      in
      let c_file = render_c_file (Codegen_support.make_shape_env ()) [ (entry, External) ] in
      List.iter
        (fun name ->
          if not (String.includes ~affix:name c_file) then
            Codegen_support.fail "no %s in:\n%s" name c_file)
        [ "l1_late"; "l2_early" ];
      List.iter
        (fun name ->
          if String.includes ~affix:name c_file then Codegen_support.fail "%s in:\n%s" name c_file)
        [ "l0_unused"; "l3_dead"; "b3:" ]);
  ()

let () =
  Codegen_support.test "a symbol names the path and the type arguments" (fun () ->
      let item =
        Lowered.Item.Code
          {
            path = Method { owner = Well_known.make_path List; name = "each"; receiver = Read };
            instantiation =
              { Ground.no_instantiation with type_arguments = [ Type Codegen_support.int64 ] };
          }
      in
      Codegen_support.expect_string ~expected:"t_standard__list__List_each_Of_test__Int64_End_"
        (Emit_c.make_symbol item));
  let render_function_symbol package modules =
    Emit_c.make_symbol
      (Lowered.Item.Code
         {
           path = Top { module_ = { package; modules }; name = "length" };
           instantiation = Ground.no_instantiation;
         })
  in
  Codegen_support.test "a symbol marks a package's owner apart from its modules" (fun () ->
      Codegen_support.expect_string ~expected:"t_acme_Owns_geometry__vector__length"
        (render_function_symbol { owner = Some "acme"; name = "geometry" } [ "vector" ]);
      if
        render_function_symbol { owner = Some "acme"; name = "geometry" } [ "vector" ]
        = render_function_symbol { owner = None; name = "acme" } [ "geometry"; "vector" ]
      then
        Codegen_support.fail
          "a package with an owner and a module of the same names have one symbol");
  Codegen_support.test "a long symbol keeps its start and ends with a hash" (fun () ->
      let make_long_symbol name =
        Emit_c.make_symbol (Codegen_support.code_item (String.make 300 name))
      in
      let left = make_long_symbol 'a' and right = make_long_symbol 'b' in
      Codegen_support.expect_int ~expected:(180 + 6 + 32) (String.length left);
      if left = right then Codegen_support.fail "two long names give one symbol")

let intrinsic_types : Backend.For_testing.Intrinsics.types =
  { uint64 = Codegen_support.uint64; string_slice = Codegen_support.named "StringSlice" }

let build_entry build_body : Codegen_support.program_fragment =
 fun env ->
  let builder = Emit_c.Builder.create env ~item:(Codegen_support.code_item "entry") in
  Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder);
  let result = build_body builder in
  Emit_c.Builder.finish builder (Return (Some (Copy (Lowered.make_local_place result))));
  Emit_c.Builder.build builder
    { parameters = []; result = Some (Codegen_support.value Codegen_support.int32); returns = true }

let operate builder ?destination ?(type_arguments = [ Codegen_support.int32 ]) ?value_arguments
    operation arguments =
  Backend.For_testing.Intrinsics.lower ?value_arguments
    (Codegen_support.make_shape_env ())
    builder intrinsic_types operation ~type_arguments arguments ~destination
    ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
    ~trace:None

let () =
  Codegen_support.test
    "storage with room is pushed onto, and inserts, removes, swaps, and pops in place" (fun () ->
      let storage_ty =
        Ground.Named
          { path = Intrinsic.make_builtin_path Storage; arguments = [ Type Codegen_support.int32 ] }
      in
      Codegen_support.expect_status 171
        [
          build_entry (fun builder ->
              let storage =
                Emit_c.Builder.allocate_local builder ~name:"storage"
                  (Codegen_support.value storage_ty)
              in
              let popped =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              let sum =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              ignore
                (operate builder
                   ~destination:(Lowered.make_local_place storage)
                   (Buffer Storage_empty) []);
              ignore
                (operate builder (Buffer Storage_set_capacity)
                   [
                     Place (Lowered.make_local_place storage);
                     Value (Lowered.make_uint64_constant 2);
                   ]);
              ignore
                (operate builder (Buffer Storage_set_capacity)
                   [
                     Place (Lowered.make_local_place storage);
                     Value (Lowered.make_uint64_constant 8);
                   ]);
              List.iter
                (fun count ->
                  ignore
                    (operate builder (Buffer Storage_push)
                       [
                         Place (Lowered.make_local_place storage);
                         Value (Codegen_support.constant_int32 count);
                       ]))
                [ 1; 2; 3; 4; 5 ];
              ignore
                (operate builder (Buffer Storage_insert)
                   [
                     Place (Lowered.make_local_place storage);
                     Value (Lowered.make_uint64_constant 0);
                     Value (Codegen_support.constant_int32 0);
                   ]);
              ignore
                (operate builder ~destination:(Lowered.make_local_place popped)
                   (Buffer Storage_remove)
                   [
                     Place (Lowered.make_local_place storage);
                     Value (Lowered.make_uint64_constant 2);
                   ]);
              ignore
                (operate builder (Buffer Storage_swap)
                   [
                     Place (Lowered.make_local_place storage);
                     Value (Lowered.make_uint64_constant 0);
                     Value (Lowered.make_uint64_constant 4);
                   ]);
              ignore
                (operate builder ~destination:(Lowered.make_local_place popped) (Buffer Storage_pop)
                   [ Place (Lowered.make_local_place storage) ]);
              let make_element index weight =
                match
                  operate builder (Lend Storage_at)
                    [
                      Place (Lowered.make_local_place storage);
                      Value (Lowered.make_uint64_constant index);
                    ]
                with
                | Some place ->
                    Lowered.Binary (Multiply, Copy place, Codegen_support.constant_int32 weight)
                | None -> failwith "storage_at lends nothing"
              in
              Emit_c.Builder.emit builder
                (Assign (Lowered.make_local_place sum, Use (Codegen_support.constant_int32 0)));
              List.iter
                (fun (index, weight) ->
                  let term =
                    Emit_c.Builder.allocate_local builder
                      (Codegen_support.value Codegen_support.int32)
                  in
                  Emit_c.Builder.emit builder
                    (Assign (Lowered.make_local_place term, make_element index weight));
                  Emit_c.Builder.emit builder
                    (Assign
                       ( Lowered.make_local_place sum,
                         Binary
                           ( Add,
                             Copy (Lowered.make_local_place sum),
                             Copy (Lowered.make_local_place term) ) )))
                [ (0, 1); (1, 3); (2, 5); (3, 7) ];
              let length =
                Emit_c.Builder.allocate_local builder
                  (Codegen_support.value (Codegen_support.named "UInt64"))
              in
              ignore
                (operate builder ~destination:(Lowered.make_local_place length)
                   (Buffer Storage_length)
                   [ Place (Lowered.make_local_place storage) ]);
              let length32 =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place length32,
                     Convert (Copy (Lowered.make_local_place length), Integer Int32) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place length32,
                     Binary
                       ( Multiply,
                         Copy (Lowered.make_local_place length32),
                         Codegen_support.constant_int32 30 ) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place sum,
                     Binary
                       ( Add,
                         Copy (Lowered.make_local_place sum),
                         Copy (Lowered.make_local_place length32) ) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place sum,
                     Binary
                       ( Add,
                         Copy (Lowered.make_local_place sum),
                         Copy (Lowered.make_local_place popped) ) ));
              sum);
        ]);
  Codegen_support.test "an array's elements are moved into new storage, in order" (fun () ->
      let storage_ty =
        Ground.Named
          { path = Intrinsic.make_builtin_path Storage; arguments = [ Type Codegen_support.int32 ] }
      in
      let array_ty =
        Ground.Named
          {
            path = Intrinsic.make_builtin_path Array;
            arguments = [ Type Codegen_support.int32; Value (Z.of_int 3) ];
          }
      in
      Codegen_support.expect_status 165
        [
          build_entry (fun builder ->
              let array =
                Emit_c.Builder.allocate_local builder ~name:"array" (Codegen_support.value array_ty)
              in
              List.iteri
                (fun index count ->
                  Emit_c.Builder.emit builder
                    (Assign
                       ( Lowered.project (Lowered.make_local_place array)
                           (Index (Lowered.make_uint64_constant index)),
                         Use (Codegen_support.constant_int32 count) )))
                [ 4; 5; 6 ];
              let storage =
                Emit_c.Builder.allocate_local builder ~name:"storage"
                  (Codegen_support.value storage_ty)
              in
              ignore
                (operate builder
                   ~destination:(Lowered.make_local_place storage)
                   ~value_arguments:[ Z.of_int 3 ]
                   (Buffer Storage_from_array)
                   [ Value (Copy (Lowered.make_local_place array)) ]);
              let last =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              and middle =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              ignore
                (operate builder ~destination:(Lowered.make_local_place last) (Buffer Storage_pop)
                   [ Place (Lowered.make_local_place storage) ]);
              ignore
                (operate builder ~destination:(Lowered.make_local_place middle) (Buffer Storage_pop)
                   [ Place (Lowered.make_local_place storage) ]);
              let length =
                Emit_c.Builder.allocate_local builder
                  (Codegen_support.value (Codegen_support.named "UInt64"))
              in
              ignore
                (operate builder ~destination:(Lowered.make_local_place length)
                   (Buffer Storage_length)
                   [ Place (Lowered.make_local_place storage) ]);
              let status =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Convert (Copy (Lowered.make_local_place length), Integer Int32) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Binary
                       ( Multiply,
                         Copy (Lowered.make_local_place status),
                         Codegen_support.constant_int32 100 ) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place last,
                     Binary
                       ( Multiply,
                         Copy (Lowered.make_local_place last),
                         Codegen_support.constant_int32 10 ) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Binary
                       ( Add,
                         Copy (Lowered.make_local_place status),
                         Copy (Lowered.make_local_place last) ) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Binary
                       ( Add,
                         Copy (Lowered.make_local_place status),
                         Copy (Lowered.make_local_place middle) ) ));
              status);
        ]);
  Codegen_support.test "a view of an array has the array's elements" (fun () ->
      let array_ty =
        Ground.Named
          {
            path = Intrinsic.make_builtin_path Array;
            arguments = [ Type Codegen_support.int32; Value (Z.of_int 3) ];
          }
      in
      let view_ty =
        Ground.Named
          { path = Intrinsic.make_builtin_path View; arguments = [ Type Codegen_support.int32 ] }
      in
      let extra =
        [
          ( Ground.to_string view_ty,
            Storage.make_view_shape ~uint64:(Codegen_support.named "UInt64") Codegen_support.int32
          );
        ]
      in
      let operate builder ?destination operation arguments =
        Backend.For_testing.Intrinsics.lower
          ~value_arguments:[ Z.of_int 3 ]
          (Codegen_support.make_shape_env ~extra ())
          builder intrinsic_types operation ~type_arguments:[ Codegen_support.int32 ] arguments
          ~destination
          ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
          ~trace:None
      in
      Codegen_support.expect_status ~extra 53
        [
          build_entry (fun builder ->
              let array =
                Emit_c.Builder.allocate_local builder ~name:"array" (Codegen_support.value array_ty)
              in
              List.iteri
                (fun index count ->
                  Emit_c.Builder.emit builder
                    (Assign
                       ( Lowered.project (Lowered.make_local_place array)
                           (Index (Lowered.make_uint64_constant index)),
                         Use (Codegen_support.constant_int32 count) )))
                [ 4; 5; 6 ];
              let view =
                Emit_c.Builder.allocate_local builder ~name:"view" (Codegen_support.value view_ty)
              in
              ignore
                (operate builder ~destination:(Lowered.make_local_place view) (Buffer Array_view)
                   [ Place (Lowered.make_local_place array) ]);
              let middle =
                match
                  operate builder (Lend View_at)
                    [
                      Place (Lowered.make_local_place view); Value (Lowered.make_uint64_constant 1);
                    ]
                with
                | Some place -> place
                | None -> failwith "view_at lends nothing"
              in
              let length =
                Emit_c.Builder.allocate_local builder
                  (Codegen_support.value (Codegen_support.named "UInt64"))
              in
              ignore
                (operate builder ~destination:(Lowered.make_local_place length) (Buffer View_length)
                   [ Place (Lowered.make_local_place view) ]);
              let status =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Convert (Copy (Lowered.make_local_place length), Integer Int32) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Binary
                       ( Add,
                         Copy (Lowered.make_local_place status),
                         Codegen_support.constant_int32 50 ) ));
              let weighted =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place weighted,
                     Binary (Subtract, Copy middle, Codegen_support.constant_int32 5) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Binary
                       ( Add,
                         Copy (Lowered.make_local_place status),
                         Copy (Lowered.make_local_place weighted) ) ));
              status);
        ]);
  Codegen_support.test
    "an array made of a storage has its elements, and the storage's buffer is freed" (fun () ->
      let storage_ty = Storage.make_storage_type Codegen_support.int32 in
      let array_ty =
        Ground.Named
          {
            path = Intrinsic.make_builtin_path Array;
            arguments = [ Type Codegen_support.int32; Value (Z.of_int 3) ];
          }
      in
      let operate builder ?destination operation arguments =
        Backend.For_testing.Intrinsics.lower
          ~value_arguments:[ Z.of_int 3 ]
          (Codegen_support.make_shape_env ())
          builder intrinsic_types operation ~type_arguments:[ Codegen_support.int32 ] arguments
          ~destination
          ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
          ~trace:None
      in
      let make_program_with pushed =
        [
          build_entry (fun builder ->
              let storage =
                Emit_c.Builder.allocate_local builder (Codegen_support.value storage_ty)
              in
              ignore
                (operate builder
                   ~destination:(Lowered.make_local_place storage)
                   (Buffer Storage_with_capacity)
                   [ Value (Lowered.make_uint64_constant 3) ]);
              List.iter
                (fun count ->
                  ignore
                    (operate builder (Buffer Storage_push)
                       [
                         Place (Lowered.make_local_place storage);
                         Value (Codegen_support.constant_int32 count);
                       ]))
                pushed;
              let array =
                Emit_c.Builder.allocate_local builder ~name:"array" (Codegen_support.value array_ty)
              in
              ignore
                (operate builder ~destination:(Lowered.make_local_place array)
                   (Buffer Array_from_storage)
                   [ Place (Lowered.make_local_place storage) ]);
              let status =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Use
                       (Copy
                          (Lowered.project (Lowered.make_local_place array)
                             (Index (Lowered.make_uint64_constant 0)))) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Binary
                       ( Add,
                         Copy (Lowered.make_local_place status),
                         Copy
                           (Lowered.project (Lowered.make_local_place array)
                              (Index (Lowered.make_uint64_constant 2))) ) ));
              status);
        ]
      in
      Codegen_support.expect_status 46 (make_program_with [ 40; 5; 6 ]);
      Codegen_support.expect_status 101 (make_program_with [ 40; 5 ]));
  Codegen_support.test "a float fits an integer type where the whole number it is cut down to does"
    (fun () ->
      let expect_all_right cases =
        Codegen_support.expect_status
          ((1 lsl List.length cases) - 1)
          [
            build_entry (fun builder ->
                let status =
                  Emit_c.Builder.allocate_local builder
                    (Codegen_support.value Codegen_support.int32)
                in
                Emit_c.Builder.emit builder
                  (Assign (Lowered.make_local_place status, Use (Codegen_support.constant_int32 0)));
                List.iteri
                  (fun index (float, target, expected) ->
                    let fits = Emit_c.Builder.allocate_local builder (Raw Bool) in
                    ignore
                      (operate builder ~destination:(Lowered.make_local_place fits)
                         ~type_arguments:[ Codegen_support.float64; target ]
                         (Scalar Fits)
                         [ Value (Constant (Float64 (Int64.bits_of_float float))) ]);
                    let right = Emit_c.Builder.allocate_local builder (Raw Bool) in
                    Emit_c.Builder.emit builder
                      (Assign
                         ( Lowered.make_local_place right,
                           Binary
                             (Equal, Copy (Lowered.make_local_place fits), Constant (Bool expected))
                         ));
                    let bit =
                      Emit_c.Builder.allocate_local builder
                        (Codegen_support.value Codegen_support.int32)
                    in
                    Emit_c.Builder.emit builder
                      (Assign
                         ( Lowered.make_local_place bit,
                           Convert (Copy (Lowered.make_local_place right), Integer Int32) ));
                    Emit_c.Builder.emit builder
                      (Assign
                         ( Lowered.make_local_place bit,
                           Binary
                             ( Shift_left,
                               Copy (Lowered.make_local_place bit),
                               Codegen_support.constant_int32 index ) ));
                    Emit_c.Builder.emit builder
                      (Assign
                         ( Lowered.make_local_place status,
                           Binary
                             ( Bit_or,
                               Copy (Lowered.make_local_place status),
                               Copy (Lowered.make_local_place bit) ) )))
                  cases;
                status);
          ]
      in
      expect_all_right
        [
          (9223372036854774784., Codegen_support.int64, true);
          (9223372036854775808., Codegen_support.int64, false);
          (-9223372036854775808., Codegen_support.int64, true);
          (-9223372036854777856., Codegen_support.int64, false);
          (Float.nan, Codegen_support.int64, false);
          (Float.infinity, Codegen_support.int64, false);
          (Float.neg_infinity, Codegen_support.int64, false);
        ];
      expect_all_right
        [
          (255.9, Codegen_support.uint8, true);
          (256., Codegen_support.uint8, false);
          (-0.5, Codegen_support.uint8, true);
          (-1., Codegen_support.uint8, false);
          (0., Codegen_support.uint8, true);
        ]);
  Codegen_support.test "a storage is shortened in place and keeps its room" (fun () ->
      let storage_ty = Storage.make_storage_type Codegen_support.uint8 in
      let operate_checked builder ?destination operation arguments =
        Backend.For_testing.Intrinsics.lower
          (Codegen_support.make_shape_env ())
          builder intrinsic_types operation ~type_arguments:[ Codegen_support.uint8 ] arguments
          ~destination
          ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
          ~trace:None
      in
      let make_shortened ~to_ =
        [
          build_entry (fun builder ->
              let storage =
                Emit_c.Builder.allocate_local builder (Codegen_support.value storage_ty)
              in
              ignore
                (operate_checked builder
                   ~destination:(Lowered.make_local_place storage)
                   (Buffer Storage_with_capacity)
                   [ Value (Lowered.make_uint64_constant 8) ]);
              String.iter
                (fun byte ->
                  ignore
                    (operate_checked builder (Buffer Storage_push)
                       [
                         Place (Lowered.make_local_place storage);
                         Value (Constant (Integer (UInt8, Z.of_int (Char.code byte))));
                       ]))
                "abcde";
              ignore
                (operate_checked builder (Buffer Storage_shorten)
                   [
                     Place (Lowered.make_local_place storage);
                     Value (Lowered.make_uint64_constant to_);
                   ]);
              let status =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              let read_part place =
                let read =
                  Emit_c.Builder.allocate_local builder
                    (Codegen_support.value Codegen_support.int32)
                in
                Emit_c.Builder.emit builder
                  (Assign (Lowered.make_local_place read, Convert (Copy place, Integer Int32)));
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place status,
                       Binary
                         ( Add,
                           Copy (Lowered.make_local_place status),
                           Copy (Lowered.make_local_place read) ) ))
              in
              Emit_c.Builder.emit builder
                (Assign (Lowered.make_local_place status, Use (Codegen_support.constant_int32 0)));
              read_part (Lowered.project (Lowered.make_local_place storage) (Field "length"));
              read_part (Lowered.project (Lowered.make_local_place storage) (Field "capacity"));
              read_part
                (Lowered.project
                   (Lowered.project (Lowered.make_local_place storage) (Field "buffer"))
                   (Index (Lowered.make_uint64_constant (to_ - 1))));
              status);
        ]
      in
      Codegen_support.expect_status (2 + 8 + Char.code 'b') (make_shortened ~to_:2);
      Codegen_support.expect_status 101 (make_shortened ~to_:6);
      match (Intrinsic_signatures.make_signature (Buffer Storage_shorten)).generics with
      | [ { kind = Type_generic [ { trait = Top { name = "Plain"; _ }; _ } ]; _ } ] -> ()
      | _ -> Codegen_support.fail "storage_shorten takes elements that are not known to be Plain");
  Codegen_support.test
    "a checked build stops a storage or view operation whose precondition does not hold" (fun () ->
      let storage_ty = Storage.make_storage_type Codegen_support.uint8 in
      let view_ty =
        Ground.Named
          { path = Intrinsic.make_builtin_path View; arguments = [ Type Codegen_support.uint8 ] }
      in
      let extra =
        [
          ( Ground.to_string view_ty,
            Storage.make_view_shape ~uint64:(Codegen_support.named "UInt64") Codegen_support.uint8
          );
        ]
      in
      let operate_checked builder ?destination operation arguments =
        ignore
          (Backend.For_testing.Intrinsics.lower
             (Codegen_support.make_shape_env ~extra ())
             builder intrinsic_types operation ~type_arguments:[ Codegen_support.uint8 ] arguments
             ~destination
             ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
             ~trace:None)
      in
      let byte : Lowered.operand = Constant (Integer (UInt8, Z.of_int 1)) in
      let expect_stop saying run_operation =
        let status, _, errors =
          Codegen_support.run_program ~extra
            [
              build_entry (fun builder ->
                  let storage =
                    Emit_c.Builder.allocate_local builder (Codegen_support.value storage_ty)
                  in
                  operate_checked builder
                    ~destination:(Lowered.make_local_place storage)
                    (Buffer Storage_with_capacity)
                    [ Value (Lowered.make_uint64_constant 3) ];
                  List.iter
                    (fun _ ->
                      operate_checked builder (Buffer Storage_push)
                        [ Place (Lowered.make_local_place storage); Value byte ])
                    [ 'a'; 'b'; 'c' ];
                  let view =
                    Emit_c.Builder.allocate_local builder ~name:"view"
                      (Codegen_support.value view_ty)
                  in
                  operate_checked builder ~destination:(Lowered.make_local_place view)
                    (Buffer Storage_view)
                    [ Place (Lowered.make_local_place storage) ];
                  run_operation builder ~storage ~view;
                  let status =
                    Emit_c.Builder.allocate_local builder
                      (Codegen_support.value Codegen_support.int32)
                  in
                  Emit_c.Builder.emit builder
                    (Assign (Lowered.make_local_place status, Use (Codegen_support.constant_int32 0)));
                  status);
            ]
        in
        if status <> 101 || not (String.includes ~affix:saying errors) then
          Codegen_support.fail "expected a panic saying %S, got status %d (%s)" saying status errors
      in
      let index = "index out of bounds" and slice = "slice out of bounds" in
      expect_stop "an element pushed to a storage that has no room" (fun builder ~storage ~view:_ ->
          operate_checked builder (Buffer Storage_push)
            [ Place (Lowered.make_local_place storage); Value byte ]);
      expect_stop "an element inserted into a storage that has no room"
        (fun builder ~storage ~view:_ ->
          operate_checked builder (Buffer Storage_insert)
            [
              Place (Lowered.make_local_place storage);
              Value (Lowered.make_uint64_constant 1);
              Value byte;
            ]);
      expect_stop index (fun builder ~storage ~view:_ ->
          operate_checked builder (Buffer Storage_insert)
            [
              Place (Lowered.make_local_place storage);
              Value (Lowered.make_uint64_constant 9);
              Value byte;
            ]);
      expect_stop "a storage lengthened to more than its capacity" (fun builder ~storage ~view:_ ->
          operate_checked builder (Buffer Storage_lengthen)
            [ Place (Lowered.make_local_place storage); Value (Lowered.make_uint64_constant 1) ]);
      expect_stop "a storage's capacity set to less than its length"
        (fun builder ~storage ~view:_ ->
          operate_checked builder (Buffer Storage_set_capacity)
            [ Place (Lowered.make_local_place storage); Value (Lowered.make_uint64_constant 2) ]);
      expect_stop index (fun builder ~storage ~view:_ ->
          let removed =
            Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.uint8)
          in
          operate_checked builder
            ~destination:(Lowered.make_local_place removed)
            (Buffer Storage_remove)
            [ Place (Lowered.make_local_place storage); Value (Lowered.make_uint64_constant 3) ]);
      expect_stop index (fun builder ~storage ~view:_ ->
          operate_checked builder (Buffer Storage_swap)
            [
              Place (Lowered.make_local_place storage);
              Value (Lowered.make_uint64_constant 0);
              Value (Lowered.make_uint64_constant 3);
            ]);
      expect_stop index (fun builder ~storage ~view:_ ->
          operate_checked builder (Lend Storage_at)
            [ Place (Lowered.make_local_place storage); Value (Lowered.make_uint64_constant 3) ]);
      expect_stop index (fun builder ~storage:_ ~view ->
          operate_checked builder (Lend View_at)
            [ Place (Lowered.make_local_place view); Value (Lowered.make_uint64_constant 3) ]);
      expect_stop index (fun builder ~storage:_ ~view ->
          operate_checked builder (Buffer View_swap)
            [
              Place (Lowered.make_local_place view);
              Value (Lowered.make_uint64_constant 3);
              Value (Lowered.make_uint64_constant 0);
            ]);
      expect_stop slice (fun builder ~storage:_ ~view ->
          let part = Emit_c.Builder.allocate_local builder (Codegen_support.value view_ty) in
          operate_checked builder ~destination:(Lowered.make_local_place part) (Buffer View_slice)
            [
              Place (Lowered.make_local_place view);
              Value (Lowered.make_uint64_constant 1);
              Value (Lowered.make_uint64_constant 4);
            ]);
      expect_stop slice (fun builder ~storage:_ ~view ->
          let part = Emit_c.Builder.allocate_local builder (Codegen_support.value view_ty) in
          operate_checked builder ~destination:(Lowered.make_local_place part) (Buffer View_slice)
            [
              Place (Lowered.make_local_place view);
              Value (Lowered.make_uint64_constant 2);
              Value (Lowered.make_uint64_constant 1);
            ]);
      expect_stop "an element popped from an empty storage" (fun builder ~storage ~view:_ ->
          operate_checked builder (Buffer Storage_shorten)
            [ Place (Lowered.make_local_place storage); Value (Lowered.make_uint64_constant 0) ];
          let popped =
            Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.uint8)
          in
          operate_checked builder ~destination:(Lowered.make_local_place popped)
            (Buffer Storage_pop)
            [ Place (Lowered.make_local_place storage) ]))

let () =
  Codegen_support.test
    "a small read-only value is passed by value unless it holds an array's elements" (fun () ->
      let make_array_type count : Ground.ty =
        Named
          {
            path = Intrinsic.make_builtin_path Array;
            arguments = [ Type Codegen_support.int32; Value (Z.of_int count) ];
          }
      in
      let pair = Codegen_support.named "Pair" in
      let extra =
        [ ("Pair", Memory_layout.Record [ Codegen_support.field "cells" (make_array_type 2) ]) ]
      in
      let env = Codegen_support.make_shape_env ~extra () in
      let is_by_value ty =
        match Convention.classify_parameter env Read ty with
        | Some (Value _) -> true
        | Some _ -> false
        | None ->
            Codegen_support.fail "a parameter with a size is not passed";
            false
      in
      if not (is_by_value Codegen_support.int64) then
        Codegen_support.fail "a number is passed by address";
      if is_by_value (make_array_type 4) then
        Codegen_support.fail "a small array is passed by value";
      if is_by_value pair then
        Codegen_support.fail "a small record that holds an array is passed by value";
      match Convention.classify_parameter env Own (make_array_type 4) with
      | Some (Value _) -> ()
      | _ -> Codegen_support.fail "a small array that is given away is passed by address")
