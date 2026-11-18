let make_storage_type = Storage.make_storage_type

let fill_storage ~target ~buffer values =
  let count = List.length values in
  let uint64_constant number = Lowered.Constant (Integer (UInt64, Z.of_int number)) in
  Lowered.Call
    {
      target = Intrinsic Allocate;
      arguments = [ uint64_constant (4 * count); uint64_constant 4 ];
      result = Returned (Codegen_support.at buffer);
    }
  :: List.mapi
       (fun index value ->
         Lowered.Assign
           ( Codegen_support.at ~projections:[ Index (uint64_constant index) ] buffer,
             Use (Codegen_support.constant_int32 value) ))
       values
  @ [
      Assign
        ( Codegen_support.at target,
          Build
            {
              ty = make_storage_type Codegen_support.int32;
              variant = None;
              fields =
                [
                  ("buffer", Codegen_support.copy buffer);
                  ("length", uint64_constant count);
                  ("capacity", uint64_constant count);
                ];
            } );
    ]

let copy_call drop_and_copy ty ~destination ~source =
  Lowered.Call
    {
      target =
        Direct
          {
            function_ = Item (Copy ty);
            signature = Backend.For_testing.copy_signature drop_and_copy ty;
          };
      arguments =
        [
          Address { place = Codegen_support.at destination; writable = true };
          Address { place = Codegen_support.at source; writable = false };
        ];
      result = Discarded;
    }

let () =
  let drop_and_copy = Backend.For_testing.drop_and_copy (Codegen_support.make_shape_env ()) in
  Codegen_support.test "plain data is trivial and storage is not" (fun () ->
      if
        not
          (Backend.For_testing.is_trivial drop_and_copy
             (Codegen_support.option Codegen_support.int32))
      then Codegen_support.fail "Option[Int32] is not trivial";
      if Backend.For_testing.is_trivial drop_and_copy (make_storage_type Codegen_support.int32) then
        Codegen_support.fail "Storage[Int32] is trivial");
  Codegen_support.test "a record's drop drops only the fields that own something" (fun () ->
      let extra =
        [
          ( "Holder",
            Memory_layout.Record
              [
                Codegen_support.field "items" (make_storage_type Codegen_support.int32);
                Codegen_support.field "count" Codegen_support.int32;
              ] );
        ]
      in
      let env = Codegen_support.make_shape_env ~extra () in
      let c =
        Emit_c.For_testing.render_c
          (Backend.For_testing.drop
             (Backend.For_testing.drop_and_copy env)
             (Codegen_support.named "Holder"))
      in
      if not (String.includes ~affix:"f_items" c) then
        Codegen_support.fail "the drop does not drop the items:\n%s" c;
      if String.includes ~affix:"f_count" c then
        Codegen_support.fail "the drop reads the count:\n%s" c);
  Codegen_support.test "a copy of storage of plain data is one allocation and one memory copy"
    (fun () ->
      let c =
        Emit_c.For_testing.render_c
          (Backend.For_testing.copy drop_and_copy (make_storage_type Codegen_support.int32))
      in
      let count sub = String.find_all ~sub (fun _ matches -> matches + 1) c 0 in
      if count "t_runtime_allocate(" <> 1 || count "__builtin_memcpy(" <> 1 then
        Codegen_support.fail "the copy does not allocate and copy once:\n%s" c);
  Codegen_support.test "a copy of storage keeps its values when the original is mutated" (fun () ->
      let ty = make_storage_type Codegen_support.int32 in
      Codegen_support.expect_status 20
        [
          Codegen_support.make_constant_item (Backend.For_testing.copy drop_and_copy ty);
          Codegen_support.make_constant_item (Backend.For_testing.drop drop_and_copy ty);
          Codegen_support.entry
            [
              Codegen_support.local (Codegen_support.value ty);
              Codegen_support.local (Raw (Pointer (Data Codegen_support.int32)));
              Codegen_support.local (Codegen_support.value ty);
              Codegen_support.local (Raw (Pointer (Data Codegen_support.int32)));
            ]
            [
              Codegen_support.block
                (fill_storage ~target:0 ~buffer:1 [ 10; 20; 30 ]
                @ [
                    copy_call drop_and_copy ty ~destination:2 ~source:0;
                    Assign
                      ( Codegen_support.at
                          ~projections:[ Index (Constant (Integer (UInt64, Z.one))) ]
                          1,
                        Use (Codegen_support.constant_int32 99) );
                    Assign
                      ( Codegen_support.at 3,
                        Use (Codegen_support.copy ~projections:[ Field "buffer" ] 2) );
                    Drop (Codegen_support.at 0);
                  ])
                (Return
                   (Some
                      (Codegen_support.copy
                         ~projections:[ Index (Constant (Integer (UInt64, Z.one))) ]
                         3)));
            ];
        ]);
  Codegen_support.test "dropping a storage with nothing allocated frees nothing" (fun () ->
      let ty = make_storage_type Codegen_support.uint8 in
      Codegen_support.expect_status 0
        [
          Codegen_support.make_constant_item (Backend.For_testing.drop drop_and_copy ty);
          Codegen_support.entry
            [ Codegen_support.local (Codegen_support.value ty) ]
            [
              Codegen_support.block
                [
                  Assign
                    ( Codegen_support.at 0,
                      Build
                        {
                          ty;
                          variant = None;
                          fields =
                            [
                              ("buffer", Constant (Bytes ""));
                              ("length", Constant (Integer (UInt64, Z.zero)));
                              ("capacity", Constant (Integer (UInt64, Z.zero)));
                            ];
                        } );
                  Drop (Codegen_support.at 0);
                ]
                (Return (Some (Codegen_support.constant_int32 0)));
            ];
        ]);
  Codegen_support.test "a copy of storage of storage copies every element and both drop cleanly"
    (fun () ->
      let inner = make_storage_type Codegen_support.int32 in
      let outer = make_storage_type inner in
      let uint64_constant number = Lowered.Constant (Integer (UInt64, Z.of_int number)) in
      Codegen_support.expect_status 4
        [
          Codegen_support.make_constant_item (Backend.For_testing.copy drop_and_copy outer);
          Codegen_support.make_constant_item (Backend.For_testing.copy drop_and_copy inner);
          Codegen_support.make_constant_item (Backend.For_testing.drop drop_and_copy outer);
          Codegen_support.make_constant_item (Backend.For_testing.drop drop_and_copy inner);
          Codegen_support.entry
            [
              Codegen_support.local (Codegen_support.value inner);
              Codegen_support.local (Raw (Pointer (Data Codegen_support.int32)));
              Codegen_support.local (Codegen_support.value inner);
              Codegen_support.local (Raw (Pointer (Data Codegen_support.int32)));
              Codegen_support.local (Raw (Pointer (Data inner)));
              Codegen_support.local (Codegen_support.value outer);
              Codegen_support.local (Codegen_support.value outer);
              Codegen_support.local (Raw (Pointer (Data inner)));
              Codegen_support.local (Raw (Pointer (Data Codegen_support.int32)));
              Codegen_support.local (Codegen_support.value Codegen_support.int32);
            ]
            [
              Codegen_support.block
                (fill_storage ~target:0 ~buffer:1 [ 3 ]
                @ fill_storage ~target:2 ~buffer:3 [ 4 ]
                @ [
                    Call
                      {
                        target = Intrinsic Allocate;
                        arguments = [ uint64_constant 48; uint64_constant 8 ];
                        result = Returned (Codegen_support.at 4);
                      };
                    Assign
                      ( Codegen_support.at ~projections:[ Index (uint64_constant 0) ] 4,
                        Use (Move (Codegen_support.at 0)) );
                    Assign
                      ( Codegen_support.at ~projections:[ Index (uint64_constant 1) ] 4,
                        Use (Move (Codegen_support.at 2)) );
                    Assign
                      ( Codegen_support.at 5,
                        Build
                          {
                            ty = outer;
                            variant = None;
                            fields =
                              [
                                ("buffer", Codegen_support.copy 4);
                                ("length", uint64_constant 2);
                                ("capacity", uint64_constant 2);
                              ];
                          } );
                    copy_call drop_and_copy outer ~destination:6 ~source:5;
                    Drop (Codegen_support.at 5);
                    Assign
                      ( Codegen_support.at 7,
                        Use (Codegen_support.copy ~projections:[ Field "buffer" ] 6) );
                    Assign
                      ( Codegen_support.at 8,
                        Use
                          (Codegen_support.copy
                             ~projections:[ Index (uint64_constant 1); Field "buffer" ]
                             7) );
                    Assign
                      ( Codegen_support.at 9,
                        Use (Codegen_support.copy ~projections:[ Index (uint64_constant 0) ] 8) );
                    Drop (Codegen_support.at 6);
                  ])
                (Return (Some (Codegen_support.copy 9)));
            ];
        ])
