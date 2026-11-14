(* The functions generated for each type, and debug output. *)

open Memory_layout
open Codegen_support

(* Generated functions for each type *)

let storage element = named "Storage" ~arguments:[ Type element ]

let representation extra (ty : Ground.ty) : Memory_layout.representation =
  match ty with
  | Named { path = Top { name = "Storage"; _ }; arguments = [ Type element ] } -> Storage element
  | _ -> Shape (shapes extra ty)

let glue ?(extra = []) () =
  Glue.create (shape_env ~extra ()) ~representation:(representation extra) ~usize ()

(* Statements that allocate a storage of [Int32]s holding [values] into
   local [target], using local [buffer]. *)
let fill_storage ~target ~buffer values =
  let count = List.length values in
  let usize_constant number = Lir.Constant (Integer (USize, Z.of_int number)) in
  Lir.Call
    {
      target = Intrinsic Allocate;
      arguments = [ usize_constant (4 * count); usize_constant 4 ];
      result = Returned (at buffer);
    }
  :: List.mapi
       (fun index value ->
         Lir.Assign
           (at ~projections:[ Index (usize_constant index) ] buffer, Use (constant_int32 value)))
       values
  @ [
      Assign
        ( at target,
          Build
            {
              ty = storage int32;
              variant = None;
              fields =
                [
                  ("buffer", copy buffer);
                  ("length", usize_constant count);
                  ("capacity", usize_constant count);
                ];
            } );
    ]

let copy_call glue ty ~destination ~source =
  Lir.Call
    {
      target =
        Direct
          { function_ = Instance (Copy ty); signature = Glue.For_testing.copy_signature glue ty };
      arguments =
        [
          Address { place = at destination; writable = true };
          Address { place = at source; writable = false };
        ];
      result = Discarded;
    }

let () =
  let glue = glue () in
  test "plain data is trivial and storage is not" (fun () ->
      if not (Glue.trivial glue (option int32)) then fail "Option[Int32] is not trivial";
      if Glue.trivial glue (storage int32) then fail "Storage[Int32] is trivial");
  test "a record's drop drops only the fields that own something" (fun () ->
      let extra = [ ("Holder", Record [ field "items" (storage int32); field "count" int32 ]) ] in
      let glue =
        Glue.create (shape_env ~extra ()) ~representation:(representation extra) ~usize ()
      in
      let c =
        Emit_c.For_testing.c
          (Emit_c.fragment (shape_env ~extra ()) (Code (Glue.drop glue (named "Holder"))))
      in
      if not (contains c "f_items") then fail "the drop does not drop the items:\n%s" c;
      if contains c "f_count" then fail "the drop reads the count:\n%s" c);
  test "a copy of storage of plain data is one allocation and one memory copy" (fun () ->
      let c =
        Emit_c.For_testing.c
          (Emit_c.fragment (shape_env ()) (Code (Glue.copy glue (storage int32))))
      in
      let count text =
        let rec from position =
          match String.index_from_opt c position text.[0] with
          | None -> 0
          | Some found ->
              (if
                 found + String.length text <= String.length c
                 && String.sub c found (String.length text) = text
               then 1
               else 0)
              + from (found + 1)
        in
        from 0
      in
      if count "t_runtime_allocate(" <> 1 || count "__builtin_memcpy(" <> 1 then
        fail "the copy does not allocate and copy once:\n%s" c);
  test "a copy of storage keeps its values when the original changes" (fun () ->
      let ty = storage int32 in
      expect_status 20
        [
          printed (Glue.copy glue ty);
          printed (Glue.drop glue ty);
          entry
            [
              local (value ty);
              local (Raw (Pointer (Data int32)));
              local (value ty);
              local (Raw (Pointer (Data int32)));
            ]
            [
              block
                (fill_storage ~target:0 ~buffer:1 [ 10; 20; 30 ]
                @ [
                    copy_call glue ty ~destination:2 ~source:0;
                    Assign
                      ( at ~projections:[ Index (Constant (Integer (USize, Z.one))) ] 1,
                        Use (constant_int32 99) );
                    Assign (at 3, Use (copy ~projections:[ Field "buffer" ] 2));
                    Drop (at 0);
                  ])
                (Return (Some (copy ~projections:[ Index (Constant (Integer (USize, Z.one))) ] 3)));
            ];
        ]);
  test "dropping storage of static bytes frees nothing" (fun () ->
      let ty = storage uint8 in
      expect_status 0
        [
          printed (Glue.drop glue ty);
          entry
            [ local (value ty) ]
            [
              block
                [
                  Assign
                    ( at 0,
                      Build
                        {
                          ty;
                          variant = None;
                          fields =
                            [
                              ("buffer", Constant (Bytes "static"));
                              ("length", Constant (Integer (USize, Z.of_int 6)));
                              ("capacity", Constant (Integer (USize, Z.zero)));
                            ];
                        } );
                  Drop (at 0);
                ]
                (Return (Some (constant_int32 0)));
            ];
        ]);
  test "a copy of storage of storage copies every element and both drop cleanly" (fun () ->
      let inner = storage int32 in
      let outer = storage inner in
      let usize_constant number = Lir.Constant (Integer (USize, Z.of_int number)) in
      expect_status 4
        [
          printed (Glue.copy glue outer);
          printed (Glue.copy glue inner);
          printed (Glue.drop glue outer);
          printed (Glue.drop glue inner);
          entry
            [
              local (value inner);
              local (Raw (Pointer (Data int32)));
              local (value inner);
              local (Raw (Pointer (Data int32)));
              local (Raw (Pointer (Data inner)));
              local (value outer);
              local (value outer);
              local (Raw (Pointer (Data inner)));
              local (Raw (Pointer (Data int32)));
              local (value int32);
            ]
            [
              block
                (fill_storage ~target:0 ~buffer:1 [ 3 ]
                @ fill_storage ~target:2 ~buffer:3 [ 4 ]
                @ [
                    Call
                      {
                        target = Intrinsic Allocate;
                        arguments = [ usize_constant 48; usize_constant 8 ];
                        result = Returned (at 4);
                      };
                    Assign (at ~projections:[ Index (usize_constant 0) ] 4, Use (Move (at 0)));
                    Assign (at ~projections:[ Index (usize_constant 1) ] 4, Use (Move (at 2)));
                    Assign
                      ( at 5,
                        Build
                          {
                            ty = outer;
                            variant = None;
                            fields =
                              [
                                ("buffer", copy 4);
                                ("length", usize_constant 2);
                                ("capacity", usize_constant 2);
                              ];
                          } );
                    copy_call glue outer ~destination:6 ~source:5;
                    Drop (at 5);
                    Assign (at 7, Use (copy ~projections:[ Field "buffer" ] 6));
                    Assign
                      (at 8, Use (copy ~projections:[ Index (usize_constant 1); Field "buffer" ] 7));
                    Assign (at 9, Use (copy ~projections:[ Index (usize_constant 0) ] 8));
                    Drop (at 6);
                  ])
                (Return (Some (copy 9)));
            ];
        ])
