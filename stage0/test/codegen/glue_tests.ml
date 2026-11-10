(* The functions generated for each type, and debug output. *)

open Memory_layout
open Codegen_support

(* Generated functions for each type *)

let storage element = named "Storage" ~arguments:[ Type element ]

let kind_of extra (ty : Ground.ty) : Glue.kind =
  match ty with
  | Named { path = Top { name = "Storage"; _ }; arguments = [ Type element ] } -> Storage element
  | _ -> Shape (shapes extra ty)

let glue ?(extra = []) () = Glue.create (shape_env ~extra ()) ~kind_of:(kind_of extra) ~usize ()

(* Statements that allocate a storage of [Int32]s holding [values] into
   local [target], using local [buffer]. *)
let fill_storage ~target ~buffer values =
  let count = List.length values in
  let usize_constant n = Lir.Constant (Integer (USize, Z.of_int n)) in
  Lir.Call
    {
      target = Intrinsic Allocate;
      arguments = [ usize_constant (4 * count); usize_constant 4 ];
      result = Returned (at buffer);
    }
  :: List.mapi
       (fun i v ->
         Lir.Assign (at ~projections:[ Index (usize_constant i) ] buffer, Use (constant_int32 v)))
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
      target = Direct { function_ = Instance (Copy ty); signature = Glue.copy_signature glue ty };
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
      let glue = Glue.create (shape_env ~extra ()) ~kind_of:(kind_of extra) ~usize () in
      expect_string ~expected:"fn(_0: *mut Holder)\nb0: drop *_0.items; return"
        (Lir.function_to_string (Lir.canonical (Glue.drop glue (named "Holder")).main)));
  test "a copy of storage of plain data is one allocation and one memory copy" (fun () ->
      let calls =
        Array.to_list (Lir.canonical (Glue.copy glue (storage int32)).main).blocks
        |> List.concat_map (fun (b : Lir.basic_block) -> b.statements)
        |> List.filter_map (function Lir.Call { target = Intrinsic i; _ } -> Some i | _ -> None)
      in
      if calls <> [ Allocate; Copy_bytes ] then fail "the copy makes other calls");
  test "a copy of storage keeps its values when the original changes" (fun () ->
      let ty = storage int32 in
      expect_status 20
        [
          Glue.copy glue ty;
          Glue.drop glue ty;
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
          Glue.drop glue ty;
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
      let usize_constant n = Lir.Constant (Integer (USize, Z.of_int n)) in
      expect_status 4
        [
          Glue.copy glue outer;
          Glue.copy glue inner;
          Glue.drop glue outer;
          Glue.drop glue inner;
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

(* Debug output *)

let () =
  test "values echo as Truss writes them" (fun () ->
      let open Lir_builder in
      let env = Memory_layout.create target_64 ~shape_of:(Monomorphic.shape standard_context) in
      let glue =
        Glue.create env
          ~kind_of:(Monomorphic.kind standard_context)
          ~usize:(Monomorphic.builtin USize) ~debug_form:Monomorphic.debug_form ()
      in
      let int64 = Monomorphic.builtin Int64
      and bool = Monomorphic.builtin Bool
      and float64 = Monomorphic.builtin Float64 in
      let option value = standard "option" "Option" ~arguments:[ Type value ] () in
      let list = standard "list" "List" ~arguments:[ Type int64 ] () in
      let string = standard "text" "String" () in
      let storage element =
        Ground.Named { path = Intrinsic.builtin_path Storage; arguments = [ Type element ] }
      in
      let intrinsic_types : Intrinsics.types =
        { usize = Monomorphic.builtin USize; string_slice = standard "text" "StringSlice" () }
      in
      let site : Lir.site = { definition = definition "entry"; line = 0; column = 1 } in
      let echo b ty place =
        emit b (Call { target = Intrinsic Debug_begin; arguments = []; result = Discarded });
        emit b
          (Call
             {
               target =
                 Direct
                   { function_ = Instance (Debug ty); signature = Glue.debug_signature glue ty };
               arguments = [ Address { place; writable = false } ];
               result = Discarded;
             });
        let bytes = local b (Raw (Pointer Opaque))
        and length = local b (Value (Monomorphic.builtin USize)) in
        emit b
          (Call { target = Intrinsic Debug_bytes; arguments = []; result = Returned (at bytes) });
        emit b
          (Call { target = Intrinsic Debug_length; arguments = []; result = Returned (at length) });
        emit b (Echo { text = Copy (at bytes); length = Copy (at length); site })
      in
      let main =
        let b = Lir_builder.create () in
        start b (block b);
        let maybe = local b (value (option bool)) in
        emit b
          (Assign
             ( at maybe,
               Build
                 {
                   ty = option bool;
                   variant = Some "Some";
                   fields = [ ("value", Constant (Bool true)) ];
                 } ));
        echo b (option bool) (at maybe);
        let real = local b (value (option float64)) in
        emit b
          (Assign
             ( at real,
               Build
                 {
                   ty = option float64;
                   variant = Some "Some";
                   fields = [ ("value", Constant (Float64 (Int64.bits_of_float 1.5))) ];
                 } ));
        echo b (option float64) (at real);
        let items = local b (value list) in
        ignore
          (Intrinsics.lower env b intrinsic_types Storage_empty ~type_arguments:[ int64 ] []
             ~destination:(Some (at items / Field "storage"))
             ~site);
        List.iter
          (fun n ->
            ignore
              (Intrinsics.lower env b intrinsic_types Storage_push ~type_arguments:[ int64 ]
                 [ Place (at items / Field "storage"); Value (constant_int64 n) ]
                 ~destination:None ~site))
          [ 1; 2; 3 ];
        echo b list (at items);
        let text = local b (value string) in
        emit b
          (Assign
             ( at text / Field "storage",
               Build
                 {
                   ty = storage (Monomorphic.builtin UInt8);
                   variant = None;
                   fields =
                     [
                       ("buffer", Constant (Bytes "hi\n"));
                       ("length", usize 3);
                       ("capacity", usize 0);
                     ];
                 } ));
        echo b string (at text);
        let status = local b (value (Monomorphic.builtin Int32)) in
        emit b (Assign (at status, Use (constant_int32 0)));
        finish b (Return (Some (Copy (at status))));
        instance "entry" (build b ~parameters:[] ~result:(Some (value (Monomorphic.builtin Int32))))
      in
      let tys = [ option bool; bool; option float64; float64; list; int64; string ] in
      let program =
        (main :: List.map (Glue.debug glue) tys) @ [ Glue.debug glue (storage int64) ]
      in
      incr counter;
      let output = Filename.concat (Lazy.force scratch) (Printf.sprintf "debug%d" !counter) in
      let sources =
        [
          ("main", Startup.main_calling (Instance.symbol (key "entry")));
          ( "anchors",
            Positions.anchors_file target_64
              [ { definition = definition "entry"; path = "echo.truss"; first_line = 1 } ] );
        ]
      in
      match
        Build.program (Lazy.force compiler) (Lazy.force cache) env settings
          ~files:[ List.map (fun i -> Lir.Code i) program ]
          ~sources ~output
      with
      | Error message -> fail "%s" message
      | Ok () ->
          let status, _, errors = Toolchain.run output [] in
          expect_int ~expected:0 status;
          expect_string
            ~expected:
              "echo echo.truss:1:1: Some(true)\n\
               echo echo.truss:1:1: Some(1.5)\n\
               echo echo.truss:1:1: [1, 2, 3]\n\
               echo echo.truss:1:1: \"hi\\n\"\n"
            errors)

let () = Harness.finish ()
