module Intrinsics = Compile.For_testing.Intrinsics

(* The LIR, the C it becomes, and the intrinsic operations. *)

open Memory_layout
open Codegen_support

(* Lowered IR and C *)

(* A file holding the instances, each with its linkage. *)
let c_file env instances =
  Emit_c.file env Development
    (List.map
       (fun (instance, linkage) -> (Emit_c.fragment env (Lir.Code instance), linkage))
       instances)

let () =
  test "a function that returns a constant runs and exits with it" (fun () ->
      expect_status 7 [ entry [] [ block [] (Return (Some (constant_int32 7))) ] ]);
  test "a counted loop over blocks sums its range" (fun () ->
      expect_status 55
        [
          entry
            [ local ~name:"total" (value int32); local ~name:"i" (value int32); local (Raw Bool) ]
            [
              block
                [ Assign (at 0, Use (constant_int32 0)); Assign (at 1, Use (constant_int32 1)) ]
                (Goto 1);
              block
                [ Assign (at 2, Binary (Less_equal, copy 1, constant_int32 10)) ]
                (Switch { value = copy 2; cases = [ (Z.one, 2) ]; default = Some 3 });
              block
                [
                  Assign (at 0, Binary (Add, copy 0, copy 1));
                  Assign (at 1, Binary (Add, copy 1, constant_int32 1));
                ]
                (Goto 1);
              block [] (Return (Some (copy 0)));
            ];
        ]);
  let point = named "Point" in
  let point_shape = ("Point", Record [ field "x" int32; field "y" int32 ]) in
  test "a record is built and its fields read" (fun () ->
      expect_status ~extra:[ point_shape ] 5
        [
          entry
            [ local (value point); local (value int32) ]
            [
              block
                [
                  Assign
                    ( at 0,
                      Build
                        {
                          ty = point;
                          variant = None;
                          fields = [ ("x", constant_int32 2); ("y", constant_int32 3) ];
                        } );
                  Assign
                    ( at 1,
                      Binary
                        (Add, copy ~projections:[ Field "x" ] 0, copy ~projections:[ Field "y" ] 0)
                    );
                ]
                (Return (Some (copy 1)));
            ];
        ]);
  let shape = named "Shape" in
  let shape_shape =
    ( "Shape",
      Sum
        [
          variant "Circle" [ field "radius" int32 ];
          variant "Square" [ field "side" int32; field "corner" int32 ];
          variant "Empty" [];
        ] )
  in
  test "a tagged sum is built and switched on, and its variant's fields read" (fun () ->
      expect_status ~extra:[ shape_shape ] 9
        [
          entry
            [ local (value shape) ]
            [
              block
                [
                  Assign
                    ( at 0,
                      Build
                        {
                          ty = shape;
                          variant = Some "Square";
                          fields = [ ("side", constant_int32 9); ("corner", constant_int32 1) ];
                        } );
                ]
                (Switch_variant
                   { place = at 0; cases = [ ("Circle", 1); ("Square", 2) ]; default = Some 3 });
              block [] (Return (Some (constant_int32 1)));
              block []
                (Return
                   (Some
                      (copy ~projections:[ Variant_field { variant = "Square"; field = "side" } ] 0)));
              block [] (Return (Some (constant_int32 3)));
            ];
        ]);
  (* Returns a [Bool] local as the exit status. *)
  let return_bool locals statements =
    entry
      (locals @ [ local (value int32) ])
      [
        block
          (statements
          @ [
              Lir.Assign
                (at (List.length locals), Convert (copy (List.length locals - 1), Integer Int32));
            ])
          (Return (Some (copy (List.length locals))));
      ]
  in
  test "a niche-encoded None is told apart from Some" (fun () ->
      let maybe = option bool in
      expect_status 1
        [
          return_bool
            [ local (value maybe); local (Raw Bool) ]
            [
              Assign (at 0, Build { ty = maybe; variant = Some "None"; fields = [] });
              Assign (at 1, Is_variant (at 0, "None"));
            ];
        ]);
  test "a niche-encoded Some is not None" (fun () ->
      let maybe = option bool in
      expect_status 0
        [
          return_bool
            [ local (value maybe); local (Raw Bool) ]
            [
              Assign
                ( at 0,
                  Build
                    {
                      ty = maybe;
                      variant = Some "Some";
                      fields = [ ("value", Constant (Bool false)) ];
                    } );
              Assign (at 1, Is_variant (at 0, "None"));
            ];
        ]);
  let tree = named "Tree" in
  let tree_shape =
    ( "Tree",
      Sum
        [
          variant "Leaf" [];
          variant ~indirect:true "Node"
            [ field "left" tree; field "value" int32; field "right" tree ];
        ] )
  in
  test "an indirect variant is built in its block and read through it" (fun () ->
      let leaf = Lir.Build { ty = tree; variant = Some "Leaf"; fields = [] } in
      expect_status ~extra:[ tree_shape ] 42
        [
          entry
            [ local (value tree); local (value tree); local (value tree) ]
            [
              block
                [
                  Assign (at 0, leaf);
                  Assign (at 1, leaf);
                  Assign
                    ( at 2,
                      Build
                        {
                          ty = tree;
                          variant = Some "Node";
                          fields =
                            [
                              ("left", Move (at 0));
                              ("value", constant_int32 42);
                              ("right", Move (at 1));
                            ];
                        } );
                ]
                (Switch_variant { place = at 2; cases = [ ("Node", 1) ]; default = Some 2 });
              block []
                (Return
                   (Some
                      (copy ~projections:[ Variant_field { variant = "Node"; field = "value" } ] 2)));
              block [] (Return (Some (constant_int32 0)));
            ];
        ]);
  let bump =
    instance "bump"
      (function_ ~parameters:[ 0 ]
         [ local ~name:"count" (Pointer { target = value int32; writable = true }) ]
         [
           block
             [
               Assign
                 ( at ~projections:[ Deref ] 0,
                   Binary (Add, copy ~projections:[ Deref ] 0, constant_int32 1) );
             ]
             (Return None);
         ])
  in
  let bump_signature = [ Lir.Pointer { target = value int32; writable = true } ] in
  test "a mut parameter is a pointer the callee writes through" (fun () ->
      expect_status 4
        [
          bump;
          entry
            [ local (value int32) ]
            [
              block
                [
                  Assign (at 0, Use (constant_int32 3));
                  call "bump" ~result:None ~parameters:bump_signature
                    [ Address { place = at 0; writable = true } ]
                    None;
                ]
                (Return (Some (copy 0)));
            ];
        ]);
  test "a mut parameter is a restrict pointer in C" (fun () ->
      let c_file = c_file (shape_env ()) [ (bump, External) ] in
      let expected = "void t_test__bump(int32_t *restrict l0_count)" in
      if not (contains c_file expected) then fail "no %S in:\n%s" expected c_file);
  let callback =
    ({ parameters = [ (Read, int32) ]; result = Returns int32; uses = [] } : Ground.function_type)
  in
  test "a lambda reads a local of its caller through its environment" (fun () ->
      let environment = [ ("offset", Lir.Pointer { target = value int32; writable = false }) ] in
      let lambda =
        function_ ~parameters:[ 0; 1 ] ~result:(value int32) ~environment
          [
            local ~name:"environment" (Raw (Nullable_pointer Opaque));
            local ~name:"argument" (value int32);
            local (Pointer { target = Environment 0; writable = false });
            local (value int32);
          ]
          [
            block
              [
                Assign (at 2, Use (copy 0));
                Assign
                  ( at 3,
                    Binary (Add, copy 1, Copy (at ~projections:[ Deref; Field "offset"; Deref ] 2))
                  );
              ]
              (Return (Some (copy 3)));
          ]
      in
      let signature = Convention.function_value (shape_env ()) callback in
      expect_status 6
        [
          entry ~nested:[ lambda ]
            [
              local ~name:"offset" (value int32);
              local (Environment 0);
              local (value (Function callback));
              local (value int32);
            ]
            [
              block
                [
                  Assign (at 0, Use (constant_int32 5));
                  Assign
                    ( at ~projections:[ Field "offset" ] 1,
                      Use (Address { place = at 0; writable = false }) );
                  Assign
                    ( at 2,
                      Function_value
                        {
                          code = Nested 0;
                          environment = Some (Address { place = at 1; writable = false });
                        } );
                  Call
                    {
                      target = Indirect { value = copy 2; signature };
                      arguments = [ constant_int32 1 ];
                      result = Returned (at 3);
                    };
                ]
                (Return (Some (copy 3)));
            ];
        ]);
  let float64_constant value = Lir.Constant (Float64 (Int64.bits_of_float value)) in
  test "float equality treats every NaN as equal" (fun () ->
      expect_status 1
        [
          return_bool
            [ local (Raw Bool) ]
            [
              Assign (at 0, Binary (Equal, float64_constant Float.nan, float64_constant Float.nan));
            ];
        ]);
  test "IEEE float equality does not" (fun () ->
      expect_status 0
        [
          return_bool
            [ local (Raw Bool) ]
            [
              Assign
                (at 0, Binary (Ieee_equal, float64_constant Float.nan, float64_constant Float.nan));
            ];
        ]);
  test "NaN is ordered after every number" (fun () ->
      expect_status 1
        [
          return_bool
            [ local (Raw Bool) ]
            [
              Assign
                (at 0, Binary (Less, float64_constant Float.infinity, float64_constant Float.nan));
            ];
        ]);
  test "negative zero equals zero" (fun () ->
      expect_status 1
        [
          return_bool
            [ local (Raw Bool) ]
            [ Assign (at 0, Binary (Equal, float64_constant (-0.0), float64_constant 0.0)) ];
        ]);
  test "a shift amount is masked to the width of the value" (fun () ->
      expect_status 2
        [
          entry
            [ local (value int64); local (value int32) ]
            [
              block
                [
                  Assign
                    ( at 0,
                      Binary
                        (Shift_left, constant_int64 1, Lir.Constant (Integer (USize, Z.of_int 65)))
                    );
                  Assign (at 1, Convert (copy 0, Integer Int32));
                ]
                (Return (Some (copy 1)));
            ];
        ]);
  test "an overflowing add reports the overflow" (fun () ->
      expect_status 1
        [
          return_bool
            [ local (value int32); local (Raw Bool) ]
            [
              Call
                {
                  target = Intrinsic Add_overflow;
                  arguments =
                    [
                      Lir.Constant (Integer (Int32, Z.of_string "2147483647"));
                      constant_int32 1;
                      Address { place = at 0; writable = true };
                    ];
                  result = Returned (at 1);
                };
            ];
        ]);
  test "a panic writes its message and position and exits with 101" (fun () ->
      let anchors =
        [ { Positions.definition = definition "entry"; path = "test.truss"; first_line = 10 } ]
      in
      let status, _, errors =
        run_program ~anchors
          [
            entry []
              [
                block []
                  (Fail
                     {
                       failure = Panic;
                       message = Constant (Bytes "boom");
                       length = Constant (Integer (USize, Z.of_int 4));
                       site = { definition = definition "entry"; line = 3; column = 5 };
                     });
              ];
          ]
      in
      expect_int ~expected:101 status;
      expect_string ~expected:"panic: boom\n  at test.truss:13:5\n" errors);
  test "a copy of a callee is a static inline function, declared before its caller" (fun () ->
      let callee =
        instance "callee"
          (function_ ~parameters:[ 0 ] ~result:(value int32)
             [ local (value int32) ]
             [ block [] (Return (Some (copy 0))) ])
      in
      let caller =
        entry
          [ local (value int32) ]
          [
            block
              [ call "callee" ~parameters:[ value int32 ] [ constant_int32 7 ] (Some (at 0)) ]
              (Return (Some (copy 0)));
          ]
      in
      let c_file = c_file (shape_env ()) [ (caller, External); (callee, Internal) ] in
      let copy = "static inline int32_t t_test__callee(int32_t l0) {" in
      if not (contains c_file copy) then fail "no %S in:\n%s" copy c_file;
      if contains c_file "\nint32_t t_test__callee(int32_t);" then
        fail "the callee is also declared as another file's:\n%s" c_file);
  test "the C checks each type's size and alignment against its layout" (fun () ->
      let pair_shape = ("Pair", Record [ field "first" int32; field "second" int64 ]) in
      let holder =
        instance "holder" (function_ [ local (value pair) ] [ block [] (Return None) ])
      in
      let c_file = c_file (shape_env ~extra:[ pair_shape ] ()) [ (holder, External) ] in
      let expected =
        "_Static_assert(sizeof(t_test__Pair) == 16 && _Alignof(t_test__Pair) == 8, \"layout\");"
      in
      if not (contains c_file expected) then fail "no %S in:\n%s" expected c_file);
  test "emitting the same instances twice gives the same C" (fun () ->
      let instances = [ (bump, Emit_c.External) ] in
      expect_string ~expected:(c_file (shape_env ()) instances) (c_file (shape_env ()) instances));
  test "canonical form numbers blocks in reverse postorder and locals by first use" (fun () ->
      let function_ =
        function_ ~result:(value int32)
          [
            local ~name:"unused" (value int32);
            local ~name:"late" (value int32);
            local ~name:"early" (value int32);
          ]
          [
            block [ Assign (at 2, Use (constant_int32 1)) ] (Goto 2);
            block [] (Return (Some (copy 1)));
            block [ Assign (at 1, Use (copy 2)) ] (Goto 1);
          ]
      in
      expect_string
        ~expected:"fn() -> Int32\nb0: _0 = 1; goto b1\nb1: _1 = _0; goto b2\nb2: return _1"
        (Lir.For_testing.function_to_string (Lir.For_testing.canonical function_)));
  ()

let () =
  test "a symbol names the path and the type arguments" (fun () ->
      let key =
        Instance.Code
          {
            path = Method { owner = Well_known.path List; name = "each"; receiver = Read };
            type_arguments = [ Type int64 ];
          }
      in
      expect_string ~expected:"t_standard__list__List_each_Of_test__Int64_End_"
        (Instance.symbol key));
  let function_in package modules =
    Instance.symbol
      (Instance.Code
         { path = Top { module_ = { package; modules }; name = "length" }; type_arguments = [] })
  in
  test "a symbol marks a package's owner apart from its modules" (fun () ->
      expect_string ~expected:"t_acme_Owns_geometry__vector__length"
        (function_in { owner = Some "acme"; name = "geometry" } [ "vector" ]);
      if
        function_in { owner = Some "acme"; name = "geometry" } [ "vector" ]
        = function_in { owner = None; name = "acme" } [ "geometry"; "vector" ]
      then fail "a package with an owner and a module of the same names have one symbol");
  test "a long symbol keeps its start and ends with a hash" (fun () ->
      let long name = Instance.symbol (key (String.make 300 name)) in
      let left = long 'a' and right = long 'b' in
      expect_int ~expected:(180 + 6 + 32) (String.length left);
      if left = right then fail "two long names give one symbol")

(* Intrinsic operations *)

let intrinsic_types : Intrinsics.types = { usize; string_slice = named "StringSlice" }

(* An [entry] built with the builder: [body] writes its statements and
   returns the local to exit with. *)
let built_entry body =
  let builder = Lir_builder.create () in
  Lir_builder.start builder (Lir_builder.block builder);
  let result = body builder in
  Lir_builder.finish builder (Return (Some (Copy (Lir_builder.at result))));
  instance "entry" (Lir_builder.build builder ~parameters:[] ~result:(Some (value int32)))

let operate builder ?destination ?(type_arguments = [ int32 ]) ?value_arguments operation arguments
    =
  Intrinsics.lower ?value_arguments (shape_env ()) builder intrinsic_types operation ~type_arguments
    arguments ~destination
    ~site:{ definition = definition "entry"; line = 0; column = 1 }

let () =
  test "storage with room is pushed onto, and inserts, removes, swaps, and pops in place" (fun () ->
      let open Lir_builder in
      let storage_ty =
        Ground.Named { path = Intrinsic.builtin_path Storage; arguments = [ Type int32 ] }
      in
      expect_status 171
        [
          built_entry (fun builder ->
              let storage = local builder ~name:"storage" (value storage_ty) in
              let popped = local builder (value int32) in
              let sum = local builder (value int32) in
              ignore (operate builder ~destination:(at storage) Storage_empty []);
              ignore (operate builder Storage_set_capacity [ Place (at storage); Value (usize 2) ]);
              ignore (operate builder Storage_set_capacity [ Place (at storage); Value (usize 8) ]);
              List.iter
                (fun count ->
                  ignore
                    (operate builder Storage_push
                       [ Place (at storage); Value (constant_int32 count) ]))
                [ 1; 2; 3; 4; 5 ];
              ignore
                (operate builder Storage_insert
                   [ Place (at storage); Value (usize 0); Value (constant_int32 0) ]);
              ignore
                (operate builder ~destination:(at popped) Storage_remove
                   [ Place (at storage); Value (usize 2) ]);
              ignore
                (operate builder Storage_swap
                   [ Place (at storage); Value (usize 0); Value (usize 4) ]);
              ignore (operate builder ~destination:(at popped) Storage_pop [ Place (at storage) ]);
              let element index weight =
                match operate builder Storage_at [ Place (at storage); Value (usize index) ] with
                | Some place -> Lir.Binary (Multiply, Copy place, constant_int32 weight)
                | None -> failwith "storage_at lends nothing"
              in
              emit builder (Assign (at sum, Use (constant_int32 0)));
              List.iter
                (fun (index, weight) ->
                  let term = local builder (value int32) in
                  emit builder (Assign (at term, element index weight));
                  emit builder (Assign (at sum, Binary (Add, Copy (at sum), Copy (at term)))))
                [ (0, 1); (1, 3); (2, 5); (3, 7) ];
              let length = local builder (value (named "USize")) in
              ignore
                (operate builder ~destination:(at length) Storage_length [ Place (at storage) ]);
              let length32 = local builder (value int32) in
              emit builder (Assign (at length32, Convert (Copy (at length), Integer Int32)));
              emit builder
                (Assign (at length32, Binary (Multiply, Copy (at length32), constant_int32 30)));
              emit builder (Assign (at sum, Binary (Add, Copy (at sum), Copy (at length32))));
              emit builder (Assign (at sum, Binary (Add, Copy (at sum), Copy (at popped))));
              sum);
        ]);
  test "an array's elements are moved into new storage, in order" (fun () ->
      let open Lir_builder in
      let storage_ty =
        Ground.Named { path = Intrinsic.builtin_path Storage; arguments = [ Type int32 ] }
      in
      let array_ty =
        Ground.Named
          { path = Intrinsic.builtin_path Array; arguments = [ Type int32; Value (Z.of_int 3) ] }
      in
      expect_status 165
        [
          built_entry (fun builder ->
              let array = local builder ~name:"array" (value array_ty) in
              List.iteri
                (fun index count ->
                  emit builder (Assign (at array / Index (usize index), Use (constant_int32 count))))
                [ 4; 5; 6 ];
              let storage = local builder ~name:"storage" (value storage_ty) in
              ignore
                (operate builder ~destination:(at storage)
                   ~value_arguments:[ Z.of_int 3 ]
                   Storage_from_array
                   [ Value (Copy (at array)) ]);
              let last = local builder (value int32) and middle = local builder (value int32) in
              ignore (operate builder ~destination:(at last) Storage_pop [ Place (at storage) ]);
              ignore (operate builder ~destination:(at middle) Storage_pop [ Place (at storage) ]);
              let length = local builder (value (named "USize")) in
              ignore
                (operate builder ~destination:(at length) Storage_length [ Place (at storage) ]);
              let status = local builder (value int32) in
              emit builder (Assign (at status, Convert (Copy (at length), Integer Int32)));
              emit builder
                (Assign (at status, Binary (Multiply, Copy (at status), constant_int32 100)));
              emit builder (Assign (at last, Binary (Multiply, Copy (at last), constant_int32 10)));
              emit builder (Assign (at status, Binary (Add, Copy (at status), Copy (at last))));
              emit builder (Assign (at status, Binary (Add, Copy (at status), Copy (at middle))));
              status);
        ]);
  test "a view of an array has the array's elements" (fun () ->
      let open Lir_builder in
      let array_ty =
        Ground.Named
          { path = Intrinsic.builtin_path Array; arguments = [ Type int32; Value (Z.of_int 3) ] }
      in
      let view_ty =
        Ground.Named { path = Intrinsic.builtin_path View; arguments = [ Type int32 ] }
      in
      let extra = [ (Ground.to_string view_ty, Storage.view_shape ~usize:(named "USize") int32) ] in
      let operate builder ?destination operation arguments =
        Intrinsics.lower
          ~value_arguments:[ Z.of_int 3 ]
          (shape_env ~extra ()) builder intrinsic_types operation ~type_arguments:[ int32 ]
          arguments ~destination
          ~site:{ definition = definition "entry"; line = 0; column = 1 }
      in
      expect_status ~extra 53
        [
          built_entry (fun builder ->
              let array = local builder ~name:"array" (value array_ty) in
              List.iteri
                (fun index count ->
                  emit builder (Assign (at array / Index (usize index), Use (constant_int32 count))))
                [ 4; 5; 6 ];
              let view = local builder ~name:"view" (value view_ty) in
              ignore (operate builder ~destination:(at view) Array_view [ Place (at array) ]);
              let middle =
                match operate builder View_at [ Place (at view); Value (usize 1) ] with
                | Some place -> place
                | None -> failwith "view_at lends nothing"
              in
              let length = local builder (value (named "USize")) in
              ignore (operate builder ~destination:(at length) View_length [ Place (at view) ]);
              let status = local builder (value int32) in
              emit builder (Assign (at status, Convert (Copy (at length), Integer Int32)));
              emit builder (Assign (at status, Binary (Add, Copy (at status), constant_int32 50)));
              let weighted = local builder (value int32) in
              emit builder (Assign (at weighted, Binary (Subtract, Copy middle, constant_int32 5)));
              emit builder (Assign (at status, Binary (Add, Copy (at status), Copy (at weighted))));
              status);
        ]);
  test "an array made of a storage has its elements, and the storage's buffer is freed" (fun () ->
      let open Lir_builder in
      let storage_ty = Storage.of_elements int32 in
      let array_ty =
        Ground.Named
          { path = Intrinsic.builtin_path Array; arguments = [ Type int32; Value (Z.of_int 3) ] }
      in
      let operate builder ?destination operation arguments =
        Intrinsics.lower ~checks:true
          ~value_arguments:[ Z.of_int 3 ]
          (shape_env ()) builder intrinsic_types operation ~type_arguments:[ int32 ] arguments
          ~destination
          ~site:{ definition = definition "entry"; line = 0; column = 1 }
      in
      let anchors =
        [ { Positions.definition = definition "entry"; path = "test.truss"; first_line = 1 } ]
      in
      let program_with pushed =
        [
          built_entry (fun builder ->
              let storage = local builder (value storage_ty) in
              ignore
                (operate builder ~destination:(at storage) Storage_with_capacity
                   [ Value (usize 3) ]);
              List.iter
                (fun count ->
                  ignore
                    (operate builder Storage_push
                       [ Place (at storage); Value (constant_int32 count) ]))
                pushed;
              let array = local builder ~name:"array" (value array_ty) in
              ignore
                (operate builder ~destination:(at array) Array_from_storage [ Place (at storage) ]);
              let status = local builder (value int32) in
              emit builder (Assign (at status, Use (Copy (at array / Index (usize 0)))));
              emit builder
                (Assign
                   (at status, Binary (Add, Copy (at status), Copy (at array / Index (usize 2)))));
              status);
        ]
      in
      expect_status ~anchors 46 (program_with [ 40; 5; 6 ]);
      (* A storage of another length stops a checked build. *)
      expect_status ~anchors 101 (program_with [ 40; 5 ]));
  test "a float fits an integer type where the whole number it is cut down to does" (fun () ->
      let open Lir_builder in
      (* Each case is a bit of the status, set where the answer is the one
         expected. *)
      let all_right cases =
        expect_status
          ((1 lsl List.length cases) - 1)
          [
            built_entry (fun builder ->
                let status = local builder (value int32) in
                emit builder (Assign (at status, Use (constant_int32 0)));
                List.iteri
                  (fun index (float, target, expected) ->
                    let fits = local builder (Raw Bool) in
                    ignore
                      (operate builder ~destination:(at fits) ~type_arguments:[ float64; target ]
                         Fits
                         [ Value (Constant (Float64 (Int64.bits_of_float float))) ]);
                    let right = local builder (Raw Bool) in
                    emit builder
                      (Assign (at right, Binary (Equal, Copy (at fits), Constant (Bool expected))));
                    let bit = local builder (value int32) in
                    emit builder (Assign (at bit, Convert (Copy (at right), Integer Int32)));
                    emit builder
                      (Assign (at bit, Binary (Shift_left, Copy (at bit), constant_int32 index)));
                    emit builder
                      (Assign (at status, Binary (Bit_or, Copy (at status), Copy (at bit)))))
                  cases;
                status);
          ]
      in
      all_right
        [
          (9223372036854774784., int64, true);
          (9223372036854775808., int64, false);
          (-9223372036854775808., int64, true);
          (-9223372036854777856., int64, false);
          (Float.nan, int64, false);
          (Float.infinity, int64, false);
          (Float.neg_infinity, int64, false);
        ];
      all_right
        [
          (255.9, uint8, true);
          (256., uint8, false);
          (-0.5, uint8, true);
          (-1., uint8, false);
          (0., uint8, true);
        ]);
  test "a storage is shortened in place, keeping its room, and a static one stays static" (fun () ->
      let open Lir_builder in
      let storage_ty = named "Storage" ~arguments:[ Type uint8 ] in
      let anchors =
        [ { Positions.definition = definition "entry"; path = "test.truss"; first_line = 1 } ]
      in
      let checked builder ?destination operation arguments =
        Intrinsics.lower ~checks:true (shape_env ()) builder intrinsic_types operation
          ~type_arguments:[ uint8 ] arguments ~destination
          ~site:{ definition = definition "entry"; line = 0; column = 1 }
      in
      let shortened ~capacity ~to_ =
        [
          built_entry (fun builder ->
              let storage = local builder (value storage_ty) in
              emit builder
                (Assign
                   ( at storage,
                     Build
                       {
                         ty = storage_ty;
                         variant = None;
                         fields =
                           [
                             ("buffer", Constant (Bytes "abcde"));
                             ("length", usize 5);
                             ("capacity", usize 0);
                           ];
                       } ));
              if capacity > 0 then
                ignore
                  (checked builder Storage_set_capacity
                     [ Place (at storage); Value (usize capacity) ]);
              ignore (checked builder Storage_shorten [ Place (at storage); Value (usize to_) ]);
              (* The length, the capacity, and the last element kept. *)
              let status = local builder (value int32) in
              let part place =
                let read = local builder (value int32) in
                emit builder (Assign (at read, Convert (Copy place, Integer Int32)));
                emit builder (Assign (at status, Binary (Add, Copy (at status), Copy (at read))))
              in
              emit builder (Assign (at status, Use (constant_int32 0)));
              part (at storage / Field "length");
              part (at storage / Field "capacity");
              part (at storage / Field "buffer" / Index (usize (to_ - 1)));
              status);
        ]
      in
      expect_status ~anchors (2 + 8 + Char.code 'b') (shortened ~capacity:8 ~to_:2);
      expect_status ~anchors (3 + 0 + Char.code 'c') (shortened ~capacity:0 ~to_:3);
      (* More than its length stops a checked build. *)
      expect_status ~anchors 101 (shortened ~capacity:8 ~to_:6);
      (* Elements that own something cannot be forgotten. *)
      match (Intrinsic_signatures.signature Storage_shorten).generics with
      | [ { kind = Type_generic [ { trait = Top { name = "Plain"; _ }; _ } ]; _ } ] -> ()
      | _ -> fail "storage_shorten takes elements that are not known to be Plain");
  test "a checked build stops a storage or view operation whose precondition does not hold"
    (fun () ->
      let open Lir_builder in
      let storage_ty = named "Storage" ~arguments:[ Type uint8 ] in
      let view_ty =
        Ground.Named { path = Intrinsic.builtin_path View; arguments = [ Type uint8 ] }
      in
      let extra = [ (Ground.to_string view_ty, Storage.view_shape ~usize:(named "USize") uint8) ] in
      let anchors =
        [ { Positions.definition = definition "entry"; path = "test.truss"; first_line = 1 } ]
      in
      let checked builder ?destination operation arguments =
        ignore
          (Intrinsics.lower ~checks:true (shape_env ~extra ()) builder intrinsic_types operation
             ~type_arguments:[ uint8 ] arguments ~destination
             ~site:{ definition = definition "entry"; line = 0; column = 1 })
      in
      let byte : Lir.operand = Constant (Integer (UInt8, Z.of_int 1)) in
      (* [operation] is given a storage of three elements with room for no
         more, and a view of them. *)
      let stops saying operation =
        let status, _, errors =
          run_program ~extra ~anchors
            [
              built_entry (fun builder ->
                  let storage = local builder (value storage_ty) in
                  emit builder
                    (Assign
                       ( at storage,
                         Build
                           {
                             ty = storage_ty;
                             variant = None;
                             fields =
                               [
                                 ("buffer", Constant (Bytes "abc"));
                                 ("length", usize 3);
                                 ("capacity", usize 0);
                               ];
                           } ));
                  checked builder Storage_set_capacity [ Place (at storage); Value (usize 3) ];
                  let view = local builder ~name:"view" (value view_ty) in
                  checked builder ~destination:(at view) Storage_view [ Place (at storage) ];
                  operation builder ~storage ~view;
                  let status = local builder (value int32) in
                  emit builder (Assign (at status, Use (constant_int32 0)));
                  status);
            ]
        in
        if status <> 101 || not (contains errors saying) then
          fail "expected a panic saying %S, got status %d (%s)" saying status errors
      in
      let index = "index out of bounds" and slice = "slice out of bounds" in
      stops "an element pushed to a storage that has no room" (fun builder ~storage ~view:_ ->
          checked builder Storage_push [ Place (at storage); Value byte ]);
      stops "an element inserted into a storage that has no room" (fun builder ~storage ~view:_ ->
          checked builder Storage_insert [ Place (at storage); Value (usize 1); Value byte ]);
      stops index (fun builder ~storage ~view:_ ->
          checked builder Storage_insert [ Place (at storage); Value (usize 9); Value byte ]);
      stops "a storage lengthened to more than its capacity" (fun builder ~storage ~view:_ ->
          checked builder Storage_lengthen [ Place (at storage); Value (usize 1) ]);
      stops "a storage's capacity set to less than its length" (fun builder ~storage ~view:_ ->
          checked builder Storage_set_capacity [ Place (at storage); Value (usize 2) ]);
      stops index (fun builder ~storage ~view:_ ->
          let removed = local builder (value uint8) in
          checked builder ~destination:(at removed) Storage_remove
            [ Place (at storage); Value (usize 3) ]);
      stops index (fun builder ~storage ~view:_ ->
          checked builder Storage_swap [ Place (at storage); Value (usize 0); Value (usize 3) ]);
      stops index (fun builder ~storage ~view:_ ->
          checked builder Storage_at [ Place (at storage); Value (usize 3) ]);
      stops index (fun builder ~storage:_ ~view ->
          checked builder View_at [ Place (at view); Value (usize 3) ]);
      stops index (fun builder ~storage:_ ~view ->
          checked builder View_swap [ Place (at view); Value (usize 3); Value (usize 0) ]);
      stops slice (fun builder ~storage:_ ~view ->
          let part = local builder (value view_ty) in
          checked builder ~destination:(at part) View_slice
            [ Place (at view); Value (usize 1); Value (usize 4) ]);
      stops slice (fun builder ~storage:_ ~view ->
          let part = local builder (value view_ty) in
          checked builder ~destination:(at part) View_slice
            [ Place (at view); Value (usize 2); Value (usize 1) ]);
      stops "an element popped from an empty storage" (fun builder ~storage ~view:_ ->
          checked builder Storage_shorten [ Place (at storage); Value (usize 0) ];
          let popped = local builder (value uint8) in
          checked builder ~destination:(at popped) Storage_pop [ Place (at storage) ]));
  test "static storage given room is copied to the heap, where it can be pushed onto" (fun () ->
      let open Lir_builder in
      let storage_ty = named "Storage" ~arguments:[ Type uint8 ] in
      expect_status 197
        [
          built_entry (fun builder ->
              let storage = local builder (value storage_ty) in
              emit builder
                (Assign
                   ( at storage,
                     Build
                       {
                         ty = storage_ty;
                         variant = None;
                         fields =
                           [
                             ("buffer", Constant (Bytes "abc"));
                             ("length", usize 3);
                             ("capacity", usize 0);
                           ];
                       } ));
              ignore
                (operate builder ~type_arguments:[ uint8 ] Storage_set_capacity
                   [ Place (at storage); Value (usize 4) ]);
              ignore
                (operate builder ~type_arguments:[ uint8 ] Storage_push
                   [ Place (at storage); Value (Constant (Integer (UInt8, Z.of_int 100))) ]);
              let first = local builder (value int32) and last = local builder (value int32) in
              let element index = at storage / Field "buffer" / Index (usize index) in
              emit builder (Assign (at first, Convert (Copy (element 0), Integer Int32)));
              emit builder (Assign (at last, Convert (Copy (element 3), Integer Int32)));
              emit builder (Assign (at first, Binary (Add, Copy (at first), Copy (at last))));
              first);
        ]);
  test "elements are changed through a view of storage, which is first given its own buffer"
    (fun () ->
      let open Lir_builder in
      let storage_ty = named "Storage" ~arguments:[ Type uint8 ] in
      let view_ty =
        Ground.Named { path = Intrinsic.builtin_path View; arguments = [ Type uint8 ] }
      in
      let extra = [ (Ground.to_string view_ty, Storage.view_shape ~usize:(named "USize") uint8) ] in
      let operate builder ?destination operation arguments =
        Intrinsics.lower (shape_env ~extra ()) builder intrinsic_types operation
          ~type_arguments:[ uint8 ] arguments ~destination
          ~site:{ definition = definition "entry"; line = 0; column = 1 }
      in
      expect_status ~extra 105
        [
          built_entry (fun builder ->
              let storage = local builder (value storage_ty) in
              emit builder
                (Assign
                   ( at storage,
                     Build
                       {
                         ty = storage_ty;
                         variant = None;
                         fields =
                           [
                             ("buffer", Constant (Bytes "abc"));
                             ("length", usize 3);
                             ("capacity", usize 0);
                           ];
                       } ));
              let view = local builder ~name:"view" (value view_ty) in
              ignore
                (operate builder ~destination:(at view) Storage_view_mut [ Place (at storage) ]);
              ignore
                (operate builder View_swap [ Place (at view); Value (usize 0); Value (usize 2) ]);
              (match operate builder View_at_mut [ Place (at view); Value (usize 1) ] with
              | Some middle ->
                  emit builder (Assign (middle, Use (Constant (Integer (UInt8, Z.of_int 100)))))
              | None -> failwith "view_at_mut lends nothing");
              let element index : Lir.operand =
                let read = local builder (value int32) in
                emit builder
                  (Assign
                     ( at read,
                       Convert
                         (Copy (at storage / Field "buffer" / Index (usize index)), Integer Int32)
                     ));
                Copy (at read)
              in
              let status = local builder (value int32) in
              emit builder
                (Assign (at status, Convert (Copy (at storage / Field "capacity"), Integer Int32)));
              emit builder (Assign (at status, Binary (Add, Copy (at status), element 0)));
              emit builder (Assign (at status, Binary (Add, Copy (at status), element 1)));
              emit builder (Assign (at status, Binary (Subtract, Copy (at status), element 2)));
              status);
        ])

let () =
  let open Lir_builder in
  let storage_ty = named "Storage" ~arguments:[ Type uint8 ] in
  let view_ty = Ground.Named { path = Intrinsic.builtin_path View; arguments = [ Type uint8 ] } in
  let extra = [ (Ground.to_string view_ty, Storage.view_shape ~usize:(named "USize") uint8) ] in
  let operate builder ?destination operation arguments =
    Intrinsics.lower ~checks:true (shape_env ~extra ()) builder intrinsic_types operation
      ~type_arguments:[ uint8 ] arguments ~destination
      ~site:{ definition = definition "entry"; line = 0; column = 1 }
  in
  (* Takes back, into storage of "abc", a view that [view_of] makes. *)
  let taking_back view_of =
    [
      built_entry (fun builder ->
          let storage = local builder (value storage_ty) in
          emit builder
            (Assign
               ( at storage,
                 Build
                   {
                     ty = storage_ty;
                     variant = None;
                     fields =
                       [
                         ("buffer", Constant (Bytes "abc"));
                         ("length", usize 3);
                         ("capacity", usize 0);
                       ];
                   } ));
          let view = local builder ~name:"view" (value view_ty) in
          view_of builder storage view;
          ignore
            (operate builder Storage_take_view
               [ Place (at storage); Place (at view); Value (usize 1) ]);
          let status = local builder (value int32) in
          emit builder (Assign (at status, Use (constant_int32 7)));
          status);
    ]
  in
  let slice_from builder whole view start stop =
    ignore
      (operate builder ~destination:(at view) View_slice
         [ Place (at whole); Value (usize start); Value (usize stop) ])
  in
  let anchors =
    [ { Positions.definition = definition "entry"; path = "test.truss"; first_line = 1 } ]
  in
  test "a checked build lets storage take back a view of its own elements" (fun () ->
      expect_status ~extra ~anchors 7
        (taking_back (fun builder storage view ->
             let whole = local builder ~name:"whole" (value view_ty) in
             ignore
               (operate builder ~destination:(at whole) Storage_view_mut [ Place (at storage) ]);
             slice_from builder whole view 1 3)));
  test "a checked build stops where storage takes back a view of other elements" (fun () ->
      let other builder storage view start stop =
        ignore storage;
        let whole = local builder ~name:"whole" (value view_ty) in
        emit builder
          (Assign
             (at whole, Storage.view view_ty ~elements:(Constant (Bytes "wxyz")) ~length:(usize 4)));
        slice_from builder whole view start stop
      in
      expect_status ~extra ~anchors 101
        (taking_back (fun builder storage view -> other builder storage view 1 3));
      expect_status ~extra ~anchors 101
        (taking_back (fun builder storage view -> other builder storage view 0 4)))

let () =
  test "a small read-only value is passed by value unless it holds an array's elements" (fun () ->
      let array_of count : Ground.ty =
        Named
          {
            path = Intrinsic.builtin_path Array;
            arguments = [ Type int32; Value (Z.of_int count) ];
          }
      in
      let pair = named "Pair" in
      let extra = [ ("Pair", Memory_layout.Record [ field "cells" (array_of 2) ]) ] in
      let env = shape_env ~extra () in
      let by_value ty =
        match Convention.parameter env Read ty with
        | Some (Value _) -> true
        | Some _ -> false
        | None ->
            fail "a parameter with a size is not passed";
            false
      in
      if not (by_value int64) then fail "a number is passed by address";
      if by_value (array_of 4) then fail "a small array is passed by value";
      if by_value pair then fail "a small record that holds an array is passed by value";
      match Convention.parameter env Own (array_of 4) with
      | Some (Value _) -> ()
      | _ -> fail "a small array that is given away is passed by address")
