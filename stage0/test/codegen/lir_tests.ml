(* The LIR, the C it becomes, and the intrinsic operations. *)

open Memory_layout
open Codegen_support

(* Lowered IR and C *)

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
      let c = Emit_c.file (shape_env ()) Development [ (bump, External) ] in
      let expected = "void t_test__bump(int32_t *restrict l0_count)" in
      if not (contains c expected) then fail "no %S in:\n%s" expected c);
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
  let float64_constant x = Lir.Constant (Float64 (Int64.bits_of_float x)) in
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
      let c = Emit_c.file (shape_env ()) Development [ (caller, External); (callee, Internal) ] in
      let copy = "static inline int32_t t_test__callee(int32_t l0) {" in
      if not (contains c copy) then fail "no %S in:\n%s" copy c;
      if contains c "\nint32_t t_test__callee(int32_t);" then
        fail "the callee is also declared as another file's:\n%s" c);
  test "the C checks each type's size and alignment against its layout" (fun () ->
      let pair_shape = ("Pair", Record [ field "first" int32; field "second" int64 ]) in
      let holder =
        instance "holder" (function_ [ local (value pair) ] [ block [] (Return None) ])
      in
      let c = Emit_c.file (shape_env ~extra:[ pair_shape ] ()) Development [ (holder, External) ] in
      let expected =
        "_Static_assert(sizeof(t_test__Pair) == 16 && _Alignof(t_test__Pair) == 8, \"layout\");"
      in
      if not (contains c expected) then fail "no %S in:\n%s" expected c);
  test "emitting the same instances twice gives the same C" (fun () ->
      let instances = [ (bump, Emit_c.External) ] in
      expect_string
        ~expected:(Emit_c.file (shape_env ()) Development instances)
        (Emit_c.file (shape_env ()) Development instances));
  test "canonical form numbers blocks in reverse postorder and locals by first use" (fun () ->
      let f =
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
        (Lir.function_to_string (Lir.canonical f)));
  ()

let () =
  let numbered first second =
    function_ ~result:(value int32)
      [ local (value int32); local (value int32) ]
      [
        block
          [ Assign (at first, Use (constant_int32 1)); Assign (at second, Use (copy first)) ]
          (Return (Some (copy second)));
      ]
  in
  test "two lowerings that differ only in numbering hash the same" (fun () ->
      let hash f = Lir.hash (instance "f" f) in
      let a = numbered 0 1 and b = numbered 1 0 in
      if hash a <> hash b then fail "the hashes differ");
  test "a change to what an instance does changes its hash" (fun () ->
      let changed =
        function_ ~result:(value int32)
          [ local (value int32) ]
          [ block [ Assign (at 0, Use (constant_int32 2)) ] (Return (Some (copy 0))) ]
      in
      if Lir.hash (instance "f" (numbered 0 1)) = Lir.hash (instance "f" changed) then
        fail "the hashes are equal");
  test "a symbol names the path and the type arguments" (fun () ->
      let key =
        Instance.Code
          {
            path =
              Method
                {
                  owner =
                    Top { module_ = { package = "standard"; modules = [ "list" ] }; name = "List" };
                  name = "each";
                  receiver = Read;
                };
            type_arguments = [ Type int64 ];
          }
      in
      expect_string ~expected:"t_standard__list__List_each_Of_test__Int64_End_"
        (Instance.symbol key));
  test "a symbol writes a package's owner and name as parts of the module path" (fun () ->
      expect_string ~expected:"t_acme__geometry__vector__length"
        (Instance.symbol
           (Instance.Code
              {
                path =
                  Top
                    {
                      module_ = { package = "acme::geometry"; modules = [ "vector" ] };
                      name = "length";
                    };
                type_arguments = [];
              })));
  test "a long symbol keeps its start and ends with a hash" (fun () ->
      let long name = Instance.symbol (key (String.make 300 name)) in
      let a = long 'a' and b = long 'b' in
      expect_int ~expected:(180 + 6 + 32) (String.length a);
      if a = b then fail "two long names give one symbol")

(* Intrinsic operations *)

let intrinsic_types : Intrinsics.types = { usize; string_slice = named "StringSlice" }

(* An [entry] built with the builder: [body] writes its statements and
   returns the local to exit with. *)
let built_entry body =
  let b = Lir_builder.create () in
  Lir_builder.start b (Lir_builder.block b);
  let result = body b in
  Lir_builder.finish b (Return (Some (Copy (Lir_builder.at result))));
  instance "entry" (Lir_builder.build b ~parameters:[] ~result:(Some (value int32)))

let operate b ?destination ?(type_arguments = [ int32 ]) ?value_arguments operation arguments =
  Intrinsics.lower ?value_arguments (shape_env ()) b intrinsic_types operation ~type_arguments
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
          built_entry (fun b ->
              let storage = local b ~name:"storage" (value storage_ty) in
              let popped = local b (value int32) in
              let sum = local b (value int32) in
              ignore (operate b ~destination:(at storage) Storage_empty []);
              ignore (operate b Storage_set_capacity [ Place (at storage); Value (usize 2) ]);
              ignore (operate b Storage_set_capacity [ Place (at storage); Value (usize 8) ]);
              List.iter
                (fun n ->
                  ignore (operate b Storage_push [ Place (at storage); Value (constant_int32 n) ]))
                [ 1; 2; 3; 4; 5 ];
              ignore
                (operate b Storage_insert
                   [ Place (at storage); Value (usize 0); Value (constant_int32 0) ]);
              ignore
                (operate b ~destination:(at popped) Storage_remove
                   [ Place (at storage); Value (usize 2) ]);
              ignore
                (operate b Storage_swap [ Place (at storage); Value (usize 0); Value (usize 4) ]);
              ignore (operate b ~destination:(at popped) Storage_pop [ Place (at storage) ]);
              let element i weight =
                match operate b Storage_at [ Place (at storage); Value (usize i) ] with
                | Some place -> Lir.Binary (Multiply, Copy place, constant_int32 weight)
                | None -> failwith "storage_at lends nothing"
              in
              emit b (Assign (at sum, Use (constant_int32 0)));
              List.iter
                (fun (i, weight) ->
                  let term = local b (value int32) in
                  emit b (Assign (at term, element i weight));
                  emit b (Assign (at sum, Binary (Add, Copy (at sum), Copy (at term)))))
                [ (0, 1); (1, 3); (2, 5); (3, 7) ];
              let length = local b (value (named "USize")) in
              ignore (operate b ~destination:(at length) Storage_length [ Place (at storage) ]);
              let length32 = local b (value int32) in
              emit b (Assign (at length32, Convert (Copy (at length), Integer Int32)));
              emit b
                (Assign (at length32, Binary (Multiply, Copy (at length32), constant_int32 30)));
              emit b (Assign (at sum, Binary (Add, Copy (at sum), Copy (at length32))));
              emit b (Assign (at sum, Binary (Add, Copy (at sum), Copy (at popped))));
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
          built_entry (fun b ->
              let array = local b ~name:"array" (value array_ty) in
              List.iteri
                (fun index n ->
                  emit b (Assign (at array / Index (usize index), Use (constant_int32 n))))
                [ 4; 5; 6 ];
              let storage = local b ~name:"storage" (value storage_ty) in
              ignore
                (operate b ~destination:(at storage)
                   ~value_arguments:[ Z.of_int 3 ]
                   Storage_from_array
                   [ Value (Copy (at array)) ]);
              let last = local b (value int32) and middle = local b (value int32) in
              ignore (operate b ~destination:(at last) Storage_pop [ Place (at storage) ]);
              ignore (operate b ~destination:(at middle) Storage_pop [ Place (at storage) ]);
              let length = local b (value (named "USize")) in
              ignore (operate b ~destination:(at length) Storage_length [ Place (at storage) ]);
              let status = local b (value int32) in
              emit b (Assign (at status, Convert (Copy (at length), Integer Int32)));
              emit b (Assign (at status, Binary (Multiply, Copy (at status), constant_int32 100)));
              emit b (Assign (at last, Binary (Multiply, Copy (at last), constant_int32 10)));
              emit b (Assign (at status, Binary (Add, Copy (at status), Copy (at last))));
              emit b (Assign (at status, Binary (Add, Copy (at status), Copy (at middle))));
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
      let operate b ?destination operation arguments =
        Intrinsics.lower
          ~value_arguments:[ Z.of_int 3 ]
          (shape_env ~extra ()) b intrinsic_types operation ~type_arguments:[ int32 ] arguments
          ~destination
          ~site:{ definition = definition "entry"; line = 0; column = 1 }
      in
      expect_status ~extra 53
        [
          built_entry (fun b ->
              let array = local b ~name:"array" (value array_ty) in
              List.iteri
                (fun index n ->
                  emit b (Assign (at array / Index (usize index), Use (constant_int32 n))))
                [ 4; 5; 6 ];
              let view = local b ~name:"view" (value view_ty) in
              ignore (operate b ~destination:(at view) Array_view [ Place (at array) ]);
              let middle =
                match operate b View_at [ Place (at view); Value (usize 1) ] with
                | Some place -> place
                | None -> failwith "view_at lends nothing"
              in
              let length = local b (value (named "USize")) in
              ignore (operate b ~destination:(at length) View_length [ Place (at view) ]);
              let status = local b (value int32) in
              emit b (Assign (at status, Convert (Copy (at length), Integer Int32)));
              emit b (Assign (at status, Binary (Add, Copy (at status), constant_int32 50)));
              let weighted = local b (value int32) in
              emit b (Assign (at weighted, Binary (Subtract, Copy middle, constant_int32 5)));
              emit b (Assign (at status, Binary (Add, Copy (at status), Copy (at weighted))));
              status);
        ]);
  test "static storage given room is copied to the heap, where it can be pushed onto" (fun () ->
      let open Lir_builder in
      let storage_ty = named "Storage" ~arguments:[ Type uint8 ] in
      expect_status 197
        [
          built_entry (fun b ->
              let storage = local b (value storage_ty) in
              emit b
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
                (operate b ~type_arguments:[ uint8 ] Storage_set_capacity
                   [ Place (at storage); Value (usize 4) ]);
              ignore
                (operate b ~type_arguments:[ uint8 ] Storage_push
                   [ Place (at storage); Value (Constant (Integer (UInt8, Z.of_int 100))) ]);
              let first = local b (value int32) and last = local b (value int32) in
              let element i = at storage / Field "buffer" / Index (usize i) in
              emit b (Assign (at first, Convert (Copy (element 0), Integer Int32)));
              emit b (Assign (at last, Convert (Copy (element 3), Integer Int32)));
              emit b (Assign (at first, Binary (Add, Copy (at first), Copy (at last))));
              first);
        ])

let () = Harness.finish ()
