(* Code generation's tests. Each test gives a small input and states one
   fact about what code generation makes of it. See IMPLEMENTATION.md,
   "Testing", and CODEGEN.md, "Testing". *)

let test = Harness.test
let fail = Harness.fail

let expect_string ~expected actual =
  if not (String.equal expected actual) then fail "expected %S, got %S" expected actual

let contains text part =
  let n = String.length part in
  let rec at i = i + n <= String.length text && (String.sub text i n = part || at (i + 1)) in
  at 0

let expect_int ~expected actual =
  if expected <> actual then fail "expected %d, got %d" expected actual

(* Types for the tests: a few prelude types and types defined by each test,
   with their shapes. *)

let definition name : Ground.definition = { package = "test"; modules = []; name }
let named ?(arguments = []) name = Ground.Named { definition = definition name; arguments }
let int64 = named "Int64"
let bool = named "Bool"
let character = named "Character"
let unit = named "Unit"
let float64 = named "Float64"
let uint8 = named "UInt8"
let option value = named "Option" ~arguments:[ Type value ]
let list element = named "List" ~arguments:[ Type element ]
let array element count = named "Array" ~arguments:[ Type element; Value (Z.of_int count) ]

open Memory_layout

let field name ty = (name, Typed ty)
let variant ?(indirect = false) name fields : variant_shape = { name; indirect; fields }

(* The shapes of the prelude types the tests use, and of [extra], which
   each test defines. *)
let shapes extra (ty : Ground.ty) : shape =
  match ty with
  | Named { definition = { name = "Int64"; _ }; _ } -> Scalar (Integer Int64)
  | Named { definition = { name = "UInt8"; _ }; _ } -> Scalar (Integer UInt8)
  | Named { definition = { name = "USize"; _ }; _ } -> Scalar (Integer USize)
  | Named { definition = { name = "Float64"; _ }; _ } -> Scalar Float64
  | Named { definition = { name = "Bool"; _ }; _ } -> Scalar Bool
  | Named { definition = { name = "Character"; _ }; _ } -> Scalar Character
  | Named { definition = { name = "Unit"; _ }; _ } -> Record []
  | Never -> Sum []
  | Named { definition = { name = "Option"; _ }; arguments = [ Type value ] } ->
      Sum [ variant "Some" [ field "value" value ]; variant "None" [] ]
  | Named { definition = { name = "List"; _ }; arguments = [ Type element ] } ->
      Record
        [
          ("buffer", Raw (Pointer (Data element)));
          field "length" (named "USize");
          field "capacity" (named "USize");
        ]
  | Named { definition = { name = "Array"; _ }; arguments = [ Type element; Value count ] } ->
      Array (element, Z.to_int count)
  | Named { definition = { name = "Int32"; _ }; _ } -> Scalar (Integer Int32)
  | Function f -> Convention.function_value_shape f
  | _ -> (
      match List.assoc_opt (Ground.to_string ty) extra with
      | Some shape -> shape
      | None -> invalid_arg ("no shape for " ^ Ground.to_string ty))

let layout ?(target = target_64) ?(extra = []) ty =
  of_type (create target ~shape_of:(shapes extra)) ty

let describe ?target ?extra ty = to_string (layout ?target ?extra ty)

(* Data layout *)

let () =
  test "fields are placed by alignment, largest first, then by name" (fun () ->
      let extra =
        [ ("Mixed", Record [ field "small" uint8; field "large" int64; field "flag" bool ]) ]
      in
      expect_string ~expected:"16/8 struct(large@0 flag@8 small@9) niche flag 2+254"
        (describe ~extra (named "Mixed")));
  test "reordering fields in the source does not change the layout" (fun () ->
      let first = [ ("Point", Record [ field "x" float64; field "y" float64; field "z" uint8 ]) ] in
      let second =
        [ ("Point", Record [ field "z" uint8; field "y" float64; field "x" float64 ]) ]
      in
      expect_string
        ~expected:(describe ~extra:first (named "Point"))
        (describe ~extra:second (named "Point")));
  test "a record with one field has the field's size and alignment" (fun () ->
      let extra = [ ("UserId", Record [ field "number" int64 ]) ] in
      let wrapped = layout ~extra (named "UserId") in
      expect_int ~expected:8 wrapped.size;
      expect_int ~expected:8 wrapped.alignment);
  test "fields of zero size take no room" (fun () ->
      let extra = [ ("Holder", Record [ field "nothing" unit; field "count" int64 ]) ] in
      expect_string ~expected:"8/8 struct(count@0)" (describe ~extra (named "Holder")));
  test "a record with no fields has zero size" (fun () ->
      expect_string ~expected:"0/1 zero" (describe unit));
  test "a sum type with no fields is just its tag" (fun () ->
      let extra =
        [ ("Ordering", Sum [ variant "Less" []; variant "Equal" []; variant "Greater" [] ]) ]
      in
      expect_string ~expected:"1/1 tag(UInt8: Less Equal Greater) niche . 3+253"
        (describe ~extra (named "Ordering")));
  test "a tag is the smallest unsigned integer that numbers every variant" (fun () ->
      let many = Sum (List.init 300 (fun i -> variant (Printf.sprintf "V%d" i) [])) in
      expect_int ~expected:2 (layout ~extra:[ ("Many", many) ] (named "Many")).size);
  test "a sum type is a tag followed by the largest variant's fields" (fun () ->
      let extra =
        [
          ( "Shape",
            Sum
              [
                variant "Circle" [ field "radius" float64 ];
                variant "Square" [ field "side" float64; field "corner" int64 ];
                variant "Empty" [];
              ] );
        ]
      in
      expect_string ~expected:"24/8 tagged(UInt8, payload@8: Circle Square Empty) niche tag 3+253"
        (describe ~extra (named "Shape")));
  test "Option of a List has no tag" (fun () ->
      expect_string ~expected:"24/8 niche-encoded(Some; None=0 at value.buffer)"
        (describe (option (list int64))));
  test "Option of a Bool is one byte" (fun () ->
      expect_string ~expected:"1/1 niche-encoded(Some; None=2 at value) niche value 3+253"
        (describe (option bool)));
  test "Option of a Character is the size of a Character" (fun () ->
      expect_int ~expected:4 (layout (option character)).size);
  test "Option of an Option of a Bool uses the next spare value" (fun () ->
      expect_string
        ~expected:"1/1 niche-encoded(Some; None=3 at value.value) niche value.value 4+252"
        (describe (option (option bool))));
  test "Option of a sum with no fields uses the tag's spare values" (fun () ->
      let extra = [ ("Bit", Sum [ variant "Zero" []; variant "One" [] ]) ] in
      expect_string ~expected:"1/1 niche-encoded(Some; None=2 at value) niche value 3+253"
        (describe ~extra (option (named "Bit"))));
  test "Option of an Int64 has a tag, since every value is in use" (fun () ->
      expect_string ~expected:"16/8 tagged(UInt8, payload@8: Some None) niche tag 2+254"
        (describe (option int64)));
  test "an indirect variant holds one pointer" (fun () ->
      let tree =
        Sum
          [
            variant "Leaf" [];
            variant ~indirect:true "Node"
              [ field "left" (named "Tree"); field "value" int64; field "right" (named "Tree") ];
          ]
      in
      expect_string ~expected:"8/8 niche-encoded(Node; Leaf=0 at .)"
        (describe ~extra:[ ("Tree", tree) ] (named "Tree")));
  test "an indirect variant's block holds its fields" (fun () ->
      let tree =
        Sum
          [
            variant "Leaf" [];
            variant ~indirect:true "Node"
              [ field "left" (named "Tree"); field "value" int64; field "right" (named "Tree") ];
          ]
      in
      let env = create target_64 ~shape_of:(shapes [ ("Tree", tree) ]) in
      expect_string ~expected:"24/8 struct(left@0 right@8 value@16)"
        (to_string (block env (named "Tree") "Node")));
  test "an Array holds its elements in place" (fun () ->
      expect_string ~expected:"32/1 array(32 x 1/1 UInt8)" (describe (array uint8 32)));
  test "USize follows the target's pointer width" (fun () ->
      expect_int ~expected:24 (layout (list int64)).size;
      expect_int ~expected:12 (layout ~target:target_32 (list int64)).size);
  test "a variant whose fields have zero size counts as having none" (fun () ->
      expect_string ~expected:"1/1 tag(UInt8: Some None) niche . 2+254" (describe (option unit)));
  test "a sum type with one variant has no tag" (fun () ->
      let extra = [ ("Only", Sum [ variant "Only" [ field "count" int64 ] ]) ] in
      expect_string ~expected:"8/8 niche-encoded(Only;  at nothing)"
        (describe ~extra (named "Only")));
  test "Never has zero size" (fun () -> expect_string ~expected:"0/1 zero" (describe Never));
  test "a variant's discriminant is its tag value or its niche value" (fun () ->
      let layout = layout (option bool) in
      (match discriminant layout "None" with
      | Niche_value value when Z.equal value (Z.of_int 2) -> ()
      | _ -> fail "None is not stored as 2");
      match discriminant layout "Some" with
      | Not_niche -> ()
      | _ -> fail "Some is not the dataful variant")

(* Building LIR by hand *)

let int32 = named "Int32"
let usize = named "USize"
let local ?name ty : Lir.local_info = { ty; name }
let value ty = Lir.Value ty
let at ?(projections = []) local : Lir.place = { root = Local local; projections }
let copy ?projections local = Lir.Copy (at ?projections local)
let constant_int32 n = Lir.Constant (Integer (Int32, Z.of_int n))
let constant_int64 n = Lir.Constant (Integer (Int64, Z.of_int n))
let block statements terminator : Lir.basic_block = { statements; terminator }

let function_ ?(parameters = []) ?result ?(returns = true) ?(environment = []) locals blocks :
    Lir.function_ =
  {
    parameters;
    result;
    returns;
    locals = Array.of_list locals;
    blocks = Array.of_list blocks;
    environment;
  }

let key name =
  Instance.Function { definition = definition name; type_arguments = []; capabilities = [] }

let instance ?(nested = []) name main : Lir.t =
  { key = key name; main; nested = Array.of_list nested }

(* [entry] returns an [Int32], which the program exits with. *)
let entry ?nested locals blocks =
  instance ?nested "entry" (function_ ~result:(value int32) locals blocks)

let call name ?(result = Some (value int32)) ?(parameters = []) arguments place : Lir.statement =
  Call
    {
      target =
        Direct
          { function_ = Instance (key name); signature = { parameters; result; returns = true } };
      arguments;
      result = place;
    }

(* Compiling and running generated C *)

let shape_env ?(extra = []) () = create target_64 ~shape_of:(shapes extra)
let scratch = lazy (Filename.temp_dir "truss-codegen-tests" "")

let compiler =
  lazy
    (match Toolchain.find () with Ok toolchain -> toolchain | Error message -> failwith message)

(* Generated C must compile with every warning an error, apart from these,
   which are known not to apply to it: parameters a function does not read
   are normal, as for an adapter's environment. *)
let strict = [ "-Wall"; "-Wextra"; "-Werror"; "-Wno-unused-parameter" ]

let runtime_object =
  lazy
    (let directory = Lazy.force scratch in
     let source = Filename.concat directory "runtime.c" in
     let output = Filename.concat directory "runtime.o" in
     Out_channel.with_open_bin source (fun channel ->
         output_string channel (Startup.runtime target_64));
     match
       Toolchain.compile (Lazy.force compiler) ~optimization:O1 ~extra:strict ~source ~output ()
     with
     | Ok () -> output
     | Error message -> failwith ("the runtime does not compile: " ^ message))

let counter = ref 0
let write path text = Out_channel.with_open_bin path (fun channel -> output_string channel text)

(* Compiles the instances into a program whose [main] calls [entry], runs
   it, and returns its status, output, and errors. *)
let run_program ?(extra = []) ?(anchors = []) (instances : Lir.t list) =
  incr counter;
  let directory = Lazy.force scratch in
  let base = Filename.concat directory (Printf.sprintf "program%d" !counter) in
  let env = shape_env ~extra () in
  let c = Emit_c.file env Development (List.map (fun i -> (i, Emit_c.External)) instances) in
  write (base ^ ".c") c;
  write (base ^ "_main.c") (Startup.main_calling (Instance.symbol (key "entry")));
  write (base ^ "_anchors.c") (Positions.anchors_file target_64 anchors);
  let toolchain = Lazy.force compiler in
  let compile name =
    match
      Toolchain.compile toolchain ~optimization:O1 ~extra:strict
        ~source:(base ^ name ^ ".c")
        ~output:(base ^ name ^ ".o")
        ()
    with
    | Ok () -> base ^ name ^ ".o"
    | Error message -> failwith (Printf.sprintf "%s%s.c does not compile:\n%s" base name message)
  in
  let objects = [ compile ""; compile "_main"; compile "_anchors"; Lazy.force runtime_object ] in
  match Toolchain.link toolchain ~objects ~output:base with
  | Ok () -> Toolchain.run base []
  | Error message -> failwith ("link failed: " ^ message)

let expect_status ?extra ?anchors expected instances =
  let status, _, errors = run_program ?extra ?anchors instances in
  if status <> expected then fail "expected status %d, got %d (%s)" expected status errors

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
                      result = Some (at 3);
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
                  result = Some (at 1);
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
                  (Panic
                     {
                       message = Constant (Bytes "boom");
                       length = Constant (Integer (USize, Z.of_int 4));
                       site = { line = 3; column = 5 };
                     });
              ];
          ]
      in
      expect_int ~expected:101 status;
      expect_string ~expected:"panic: boom\n  at test.truss:13:5\n" errors);
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
        Instance.Method
          {
            owner = { package = "standard"; modules = [ "list" ]; name = "List" };
            name = "each";
            receiver = Some Read;
            type_arguments = [ Type int64 ];
            capabilities = [];
          }
      in
      expect_string ~expected:"t_standard__list__List_each_Of_test__Int64_End_"
        (Instance.symbol key));
  test "a long symbol keeps its start and ends with a hash" (fun () ->
      let long name = Instance.symbol (key (String.make 300 name)) in
      let a = long 'a' and b = long 'b' in
      expect_int ~expected:(180 + 6 + 32) (String.length a);
      if a = b then fail "two long names give one symbol")

let () = Harness.finish ()
