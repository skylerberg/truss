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

let definition name : Path.t = Top { module_ = { package = "test"; modules = [] }; name }
let named ?(arguments = []) name = Ground.Named { path = definition name; arguments }
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
  | Named { path = Top { name = "Int64"; _ }; _ } -> Scalar (Integer Int64)
  | Named { path = Top { name = "UInt8"; _ }; _ } -> Scalar (Integer UInt8)
  | Named { path = Top { name = "USize"; _ }; _ } -> Scalar (Integer USize)
  | Named { path = Top { name = "Float64"; _ }; _ } -> Scalar Float64
  | Named { path = Top { name = "Bool"; _ }; _ } -> Scalar Bool
  | Named { path = Top { name = "Character"; _ }; _ } -> Scalar Character
  | Named { path = Top { name = "Unit"; _ }; _ } -> Record []
  | Never -> Sum []
  | Named { path = Top { name = "Option"; _ }; arguments = [ Type value ] } ->
      Sum [ variant "Some" [ field "value" value ]; variant "None" [] ]
  | Named { path = Top { name = "List"; _ }; arguments = [ Type element ] } ->
      Record
        [
          ("buffer", Raw (Pointer (Data element)));
          field "length" (named "USize");
          field "capacity" (named "USize");
        ]
  | Named { path = Top { name = "Array"; _ }; arguments = [ Type element; Value count ] } ->
      Array (element, Z.to_int count)
  | Named { path = Top { name = "Int32"; _ }; _ } -> Scalar (Integer Int32)
  | Named { path = Top { name = "Storage"; _ }; arguments = [ Type element ] } ->
      Record
        [
          ("buffer", Raw (Pointer (Data element)));
          ("length", Typed (named "USize"));
          ("capacity", Typed (named "USize"));
        ]
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

let key name = Instance.Code { path = definition name; type_arguments = [] }

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
      result = (match place with Some place -> Returned place | None -> Discarded);
    }

(* Compiling and running generated C *)

let shape_env ?(extra = []) () = create target_64 ~shape_of:(shapes extra)
let scratch = lazy (Filename.temp_dir "truss-codegen-tests" "")

let compiler =
  lazy
    (match Toolchain.find () with Ok toolchain -> toolchain | Error message -> failwith message)

(* Generated C must compile with every warning an error, apart from these,
   which are known not to apply to it: parameters a function does not read
   are normal, as for an adapter's environment, and so is a value computed
   and never read, as [let _ = ...] does. *)
let strict =
  [ "-Wall"; "-Wextra"; "-Werror"; "-Wno-unused-parameter"; "-Wno-unused-but-set-variable" ]

let counter = ref 0
let cache = lazy (Build.cache (Filename.concat (Lazy.force scratch) "objects"))
let settings : Build.settings = { build = Development; optimization = O1; extra = strict }

(* Compiles the instances into a program whose [main] calls [entry], runs
   it, and returns its status, output, and errors. *)
let run_program ?(extra = []) ?(anchors = []) (instances : Lir.t list) =
  incr counter;
  let output = Filename.concat (Lazy.force scratch) (Printf.sprintf "program%d" !counter) in
  let env = shape_env ~extra () in
  let sources =
    [
      ("main", Startup.main_calling (Instance.symbol (key "entry")));
      ("anchors", Positions.anchors_file target_64 anchors);
    ]
  in
  match
    Build.program (Lazy.force compiler) (Lazy.force cache) env settings
      ~files:[ List.map (fun i -> Lir.Code i) instances ]
      ~sources ~output
  with
  | Ok () -> Toolchain.run output []
  | Error message -> failwith message

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
  test "a long symbol keeps its start and ends with a hash" (fun () ->
      let long name = Instance.symbol (key (String.make 300 name)) in
      let a = long 'a' and b = long 'b' in
      expect_int ~expected:(180 + 6 + 32) (String.length a);
      if a = b then fail "two long names give one symbol")

(* Drop elaboration *)

let text = named "Text"
let pair = named "Pair"

let drop_shapes =
  [
    ("Text", Record [ ("buffer", Raw (Pointer Opaque)) ]);
    ("Pair", Record [ field "first" text; field "second" text ]);
    ( "Box",
      Sum
        [
          variant "Empty" [];
          variant ~indirect:true "Full" [ field "contents" text; field "count" int32 ];
        ] );
    ("Counter", Record [ ("target", Raw (Pointer (Data int32))) ]);
  ]

let rec needs_drop (ty : Ground.ty) =
  match ty with
  | Named { path = Top { name = "Text" | "Box" | "Counter"; _ }; _ } -> true
  | Named { path = Top { name = "Pair"; _ }; _ } -> true
  | Named { path = Top { name = "Option"; _ }; arguments = [ Type inner ] } -> needs_drop inner
  | _ -> false

let elaborate f =
  Lir.canonical
    (Drops.elaborate (shape_env ~extra:drop_shapes ()) ~needs_drop ~environment:(fun _ -> []) f)

let elaborated f = Lir.function_to_string (elaborate f)
let condition = local ~name:"ready" (Raw Bool)
let consume = call "consume" ~result:None ~parameters:[ value text ]

let expect_lir ~expected f =
  let actual = elaborated f in
  if actual <> String.concat "\n" expected then
    fail "expected:\n%s\ngot:\n%s" (String.concat "\n" expected) actual

let () =
  test "a drop of a place moved out on every path is removed" (fun () ->
      expect_lir
        ~expected:[ "fn(_0: Text)"; "b0: call test::consume(move _0); return" ]
        (function_ ~parameters:[ 0 ]
           [ local (value text) ]
           [ block [ consume [ Move (at 0) ] None; Drop (at 0) ] (Return None) ]));
  test "a drop of a place nothing moved out of is kept" (fun () ->
      expect_lir
        ~expected:[ "fn(_0: Text)"; "b0: drop _0; return" ]
        (function_ ~parameters:[ 0 ] [ local (value text) ] [ block [ Drop (at 0) ] (Return None) ]));
  test "a drop of plain data is removed" (fun () ->
      expect_lir ~expected:[ "fn(_0: Int32)"; "b0: return" ]
        (function_ ~parameters:[ 0 ]
           [ local (value int32) ]
           [ block [ Drop (at 0) ] (Return None) ]));
  test "a place moved out on one path is dropped behind a flag" (fun () ->
      expect_lir
        ~expected:
          [
            "fn(_0: Text, _1: raw Bool)";
            "b0: _2 = true; switch _1 [1 => b1, _ => b2]";
            "b1: call test::consume(move _0); _2 = false; goto b2";
            "b2: switch _2 [1 => b3, _ => b4]";
            "b3: drop _0; goto b4";
            "b4: _2 = false; return";
          ]
        (function_ ~parameters:[ 0; 1 ]
           [ local (value text); condition ]
           [
             block [] (Switch { value = copy 1; cases = [ (Z.one, 1) ]; default = Some 2 });
             block [ consume [ Move (at 0) ] None ] (Goto 2);
             block [ Drop (at 0) ] (Return None);
           ]));
  test "after a field is moved out, the rest of the record is dropped field by field" (fun () ->
      expect_lir
        ~expected:
          [ "fn(_0: Pair)"; "b0: call test::consume(move _0.first); drop _0.second; return" ]
        (function_ ~parameters:[ 0 ]
           [ local (value pair) ]
           [
             block
               [ consume [ Move (at ~projections:[ Field "first" ] 0) ] None; Drop (at 0) ]
               (Return None);
           ]));
  test "a record whose moved field is given a value again is dropped whole" (fun () ->
      expect_lir
        ~expected:
          [
            "fn(_0: Pair, _1: Text)";
            "b0: call test::consume(move _0.first); _0.first = move _1; drop _0; return";
          ]
        (function_ ~parameters:[ 0; 1 ]
           [ local (value pair); local (value text) ]
           [
             block
               [
                 consume [ Move (at ~projections:[ Field "first" ] 0) ] None;
                 Assign (at ~projections:[ Field "first" ] 0, Use (Move (at 1)));
                 Drop (at 0);
               ]
               (Return None);
           ]));
  test "an assignment drops the value it replaces" (fun () ->
      expect_lir
        ~expected:
          [ "fn(_0: Text, _1: Text)"; "b0: _2 = move _1; drop _0; _0 = move _2; drop _0; return" ]
        (function_ ~parameters:[ 0; 1 ]
           [ local (value text); local (value text) ]
           [ block [ Assign (at 0, Use (Move (at 1))); Drop (at 0) ] (Return None) ]));
  test "an assignment that moves out of its own place first drops nothing" (fun () ->
      let rebuild = call "rebuild" ~result:(Some (value text)) ~parameters:[ value text ] in
      expect_lir
        ~expected:[ "fn(_0: Text)"; "b0: _0 = call test::rebuild(move _0); drop _0; return" ]
        (function_ ~parameters:[ 0 ]
           [ local (value text) ]
           [ block [ rebuild [ Move (at 0) ] (Some (at 0)); Drop (at 0) ] (Return None) ]));
  test "an indirect variant whose fields were moved out frees its block" (fun () ->
      let full field = at ~projections:[ Variant_field { variant = "Full"; field } ] 0 in
      expect_lir
        ~expected:
          [ "fn(_0: Box)"; "b0: call test::consume(move _0.Full.contents); free _0.Full; return" ]
        (function_ ~parameters:[ 0 ]
           [ local (value (named "Box")) ]
           [ block [ consume [ Move (full "contents") ] None; Drop (at 0) ] (Return None) ]));
  test "a value moved out on one path is dropped exactly once when the program runs" (fun () ->
      let counter = named "Counter" in
      let pointer = Lir.Pointer { target = value counter; writable = true } in
      let drop_counter : Lir.t =
        {
          key = Drop counter;
          main =
            function_ ~parameters:[ 0 ]
              [ local pointer; local (Raw (Pointer (Data int32))) ]
              [
                block
                  [
                    Assign (at 1, Use (copy ~projections:[ Deref; Field "target" ] 0));
                    Assign
                      ( at ~projections:[ Deref ] 1,
                        Binary (Add, copy ~projections:[ Deref ] 1, constant_int32 1) );
                  ]
                  (Return None);
              ];
          nested = [||];
        }
      in
      let keep =
        instance "keep"
          (function_ ~parameters:[ 0 ]
             [ local (value counter) ]
             [ block [ Drop (at 0) ] (Return None) ])
      in
      let main =
        function_ ~result:(value int32)
          [
            local ~name:"count" (value int32);
            local ~name:"counter" (value counter);
            local (Raw Bool);
          ]
          [
            block
              [
                Assign (at 0, Use (constant_int32 0));
                Assign
                  ( at 1,
                    Build
                      {
                        ty = counter;
                        variant = None;
                        fields = [ ("target", Address { place = at 0; writable = true }) ];
                      } );
                Assign (at 2, Use (Constant (Bool true)));
              ]
              (Switch { value = copy 2; cases = [ (Z.one, 1) ]; default = Some 2 });
            block
              [ call "keep" ~result:None ~parameters:[ value counter ] [ Move (at 1) ] None ]
              (Goto 2);
            block [ Drop (at 1) ] (Return (Some (copy 0)));
          ]
      in
      let program =
        [
          drop_counter;
          {
            keep with
            main =
              Drops.elaborate (shape_env ~extra:drop_shapes ()) ~needs_drop
                ~environment:(fun _ -> [])
                keep.main;
          };
          ( entry [] [] |> fun e ->
            {
              e with
              main =
                Drops.elaborate (shape_env ~extra:drop_shapes ()) ~needs_drop
                  ~environment:(fun _ -> [])
                  main;
            } );
        ]
      in
      expect_status ~extra:drop_shapes 1 program)

(* Yield lowering *)

(* [count_to(limit)] yields 1, 2, and so on up to [limit]. *)
let count_to =
  function_ ~parameters:[ 0 ]
    [ local ~name:"limit" (value int32); local ~name:"i" (value int32); local (Raw Bool) ]
    [
      block [ Assign (at 1, Use (constant_int32 1)) ] (Goto 1);
      block
        [ Assign (at 2, Binary (Less_equal, copy 1, copy 0)) ]
        (Switch { value = copy 2; cases = [ (Z.one, 2) ]; default = Some 3 });
      block [] (Yield { value = copy 1; resume = 4; stop = Some 3 });
      block [] (Return None);
      block [ Assign (at 1, Binary (Add, copy 1, constant_int32 1)) ] (Goto 1);
    ]

let body_type : Ground.function_type =
  { parameters = [ (Read, int32) ]; result = Returns bool; uses = [] }

(* A program that loops over [count_to(4)] with a body that adds each item
   to a total, and goes on while [go_on] says so. *)
let loop_program go_on =
  let env = shape_env () in
  let method_ = instance "count_to" (Yields.loop_form env ~body:body_type count_to) in
  let total = Lir.Pointer { target = value int32; writable = true } in
  let body =
    function_ ~parameters:[ 0; 1 ] ~result:(value bool)
      ~environment:[ ("total", total) ]
      [
        local (Raw (Nullable_pointer Opaque));
        local ~name:"item" (value int32);
        local (Pointer { target = Environment 0; writable = false });
        local (value bool);
      ]
      [
        block
          [
            Assign (at 2, Use (copy 0));
            Assign
              ( at ~projections:[ Deref; Field "total"; Deref ] 2,
                Binary (Add, copy ~projections:[ Deref; Field "total"; Deref ] 2, copy 1) );
            Assign (at 3, go_on (copy 1));
          ]
          (Return (Some (copy 3)));
      ]
  in
  let signature = Lir.signature method_.main in
  [
    method_;
    entry ~nested:[ body ]
      [
        local ~name:"total" (value int32); local (Environment 0); local (value (Function body_type));
      ]
      [
        block
          [
            Assign (at 0, Use (constant_int32 0));
            Assign
              (at ~projections:[ Field "total" ] 1, Use (Address { place = at 0; writable = true }));
            Assign
              ( at 2,
                Function_value
                  {
                    code = Nested 0;
                    environment = Some (Address { place = at 1; writable = false });
                  } );
            Call
              {
                target = Direct { function_ = Instance (key "count_to"); signature };
                arguments = [ constant_int32 4; copy 2 ];
                result = Discarded;
              };
          ]
          (Return (Some (copy 0)));
      ];
  ]

let () =
  test "a yielding method calls the loop body at each yield" (fun () ->
      expect_status 10 (loop_program (fun _ -> Use (Constant (Bool true)))));
  test "a loop body that stops ends the method at that yield" (fun () ->
      expect_status 6 (loop_program (fun item -> Binary (Not_equal, item, constant_int32 3))));
  let yielding : Ground.yielding = { method_ = definition "count_to"; type_arguments = [] } in
  let cursor = Ground.Cursor yielding in
  test "a cursor keeps the parameters and the locals live across a yield" (fun () ->
      let fields = List.map fst (Yields.cursor_fields (shape_env ()) count_to) in
      expect_string ~expected:"state local0 local1" (String.concat " " fields));
  test "a pulled method yields each value and then None" (fun () ->
      let cursor_shape =
        ("cursor of count_to", Record (Yields.cursor_fields (shape_env ()) count_to))
      in
      let env = shape_env ~extra:[ cursor_shape ] () in
      let result = option int32 in
      let next =
        {
          (instance "next" (Lir.canonical (Yields.cursor_next env ~cursor ~result count_to))) with
          key = Cursor_next yielding;
        }
      in
      let release : Lir.t =
        {
          key = Drop cursor;
          main = Lir.canonical (Yields.cursor_drop env ~cursor ~owned:[] count_to);
          nested = [||];
        }
      in
      let next_call place =
        Lir.Call
          {
            target =
              Direct
                { function_ = Instance (Cursor_next yielding); signature = Lir.signature next.main };
            arguments = [ Address { place = at 0; writable = true } ];
            result = Returned place;
          }
      in
      let pulled = at 1 in
      let add_value =
        Lir.Assign
          ( at 2,
            Binary
              ( Add,
                copy 2,
                copy ~projections:[ Variant_field { variant = "Some"; field = "value" } ] 1 ) )
      in
      expect_status ~extra:[ cursor_shape ] 16
        [
          next;
          release;
          entry
            [
              local ~name:"cursor" (value cursor);
              local (value result);
              local ~name:"sum" (value int32);
              local (Raw Bool);
              local (value int32);
            ]
            [
              block
                [
                  Assign
                    ( at 0,
                      Build
                        {
                          ty = cursor;
                          variant = None;
                          fields =
                            [
                              ("state", Constant (Integer (UInt32, Z.zero)));
                              ("local0", constant_int32 3);
                            ];
                        } );
                  Assign (at 2, Use (constant_int32 0));
                  next_call pulled;
                  add_value;
                  next_call pulled;
                  add_value;
                  next_call pulled;
                  add_value;
                  next_call pulled;
                  Assign (at 3, Is_variant (at 1, "None"));
                  Assign (at 4, Convert (copy 3, Integer Int32));
                  Assign (at 4, Binary (Multiply, copy 4, constant_int32 10));
                  Assign (at 2, Binary (Add, copy 2, copy 4));
                  Drop (at 0);
                ]
                (Return (Some (copy 2)));
            ];
        ])

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

(* What a build reaches, and test keys *)

(* A program whose [entry] calls [helper], under the given names, and whose
   [helper] returns [value]. *)
let named_program ~entry_name ~helper_name returned =
  let helper =
    instance helper_name
      (function_ ~result:(value int32) [] [ block [] (Return (Some (constant_int32 returned))) ])
  in
  let main =
    instance entry_name
      (function_ ~result:(value int32)
         [ local (Lir.Value int32) ]
         [ block [ call helper_name [] (Some (at 0)) ] (Return (Some (copy 0))) ])
  in
  [ main; helper ]

let lookup instances key = List.find (fun (i : Lir.t) -> Instance.equal i.key key) instances

let () =
  test "a build reaches each called instance once, in order" (fun () ->
      let program = named_program ~entry_name:"start" ~helper_name:"helper" 1 in
      let reached =
        Reachable.reachable (shape_env ())
          ~lookup:(fun k -> Lir.Code (lookup program k))
          [ key "start" ]
      in
      expect_string ~expected:"test::start test::helper"
        (String.concat " "
           (List.map
              (function
                | Lir.Code i -> Instance.to_string i.key
                | Data d -> Instance.to_string d.data_key
                | Table t -> Instance.to_string t.table_key
                | Evidence e -> Instance.to_string e.evidence_key)
              reached)));
  test "a drop reaches the type's drop function" (fun () ->
      let f =
        instance "f"
          (function_ ~parameters:[ 0 ]
             [ local (value text) ]
             [ block [ Drop (at 0) ] (Return None) ])
      in
      let references = Reachable.references (shape_env ~extra:drop_shapes ()) f in
      expect_string ~expected:"drop Text"
        (String.concat " " (List.map Instance.to_string references)));
  let test_key ~entry_name ~helper_name returned =
    let program = named_program ~entry_name ~helper_name returned in
    Reachable.test_key (shape_env ())
      ~lookup:(fun k -> Lir.Code (lookup program k))
      (key entry_name)
  in
  test "renaming the definitions a test reaches keeps its key" (fun () ->
      if
        test_key ~entry_name:"start" ~helper_name:"helper" 1
        <> test_key ~entry_name:"begin" ~helper_name:"assist" 1
      then fail "the keys differ");
  test "changing what a test reaches changes its key" (fun () ->
      if
        test_key ~entry_name:"start" ~helper_name:"helper" 1
        = test_key ~entry_name:"start" ~helper_name:"helper" 2
      then fail "the keys are equal")

(* The test runner *)

let () =
  test "the test runner reports each test's outcome, message, and echo output in order, and a leak"
    (fun () ->
      let site : Lir.site = { definition = definition "suite"; line = 2; column = 3 } in
      let text value = Lir.Constant (Bytes value) in
      let length value = Lir.Constant (Integer (USize, Z.of_int (String.length value))) in
      let ending failure message =
        Lir.Fail { failure; message = text message; length = length message; site }
      in
      let suite name blocks = instance name (function_ [] blocks) in
      let tests =
        [
          suite "passes" [ block [] (Return None) ];
          suite "fails" [ block [] (ending Assertion "values differ") ];
          suite "panics" [ block [] (ending Panic "boom") ];
          suite "echoes"
            [ block [ Echo { text = text "42"; length = length "42"; site } ] (Return None) ];
          suite "never_ends" [ block [] (Goto 0) ];
          suite "unfinished" [ block [] (ending Todo "hole of type Int64") ];
          suite "leaks"
            [
              block
                [
                  Call
                    {
                      target = Intrinsic Allocate;
                      arguments =
                        [
                          Constant (Integer (USize, Z.of_int 8)); Constant (Integer (USize, Z.one));
                        ];
                      result = Discarded;
                    };
                ]
                (Return None);
            ];
        ]
      in
      incr counter;
      let output = Filename.concat (Lazy.force scratch) (Printf.sprintf "tests%d" !counter) in
      let symbols = List.map (fun (t : Lir.t) -> Instance.symbol t.key) tests in
      let sources =
        [
          ("tests", Startup.tests_calling ~time_limit:300 symbols);
          ( "anchors",
            Positions.anchors_file target_64
              [ { definition = definition "suite"; path = "suite.truss"; first_line = 10 } ] );
        ]
      in
      match
        Build.program (Lazy.force compiler) (Lazy.force cache) (shape_env ()) settings
          ~files:[ List.map (fun t -> Lir.Code t) tests ]
          ~sources ~output
      with
      | Error message -> fail "%s" message
      | Ok () ->
          let status, out, _ = Toolchain.run output [] in
          expect_int ~expected:1 status;
          expect_string
            ~expected:
              (String.concat ""
                 [
                   "test 0 passed\n";
                   "test 1 failed\nmessage 35\nvalues differ\n  at suite.truss:12:3\n";
                   "test 2 panicked\nmessage 26\nboom\n  at suite.truss:12:3\n";
                   "test 3 passed\necho 21\nsuite.truss:12:3: 42\n\n";
                   "test 4 timed_out\nmessage 23\nran past the time limit\n";
                   "test 5 incomplete\nmessage 40\nhole of type Int64\n  at suite.truss:12:3\n";
                   "test 6 panicked\nmessage 45\ncompiler bug: the test left 1 block allocated\n";
                 ])
            out)

(* Ground types and shapes from the standard library *)

let standard_database =
  lazy
    (let database = Query.create () in
     List.iter
       (fun (module_, text) -> Query.set database Workspace.file_text module_ text)
       Standard_library.modules;
     Query.set database Workspace.packages Standard_library.package
       {
         name = Standard_library.package;
         dependencies = [];
         modules = List.map fst Standard_library.modules;
       };
     database)

let standard_context : Monomorphic.context =
  {
    type_interface =
      (fun path ->
        Query.demand (Lazy.force standard_database) Interface.Environment.type_interface path);
    normalize = Fun.id;
    capabilities = (fun _ -> []);
    cursor_fields = (fun _ -> []);
  }

let standard module_ name ?(arguments = []) () =
  Ground.Named
    { path = Top { module_ = { package = "standard"; modules = [ module_ ] }; name }; arguments }

let standard_layout ty =
  Memory_layout.to_string
    (Memory_layout.of_type (create target_64 ~shape_of:(Monomorphic.shape standard_context)) ty)

let () =
  let int64 = Monomorphic.builtin Int64 in
  let bool = Monomorphic.builtin Bool in
  let list element = standard "list" "List" ~arguments:[ Type element ] () in
  let option value = standard "option" "Option" ~arguments:[ Type value ] () in
  test "the standard library's Option of a List has no tag" (fun () ->
      expect_string ~expected:"24/8 niche-encoded(Some; None=0 at value.storage.buffer)"
        (standard_layout (option (list int64))));
  test "the standard library's Option of a Bool is one byte" (fun () ->
      expect_int ~expected:1
        (Memory_layout.of_type
           (create target_64 ~shape_of:(Monomorphic.shape standard_context))
           (option bool))
          .size);
  test "a String is its storage's buffer, length, and capacity" (fun () ->
      expect_string ~expected:"24/8 struct(storage@0) niche storage.buffer 0+1"
        (standard_layout (standard "text" "String" ())));
  test "storage is not trivial, and an Option of an integer is" (fun () ->
      let glue =
        Glue.create
          (create target_64 ~shape_of:(Monomorphic.shape standard_context))
          ~kind_of:(Monomorphic.kind standard_context)
          ~usize:(Monomorphic.builtin USize) ()
      in
      if Glue.trivial glue (list int64) then fail "a List is trivial";
      if not (Glue.trivial glue (option int64)) then fail "an Option of an Int64 is not trivial")

(* Intrinsic operations *)

let intrinsic_types : Intrinsics.types =
  { usize; isize = named "ISize"; string_slice = named "StringSlice" }

(* An [entry] built with the builder: [body] writes its statements and
   returns the local to exit with. *)
let built_entry body =
  let b = Lir_builder.create () in
  Lir_builder.start b (Lir_builder.block b);
  let result = body b in
  Lir_builder.finish b (Return (Some (Copy (Lir_builder.at result))));
  instance "entry" (Lir_builder.build b ~parameters:[] ~result:(Some (value int32)))

let operate b ?destination ?(type_arguments = [ int32 ]) operation arguments =
  Intrinsics.lower (shape_env ()) b intrinsic_types operation ~type_arguments arguments ~destination
    ~site:{ definition = definition "entry"; line = 0; column = 1 }

let () =
  test "storage grows as it is pushed, and inserts, removes, swaps, and pops in place" (fun () ->
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
  test "pushing onto static storage copies it to the heap first" (fun () ->
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
                (operate b ~type_arguments:[ uint8 ] Storage_push
                   [ Place (at storage); Value (Constant (Integer (UInt8, Z.of_int 100))) ]);
              let first = local b (value int32) and last = local b (value int32) in
              let element i = at storage / Field "buffer" / Index (usize i) in
              emit b (Assign (at first, Convert (Copy (element 0), Integer Int32)));
              emit b (Assign (at last, Convert (Copy (element 3), Integer Int32)));
              emit b (Assign (at first, Binary (Add, Copy (at first), Copy (at last))));
              first);
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
        {
          usize = Monomorphic.builtin USize;
          isize = Monomorphic.builtin ISize;
          string_slice = standard "text" "StringSlice" ();
        }
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

(* Programs from source *)

let example : Path.module_ = { package = "example"; modules = [ "main" ] }

(* A module of Truss source with the standard library, which must check
   cleanly, ready to compile. *)
let load text =
  let database = Query.create () in
  Type_checker.load_standard database;
  Type_checker.load_package database ~name:"example" ~dependencies:[] [ (example, text) ];
  let source = (Query.demand database Workspace.file example).source in
  (match Type_checker.diagnostics database example with
  | [] -> ()
  | diagnostics ->
      fail "the source has diagnostics:\n%s"
        (String.concat "" (List.map (Diagnostic.render source) diagnostics)));
  (database, Compile.create database target_64 (Lazy.force compiler) (Lazy.force cache) settings)

(* The paths of a module's tests, in order. *)
let tests_of database =
  List.filter_map
    (fun (d : Resolve.Names.declaration) -> match d.path with Test _ -> Some d.path | _ -> None)
    (Query.demand database Resolve.Names.declarations example)

(* Compiles a module of Truss source with the standard library, runs its
   tests, and returns the runner's output. *)
let run_source text =
  let database, compile = load text in
  match Compile.run_tests compile ~time_limit:2000 (tests_of database) with
  | Ok (_, output) -> output
  | Error message -> failwith message

let expect_output text expected = expect_string ~expected (run_source text)

let () =
  test "a test calls a function that uses the standard library's arithmetic" (fun () ->
      expect_output
        {|fn square(value: Int64) -> Int64 {
  value * value
}

test "squares" {
  assert square(3) == 9
}

test "squares wrongly" {
  assert square(3) == 10
}
|}
        "test 0 passed\n\
         test 1 failed\n\
         message 51\n\
         assert square(3) == 10\n\
        \  at example/main.truss:10:3\n")

(* A test of a module whose one test passes. *)
let passes name source = test name (fun () -> expect_output source "test 0 passed\n")

let () =
  passes "loops, variables, and comparisons run"
    {|fn sum_to(limit: Int64) -> Int64 {
  var total = 0
  var i = 1
  while i <= limit {
    total += i
    i += 1
  }
  total
}

test "sums" {
  assert sum_to(10) == 55
}
|};
  passes "a counted for loop runs once per value"
    {|fn sum_below(limit: Int64) -> Int64 {
  var total = 0
  for i in 0..limit {
    total += i
  }
  total
}

test "sums" {
  assert sum_below(5) == 10
}
|};
  passes "records are built and read, and sums matched"
    {|type Point(x: Int64, y: Int64)

type Shape =
  | Circle(radius: Int64)
  | Rectangle(width: Int64, height: Int64)
  | Empty

fn area(shape: Shape) -> Int64 {
  match shape {
    Circle(radius) => 3 * radius * radius
    Rectangle(width, height) => width * height
    Empty => 0
  }
}

test "areas" {
  let origin = Point(x: 1, y: 2)
  assert origin.x + origin.y == 3
  assert area(Shape.Rectangle(width: 2, height: 5)) == 10
  assert area(Shape.Circle(radius: 2)) == 12
  assert area(Shape.Empty) == 0
}
|};
  passes "an if is a value, and a return leaves early"
    {|fn sign(value: Int64) -> Int64 {
  if value < 0 {
    return -1
  }
  if value == 0 { 0 } else { 1 }
}

test "signs" {
  assert sign(-5) == -1
  assert sign(0) == 0
  assert sign(7) == 1
}
|};
  passes "the standard library's Option methods run"
    {|fn first_positive(a: Int64, b: Int64) -> Option[Int64] {
  if a > 0 { Some(a) } else if b > 0 { Some(b) } else { None }
}

test "options" {
  assert first_positive(-1, b: 4) == Some(4)
  assert first_positive(-1, b: -2).is_none()
}
|}

let () =
  passes "lists are built, pushed onto, indexed, and looped over"
    {|fn total(items: List[Int64]) -> Int64 {
  var sum = 0
  for item in items {
    sum += item
  }
  sum
}

test "lists" {
  var items: List[Int64] = [1, 2, 3]
  mut items.push(4)
  assert items.length() == 4
  assert items[0] == 1
  assert items[3] == 4
  assert total(items) == 10
}
|};
  passes "a question mark returns an error early"
    {|type ParseError = Empty | TooLarge
  derives Equal

fn check(value: Int64) -> Result[Int64, ParseError] {
  if value > 100 { Err(ParseError.TooLarge) } else { Ok(value) }
}

fn doubled(value: Int64) -> Result[Int64, ParseError] {
  let checked = check(value)?
  Ok(checked * 2)
}

test "results" {
  assert doubled(4) == Ok(8)
  assert doubled(400) == Err(ParseError.TooLarge)
}
|}

let () =
  passes "a string interpolates its parts"
    {|test "interpolation" {
  let count = 3
  let name = "apples"
  assert "${count} ${name}" == "3 apples"
}
|};
  passes "a record is updated with with"
    {|type Point(x: Int64, y: Int64)
  derives Equal

test "updates" {
  let origin = Point(x: 0, y: 0)
  let moved = origin with (x: 5)
  assert moved == Point(x: 5, y: 0)
}
|};
  passes "a lambda reads its caller's locals"
    {|fn apply(value: Int64, transform: fn(Int64) -> Int64) -> Int64 {
  transform(value)
}

test "lambdas" {
  let offset = 10
  assert apply(5, transform: fn(value) { value + offset }) == 15
}
|}

let () =
  passes "integers display in decimal, negative ones too"
    {|test "display" {
  let small: Int8 = -128
  let large: UInt64 = 18446744073709551615
  let least: Int64 = -9223372036854775808
  assert "${small} ${large} ${least} ${0}" == "-128 18446744073709551615 -9223372036854775808 0"
}
|};
  passes "strings compare, order, and trim"
    {|test "strings" {
  let padded = "  hello \n"
  assert padded.trim().to_string() == "hello"
  assert "apple" < "banana"
  assert "apple" != "apples"
}
|}

let () =
  passes "constants are static data, worked out exactly"
    {|type Point(x: Int64, y: Int64)
  derives Equal

let seconds_per_day: Int64 = 24 * 60 * 60
let origin: Point = Point(x: -1, y: 2)
let greeting: String = "hello"
let primes: List[Int64] = [2, 3, 5, 7]

test "constants" {
  assert seconds_per_day == 86400
  assert origin == Point(x: -1, y: 2)
  assert greeting == "hello"
  assert primes[3] == 7
  assert primes.length() == 4
  assert ExitCode.failure.code == 1
}
|}

let () =
  passes "a named function is passed as a function value"
    {|fn double(value: Int64) -> Int64 {
  value * 2
}

fn apply(value: Int64, transform: fn(Int64) -> Int64) -> Int64 {
  transform(value)
}

test "named functions" {
  assert apply(21, transform: double) == 42
}
|};
  passes "a field left out takes its default"
    {|type Request(path: String, retries: Int64 = 3, secure: Bool = true)

test "defaults" {
  let request = Request(path: "/")
  assert request.retries == 3
  assert request.secure
  let other = Request(path: "/", retries: 5)
  assert other.retries == 5
}
|};
  passes "a parameter left out takes its default"
    {|fn connect(port: Int64 = 443, secure: Bool = true) -> Int64 {
  if secure { port } else { 0 }
}

test "parameter defaults" {
  assert connect() == 443
  assert connect(port: 80) == 80
  assert connect(secure: false) == 0
}
|};
  passes "an any value calls its implementation's method"
    {|trait Shape {
  fn area(self) -> Int64
}

type Square(side: Int64)
type Rectangle(width: Int64, height: Int64)

impl Shape for Square {
  fn area(self) -> Int64 { self.side * self.side }
}

impl Shape for Rectangle {
  fn area(self) -> Int64 { self.width * self.height }
}

fn total(shapes: List[any Shape]) -> Int64 {
  var sum = 0
  for shape in shapes {
    sum += shape.area()
  }
  sum
}

test "any" {
  let shapes: List[any Shape] = [any Square(side: 2), any Rectangle(width: 3, height: 4)]
  assert total(shapes) == 16
}
|}

let () =
  passes "a pulled cursor yields each value and then None"
    {|fn count_to(limit: Int64) yields Int64 {
  var i = 1
  while i <= limit {
    yield i
    i += 1
  }
}

test "cursors" {
  var first = count_to(3)
  var second = count_to(2)
  var total = 0
  while mut first.next() is Some(left) && mut second.next() is Some(right) {
    total += left * right
  }
  assert total == 5
  assert mut first.next() == None
  var third = count_to(1)
  assert mut third.next() == Some(1)
  assert mut third.next() == None
}
|};
  passes "a cursor dropped before it ends drops what it holds"
    {|fn words(prefix: own String) yields String {
  yield "${prefix} one"
  yield "${prefix} two"
}

test "dropped early" {
  var each = words("a${1}")
  assert mut each.next() == Some("a1 one")
  let _ = words("b${2}")
}
|};
  passes "sets and maps keep one of each key, in order"
    {|test "collections" {
  var colors: Set[String] = ["red", "green", "red"]
  assert colors.length() == 2
  assert colors.contains("green")
  assert !colors.contains("blue")
  mut colors.insert("blue")
  mut colors.insert("${1}")
  assert colors.length() == 4
  var ages: Map[String, Int64] = ["ada": 36, "alan": 41, "ada": 37]
  assert ages.length() == 2
  assert ages.contains("ada")
  mut ages.insert("grace", value: 85)
  mut ages.insert("alan", value: 42)
  assert ages.length() == 3
  let empty: Map[Int64, Int64] = [:]
  assert empty.length() == 0
}
|};
  passes "strings, constants, and ranges of constants are patterns"
    {|let limit: Int64 = 10
let origin: Int64 = 0

fn command(text: String) -> Int64 {
  match text {
    "quit" => 0
    "help" => 1
    _ => 2
  }
}

fn sized(value: Int64) -> String {
  match value {
    origin => "origin"
    1..limit => "small"
    _ => "large"
  }
}

fn word(text: StringSlice) -> Bool {
  text is "yes" | "y"
}

test "patterns" {
  assert command("quit") == 0
  assert command("help") == 1
  assert command("${1}") == 2
  assert sized(0) == "origin"
  assert sized(5) == "small"
  assert sized(10) == "large"
  assert word("y".slice())
  assert !word("no".slice())
}
|};
  passes "floats display as the shortest decimal that reads back"
    {|test "floats" {
  let half: Float64 = 0.5
  let third: Float32 = 0.25
  let big: Float64 = 1e300
  assert "${half} ${third} ${big} ${2.0}" == "0.5 0.25 1e+300 2.0"
}
|};
  passes "names an is test binds are used where it holds"
    {|fn describe(found: Option[String], limit: USize) -> String {
  if found is Some(text) && text.length() > limit {
    text
  } else if !(found is Some(_)) || limit == 0 {
    "nothing"
  } else {
    "short"
  }
}

fn longer(found: Option[String]) -> Bool {
  found is Some(text) && text.length() > 3
}

test "is" {
  assert describe(Some("long enough"), limit: 3) == "long enough"
  assert describe(Some("ab"), limit: 3) == "short"
  assert describe(None, limit: 3) == "nothing"
  assert longer(Some("four"))
  assert !longer(Some("abc"))
  assert !longer(None)
}
|};
  passes "a guard that fails leaves the value for the next arm"
    {|fn classify(found: Option[String]) -> String {
  match found {
    Some(text) if text.length() > 3 => text
    Some(text) => "short ${text}"
    None => "none"
  }
}

test "guards" {
  assert classify(Some("lengthy")) == "lengthy"
  assert classify(Some("ab")) == "short ab"
  assert classify(None) == "none"
}
|};
  passes "an expression a pattern looks into is evaluated once"
    {|fn next_index(counter: mut USize) -> USize {
  counter += 1
  counter - 1
}

test "once" {
  var counter: USize = 0
  let items = [Some(10), Some(20), None]
  let Some(first) = items[next_index(mut counter)] else {
    return
  }
  assert first == 10
  assert counter == 1
  if items[next_index(mut counter)] is Some(second) {
    assert second == 20
  }
  assert counter == 2
}
|}

(* Programs *)

(* Compiles a module with a [main] and runs it with the arguments. *)
let run_main ?(arguments = []) text =
  let _, compile = load text in
  match Compile.run_program compile ~main:(Top { module_ = example; name = "main" }) ~arguments with
  | Ok result -> result
  | Error message -> failwith message

let () =
  test "a program prints through the real console and exits with its code" (fun () ->
      let status, output, _ =
        run_main ~arguments:[ "one"; "two" ]
          {|fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  Console.print_line("hello")
  Console.print_line("${arguments.length()} arguments, then ${arguments[1]}")
  ExitCode(3)
}
|}
      in
      expect_int ~expected:3 status;
      expect_string ~expected:"hello\n3 arguments, then one\n" output)

(* The documents' examples: in every block that checks cleanly, each
   function that is not generic lowers, and each test passes or reaches a
   [todo]. Most blocks are excerpts, which do not check alone. *)
let () =
  let root = "../../.." in
  Sys.readdir root |> Array.to_list
  |> List.filter (fun name -> Filename.check_suffix name ".md")
  |> List.sort compare
  |> List.iter (fun name ->
      List.iteri
        (fun index text ->
          let database = Query.create () in
          Type_checker.load_standard database;
          Type_checker.load_package database ~name:"example" ~dependencies:[] [ (example, text) ];
          if Type_checker.diagnostics database example = [] then
            test
              (Printf.sprintf "%s block %d lowers, and its tests pass" name (index + 1))
              (fun () ->
                let database, compile = load text in
                List.iter
                  (fun (d : Resolve.Names.declaration) ->
                    match
                      (d.path, Query.demand database Interface.Environment.signature d.path)
                    with
                    | Top _, Some { generics = []; _ } ->
                        ignore
                          (Compile.compiled compile (Code { path = d.path; type_arguments = [] }))
                    | _ -> ())
                  (Query.demand database Resolve.Names.declarations example);
                if tests_of database <> [] then
                  String.split_on_char '\n' (run_source text)
                  |> List.iter (fun line ->
                      match String.split_on_char ' ' line with
                      | [ "test"; _; ("passed" | "incomplete") ] | [ "test"; _ ] -> ()
                      | [ "test"; _; outcome ] -> fail "a test %s" outcome
                      | _ -> ())))
        (Documents.truss_blocks (Documents.read (Filename.concat root name))))

let () = Harness.finish ()
