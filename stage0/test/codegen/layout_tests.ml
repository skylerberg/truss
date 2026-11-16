let () =
  Codegen_support.test "fields are placed by alignment, largest first, then by name" (fun () ->
      let extra =
        [
          ( "Mixed",
            Memory_layout.Record
              [
                Codegen_support.field "small" Codegen_support.uint8;
                Codegen_support.field "large" Codegen_support.int64;
                Codegen_support.field "flag" Codegen_support.bool;
              ] );
        ]
      in
      Codegen_support.expect_string ~expected:"16/8 struct(large@0 flag@8 small@9) niche flag 2+254"
        (Codegen_support.describe ~extra (Codegen_support.named "Mixed")));
  Codegen_support.test "reordering fields in the source does not change the layout" (fun () ->
      let first =
        [
          ( "Point",
            Memory_layout.Record
              [
                Codegen_support.field "x" Codegen_support.float64;
                Codegen_support.field "y" Codegen_support.float64;
                Codegen_support.field "z" Codegen_support.uint8;
              ] );
        ]
      in
      let second =
        [
          ( "Point",
            Memory_layout.Record
              [
                Codegen_support.field "z" Codegen_support.uint8;
                Codegen_support.field "y" Codegen_support.float64;
                Codegen_support.field "x" Codegen_support.float64;
              ] );
        ]
      in
      Codegen_support.expect_string
        ~expected:(Codegen_support.describe ~extra:first (Codegen_support.named "Point"))
        (Codegen_support.describe ~extra:second (Codegen_support.named "Point")));
  Codegen_support.test "a record with one field has the field's size and alignment" (fun () ->
      let extra =
        [
          ("UserId", Memory_layout.Record [ Codegen_support.field "number" Codegen_support.int64 ]);
        ]
      in
      let wrapped = Codegen_support.layout ~extra (Codegen_support.named "UserId") in
      Codegen_support.expect_int ~expected:8 wrapped.size;
      Codegen_support.expect_int ~expected:8 wrapped.alignment);
  Codegen_support.test "fields of zero size take no room" (fun () ->
      let extra =
        [
          ( "Holder",
            Memory_layout.Record
              [
                Codegen_support.field "nothing" Codegen_support.unit;
                Codegen_support.field "count" Codegen_support.int64;
              ] );
        ]
      in
      Codegen_support.expect_string ~expected:"8/8 struct(count@0)"
        (Codegen_support.describe ~extra (Codegen_support.named "Holder")));
  Codegen_support.test "a record with no fields has zero size" (fun () ->
      Codegen_support.expect_string ~expected:"0/1 zero"
        (Codegen_support.describe Codegen_support.unit));
  Codegen_support.test "a sum type with no fields is just its tag" (fun () ->
      let extra =
        [
          ( "Ordering",
            Memory_layout.Sum
              [
                Codegen_support.variant "Less" [];
                Codegen_support.variant "Equal" [];
                Codegen_support.variant "Greater" [];
              ] );
        ]
      in
      Codegen_support.expect_string ~expected:"1/1 tag(UInt8: Less Equal Greater) niche . 3+253"
        (Codegen_support.describe ~extra (Codegen_support.named "Ordering")));
  Codegen_support.test "a sum type with one variant offers no niche when its field's niche is full"
    (fun () ->
      let full =
        Memory_layout.Sum
          (List.init 256 (fun index -> Codegen_support.variant (Printf.sprintf "V%d" index) []))
      in
      let extra =
        [
          ("Full", full);
          ( "Wrapper",
            Sum
              [
                Codegen_support.variant "Only"
                  [ Codegen_support.field "full" (Codegen_support.named "Full") ];
              ] );
        ]
      in
      Codegen_support.expect_string ~expected:"1/1 niche-encoded(Only;  at nothing)"
        (Codegen_support.describe ~extra (Codegen_support.named "Wrapper")));
  Codegen_support.test "a tag is the smallest unsigned integer that numbers every variant"
    (fun () ->
      let many =
        Memory_layout.Sum
          (List.init 300 (fun index -> Codegen_support.variant (Printf.sprintf "V%d" index) []))
      in
      Codegen_support.expect_int ~expected:2
        (Codegen_support.layout ~extra:[ ("Many", many) ] (Codegen_support.named "Many")).size);
  Codegen_support.test "a sum type is a tag followed by the largest variant's fields" (fun () ->
      let extra =
        [
          ( "Shape",
            Memory_layout.Sum
              [
                Codegen_support.variant "Circle"
                  [ Codegen_support.field "radius" Codegen_support.float64 ];
                Codegen_support.variant "Square"
                  [
                    Codegen_support.field "side" Codegen_support.float64;
                    Codegen_support.field "corner" Codegen_support.int64;
                  ];
                Codegen_support.variant "Empty" [];
              ] );
        ]
      in
      Codegen_support.expect_string
        ~expected:"24/8 tagged(UInt8, payload@8: Circle Square Empty) niche tag 3+253"
        (Codegen_support.describe ~extra (Codegen_support.named "Shape")));
  Codegen_support.test "Option of a List has no tag" (fun () ->
      Codegen_support.expect_string ~expected:"24/8 niche-encoded(Some; None=0 at value.buffer)"
        (Codegen_support.describe
           (Codegen_support.option (Codegen_support.list Codegen_support.int64))));
  Codegen_support.test "Option of a Bool is one byte" (fun () ->
      Codegen_support.expect_string
        ~expected:"1/1 niche-encoded(Some; None=2 at value) niche value 3+253"
        (Codegen_support.describe (Codegen_support.option Codegen_support.bool)));
  Codegen_support.test "Option of a Character is the size of a Character" (fun () ->
      Codegen_support.expect_int ~expected:4
        (Codegen_support.layout (Codegen_support.option Codegen_support.character)).size);
  Codegen_support.test "Option of an Option of a Bool uses the next spare value" (fun () ->
      Codegen_support.expect_string
        ~expected:"1/1 niche-encoded(Some; None=3 at value.value) niche value.value 4+252"
        (Codegen_support.describe
           (Codegen_support.option (Codegen_support.option Codegen_support.bool))));
  Codegen_support.test "Option of a sum with no fields uses the tag's spare values" (fun () ->
      let extra =
        [
          ( "Bit",
            Memory_layout.Sum
              [ Codegen_support.variant "Zero" []; Codegen_support.variant "One" [] ] );
        ]
      in
      Codegen_support.expect_string
        ~expected:"1/1 niche-encoded(Some; None=2 at value) niche value 3+253"
        (Codegen_support.describe ~extra (Codegen_support.option (Codegen_support.named "Bit"))));
  Codegen_support.test "Option of an Int64 has a tag, since every value is in use" (fun () ->
      Codegen_support.expect_string
        ~expected:"16/8 tagged(UInt8, payload@8: Some None) niche tag 2+254"
        (Codegen_support.describe (Codegen_support.option Codegen_support.int64)));
  Codegen_support.test "an indirect variant holds one pointer" (fun () ->
      let tree =
        Memory_layout.Sum
          [
            Codegen_support.variant "Leaf" [];
            Codegen_support.variant ~indirect:true "Node"
              [
                Codegen_support.field "left" (Codegen_support.named "Tree");
                Codegen_support.field "value" Codegen_support.int64;
                Codegen_support.field "right" (Codegen_support.named "Tree");
              ];
          ]
      in
      Codegen_support.expect_string ~expected:"8/8 niche-encoded(Node; Leaf=0 at .)"
        (Codegen_support.describe ~extra:[ ("Tree", tree) ] (Codegen_support.named "Tree")));
  Codegen_support.test "an indirect variant's block holds its fields" (fun () ->
      let tree =
        Memory_layout.Sum
          [
            Codegen_support.variant "Leaf" [];
            Codegen_support.variant ~indirect:true "Node"
              [
                Codegen_support.field "left" (Codegen_support.named "Tree");
                Codegen_support.field "value" Codegen_support.int64;
                Codegen_support.field "right" (Codegen_support.named "Tree");
              ];
          ]
      in
      let env =
        Memory_layout.create Codegen_support.host
          ~shape_of:(Codegen_support.shapes [ ("Tree", tree) ])
      in
      Codegen_support.expect_string ~expected:"24/8 struct(left@0 right@8 value@16)"
        (Memory_layout.For_testing.to_string
           (Memory_layout.lay_out_block env (Codegen_support.named "Tree") "Node")));
  Codegen_support.test "an Array holds its elements in place" (fun () ->
      Codegen_support.expect_string ~expected:"32/1 array(32 x 1/1 UInt8)"
        (Codegen_support.describe (Codegen_support.array Codegen_support.uint8 32)));
  Codegen_support.test "a List holds a pointer and two 64-bit UInt64 fields" (fun () ->
      Codegen_support.expect_int ~expected:24
        (Codegen_support.layout (Codegen_support.list Codegen_support.int64)).size);
  Codegen_support.test "a variant whose fields have zero size counts as having none" (fun () ->
      Codegen_support.expect_string ~expected:"1/1 tag(UInt8: Some None) niche . 2+254"
        (Codegen_support.describe (Codegen_support.option Codegen_support.unit)));
  Codegen_support.test "a sum type with one variant has no tag" (fun () ->
      let extra =
        [
          ( "Only",
            Memory_layout.Sum
              [
                Codegen_support.variant "Only"
                  [ Codegen_support.field "count" Codegen_support.int64 ];
              ] );
        ]
      in
      Codegen_support.expect_string ~expected:"8/8 niche-encoded(Only;  at nothing)"
        (Codegen_support.describe ~extra (Codegen_support.named "Only")));
  Codegen_support.test "Never has zero size" (fun () ->
      Codegen_support.expect_string ~expected:"0/1 zero" (Codegen_support.describe Never));
  Codegen_support.test "a variant's discriminant is its tag value or its niche value" (fun () ->
      let layout = Codegen_support.layout (Codegen_support.option Codegen_support.bool) in
      (match Memory_layout.compute_discriminant layout "None" with
      | Niche_value { value; _ } when Z.equal value (Z.of_int 2) -> ()
      | _ -> Codegen_support.fail "None is not stored as 2");
      match Memory_layout.compute_discriminant layout "Some" with
      | Not_niche { stop; _ } when Z.equal stop (Z.of_int 3) -> ()
      | _ ->
          Codegen_support.fail "Some is not the dataful variant, outside the niche values below 3")

let () =
  let int64 = Ground.make_builtin Int64 in
  let bool = Ground.make_builtin Bool in
  let list element = Codegen_support.standard "list" "List" ~arguments:[ Type element ] () in
  let option value = Codegen_support.standard "option" "Option" ~arguments:[ Type value ] () in
  Codegen_support.test "the standard library's Option of a List has no tag" (fun () ->
      Codegen_support.expect_string
        ~expected:"24/8 niche-encoded(Some; None=0 at value.storage.buffer)"
        (Codegen_support.standard_layout (option (list int64))));
  Codegen_support.test "the standard library's Option of a Bool is one byte" (fun () ->
      Codegen_support.expect_int ~expected:1
        (Memory_layout.of_type
           (Memory_layout.create Codegen_support.host
              ~shape_of:(Monomorphic.compute_shape Codegen_support.standard_context))
           (option bool))
          .size);
  Codegen_support.test "a String is its storage's buffer, length, and capacity" (fun () ->
      Codegen_support.expect_string ~expected:"24/8 struct(storage@0) niche storage.buffer 0+1"
        (Codegen_support.standard_layout (Codegen_support.standard "text" "String" ())))
