(* Data layout, and the shapes of the standard library's types. *)

open Memory_layout
open Codegen_support

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
        (to_string (Memory_layout.block env (named "Tree") "Node")));
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
          ~representation:(Monomorphic.representation standard_context)
          ~usize:(Monomorphic.builtin USize) ()
      in
      if Glue.trivial glue (list int64) then fail "a List is trivial";
      if not (Glue.trivial glue (option int64)) then fail "an Option of an Int64 is not trivial")
