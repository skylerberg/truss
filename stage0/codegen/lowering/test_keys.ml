let derive_test_key = Blake3.derive_key ~context:"truss 2026-11-23 test key"
let encode_test_key fields = derive_test_key (Cbor.encode (Cbor.Array fields))

let derive ~read_hash_and_references ~read_known_key component =
  let is_member item = List.exists (Lowered.Item.equal item) component in
  let encode_member item =
    let fragment_hash, references = read_hash_and_references item in
    Cbor.Array
      [
        Bytes fragment_hash;
        Cbor.Array
          (List.filter_map
             (fun reference ->
               if is_member reference then None else Some (Cbor.Bytes (read_known_key reference)))
             references);
      ]
  in
  match component with
  | [ item ] -> [ (item, encode_test_key [ Text "item"; encode_member item ]) ]
  | component ->
      let group =
        encode_test_key
          [
            Text "group";
            Cbor.Array (List.map encode_member (List.sort Lowered.Item.compare component));
          ]
      in
      List.map
        (fun member ->
          ( member,
            encode_test_key
              [ Text "member"; Bytes group; Bytes (fst (read_hash_and_references member)) ] ))
        component
