module Instance_table = Hashtbl.Make (Instance)

let derive_test_key = Blake3.derive_key ~context:"truss 2026-11-12 reach key"
let encode_test_key fields = derive_test_key (Cbor.encode (Cbor.Array fields))

let derive_cycle_member_key ~read_known_key members start =
  let visit_order = Instance_table.create 8 in
  let rec visit visited = function
    | [] -> List.rev visited
    | key :: queue ->
        if Instance_table.mem visit_order key then visit visited queue
        else begin
          Instance_table.replace visit_order key (Instance_table.length visit_order);
          let fragment_hash, references = Instance_table.find members key in
          visit
            ((fragment_hash, references) :: visited)
            (queue @ List.filter (Instance_table.mem members) references)
        end
  in
  encode_test_key
    [
      Text "group";
      Cbor.Array
        (List.map
           (fun (fragment_hash, references) ->
             Cbor.Array
               [
                 Bytes fragment_hash;
                 Cbor.Array
                   (List.map
                      (fun reference ->
                        if Instance_table.mem members reference then
                          Cbor.Array
                            [ Text "in"; Cbor.int (Instance_table.find visit_order reference) ]
                        else Cbor.Array [ Text "out"; Bytes (read_known_key reference) ])
                      references);
               ])
           (visit [] [ start ]));
    ]

let derive ~read_hash_and_references ~read_known_key component =
  match component with
  | [ key ] ->
      let fragment_hash, references = read_hash_and_references key in
      [
        ( key,
          encode_test_key
            [
              Text "unit";
              Bytes fragment_hash;
              Cbor.Array
                (List.map (fun reference -> Cbor.Bytes (read_known_key reference)) references);
            ] );
      ]
  | component ->
      let members = Instance_table.create 8 in
      List.iter
        (fun member -> Instance_table.replace members member (read_hash_and_references member))
        component;
      List.map
        (fun member -> (member, derive_cycle_member_key ~read_known_key members member))
        component
