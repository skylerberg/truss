module Table = Hashtbl.Make (struct
  type t = Instance.key

  let equal = Instance.equal
  let hash key = Hashtbl.hash_param 64 256 key
end)

let bug format = Compiler_bug.bug ~stage:"Reachable" format

let walk ~lookup ~by_call roots =
  let seen = Table.create 256 in
  let queue = Queue.create () in
  List.iter (fun root -> Queue.add (root, []) queue) roots;
  let reached = ref [] in
  let tables = Hashtbl.create 16 and called = Hashtbl.create 16 in
  let entry table (slot, way) =
    match List.nth_opt (Emit_c.references table) slot with
    | Some key -> Queue.add (key, way) queue
    | None -> bug "a call of method %d of %s" slot (Instance.to_string (Emit_c.key table))
  in
  while not (Queue.is_empty queue) do
    let key, way = Queue.pop queue in
    if not (Table.mem seen key) then begin
      Table.replace seen key ();
      let compiled = lookup key in
      let way = key :: way in
      reached := (compiled, List.rev way) :: !reached;
      let all () =
        List.iter (fun next -> Queue.add (next, way) queue) (Emit_c.references compiled)
      in
      match Emit_c.table compiled with
      | Some (Some capability) when by_call ->
          Hashtbl.add tables capability compiled;
          List.iter (entry compiled) (List.rev (Hashtbl.find_all called capability))
      | _ when by_call ->
          List.iter
            (fun (capability, slot) ->
              if not (List.mem_assoc slot (Hashtbl.find_all called capability)) then begin
                Hashtbl.add called capability (slot, way);
                List.iter
                  (fun table -> entry table (slot, way))
                  (List.rev (Hashtbl.find_all tables capability))
              end)
            (Emit_c.calls compiled);
          all ()
      | _ -> all ()
    end
  done;
  List.rev !reached

let running ~lookup roots = walk ~lookup ~by_call:true roots
let reachable ~lookup roots = List.map fst (walk ~lookup ~by_call:false roots)
let derive_own_hash = Blake3.derive_key ~context:"truss 2026-11-12 instance own hash"
let own_hash compiled = derive_own_hash (Emit_c.text compiled)

module Keys = Map.Make (struct
  type t = Instance.key

  let compare = Instance.compare
end)

let derive_reach_key = Blake3.derive_key ~context:"truss 2026-11-12 reach key"
let key_of parts = derive_reach_key (Cbor.encode (Cbor.Array parts))

let unit_key ~own reached =
  key_of [ Text "unit"; Bytes own; Cbor.Array (List.map (fun key -> Cbor.Bytes key) reached) ]

let group_key ~link ~deep ~members start =
  let inside key = List.exists (Instance.equal key) members in
  let order = Table.create 8 in
  let rec walk visited = function
    | [] -> List.rev visited
    | key :: queue ->
        if Table.mem order key then walk visited queue
        else begin
          Table.replace order key (Table.length order);
          let own, references = link key in
          walk ((own, references) :: visited) (queue @ List.filter inside references)
        end
  in
  let walked = walk [] [ start ] in
  key_of
    [
      Text "group";
      Cbor.Array
        (List.map
           (fun (own, references) ->
             Cbor.Array
               [
                 Bytes own;
                 Cbor.Array
                   (List.map
                      (fun key ->
                        if inside key then Cbor.Array [ Text "in"; Cbor.int (Table.find order key) ]
                        else Cbor.Array [ Text "out"; Bytes (deep key) ])
                      references);
               ])
           walked);
    ]

let component_keys ~link ~deep members =
  match members with
  | [ key ] ->
      let own, references = link key in
      [ (key, unit_key ~own (List.map deep references)) ]
  | members -> List.map (fun member -> (member, group_key ~link ~deep ~members member)) members
