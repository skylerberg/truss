let add key keys = if List.exists (Instance.equal key) keys then keys else key :: keys

let rec place_keys (place : Lir.place) keys =
  let keys = match place.root with Static { key; _ } -> add key keys | Local _ -> keys in
  List.fold_left
    (fun keys -> function Lir.Index o -> operand_keys o keys | _ -> keys)
    keys place.projections

and operand_keys (operand : Lir.operand) keys =
  match operand with
  | Copy place | Move place | Address { place; _ } | Moved_address place -> place_keys place keys
  | Constant (Symbol_address key) -> add key keys
  | Constant _ -> keys

let function_ref_keys (f : Lir.function_ref) keys =
  match f with Instance key -> add key keys | Nested _ -> keys

let rvalue_keys (rvalue : Lir.rvalue) keys =
  match rvalue with
  | Use o | Unary (_, o) | Convert (o, _) -> operand_keys o keys
  | Binary (_, a, b) -> operand_keys b (operand_keys a keys)
  | Build { fields; _ } -> List.fold_left (fun keys (_, o) -> operand_keys o keys) keys fields
  | Is_variant (place, _) -> place_keys place keys
  | Function_value { code; environment } ->
      Option.fold ~none:keys ~some:(fun e -> operand_keys e keys) environment
      |> function_ref_keys code

let references env (instance : Lir.t) =
  let environment n = instance.nested.(n).environment in
  let in_function keys (f : Lir.function_) =
    Array.fold_left
      (fun keys (block : Lir.basic_block) ->
        let keys =
          List.fold_left
            (fun keys (statement : Lir.statement) ->
              match statement with
              | Assign (place, rvalue) -> rvalue_keys rvalue (place_keys place keys)
              | Call { target; arguments; result } -> (
                  let keys =
                    match target with
                    | Direct { function_; _ } -> function_ref_keys function_ keys
                    | _ ->
                        List.fold_left
                          (fun keys o -> operand_keys o keys)
                          keys (Lir.target_operands target)
                  in
                  let keys = List.fold_left (fun keys o -> operand_keys o keys) keys arguments in
                  match result with
                  | Returned p | Written p -> place_keys p keys
                  | Discarded -> keys)
              | Drop place -> (
                  let keys = place_keys place keys in
                  match Lir.place_type env ~environment f place with
                  | Some (Value ty) -> add (Drop ty) keys
                  | _ -> keys)
              | Free_block { place; _ } -> place_keys place keys
              | Echo { text; length; _ } -> operand_keys length (operand_keys text keys)
              | Region _ | Regions_end _ -> keys
              | Fork { branches } ->
                  List.fold_left (fun keys (_, o) -> operand_keys o keys) keys branches
              | Fork_range { environment; first; last; _ } ->
                  operand_keys last (operand_keys first (operand_keys environment keys)))
            keys block.statements
        in
        match block.terminator with
        | Switch { value; _ } -> operand_keys value keys
        | Switch_variant { place; _ } -> place_keys place keys
        | Return value -> Option.fold ~none:keys ~some:(fun o -> operand_keys o keys) value
        | Fail { message; length; _ } -> operand_keys length (operand_keys message keys)
        | Yield { value; _ } -> operand_keys value keys
        | Goto _ | Unreachable -> keys)
      keys f.blocks
  in
  let keys = Array.fold_left in_function (in_function [] instance.main) instance.nested in
  List.filter (fun key -> not (Instance.equal key instance.key)) (List.rev keys)

let compiled_key : Lir.compiled -> Instance.key = function
  | Code t -> t.key
  | Data d -> d.data_key
  | Table t -> t.table_key

let compiled_references env : Lir.compiled -> Instance.key list = function
  | Code t -> references env t
  | Data _ -> []
  | Table t -> List.map fst t.entries

module Table = Hashtbl.Make (struct
  type t = Instance.key

  let equal = Instance.equal
  let hash key = Hashtbl.hash_param 64 256 key
end)

let bug format = Compiler_bug.bug ~stage:"Reachable" format

(* The methods of capabilities an instance calls: each capability, with the
   method's place among its methods. *)
let methods_called (instance : Lir.t) =
  let in_function found (f : Lir.function_) =
    Array.fold_left
      (fun found (block : Lir.basic_block) ->
        List.fold_left
          (fun found (statement : Lir.statement) ->
            match statement with
            | Call { target = Evidence_call { capability; slot; _ }; _ } ->
                (capability, slot) :: found
            | _ -> found)
          found block.statements)
      found f.blocks
  in
  List.rev (Array.fold_left in_function (in_function [] instance.main) instance.nested)

(* Breadth-first, so an instance's number depends only on the shape of the
   walk up to it. Each key in the queue carries the way it was reached,
   nearest first. With [by_call], an entry of a capability's table is
   reached by a call of its method, with the caller's way, and only once
   the table is reached too; without, a table reaches its every entry. *)
let walk env ~lookup ~by_call roots =
  let seen = Table.create 256 in
  let queue = Queue.create () in
  List.iter (fun root -> Queue.add (root, []) queue) roots;
  let found = ref [] in
  let tables = Hashtbl.create 16 and called = Hashtbl.create 16 in
  let entry (table : Lir.table) (slot, way) =
    match List.nth_opt table.entries slot with
    | Some (key, _) -> Queue.add (key, way) queue
    | None -> bug "a call of method %d of %s" slot (Instance.to_string table.table_key)
  in
  while not (Queue.is_empty queue) do
    let key, way = Queue.pop queue in
    if not (Table.mem seen key) then begin
      Table.replace seen key ();
      let compiled = lookup key in
      let way = key :: way in
      found := (compiled, List.rev way) :: !found;
      let all () =
        List.iter (fun next -> Queue.add (next, way) queue) (compiled_references env compiled)
      in
      match compiled with
      | Table ({ capability = Some capability; _ } as table) when by_call ->
          Hashtbl.add tables capability table;
          List.iter (entry table) (List.rev (Hashtbl.find_all called capability))
      | Code instance when by_call ->
          List.iter
            (fun (capability, slot) ->
              if not (List.mem_assoc slot (Hashtbl.find_all called capability)) then begin
                Hashtbl.add called capability (slot, way);
                List.iter
                  (fun table -> entry table (slot, way))
                  (List.rev (Hashtbl.find_all tables capability))
              end)
            (methods_called instance);
          all ()
      | _ -> all ()
    end
  done;
  List.rev !found

let reached env ~lookup roots = walk env ~lookup ~by_call:false roots
let running env ~lookup roots = walk env ~lookup ~by_call:true roots
let reachable env ~lookup roots = List.map fst (reached env ~lookup roots)

(* The hash of what an instance compiles to, by itself: its encoding with
   each instance it refers to written as that instance's place among
   [references], itself as a mark, and each path as a number given in the
   order paths are first met. So the hash holds no name, and renaming or
   moving a definition changes no hash. *)
let own_hash ~references compiled =
  let self = compiled_key compiled in
  let paths = ref [] in
  let path p =
    let rec find i = function
      | [] ->
          paths := !paths @ [ p ];
          i
      | q :: rest -> if Path.equal p q then i else find (i + 1) rest
    in
    Cbor.int (find 0 !paths)
  in
  let instance key =
    if Instance.equal key self then Cbor.Array [ Text "self" ]
    else
      let rec find i = function
        | [] ->
            Compiler_bug.bug ~stage:"Reachable" "a reference that was not collected, to %s"
              (Instance.to_string key)
        | other :: rest -> if Instance.equal other key then i else find (i + 1) rest
      in
      Cbor.Array [ Text "instance"; Cbor.int (find 0 references) ]
  in
  let encoded =
    match compiled with
    | Lir.Code i -> Lir.encode ~path ~instance (Lir.canonical_instance i)
    | Data d -> Lir.encode_data ~path ~instance d
    | Table t -> Lir.encode_table ~path ~instance t
  in
  Blake3.hash (Cbor.encode encoded)

module Keys = Map.Make (struct
  type t = Instance.key

  let compare = Instance.compare
end)

(* The groups of instances that reach each other, among everything the
   roots reach: for each instance of such a group, the group's instances in
   order. An instance that refers only to itself is no group, since its own
   hash marks that. Tarjan's algorithm, with a stack of its own in place of
   recursion, so that a long chain of calls is no deeper than a short one. *)
let groups ~edges roots =
  let counter = ref 0 in
  let number = Table.create 1024 and low = Table.create 1024 in
  let waiting = Table.create 1024 in
  let stack = ref [] in
  let found = ref Keys.empty in
  let work = Stack.create () in
  let enter key =
    Table.replace number key !counter;
    Table.replace low key !counter;
    incr counter;
    stack := key :: !stack;
    Table.replace waiting key ();
    Stack.push (key, ref (edges key)) work
  in
  let lower key to_ = if to_ < Table.find low key then Table.replace low key to_ in
  let leave key =
    if Table.find low key = Table.find number key then begin
      let rec pop members =
        match !stack with
        | [] -> members
        | top :: rest ->
            stack := rest;
            Table.remove waiting top;
            let members = top :: members in
            if Instance.equal top key then members else pop members
      in
      match pop [] with
      | [] | [ _ ] -> ()
      | members ->
          let members = List.sort Instance.compare members in
          found := List.fold_left (fun found member -> Keys.add member members found) !found members
    end
  in
  List.iter
    (fun root ->
      if not (Table.mem number root) then begin
        enter root;
        while not (Stack.is_empty work) do
          let key, rest = Stack.top work in
          match !rest with
          | next :: more ->
              rest := more;
              if not (Table.mem number next) then enter next
              else if Table.mem waiting next then lower key (Table.find number next)
          | [] ->
              ignore (Stack.pop work);
              if not (Stack.is_empty work) then lower (fst (Stack.top work)) (Table.find low key);
              leave key
        done
      end)
    roots;
  !found

let key_of parts = Blake3.hash (Cbor.encode (Cbor.Array parts))

(* The key of everything an instance that is in no group can reach: its own
   hash, and the key of each instance it refers to, in order. *)
let unit_key ~own reached =
  key_of [ Text "unit"; Bytes own; Cbor.Array (List.map (fun key -> Cbor.Bytes key) reached) ]

(* The key of everything an instance of a group can reach. The group's
   instances are numbered in the order a walk from the instance first
   reaches them, and each is written as its own hash and what it refers to:
   a number for an instance of the group, and the key of everything it can
   reach for any other. [link] gives an instance's own hash and what it
   refers to, and [deep] the key of an instance outside the group. *)
let group_key ~link ~deep ~members start =
  let inside key = List.exists (Instance.equal key) members in
  let order = Table.create 8 in
  let rec walk found = function
    | [] -> List.rev found
    | key :: queue ->
        if Table.mem order key then walk found queue
        else begin
          Table.replace order key (Table.length order);
          let own, references = link key in
          walk ((own, references) :: found) (queue @ List.filter inside references)
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
