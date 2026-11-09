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
              | Echo { text; length; _ } -> operand_keys length (operand_keys text keys))
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
  | Evidence e -> e.evidence_key

let compiled_references env : Lir.compiled -> Instance.key list = function
  | Code t -> references env t
  | Data _ -> []
  | Table t -> List.map fst t.entries
  | Evidence e -> e.table :: e.outer

let reachable env ~lookup roots =
  (* Breadth-first, so an instance's number depends only on the shape of
     the walk up to it. *)
  let rec walk seen found = function
    | [] -> List.rev found
    | key :: queue ->
        if List.exists (Instance.equal key) seen then walk seen found queue
        else
          let compiled = lookup key in
          walk (key :: seen) (compiled :: found) (queue @ compiled_references env compiled)
  in
  walk [] [] roots

let test_key env ~lookup root =
  let instances = reachable env ~lookup [ root ] in
  let number_of_instance key =
    let rec find i = function
      | [] ->
          invalid_arg ("Reachable.test_key: an unreachable reference to " ^ Instance.to_string key)
      | compiled :: rest ->
          if Instance.equal (compiled_key compiled) key then i else find (i + 1) rest
    in
    find 0 instances
  in
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
  let instance key = Cbor.Array [ Text "instance"; Cbor.int (number_of_instance key) ] in
  let encoded =
    List.map
      (function
        | Lir.Code i -> Lir.encode ~path ~instance (Lir.canonical_instance i)
        | Data d -> Lir.encode_data ~path ~instance d
        | Table t -> Lir.encode_table ~path ~instance t
        | Evidence e -> Lir.encode_evidence ~path ~instance e)
      instances
  in
  (* The target is in the key because [USize] is a [typedef] in the C, so
     the LIR is the same for every width while results such as
     [USize.maximum] are not. *)
  let target = Memory_layout.target env in
  Blake3.hash
    (Cbor.encode
       (Cbor.Array
          [
            Text "truss test";
            Cbor.int Lir.version;
            Cbor.Array [ Cbor.int target.pointer_bytes; Cbor.int target.usize_bytes ];
            Cbor.Array encoded;
          ]))
