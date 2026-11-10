let bug format = Compiler_bug.bug ~stage:"Verify" format
let environment (instance : Lir.t) n = instance.nested.(n).environment

let each_function (instance : Lir.t) f =
  f "the function" instance.main;
  Array.iteri (fun n nested -> f (Printf.sprintf "nested function %d" n) nested) instance.nested

let each_statement (f : Lir.function_) visit =
  Array.iter (fun (block : Lir.basic_block) -> List.iter visit block.statements) f.blocks

(* How many arguments a call passes: what its target is given first, the
   pointer a large result is written through, and each argument that has a
   size. *)
let passed env (instance : Lir.t) (f : Lir.function_) (target : Lir.target) arguments
    (result : Lir.destination) =
  let sized (operand : Lir.operand) =
    match operand with
    | Copy place | Move place ->
        Lir.place_type env ~environment:(environment instance) f place <> None
    | Address _ | Moved_address _ | Constant _ -> true
  in
  (match target with
    | Direct _ | Intrinsic _ -> 0
    | Indirect _ | Evidence_call _ | Table_call _ -> 1)
  + (match result with Written _ -> 1 | Returned _ | Discarded -> 0)
  + List.length (List.filter sized arguments)

let target_signature (instance : Lir.t) : Lir.target -> Lir.signature option = function
  | Direct { function_ = Nested n; signature } ->
      if n < 0 || n >= Array.length instance.nested then bug "a call of nested function %d" n;
      if not (Lir.equal_signature signature (Lir.signature instance.nested.(n))) then
        bug "a call of nested function %d with a signature it does not have" n;
      Some signature
  | Direct { signature; _ }
  | Indirect { signature; _ }
  | Evidence_call { signature; _ }
  | Table_call { signature; _ } ->
      Some signature
  | Intrinsic _ -> None

let function_ env (instance : Lir.t) what (f : Lir.function_) =
  let blocks = Array.length f.blocks and locals = Array.length f.locals in
  let bug format = Printf.ksprintf (fun message -> bug "%s: %s" what message) format in
  let local l = if l < 0 || l >= locals then bug "local %d, of %d" l locals in
  List.iter local f.parameters;
  Option.iter
    (fun l -> if not (List.mem l f.parameters) then bug "a result pointer that is no parameter")
    f.written_result;
  let visitor : Lir.visitor =
    {
      place =
        (fun place ->
          (match place.root with Local l -> local l | Static _ -> ());
          ignore (Lir.place_type env ~environment:(environment instance) f place));
      operand = ignore;
    }
  in
  let nested_value : Lir.statement -> unit = function
    | Assign (_, Function_value { code = Nested n; _ }) ->
        if n < 0 || n >= Array.length instance.nested then bug "a value of nested function %d" n
    | _ -> ()
  in
  (* The emitter leaves out a field that has no size, which it knows by
     finding no such field in the layout, so a field the type does not have
     would be left out too. *)
  let built : Lir.statement -> unit = function
    | Assign (_, Build { ty; variant; fields }) when (Memory_layout.of_type env ty).size > 0 -> (
        let has =
          match (Memory_layout.shape env ty, variant) with
          | Record members, None -> Some (List.map fst members)
          | Sum variants, Some name ->
              Option.map
                (fun (v : Memory_layout.variant_shape) -> List.map fst v.fields)
                (List.find_opt (fun (v : Memory_layout.variant_shape) -> v.name = name) variants)
          | _ -> None
        in
        match has with
        | None -> bug "a value of %s built as what it is not" (Ground.to_string ty)
        | Some names ->
            List.iter
              (fun (name, _) ->
                if not (List.mem name names) then
                  bug "a value of %s built with a field %s, which it does not have"
                    (Ground.to_string ty) name)
              fields)
    | _ -> ()
  in
  Array.iter
    (fun (block : Lir.basic_block) ->
      List.iter
        (fun (statement : Lir.statement) ->
          Lir.visit_statement visitor statement;
          nested_value statement;
          built statement;
          match statement with
          | Call { target; arguments; result } ->
              Option.iter
                (fun (signature : Lir.signature) ->
                  let given = passed env instance f target arguments result in
                  let taken = List.length signature.parameters in
                  if given <> taken then
                    bug "a call that passes %d arguments to a target that takes %d" given taken)
                (target_signature instance target)
          | Assign _ | Drop _ | Echo _ | Free_block _ -> ())
        block.statements;
      Lir.visit_terminator visitor block.terminator;
      List.iter
        (fun b -> if b < 0 || b >= blocks then bug "block %d, of %d" b blocks)
        (Lir.successors block.terminator);
      match (block.terminator, f.result) with
      | Yield _, _ -> bug "a yield that yield lowering left in place"
      | Return None, Some _ -> bug "a return of nothing from a function with a result"
      | Return (Some _), None -> bug "a return of a value from a function with no result"
      | _ -> ())
    f.blocks

let instance env (instance : Lir.t) = each_function instance (function_ env instance)

let links env ~find (compiled : Lir.compiled) =
  let code key =
    match find key with
    | Some (Lir.Code callee) -> callee
    | Some _ -> bug "%s is called, and is not code" (Instance.to_string key)
    | None -> bug "%s is called, and is not built" (Instance.to_string key)
  in
  let has key (signature : Lir.signature) =
    if not (Lir.equal_signature signature (Lir.signature (code key).main)) then
      bug "%s is named with a signature it does not have" (Instance.to_string key)
  in
  let reaches key ~is what =
    match find key with
    | Some found when is found -> ()
    | _ -> bug "the address of %s, which is not %s" (Instance.to_string key) what
  in
  let is_table = function Lir.Table _ -> true | _ -> false
  and is_evidence = function Lir.Evidence _ -> true | _ -> false
  and is_data = function Lir.Data _ -> true | _ -> false in
  match compiled with
  | Data _ -> ()
  | Table table -> List.iter (fun (key, signature) -> has key signature) table.entries
  | Evidence evidence ->
      reaches evidence.table ~is:is_table "a table";
      List.iter (fun key -> reaches key ~is:is_evidence "evidence") evidence.outer
  | Code instance ->
      each_function instance (fun _ f ->
          let type_of place = Lir.place_type env ~environment:(environment instance) f place in
          let visitor : Lir.visitor =
            {
              place =
                (fun place ->
                  match place.root with
                  | Static { key; _ } -> reaches key ~is:is_data "a constant"
                  | Local _ -> ());
              operand =
                (function
                | Constant (Symbol_address ((Table _ | Any_table _) as key)) ->
                    reaches key ~is:is_table "a table"
                | Constant (Symbol_address key) -> reaches key ~is:is_evidence "evidence"
                | _ -> ());
            }
          in
          each_statement f (fun statement ->
              Lir.visit_statement visitor statement;
              match statement with
              | Call { target = Direct { function_ = Instance key; signature }; _ } ->
                  has key signature
              | Assign (place, Function_value { code = Instance key; _ }) -> (
                  match type_of place with
                  | Some (Value (Function ty)) -> has key (Convention.function_value env ty)
                  | _ -> bug "a function value stored where no function goes")
              | Drop place -> (
                  match type_of place with
                  | Some (Value ty) -> has (Drop ty) (Convention.drop_signature ty)
                  | Some _ -> bug "a drop of a place that is not a value"
                  | None -> ())
              | Assign _ | Call _ | Echo _ | Free_block _ -> ());
          Array.iter
            (fun (block : Lir.basic_block) -> Lir.visit_terminator visitor block.terminator)
            f.blocks)
