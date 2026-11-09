let bug format = Printf.ksprintf (fun message -> invalid_arg ("Yields: " ^ message)) format
let local_place local : Lir.place = { root = Local local; projections = [] }

(* The loop form *)

let loop_form env ~(body : Ground.function_type) (f : Lir.function_) =
  let go_on_ty =
    match body.result with
    | Returns ty -> Lir.Value ty
    | _ -> bug "a loop body that does not return"
  in
  let body_local = Array.length f.locals in
  let go_on = body_local + 1 in
  let signature = Convention.function_value env body in
  let blocks =
    Array.map
      (fun (block : Lir.basic_block) ->
        match block.terminator with
        | Yield { value; resume; stop } ->
            let call =
              Lir.Call
                {
                  target = Indirect { value = Copy (local_place body_local); signature };
                  arguments = [ value ];
                  result = Some (local_place go_on);
                }
            in
            let terminator : Lir.terminator =
              match stop with
              | Some stop ->
                  Switch
                    {
                      value = Copy (local_place go_on);
                      cases = [ (Z.one, resume) ];
                      default = Some stop;
                    }
              | None -> Goto resume
            in
            { Lir.statements = block.statements @ [ call ]; terminator }
        | _ -> block)
      f.blocks
  in
  {
    f with
    parameters = f.parameters @ [ body_local ];
    locals =
      Array.append f.locals
        [|
          { ty = Value (Function body); name = Some "body" }; { ty = go_on_ty; name = Some "go_on" };
        |];
    blocks;
  }

(* Liveness of locals, to find what a cursor must keep *)

let rec place_reads (place : Lir.place) =
  let indexes =
    List.concat_map (function Lir.Index o -> operand_reads o | _ -> []) place.projections
  in
  match place.root with Local local -> local :: indexes | Static _ -> indexes

and operand_reads = function
  | Lir.Copy place | Move place | Address { place; _ } -> place_reads place
  | Constant _ -> []

let rvalue_reads (rvalue : Lir.rvalue) =
  match rvalue with
  | Use o | Unary (_, o) | Convert (o, _) -> operand_reads o
  | Binary (_, a, b) -> operand_reads a @ operand_reads b
  | Build { fields; _ } -> List.concat_map (fun (_, o) -> operand_reads o) fields
  | Is_variant (place, _) -> place_reads place
  | Function_value { environment; _ } -> Option.fold ~none:[] ~some:operand_reads environment

(* A write to a whole local defines it. A write to a part of one reads the
   rest of it, so it keeps the local live. *)
let written (place : Lir.place) =
  match place with
  | { root = Local local; projections = [] } -> ([], Some local)
  | _ -> (place_reads place, None)

let statement_uses_defines (statement : Lir.statement) =
  match statement with
  | Assign (place, rvalue) ->
      let reads, defined = written place in
      (rvalue_reads rvalue @ reads, defined)
  | Call { target; arguments; result } ->
      let target_reads =
        match target with
        | Indirect { value; _ } | Evidence_call { evidence = value; _ } -> operand_reads value
        | Direct _ | Intrinsic _ -> []
      in
      let reads, defined = match result with Some place -> written place | None -> ([], None) in
      (target_reads @ List.concat_map operand_reads arguments @ reads, defined)
  | Drop place | Free_block { place; _ } -> (place_reads place, None)
  | Echo { text; length; _ } -> (operand_reads text @ operand_reads length, None)

let terminator_reads (terminator : Lir.terminator) =
  match terminator with
  | Switch { value; _ } -> operand_reads value
  | Switch_variant { place; _ } -> place_reads place
  | Return value -> Option.fold ~none:[] ~some:operand_reads value
  | Fail { message; length; _ } -> operand_reads message @ operand_reads length
  | Yield { value; _ } -> operand_reads value
  | Goto _ | Unreachable -> []

(* The locals live at the start of each block. *)
let live_in (f : Lir.function_) =
  let n = Array.length f.locals in
  let live = Array.map (fun _ -> Array.make n false) f.blocks in
  let changed = ref true in
  while !changed do
    changed := false;
    for b = Array.length f.blocks - 1 downto 0 do
      let block = f.blocks.(b) in
      let current = Array.make n false in
      List.iter
        (fun s -> Array.iteri (fun i v -> if v then current.(i) <- true) live.(s))
        (Lir.successors block.terminator);
      List.iter (fun local -> current.(local) <- true) (terminator_reads block.terminator);
      List.iter
        (fun statement ->
          let reads, defined = statement_uses_defines statement in
          Option.iter (fun local -> current.(local) <- false) defined;
          List.iter (fun local -> current.(local) <- true) reads)
        (List.rev block.statements);
      if current <> live.(b) then begin
        live.(b) <- current;
        changed := true
      end
    done
  done;
  live

let yields (f : Lir.function_) =
  List.filter_map
    (fun b ->
      match f.blocks.(b).terminator with
      | Yield { resume; stop; _ } -> Some (b, resume, stop)
      | _ -> None)
    (List.init (Array.length f.blocks) Fun.id)

(* The parameters, and every local live where a [yield] resumes or stops. *)
let kept (f : Lir.function_) =
  let live = live_in f in
  let keep = Array.make (Array.length f.locals) false in
  List.iter (fun p -> keep.(p) <- true) f.parameters;
  List.iter
    (fun (_, resume, stop) ->
      List.iter
        (fun b -> Array.iteri (fun i v -> if v then keep.(i) <- true) live.(b))
        (resume :: Option.to_list stop))
    (yields f);
  List.filter (fun i -> keep.(i)) (List.init (Array.length f.locals) Fun.id)

let field_name local = Printf.sprintf "local%d" local

let member : Lir.ty -> Memory_layout.member = function
  | Value ty -> Typed ty
  | Raw scalar -> Raw scalar
  | Pointer { target = Value ty; _ } -> Raw (Pointer (Data ty))
  | Pointer _ | Environment _ -> bug "a local a cursor cannot keep"

let state_ty = Lir.Raw (Integer UInt32)

let cursor_fields _env (f : Lir.function_) =
  ("state", Memory_layout.Raw (Integer UInt32))
  :: List.map (fun local -> (field_name local, member f.locals.(local).ty)) (kept f)

(* The state machine *)

(* The function's blocks, shifted up by one for a new entry block, with
   every kept local moved into the cursor that local [cursor] points at,
   every other local shifted by [base], and each [yield] and [return] given
   to [yield_] and [return_]. *)
let state_machine (f : Lir.function_) ~cursor ~base ~yield_ ~return_ =
  let kept = kept f in
  let place (p : Lir.place) =
    match p.root with
    | Local local when List.mem local kept ->
        {
          Lir.root = Local cursor;
          projections = Deref :: Field (field_name local) :: p.projections;
        }
    | Local local -> { p with root = Local (local + base) }
    | Static _ -> p
  in
  let block b = b + 1 in
  let numbered = List.mapi (fun i (b, _, _) -> (b, i + 1)) (yields f) in
  let blocks =
    Array.mapi
      (fun b (original : Lir.basic_block) ->
        let statements = List.map (Lir.map_statement ~place ~block) original.statements in
        match Lir.map_terminator ~place ~block original.terminator with
        | Yield { value; resume; stop } ->
            let more, terminator = yield_ ~state:(List.assoc b numbered) ~value ~resume ~stop in
            { Lir.statements = statements @ more; terminator }
        | Return _ ->
            let more, terminator = return_ () in
            { statements = statements @ more; terminator }
        | terminator -> { statements; terminator })
      f.blocks
  in
  (blocks, List.length numbered)

let set_state cursor state : Lir.statement =
  Assign
    ( { root = Local cursor; projections = [ Deref; Field "state" ] },
      Use (Constant (Integer (UInt32, Z.of_int state))) )

let entry_switch cursor cases ~default : Lir.basic_block =
  {
    statements = [];
    terminator =
      Switch
        {
          value = Copy { root = Local cursor; projections = [ Deref; Field "state" ] };
          cases = List.map (fun (state, block) -> (Z.of_int state, block)) cases;
          default;
        };
  }

let cursor_next env ~cursor ~result (f : Lir.function_) =
  let convention = Convention.result env result in
  let through_pointer = match convention with Through_pointer _ -> true | _ -> false in
  let cursor_local = if through_pointer then 1 else 0 in
  let base = if through_pointer then 2 else 1 in
  let result_local = base + Array.length f.locals in
  let result_place : Lir.place =
    if through_pointer then { root = Local 0; projections = [ Deref ] }
    else local_place result_local
  in
  let give rvalue : Lir.statement list * Lir.terminator =
    ( [ Assign (result_place, rvalue) ],
      if through_pointer then Return None else Return (Some (Move (local_place result_local))) )
  in
  let some value =
    Lir.Build { ty = result; variant = Some "Some"; fields = [ ("value", value) ] }
  in
  let none = Lir.Build { ty = result; variant = Some "None"; fields = [] } in
  let finished = List.length (yields f) + 1 in
  let blocks, _ =
    state_machine f ~cursor:cursor_local ~base
      ~yield_:(fun ~state ~value ~resume:_ ~stop:_ ->
        let statements, terminator = give (some value) in
        (set_state cursor_local state :: statements, terminator))
      ~return_:(fun () ->
        let statements, terminator = give none in
        (set_state cursor_local finished :: statements, terminator))
  in
  let done_block = Array.length blocks + 1 in
  let resumes = List.mapi (fun i (_, resume, _) -> (i + 1, resume + 1)) (yields f) in
  let done_statements, done_terminator = give none in
  let entry =
    entry_switch cursor_local (((0, 1) :: resumes) @ [ (finished, done_block) ]) ~default:None
  in
  let cursor_ty = Lir.Pointer { target = Value cursor; writable = true } in
  let result_pointer = match convention with Through_pointer ty -> [ ty ] | _ -> [] in
  {
    Lir.parameters = (if through_pointer then [ 0; 1 ] else [ 0 ]);
    result = (match convention with Returned ty -> Some ty | Nothing | Through_pointer _ -> None);
    returns = true;
    locals =
      Array.concat
        [
          Array.of_list (List.map (fun ty -> { Lir.ty; name = Some "result" }) result_pointer);
          [| { ty = cursor_ty; name = Some "cursor" } |];
          f.locals;
          (if through_pointer then [||] else [| { Lir.ty = Value result; name = Some "result" } |]);
        ];
    blocks =
      Array.concat
        [
          [| entry |]; blocks; [| { statements = done_statements; terminator = done_terminator } |];
        ];
    environment = [];
  }

let cursor_drop _env ~cursor ~owned (f : Lir.function_) =
  let blocks, count =
    state_machine f ~cursor:0 ~base:1
      ~yield_:(fun ~state:_ ~value:_ ~resume:_ ~stop:_ -> ([], Unreachable))
      ~return_:(fun () -> ([], Return None))
  in
  let finished = count + 1 in
  let start_block = Array.length blocks + 1 in
  let done_block = start_block + 1 in
  let stops =
    List.mapi
      (fun i (_, _, stop) ->
        match stop with
        | Some stop -> (i + 1, stop + 1)
        | None -> bug "a lending method's yield in a cursor")
      (yields f)
  in
  let entry =
    entry_switch 0 (((0, start_block) :: stops) @ [ (finished, done_block) ]) ~default:None
  in
  let start : Lir.basic_block =
    {
      statements =
        List.map
          (fun local ->
            Lir.Drop { root = Local 0; projections = [ Deref; Field (field_name local) ] })
          owned;
      terminator = Return None;
    }
  in
  {
    Lir.parameters = [ 0 ];
    result = None;
    returns = true;
    locals =
      Array.append
        [| { Lir.ty = Pointer { target = Value cursor; writable = true }; name = Some "cursor" } |]
        f.locals;
    blocks =
      Array.concat
        [ [| entry |]; blocks; [| start; { statements = []; terminator = Return None } |] ];
    environment = [];
  }
