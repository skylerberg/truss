let bug format = Compiler_bug.bug ~stage:"Yields" format
let local_place = Lir.local_place

let loop_form env ~(body : Ground.function_type) (function_ : Lir.function_) =
  let go_on_ty =
    match body.result with
    | Returns ty -> Lir.Value ty
    | _ -> bug "a loop body that does not return"
  in
  let body_local = Array.length function_.locals in
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
                  result = Returned (local_place go_on);
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
      function_.blocks
  in
  {
    function_ with
    parameters = function_.parameters @ [ body_local ];
    locals =
      Array.append function_.locals
        [|
          { ty = Value (Function body); name = Some "body"; borrowed = true };
          { ty = go_on_ty; name = Some "go_on"; borrowed = false };
        |];
    blocks;
  }

(* Liveness of locals, to find what a cursor must keep *)

let rec place_reads (place : Lir.place) =
  let indexes =
    List.concat_map
      (function Lir.Index lir_operand -> operand_reads lir_operand | _ -> [])
      place.projections
  in
  match place.root with Local local -> local :: indexes | Static _ -> indexes

and operand_reads = function
  | Lir.Copy place | Move place | Address { place; _ } | Moved_address place -> place_reads place
  | Constant _ -> []

let rvalue_reads (rvalue : Lir.rvalue) =
  match rvalue with
  | Use lir_operand | Unary (_, lir_operand) | Convert (lir_operand, _) -> operand_reads lir_operand
  | Binary (_, left, right) -> operand_reads left @ operand_reads right
  | Build { fields; _ } ->
      List.concat_map (fun (_, lir_operand) -> operand_reads lir_operand) fields
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
      let target_reads = List.concat_map operand_reads (Lir.target_operands target) in
      let reads, defined =
        match result with Returned place | Written place -> written place | Discarded -> ([], None)
      in
      (target_reads @ List.concat_map operand_reads arguments @ reads, defined)
  | Drop place | Free_block { place; _ } -> (place_reads place, None)
  | Echo { text; length; _ } -> (operand_reads text @ operand_reads length, None)
  | Region _ | Regions_end _ | Fork _ | Fork_range _ ->
      bug "a parallel statement in a method that is pulled, which runs its branches in order"

let terminator_reads (terminator : Lir.terminator) =
  match terminator with
  | Switch { value; _ } -> operand_reads value
  | Switch_variant { place; _ } -> place_reads place
  | Return value -> Option.fold ~none:[] ~some:operand_reads value
  | Fail { message; length; _ } -> operand_reads message @ operand_reads length
  | Yield { value; _ } -> operand_reads value
  | Goto _ | Unreachable -> []

let live_in (function_ : Lir.function_) =
  let count = Array.length function_.locals in
  let live = Array.map (fun _ -> Array.make count false) function_.blocks in
  let changed = ref true in
  while !changed do
    changed := false;
    for block_index = Array.length function_.blocks - 1 downto 0 do
      let block = function_.blocks.(block_index) in
      let current = Array.make count false in
      List.iter
        (fun successor ->
          Array.iteri
            (fun local is_live -> if is_live then current.(local) <- true)
            live.(successor))
        (Lir.successors block.terminator);
      List.iter (fun local -> current.(local) <- true) (terminator_reads block.terminator);
      List.iter
        (fun statement ->
          let reads, defined = statement_uses_defines statement in
          Option.iter (fun local -> current.(local) <- false) defined;
          List.iter (fun local -> current.(local) <- true) reads)
        (List.rev block.statements);
      if current <> live.(block_index) then begin
        live.(block_index) <- current;
        changed := true
      end
    done
  done;
  live

let yields (function_ : Lir.function_) =
  List.filter_map
    (fun block_index ->
      match function_.blocks.(block_index).terminator with
      | Yield { resume; stop; _ } -> Some (block_index, resume, stop)
      | _ -> None)
    (List.init (Array.length function_.blocks) Fun.id)

(* The parameters, and every local live where a [yield] resumes or stops,
   but the parameters in [evidence]. A cursor holds no evidence: [next]
   takes it from its caller. A cursor that held the evidence it was made
   with could use an implementation after the [provide] block that
   provided it had ended, which is a use after free. *)
let saved_locals ~evidence (function_ : Lir.function_) =
  let live = live_in function_ in
  let is_saved = Array.make (Array.length function_.locals) false in
  List.iter (fun parameter -> is_saved.(parameter) <- true) function_.parameters;
  List.iter
    (fun (_, resume, stop) ->
      List.iter
        (fun block_index ->
          Array.iteri
            (fun local is_live -> if is_live then is_saved.(local) <- true)
            live.(block_index))
        (resume :: Option.to_list stop))
    (yields function_);
  List.iter (fun local -> is_saved.(local) <- false) evidence;
  List.filter (fun local -> is_saved.(local)) (List.init (Array.length function_.locals) Fun.id)

(* A saved local's field of the cursor: a parameter's is named by its place
   among the parameters, which is how whoever makes a cursor fills it in. *)
let field_name (function_ : Lir.function_) local =
  match List.find_index (Int.equal local) function_.parameters with
  | Some position -> Convention.cursor_parameter position
  | None -> Printf.sprintf "local%d" local

let member : Lir.ty -> Memory_layout.member = function
  | Value ty -> Typed ty
  | Raw scalar -> Raw scalar
  | Pointer { target = Value ty; _ } -> Raw (Pointer (Data ty))
  | Pointer _ | Environment _ | Evidence _ -> bug "a local a cursor cannot keep"

let cursor_fields _env ~evidence (function_ : Lir.function_) =
  (Convention.cursor_state, Memory_layout.Raw (Integer UInt32))
  :: List.map
       (fun local -> (field_name function_ local, member function_.locals.(local).ty))
       (saved_locals ~evidence function_)

(* The function's blocks, shifted up by one for a new entry block, with
   every saved local moved into the cursor that local [cursor] points at,
   every other local shifted by [base], and each [yield] and [return] given
   to [yield_] and [return_]. *)
let state_machine (function_ : Lir.function_) ~evidence ~cursor ~base ~yield_ ~return_ =
  let saved = saved_locals ~evidence function_ in
  let place (parameter : Lir.place) =
    match parameter.root with
    | Local local when List.mem local saved ->
        {
          Lir.root = Local cursor;
          projections = Deref :: Field (field_name function_ local) :: parameter.projections;
        }
    | Local local -> { parameter with root = Local (local + base) }
    | Static _ -> parameter
  in
  let block block_index = block_index + 1 in
  let numbered =
    List.mapi (fun local (block_index, _, _) -> (block_index, local + 1)) (yields function_)
  in
  let blocks =
    Array.mapi
      (fun block_index (original : Lir.basic_block) ->
        let statements = List.map (Lir.map_statement ~place ~block) original.statements in
        match Lir.map_terminator ~place ~block original.terminator with
        | Yield { value; resume; stop } ->
            let more, terminator =
              yield_ ~state:(List.assoc block_index numbered) ~value ~resume ~stop
            in
            { Lir.statements = statements @ more; terminator }
        | Return _ ->
            let more, terminator = return_ () in
            { statements = statements @ more; terminator }
        | terminator -> { statements; terminator })
      function_.blocks
  in
  (blocks, List.length numbered)

let set_state cursor state : Lir.statement =
  Assign
    ( { root = Local cursor; projections = [ Deref; Field Convention.cursor_state ] },
      Use (Constant (Integer (UInt32, Z.of_int state))) )

let entry_switch cursor cases ~default : Lir.basic_block =
  {
    statements = [];
    terminator =
      Switch
        {
          value =
            Copy { root = Local cursor; projections = [ Deref; Field Convention.cursor_state ] };
          cases = List.map (fun (state, block) -> (Z.of_int state, block)) cases;
          default;
        };
  }

let cursor_next env ~cursor ~result ~evidence (function_ : Lir.function_) =
  let convention = Convention.result env result in
  let through_pointer = match convention with Through_pointer _ -> true | _ -> false in
  let cursor_local = if through_pointer then 1 else 0 in
  let base = if through_pointer then 2 else 1 in
  let result_local = base + Array.length function_.locals in
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
  let finished = List.length (yields function_) + 1 in
  let blocks, _ =
    state_machine function_ ~evidence ~cursor:cursor_local ~base
      ~yield_:(fun ~state ~value ~resume:_ ~stop:_ ->
        let statements, terminator = give (some value) in
        (set_state cursor_local state :: statements, terminator))
      ~return_:(fun () ->
        let statements, terminator = give none in
        (set_state cursor_local finished :: statements, terminator))
  in
  let done_block = Array.length blocks + 1 in
  let resumes =
    List.mapi (fun local (_, resume, _) -> (local + 1, resume + 1)) (yields function_)
  in
  let done_statements, done_terminator = give none in
  let entry =
    entry_switch cursor_local (((0, 1) :: resumes) @ [ (finished, done_block) ]) ~default:None
  in
  let cursor_ty = Lir.Pointer { target = Value cursor; writable = true } in
  let result_pointer = match convention with Through_pointer ty -> [ ty ] | _ -> [] in
  {
    Lir.parameters =
      (if through_pointer then [ 0; 1 ] else [ 0 ]) @ List.map (fun local -> local + base) evidence;
    written_result = (if through_pointer then Some 0 else None);
    result = (match convention with Returned ty -> Some ty | Nothing | Through_pointer _ -> None);
    returns = true;
    locals =
      Array.concat
        [
          Array.of_list
            (List.map (fun ty -> { Lir.ty; name = Some "result"; borrowed = false }) result_pointer);
          [| { ty = cursor_ty; name = Some "cursor"; borrowed = false } |];
          function_.locals;
          (if through_pointer then [||]
           else [| { Lir.ty = Value result; name = Some "result"; borrowed = false } |]);
        ];
    blocks =
      Array.concat
        [
          [| entry |]; blocks; [| { statements = done_statements; terminator = done_terminator } |];
        ];
    environment = [];
  }

let cursor_drop _env ~cursor ~owned ~evidence (function_ : Lir.function_) =
  (* A drop is given no evidence, so no [stop] path may read any. *)
  let live = live_in function_ in
  List.iter
    (fun (_, _, stop) ->
      Option.iter
        (fun stop ->
          if List.exists (fun local -> live.(stop).(local)) evidence then
            bug "a pulled method uses a capability where it ends early")
        stop)
    (yields function_);
  let blocks, count =
    state_machine function_ ~evidence ~cursor:0 ~base:1
      ~yield_:(fun ~state:_ ~value:_ ~resume:_ ~stop:_ -> ([], Unreachable))
      ~return_:(fun () -> ([], Return None))
  in
  let finished = count + 1 in
  let done_block = Array.length blocks + 1 in
  let start_block = done_block + 1 in
  let stops =
    List.mapi
      (fun local (_, _, stop) ->
        match stop with
        | Some stop -> (local + 1, stop + 1)
        | None -> bug "a lending method's yield in a cursor")
      (yields function_)
  in
  let entry =
    entry_switch 0 (((0, start_block) :: stops) @ [ (finished, done_block) ]) ~default:None
  in
  (* Before the method starts, the blocks from [start_block] drop each
     argument the cursor owns, testing the mask first for one that is there
     only when it was passed. *)
  let field local : Lir.place =
    { root = Local 0; projections = [ Deref; Field (field_name function_ local) ] }
  in
  let added = ref [] in
  let new_local ty =
    added := { Lir.ty; name = None; borrowed = false } :: !added;
    Array.length function_.locals + List.length !added
  in
  let started = ref [] and statements = ref [] in
  let close terminator =
    started := { Lir.statements = List.rev !statements; terminator } :: !started;
    statements := []
  in
  List.iter
    (fun (local, default_bit) ->
      match default_bit with
      | None -> statements := Lir.Drop (field local) :: !statements
      | Some (mask, bit) ->
          let passed = new_local (Raw (Integer UInt64)) and is_passed = new_local (Raw Bool) in
          statements :=
            Lir.Assign
              ( local_place is_passed,
                Binary (Not_equal, Copy (local_place passed), Constant (Integer (UInt64, Z.zero)))
              )
            :: Assign
                 ( local_place passed,
                   Binary
                     ( Bit_and,
                       Copy (field mask),
                       Constant (Integer (UInt64, Z.shift_left Z.one bit)) ) )
            :: !statements;
          let here = start_block + List.length !started in
          close
            (Switch
               {
                 value = Copy (local_place is_passed);
                 cases = [ (Z.one, here + 1) ];
                 default = Some (here + 2);
               });
          statements := [ Lir.Drop (field local) ];
          close (Goto (here + 2)))
    owned;
  close (Return None);
  {
    Lir.parameters = [ 0 ];
    written_result = None;
    result = None;
    returns = true;
    locals =
      Array.concat
        [
          [|
            {
              Lir.ty = Pointer { target = Value cursor; writable = true };
              name = Some "cursor";
              borrowed = false;
            };
          |];
          function_.locals;
          Array.of_list (List.rev !added);
        ];
    blocks =
      Array.concat
        [
          [| entry |];
          blocks;
          [| { statements = []; terminator = Return None } |];
          Array.of_list (List.rev !started);
        ];
    environment = [];
  }

module For_testing = struct
  let loop_form = loop_form
end
