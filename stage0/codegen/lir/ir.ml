(* The lowered IR's types, the queries over them, mapping a function's
   places and blocks, and putting a function in canonical form. *)

include Ir_types

let signature (f : function_) =
  {
    parameters = List.map (fun local -> f.locals.(local).ty) f.parameters;
    result = f.result;
    returns = f.returns;
  }

let bug format = Compiler_bug.bug ~stage:"Lir" format

(* A cursor always holds its state, which lets code over a cursor that holds
   another be lowered before the cursor's fields are known. *)
let erased env = function
  | Value (Cursor _) -> false
  | Value ty -> (Memory_layout.of_type env ty).size = 0
  | Pointer _ | Raw _ | Environment _ | Evidence _ -> false

let member_ty : Memory_layout.member -> ty = function
  | Typed ty -> Value ty
  | Raw scalar -> Raw scalar

let find_field (fields : Memory_layout.field list) name =
  List.find_map
    (fun (field : Memory_layout.field) ->
      if field.name = name then Some (member_ty field.member) else None)
    fields

let struct_field (layout : Memory_layout.t) name =
  match layout.form with Struct fields -> find_field fields name | _ -> None

let variant_field_type env sum variant field =
  let layout = Memory_layout.of_type env sum in
  let in_payload (payload : Memory_layout.t) =
    match payload.form with
    | Struct fields -> find_field fields field
    | Scalar (Pointer (Block _)) -> struct_field (Memory_layout.block env sum variant) field
    | _ -> None
  in
  match layout.form with
  | Tagged { variants; _ } -> (
      match List.find_opt (fun (v : Memory_layout.variant) -> v.name = variant) variants with
      | Some v -> in_payload v.payload
      | None -> bug "%s has no variant %s" (Ground.to_string sum) variant)
  | Niche_encoded { dataful; _ } when dataful.name = variant -> in_payload dataful.payload
  | Niche_encoded _ | Tag_only _ | Zero_size -> None
  | _ -> bug "a variant of %s, which is not a sum type" (Ground.to_string sum)

let projection_type env ~environment ty projection =
  let result =
    match (projection, ty) with
    | Deref, Pointer { target; _ } -> Some target
    | Deref, Raw (Pointer (Data target) | Nullable_pointer (Data target)) -> Some (Value target)
    | Field name, Value record -> (
        let layout = Memory_layout.of_type env record in
        match layout.form with
        | Struct _ -> struct_field layout name
        | Zero_size -> None
        | _ -> bug "field %s of %s, which is not a record" name (Ground.to_string record))
    | Field name, Environment n -> (
        match List.assoc_opt name (environment n) with
        | Some ty -> Some ty
        | None -> bug "environment %d has no field %s" n name)
    | Variant_field { variant; field }, Value sum -> variant_field_type env sum variant field
    | Index _, Value array -> (
        match (Memory_layout.of_type env array).form with
        | Array { element; _ } -> Some (Value element)
        | Zero_size -> None
        | _ -> bug "an index into %s" (Ground.to_string array))
    | Index _, Raw (Pointer (Data element) | Nullable_pointer (Data element)) ->
        Some (Value element)
    | _ -> bug "a projection that does not fit its place"
  in
  match result with Some ty when erased env ty -> None | other -> other

let place_type env ~environment (f : function_) (place : place) =
  let root =
    match place.root with Local local -> f.locals.(local).ty | Static { ty; _ } -> Value ty
  in
  if erased env root then None
  else
    List.fold_left
      (fun ty projection ->
        Option.bind ty (fun ty -> projection_type env ~environment ty projection))
      (Some root) place.projections

let target_operands = function
  | Indirect { value; _ } | Evidence_call { evidence = value; _ } -> [ value ]
  | Table_call { table; value; _ } -> [ table; value ]
  | Direct _ | Intrinsic _ | Foreign _ -> []

(* Visits every place and every operand of a statement or a terminator,
   each after the places and operands inside it. *)
type visitor = { place : place -> unit; operand : operand -> unit }

let rec visit_place v (p : place) =
  List.iter
    (function Index o -> visit_operand v o | Field _ | Variant_field _ | Deref -> ())
    p.projections;
  v.place p

and visit_operand v (o : operand) =
  (match o with
  | Copy p | Move p | Address { place = p; _ } | Moved_address p -> visit_place v p
  | Constant _ -> ());
  v.operand o

let visit_rvalue v = function
  | Use o | Unary (_, o) | Convert (o, _) -> visit_operand v o
  | Binary (_, a, b) ->
      visit_operand v a;
      visit_operand v b
  | Build { fields; _ } -> List.iter (fun (_, o) -> visit_operand v o) fields
  | Is_variant (p, _) -> visit_place v p
  | Function_value { environment; _ } -> Option.iter (visit_operand v) environment

let visit_statement v = function
  | Assign (p, rvalue) ->
      visit_rvalue v rvalue;
      visit_place v p
  | Call { target; arguments; result } -> (
      List.iter (visit_operand v) (target_operands target);
      List.iter (visit_operand v) arguments;
      match result with Returned p | Written p -> visit_place v p | Discarded -> ())
  | Drop p | Free_block { place = p; _ } -> visit_place v p
  | Echo { text; length; _ } ->
      visit_operand v text;
      visit_operand v length

let visit_terminator v = function
  | Switch { value; _ } | Yield { value; _ } -> visit_operand v value
  | Switch_variant { place; _ } -> visit_place v place
  | Return value -> Option.iter (visit_operand v) value
  | Fail { message; length; _ } ->
      visit_operand v message;
      visit_operand v length
  | Goto _ | Unreachable -> ()

let successors = function
  | Goto block -> [ block ]
  | Switch { cases; default; _ } -> List.map snd cases @ Option.to_list default
  | Switch_variant { cases; default; _ } -> List.map snd cases @ Option.to_list default
  | Return _ | Unreachable | Fail _ -> []
  | Yield { resume; stop; _ } -> resume :: Option.to_list stop

(* Blocks in reverse postorder of a depth-first walk that takes successors
   in order. *)
let reverse_postorder (blocks : basic_block array) =
  let visited = Array.make (Array.length blocks) false in
  let order = ref [] in
  let rec visit block =
    if not visited.(block) then begin
      visited.(block) <- true;
      List.iter visit (successors blocks.(block).terminator);
      order := block :: !order
    end
  in
  if Array.length blocks > 0 then visit 0;
  !order

(* Rewrites every place, each after the places in its indexes, and every
   block number. *)
let rec map_place ~place ~block (p : place) =
  place { p with projections = List.map (map_projection ~place ~block) p.projections }

and map_projection ~place ~block = function
  | Index operand -> Index (map_operand ~place ~block operand)
  | (Field _ | Variant_field _ | Deref) as projection -> projection

and map_operand ~place ~block = function
  | Copy p -> Copy (map_place ~place ~block p)
  | Move p -> Move (map_place ~place ~block p)
  | Address { place = p; writable } -> Address { place = map_place ~place ~block p; writable }
  | Moved_address p -> Moved_address (map_place ~place ~block p)
  | Constant _ as operand -> operand

let map_rvalue ~place ~block rvalue =
  let operand = map_operand ~place ~block in
  match rvalue with
  | Use o -> Use (operand o)
  | Unary (op, o) -> Unary (op, operand o)
  | Binary (op, a, b) -> Binary (op, operand a, operand b)
  | Convert (o, scalar) -> Convert (operand o, scalar)
  | Build { ty; variant; fields } ->
      Build { ty; variant; fields = List.map (fun (name, o) -> (name, operand o)) fields }
  | Is_variant (p, variant) -> Is_variant (map_place ~place ~block p, variant)
  | Function_value { code; environment } ->
      Function_value { code; environment = Option.map operand environment }

let map_target ~place ~block = function
  | Indirect { value; signature } -> Indirect { value = map_operand ~place ~block value; signature }
  | Evidence_call { evidence; slot; signature } ->
      Evidence_call { evidence = map_operand ~place ~block evidence; slot; signature }
  | Table_call { table; value; slot; signature } ->
      Table_call
        {
          table = map_operand ~place ~block table;
          value = map_operand ~place ~block value;
          slot;
          signature;
        }
  | (Direct _ | Intrinsic _ | Foreign _) as target -> target

let map_destination ~place ~block = function
  | Discarded -> Discarded
  | Returned p -> Returned (map_place ~place ~block p)
  | Written p -> Written (map_place ~place ~block p)

let map_statement ~place ~block = function
  | Assign (p, rvalue) -> Assign (map_place ~place ~block p, map_rvalue ~place ~block rvalue)
  | Call { target; arguments; result } ->
      Call
        {
          target = map_target ~place ~block target;
          arguments = List.map (map_operand ~place ~block) arguments;
          result = map_destination ~place ~block result;
        }
  | Drop p -> Drop (map_place ~place ~block p)
  | Free_block { place = p; variant } -> Free_block { place = map_place ~place ~block p; variant }
  | Echo { text; length; site } ->
      Echo
        { text = map_operand ~place ~block text; length = map_operand ~place ~block length; site }

let map_terminator ~place ~block terminator =
  let operand = map_operand ~place ~block in
  match terminator with
  | Goto b -> Goto (block b)
  | Switch { value; cases; default } ->
      Switch
        {
          value = operand value;
          cases = List.map (fun (value, b) -> (value, block b)) cases;
          default = Option.map block default;
        }
  | Switch_variant { place = p; cases; default } ->
      Switch_variant
        {
          place = map_place ~place ~block p;
          cases = List.map (fun (variant, b) -> (variant, block b)) cases;
          default = Option.map block default;
        }
  | Return value -> Return (Option.map operand value)
  | Unreachable -> Unreachable
  | Fail { failure; message; length; site } ->
      Fail { failure; message = operand message; length = operand length; site }
  | Yield { value; resume; stop } ->
      Yield { value = operand value; resume = block resume; stop = Option.map block stop }

let rename map_local (p : place) =
  match p.root with Local local -> { p with root = Local (map_local local) } | Static _ -> p

let canonical (f : function_) =
  let order = reverse_postorder f.blocks in
  let block_number = Array.make (Array.length f.blocks) (-1) in
  List.iteri (fun index block -> block_number.(block) <- index) order;
  let local_number = Array.make (Array.length f.locals) (-1) in
  let next = ref 0 in
  let number local =
    if local_number.(local) < 0 then begin
      local_number.(local) <- !next;
      incr next
    end;
    local
  in
  List.iter (fun local -> ignore (number local)) f.parameters;
  let identity block = block in
  List.iter
    (fun b ->
      let { statements; terminator } = f.blocks.(b) in
      List.iter
        (fun statement -> ignore (map_statement ~place:(rename number) ~block:identity statement))
        statements;
      ignore (map_terminator ~place:(rename number) ~block:identity terminator))
    order;
  let locals = Array.make !next { ty = Raw Bool; name = None; borrowed = false } in
  Array.iteri (fun old index -> if index >= 0 then locals.(index) <- f.locals.(old)) local_number;
  let map_local local = local_number.(local) in
  let map_block block = block_number.(block) in
  let blocks =
    Array.of_list
      (List.map
         (fun block ->
           let { statements; terminator } = f.blocks.(block) in
           {
             statements =
               List.map (map_statement ~place:(rename map_local) ~block:map_block) statements;
             terminator = map_terminator ~place:(rename map_local) ~block:map_block terminator;
           })
         order)
  in
  {
    f with
    parameters = List.map map_local f.parameters;
    written_result = Option.map map_local f.written_result;
    locals;
    blocks;
  }

let canonical_instance t = { t with main = canonical t.main; nested = Array.map canonical t.nested }
