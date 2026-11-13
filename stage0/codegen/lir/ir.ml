(* The lowered IR's types, the queries over them, mapping a function's
   places and blocks, and putting a function in canonical form. *)

include Ir_types

let local_place local = { root = Local local; projections = [] }

let signature (function_ : function_) =
  {
    parameters = List.map (fun local -> function_.locals.(local).ty) function_.parameters;
    result = function_.result;
    returns = function_.returns;
  }

let bug format = Compiler_bug.bug ~stage:"Lir" format

(* A cursor always holds its state, which lets code over a cursor that holds
   another be lowered before the cursor's fields are known. *)
let erased env = function
  | Value (Cursor _) -> false
  | Value ty -> Memory_layout.has_zero_size env ty
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
      match
        List.find_opt
          (fun (variant_layout : Memory_layout.variant) -> variant_layout.name = variant)
          variants
      with
      | Some variant_layout -> in_payload variant_layout.payload
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
    | Field name, Environment nested_index -> (
        match List.assoc_opt name (environment nested_index) with
        | Some ty -> Some ty
        | None -> bug "environment %d has no field %s" nested_index name)
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

let place_type env ~environment (function_ : function_) (place : place) =
  let root =
    match place.root with
    | Local local -> function_.locals.(local).ty
    | Static { ty; _ } -> Value ty
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

let rec visit_place visitor (lir_place : place) =
  List.iter
    (function
      | Index lir_operand -> visit_operand visitor lir_operand
      | Field _ | Variant_field _ | Deref -> ())
    lir_place.projections;
  visitor.place lir_place

and visit_operand visitor (lir_operand : operand) =
  (match lir_operand with
  | Copy lir_place | Move lir_place | Address { place = lir_place; _ } | Moved_address lir_place ->
      visit_place visitor lir_place
  | Constant _ -> ());
  visitor.operand lir_operand

let visit_rvalue visitor = function
  | Use lir_operand | Unary (_, lir_operand) | Convert (lir_operand, _) ->
      visit_operand visitor lir_operand
  | Binary (_, left, right) ->
      visit_operand visitor left;
      visit_operand visitor right
  | Build { fields; _ } ->
      List.iter (fun (_, lir_operand) -> visit_operand visitor lir_operand) fields
  | Is_variant (lir_place, _) -> visit_place visitor lir_place
  | Function_value { environment; _ } -> Option.iter (visit_operand visitor) environment

let visit_statement visitor = function
  | Assign (lir_place, rvalue) ->
      visit_rvalue visitor rvalue;
      visit_place visitor lir_place
  | Call { target; arguments; result } -> (
      List.iter (visit_operand visitor) (target_operands target);
      List.iter (visit_operand visitor) arguments;
      match result with
      | Returned lir_place | Written lir_place -> visit_place visitor lir_place
      | Discarded -> ())
  | Drop lir_place | Free_block { place = lir_place; _ } -> visit_place visitor lir_place
  | Echo { text; length; _ } ->
      visit_operand visitor text;
      visit_operand visitor length
  | Fork { branches } ->
      List.iter (fun (_, environment) -> visit_operand visitor environment) branches
  | Fork_range { environment; first; last; _ } ->
      visit_operand visitor environment;
      visit_operand visitor first;
      visit_operand visitor last

let visit_terminator visitor = function
  | Switch { value; _ } | Yield { value; _ } -> visit_operand visitor value
  | Switch_variant { place; _ } -> visit_place visitor place
  | Return value -> Option.iter (visit_operand visitor) value
  | Fail { message; length; _ } ->
      visit_operand visitor message;
      visit_operand visitor length
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
let rec map_place ~place ~block (lir_place : place) =
  place
    { lir_place with projections = List.map (map_projection ~place ~block) lir_place.projections }

and map_projection ~place ~block = function
  | Index operand -> Index (map_operand ~place ~block operand)
  | (Field _ | Variant_field _ | Deref) as projection -> projection

and map_operand ~place ~block = function
  | Copy lir_place -> Copy (map_place ~place ~block lir_place)
  | Move lir_place -> Move (map_place ~place ~block lir_place)
  | Address { place = lir_place; writable } ->
      Address { place = map_place ~place ~block lir_place; writable }
  | Moved_address lir_place -> Moved_address (map_place ~place ~block lir_place)
  | Constant _ as operand -> operand

let map_rvalue ~place ~block rvalue =
  let operand = map_operand ~place ~block in
  match rvalue with
  | Use lir_operand -> Use (operand lir_operand)
  | Unary (op, lir_operand) -> Unary (op, operand lir_operand)
  | Binary (op, left, right) -> Binary (op, operand left, operand right)
  | Convert (lir_operand, scalar) -> Convert (operand lir_operand, scalar)
  | Build { ty; variant; fields } ->
      Build
        {
          ty;
          variant;
          fields = List.map (fun (name, lir_operand) -> (name, operand lir_operand)) fields;
        }
  | Is_variant (lir_place, variant) -> Is_variant (map_place ~place ~block lir_place, variant)
  | Function_value { code; environment } ->
      Function_value { code; environment = Option.map operand environment }

let map_target ~place ~block = function
  | Indirect { value; signature } -> Indirect { value = map_operand ~place ~block value; signature }
  | Evidence_call { evidence; capability; slot; signature } ->
      Evidence_call { evidence = map_operand ~place ~block evidence; capability; slot; signature }
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
  | Returned lir_place -> Returned (map_place ~place ~block lir_place)
  | Written lir_place -> Written (map_place ~place ~block lir_place)

let map_statement ~place ~block = function
  | Assign (lir_place, rvalue) ->
      Assign (map_place ~place ~block lir_place, map_rvalue ~place ~block rvalue)
  | Call { target; arguments; result } ->
      Call
        {
          target = map_target ~place ~block target;
          arguments = List.map (map_operand ~place ~block) arguments;
          result = map_destination ~place ~block result;
        }
  | Drop lir_place -> Drop (map_place ~place ~block lir_place)
  | Free_block { place = lir_place; variant } ->
      Free_block { place = map_place ~place ~block lir_place; variant }
  | Echo { text; length; site } ->
      Echo
        { text = map_operand ~place ~block text; length = map_operand ~place ~block length; site }
  | Fork { branches } ->
      Fork
        {
          branches =
            List.map
              (fun (nested, environment) -> (nested, map_operand ~place ~block environment))
              branches;
        }
  | Fork_range { body; environment; first; last } ->
      Fork_range
        {
          body;
          environment = map_operand ~place ~block environment;
          first = map_operand ~place ~block first;
          last = map_operand ~place ~block last;
        }

let map_terminator ~place ~block terminator =
  let operand = map_operand ~place ~block in
  match terminator with
  | Goto block_index -> Goto (block block_index)
  | Switch { value; cases; default } ->
      Switch
        {
          value = operand value;
          cases = List.map (fun (value, block_index) -> (value, block block_index)) cases;
          default = Option.map block default;
        }
  | Switch_variant { place = lir_place; cases; default } ->
      Switch_variant
        {
          place = map_place ~place ~block lir_place;
          cases = List.map (fun (variant, block_index) -> (variant, block block_index)) cases;
          default = Option.map block default;
        }
  | Return value -> Return (Option.map operand value)
  | Unreachable -> Unreachable
  | Fail { failure; message; length; site } ->
      Fail { failure; message = operand message; length = operand length; site }
  | Yield { value; resume; stop } ->
      Yield { value = operand value; resume = block resume; stop = Option.map block stop }

let rename map_local (lir_place : place) =
  match lir_place.root with
  | Local local -> { lir_place with root = Local (map_local local) }
  | Static _ -> lir_place

let canonical (function_ : function_) =
  let order = reverse_postorder function_.blocks in
  let block_number = Array.make (Array.length function_.blocks) (-1) in
  List.iteri (fun index block -> block_number.(block) <- index) order;
  let local_number = Array.make (Array.length function_.locals) (-1) in
  let next = ref 0 in
  let number local =
    if local_number.(local) < 0 then begin
      local_number.(local) <- !next;
      incr next
    end;
    local
  in
  List.iter (fun local -> ignore (number local)) function_.parameters;
  let identity block = block in
  List.iter
    (fun block_index ->
      let { statements; terminator } = function_.blocks.(block_index) in
      List.iter
        (fun statement -> ignore (map_statement ~place:(rename number) ~block:identity statement))
        statements;
      ignore (map_terminator ~place:(rename number) ~block:identity terminator))
    order;
  let locals = Array.make !next { ty = Raw Bool; name = None } in
  Array.iteri
    (fun old index -> if index >= 0 then locals.(index) <- function_.locals.(old))
    local_number;
  let map_local local = local_number.(local) in
  let map_block block = block_number.(block) in
  let blocks =
    Array.of_list
      (List.map
         (fun block ->
           let { statements; terminator } = function_.blocks.(block) in
           {
             statements =
               List.map (map_statement ~place:(rename map_local) ~block:map_block) statements;
             terminator = map_terminator ~place:(rename map_local) ~block:map_block terminator;
           })
         order)
  in
  {
    function_ with
    parameters = List.map map_local function_.parameters;
    written_result = Option.map map_local function_.written_result;
    locals;
    blocks;
  }

let canonical_instance lir =
  { lir with main = canonical lir.main; nested = Array.map canonical lir.nested }
