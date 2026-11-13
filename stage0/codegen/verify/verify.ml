let bug format = Compiler_bug.bug ~stage:"Verify" format
let environment (instance : Lir.t) nested_index = instance.nested.(nested_index).environment

let each_function (instance : Lir.t) visit =
  visit "the function" instance.main;
  Array.iteri
    (fun nested_index nested -> visit (Printf.sprintf "nested function %d" nested_index) nested)
    instance.nested

let each_statement (function_ : Lir.function_) visit =
  Array.iter (fun (block : Lir.basic_block) -> List.iter visit block.statements) function_.blocks

(* Whether two places may share memory. Places under different roots do
   not. Under one root they do not if their paths part at different fields
   of a record or of one variant, or if one path is the other followed by a
   dereference, which leads to another object. Two elements are assumed to
   overlap unless their indexes are written the same way. *)
let may_alias (first : Lir.place) (second : Lir.place) =
  let rec overlap (first : Lir.projection list) (second : Lir.projection list) =
    match (first, second) with
    | [], rest | rest, [] -> not (List.mem Lir.Deref rest)
    | Field left :: first, Field right :: second -> left = right && overlap first second
    | Variant_field left :: first, Variant_field right :: second ->
        left.variant <> right.variant || (left.field = right.field && overlap first second)
    | Deref :: first, Deref :: second -> overlap first second
    | Index left :: first, Index right :: second -> left <> right || overlap first second
    | (Field _ | Variant_field _ | Deref | Index _) :: _, _ -> true
  in
  first.root = second.root && overlap first.projections second.projections

(* How many arguments a call passes: its target's leading arguments, the
   pointer a large result is written through, and each argument that has a
   size. *)
let passed env (instance : Lir.t) (function_ : Lir.function_) (target : Lir.target) arguments
    (result : Lir.destination) =
  let sized (operand : Lir.operand) =
    match operand with
    | Copy place | Move place ->
        Lir.place_type env ~environment:(environment instance) function_ place <> None
    | Address _ | Moved_address _ | Constant _ -> true
  in
  (match target with
    | Direct _ | Intrinsic _ | Foreign _ -> 0
    | Indirect _ | Evidence_call _ | Table_call _ -> 1)
  + (match result with Written _ -> 1 | Returned _ | Discarded -> 0)
  + List.length (List.filter sized arguments)

let target_signature (instance : Lir.t) : Lir.target -> Lir.signature option = function
  | Direct { function_ = Nested nested_index; signature } ->
      if nested_index < 0 || nested_index >= Array.length instance.nested then
        bug "a call of nested function %d" nested_index;
      if not (Lir.equal_signature signature (Lir.signature instance.nested.(nested_index))) then
        bug "a call of nested function %d with a signature it does not have" nested_index;
      Some signature
  | Direct { signature; _ }
  | Indirect { signature; _ }
  | Evidence_call { signature; _ }
  | Table_call { signature; _ } ->
      Some signature
  | Intrinsic _ | Foreign _ -> None

let function_ env (instance : Lir.t) label (function_ : Lir.function_) =
  let blocks = Array.length function_.blocks and locals = Array.length function_.locals in
  let bug format = Printf.ksprintf (fun message -> bug "%s: %s" label message) format in
  let local local_number =
    if local_number < 0 || local_number >= locals then bug "local %d, of %d" local_number locals
  in
  List.iter local function_.parameters;
  Option.iter
    (fun local_number ->
      if not (List.mem local_number function_.parameters) then
        bug "a result pointer that is no parameter")
    function_.written_result;
  let visitor : Lir.visitor =
    {
      place =
        (fun place ->
          (match place.root with Local local_number -> local local_number | Static _ -> ());
          ignore (Lir.place_type env ~environment:(environment instance) function_ place));
      operand =
        (function
        | Move { root = Static { key; _ }; _ } | Moved_address { root = Static { key; _ }; _ } ->
            bug "a move out of %s, which is static data" (Instance.to_string key)
        | _ -> ());
    }
  in
  (* A nested function that a fork runs takes its environment, and for a
     range the part to cover, and returns nothing. *)
  let forked nested_index (parameters : Lir.ty list) =
    if nested_index < 0 || nested_index >= Array.length instance.nested then
      bug "a fork of nested function %d" nested_index;
    let signature = Lir.signature instance.nested.(nested_index) in
    if signature.parameters <> parameters || signature.result <> None then
      bug "a fork of nested function %d, which does not take a fork's arguments" nested_index
  in
  let nested_value : Lir.statement -> unit = function
    | Assign (_, Function_value { code = Nested nested_index; _ }) ->
        if nested_index < 0 || nested_index >= Array.length instance.nested then
          bug "a value of nested function %d" nested_index
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
                (fun (variant : Memory_layout.variant_shape) -> List.map fst variant.fields)
                (List.find_opt
                   (fun (variant : Memory_layout.variant_shape) -> variant.name = name)
                   variants)
          | _ -> None
        in
        match has with
        | None -> bug "a value of %s built as another type" (Ground.to_string ty)
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
              (* Every pointer a callee is given is [restrict], so the place
                 it writes its result to is none it is also given to read. *)
              (match result with
              | Written ({ root = Local local; _ } as written) ->
                  List.iter
                    (fun (argument : Lir.operand) ->
                      match argument with
                      | (Address { place = passed; _ } | Moved_address passed)
                        when may_alias written passed ->
                          bug "a call that writes its result to local %d, which it is also given"
                            local
                      | _ -> ())
                    arguments
              | _ -> ());
              (match (target, result) with
              | Foreign declaration, _ when List.length arguments <> List.length declaration.takes
                ->
                  bug "a call of %s with %d arguments, which takes %d" declaration.symbol
                    (List.length arguments) (List.length declaration.takes)
              | Foreign declaration, Written _ ->
                  bug "a call of %s that writes its result through a pointer" declaration.symbol
              | _ -> ());
              Option.iter
                (fun (signature : Lir.signature) ->
                  let passed_count = passed env instance function_ target arguments result in
                  let arity = List.length signature.parameters in
                  if passed_count <> arity then
                    bug "a call that passes %d arguments to a target that takes %d" passed_count
                      arity)
                (target_signature instance target)
          | Region _ | Regions_end _ | Loop_body _ | Loop_exit _ ->
              bug "a region that outlining left in place"
          | Fork { branches } ->
              List.iter
                (fun (nested, _) -> forked nested [ Lir.Raw (Nullable_pointer Opaque) ])
                branches
          | Fork_range { body; _ } ->
              forked body
                [ Lir.Raw (Nullable_pointer Opaque); Raw (Integer UInt64); Raw (Integer UInt64) ]
          | Assign _ | Drop _ | Echo _ | Free_block _ -> ())
        block.statements;
      Lir.visit_terminator visitor block.terminator;
      List.iter
        (fun block_index ->
          if block_index < 0 || block_index >= blocks then bug "block %d, of %d" block_index blocks)
        (Lir.successors block.terminator);
      match (block.terminator, function_.result) with
      | Yield _, _ -> bug "a yield that yield lowering left in place"
      | (Loop_call _ | Loop_next _), _ -> bug "a loop that outlining left in place"
      | Return None, Some _ -> bug "a return of nothing from a function with a result"
      | Return (Some _), None -> bug "a return of a value from a function with no result"
      | _ -> ())
    function_.blocks

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
  let reaches key ~is expected =
    match find key with
    | Some unit when is unit -> ()
    | _ -> bug "the address of %s, which is not %s" (Instance.to_string key) expected
  in
  let is_table = function Lir.Table _ -> true | _ -> false
  and is_data = function Lir.Data _ -> true | _ -> false in
  match compiled with
  | Data _ -> ()
  | Table table -> List.iter (fun (key, signature) -> has key signature) table.entries
  | Code instance ->
      each_function instance (fun _ function_ ->
          let type_of place =
            Lir.place_type env ~environment:(environment instance) function_ place
          in
          let visitor : Lir.visitor =
            {
              place =
                (fun place ->
                  match place.root with
                  | Static { key; _ } -> reaches key ~is:is_data "a constant"
                  | Local _ -> ());
              operand =
                (function
                | Constant (Symbol_address ((Table _ | Any_table _ | Locked_table _) as key)) ->
                    reaches key ~is:is_table "a table"
                | Constant (Symbol_address key) ->
                    bug "the address of %s, which is not a table" (Instance.to_string key)
                | _ -> ());
            }
          in
          each_statement function_ (fun statement ->
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
              | Assign _ | Call _ | Echo _ | Free_block _ | Region _ | Regions_end _ | Loop_body _
              | Loop_exit _ | Fork _ | Fork_range _ ->
                  ());
          Array.iter
            (fun (block : Lir.basic_block) -> Lir.visit_terminator visitor block.terminator)
            function_.blocks)
