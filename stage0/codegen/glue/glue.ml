let bug format = Printf.ksprintf (fun message -> invalid_arg ("Glue: " ^ message)) format

type kind = Shape of Memory_layout.shape | Storage of Ground.ty

module Types = Map.Make (struct
  type t = Ground.ty

  let compare = Ground.compare
end)

type t = {
  env : Memory_layout.env;
  kind_of : Ground.ty -> kind;
  usize : Ground.ty;
  mutable trivial_types : bool Types.t;
}

let create env ~kind_of ~usize = { env; kind_of; usize; trivial_types = Types.empty }

let rec trivial t ty =
  match Types.find_opt ty t.trivial_types with
  | Some answer -> answer
  | None ->
      (* A type that contains itself does so through an [indirect] variant
         or storage, so it is not trivial, which is the answer a cycle
         gets. *)
      t.trivial_types <- Types.add ty false t.trivial_types;
      let member : Memory_layout.member -> bool = function
        | Typed ty -> trivial t ty
        | Raw _ -> true
      in
      let answer =
        match t.kind_of ty with
        | Storage _ -> false
        | Shape (Scalar _) -> true
        | Shape (Record fields) -> List.for_all (fun (_, m) -> member m) fields
        | Shape (Array (element, _)) -> trivial t element
        | Shape (Sum variants) ->
            List.for_all
              (fun (v : Memory_layout.variant_shape) ->
                (not v.indirect) && List.for_all (fun (_, m) -> member m) v.fields)
              variants
      in
      t.trivial_types <- Types.add ty answer t.trivial_types;
      answer

(* A small builder for the LIR of one function. *)
type builder = {
  mutable locals : Lir.local_info list;  (** Most recent first *)
  mutable blocks : Lir.basic_block array;
  mutable current : int;
  mutable statements : Lir.statement list;  (** Of the current block, most recent first *)
}

let builder () = { locals = []; blocks = [||]; current = 0; statements = [] }

let local b ?name ty =
  b.locals <- { Lir.ty; name } :: b.locals;
  List.length b.locals - 1

let new_block b =
  b.blocks <- Array.append b.blocks [| { Lir.statements = []; terminator = Unreachable } |];
  Array.length b.blocks - 1

let start b block =
  b.current <- block;
  b.statements <- []

let emit b statement = b.statements <- statement :: b.statements

let finish b terminator =
  b.blocks.(b.current) <- { statements = List.rev b.statements; terminator };
  b.statements <- []

let build b ~parameters ~result : Lir.function_ =
  {
    parameters;
    result;
    returns = true;
    locals = Array.of_list (List.rev b.locals);
    blocks = b.blocks;
    environment = [];
  }

let at local : Lir.place = { root = Local local; projections = [] }

let ( / ) (place : Lir.place) projection : Lir.place =
  { place with projections = place.projections @ [ projection ] }

let usize_constant n = Lir.Constant (Integer (USize, Z.of_int n))

(* A counted loop from 0 to [count], running [body] with the index local. *)
let loop t b ~count body =
  let index = local b ~name:"index" (Value t.usize) in
  let going = local b (Raw Bool) in
  let test = new_block b in
  let inside = new_block b in
  let after = new_block b in
  emit b (Assign (at index, Use (usize_constant 0)));
  finish b (Goto test);
  start b test;
  emit b (Assign (at going, Binary (Less, Copy (at index), count)));
  finish b (Switch { value = Copy (at going); cases = [ (Z.one, inside) ]; default = Some after });
  start b inside;
  body index;
  emit b (Assign (at index, Binary (Add, Copy (at index), usize_constant 1)));
  finish b (Goto test);
  start b after

let instance key main : Lir.t = { key; main; nested = [||] }

let variant_shapes t ty =
  match t.kind_of ty with
  | Shape (Sum variants) -> variants
  | _ -> bug "%s is not a sum type" (Ground.to_string ty)

(* Drop *)

let droppable t : Memory_layout.member -> bool = function
  | Typed ty -> not (trivial t ty)
  | Raw _ -> false

let drop t ty =
  let b = builder () in
  let pointer = local b ~name:"value" (Pointer { target = Value ty; writable = true }) in
  let value : Lir.place = { root = Local pointer; projections = [ Deref ] } in
  start b (new_block b);
  (match t.kind_of ty with
  | Storage element ->
      if not (trivial t element) then
        loop t b
          ~count:(Copy (value / Field "length"))
          (fun index -> emit b (Drop (value / Field "buffer" / Index (Copy (at index)))));
      let owned = local b (Raw Bool) in
      let free = new_block b in
      let after = new_block b in
      emit b
        (Assign (at owned, Binary (Not_equal, Copy (value / Field "capacity"), usize_constant 0)));
      finish b (Switch { value = Copy (at owned); cases = [ (Z.one, free) ]; default = Some after });
      start b free;
      emit b
        (Call
           { target = Intrinsic Free; arguments = [ Copy (value / Field "buffer") ]; result = None });
      finish b (Goto after);
      start b after
  | Shape (Record fields) ->
      List.iter
        (fun (name, member) -> if droppable t member then emit b (Drop (value / Field name)))
        fields
  | Shape (Array (element, count)) ->
      if not (trivial t element) then
        loop t b ~count:(usize_constant count) (fun index ->
            emit b (Drop (value / Index (Copy (at index)))))
  | Shape (Sum variants) ->
      let after = new_block b in
      let cases =
        List.filter_map
          (fun (v : Memory_layout.variant_shape) ->
            if v.indirect || List.exists (fun (_, m) -> droppable t m) v.fields then begin
              let block = new_block b in
              let saved = (b.current, b.statements) in
              start b block;
              List.iter
                (fun (field, member) ->
                  if droppable t member then
                    emit b (Drop (value / Variant_field { variant = v.name; field })))
                v.fields;
              if v.indirect then emit b (Free_block { place = value; variant = v.name });
              finish b (Goto after);
              b.current <- fst saved;
              b.statements <- snd saved;
              Some (v.name, block)
            end
            else None)
          variants
      in
      finish b (Switch_variant { place = value; cases; default = Some after });
      start b after
  | Shape (Scalar _) -> ());
  finish b (Return None);
  instance (Drop ty) (build b ~parameters:[ pointer ] ~result:None)

(* Copy *)

let copy_signature t ty : Lir.signature =
  let parameter = Option.to_list (Convention.parameter t.env Read ty) in
  match Convention.result t.env ty with
  | Nothing -> { parameters = parameter; result = None; returns = true }
  | Returned result -> { parameters = parameter; result = Some result; returns = true }
  | Through_pointer pointer -> { parameters = pointer :: parameter; result = None; returns = true }

(* Copies [source] into [destination], both of type [ty]. *)
let copy_into t b ~destination ~source ty =
  if trivial t ty then emit b (Assign (destination, Use (Copy source)))
  else
    let signature = copy_signature t ty in
    let argument =
      match Convention.parameter t.env Read ty with
      | Some (Pointer _) -> [ Lir.Address { place = source; writable = false } ]
      | Some _ -> [ Lir.Copy source ]
      | None -> []
    in
    let target = Lir.Direct { function_ = Instance (Copy ty); signature } in
    match Convention.result t.env ty with
    | Through_pointer _ ->
        emit b
          (Call
             {
               target;
               arguments = Address { place = destination; writable = true } :: argument;
               result = None;
             })
    | Returned _ | Nothing ->
        emit b (Call { target; arguments = argument; result = Some destination })

(* The operand for a copy of a field, through a temporary when the field's
   type is not trivial. *)
let copied_field t b ~source (name, member) =
  match member with
  | Memory_layout.Raw _ -> (name, Lir.Copy source)
  | Typed ty when trivial t ty -> (name, Lir.Copy source)
  | Typed ty ->
      let temporary = local b (Value ty) in
      copy_into t b ~destination:(at temporary) ~source ty;
      (name, Lir.Move (at temporary))

let copy t ty =
  let b = builder () in
  let convention = Convention.result t.env ty in
  let result_pointer =
    match convention with
    | Through_pointer pointer -> Some (local b ~name:"result" pointer)
    | Returned _ | Nothing -> None
  in
  let parameter = Convention.parameter t.env Read ty in
  let self_local = Option.map (fun ty -> local b ~name:"self" ty) parameter in
  let self : Lir.place =
    match (parameter, self_local) with
    | Some (Pointer _), Some local -> { root = Local local; projections = [ Deref ] }
    | Some _, Some local -> at local
    | _ -> at 0
  in
  let result_local =
    match result_pointer with None -> Some (local b ~name:"copy" (Value ty)) | Some _ -> None
  in
  let result : Lir.place =
    match (result_pointer, result_local) with
    | Some pointer, _ -> { root = Local pointer; projections = [ Deref ] }
    | None, Some local -> at local
    | None, None -> bug "no place for the copy"
  in
  start b (new_block b);
  (if trivial t ty then emit b (Assign (result, Use (Copy self)))
   else
     match t.kind_of ty with
     | Storage element ->
         let layout = Memory_layout.of_type t.env element in
         let shared = local b (Raw Bool) in
         let empty = local b (Raw Bool) in
         let share = new_block b in
         let check = new_block b in
         let allocate = new_block b in
         let after = new_block b in
         (* Static bytes, an empty buffer, and elements of zero size are
            shared, not copied. *)
         emit b
           (Assign (at shared, Binary (Equal, Copy (self / Field "capacity"), usize_constant 0)));
         finish b
           (Switch { value = Copy (at shared); cases = [ (Z.one, share) ]; default = Some check });
         start b check;
         emit b (Assign (at empty, Binary (Equal, Copy (self / Field "length"), usize_constant 0)));
         finish b
           (Switch
              {
                value = Copy (at empty);
                cases = [ (Z.one, share) ];
                default = Some (if layout.size = 0 then share else allocate);
              });
         start b share;
         emit b (Assign (result, Use (Copy self)));
         finish b (Goto after);
         start b allocate;
         let bytes = local b (Value t.usize) in
         let buffer = local b ~name:"buffer" (Raw (Pointer (Data element))) in
         emit b
           (Assign
              (at bytes, Binary (Multiply, Copy (self / Field "length"), usize_constant layout.size)));
         emit b
           (Call
              {
                target = Intrinsic Allocate;
                arguments = [ Copy (at bytes); usize_constant layout.alignment ];
                result = Some (at buffer);
              });
         if trivial t element then
           emit b
             (Call
                {
                  target = Intrinsic Copy_bytes;
                  arguments = [ Copy (at buffer); Copy (self / Field "buffer"); Copy (at bytes) ];
                  result = None;
                })
         else
           loop t b
             ~count:(Copy (self / Field "length"))
             (fun index ->
               copy_into t b
                 ~destination:(at buffer / Index (Copy (at index)))
                 ~source:(self / Field "buffer" / Index (Copy (at index)))
                 element);
         emit b
           (Assign
              ( result,
                Build
                  {
                    ty;
                    variant = None;
                    fields =
                      [
                        ("buffer", Copy (at buffer));
                        ("length", Copy (self / Field "length"));
                        ("capacity", Copy (self / Field "length"));
                      ];
                  } ));
         finish b (Goto after);
         start b after
     | Shape (Record fields) ->
         let fields =
           List.map
             (fun (name, member) -> copied_field t b ~source:(self / Field name) (name, member))
             fields
         in
         emit b (Assign (result, Build { ty; variant = None; fields }))
     | Shape (Array (element, count)) ->
         loop t b ~count:(usize_constant count) (fun index ->
             copy_into t b
               ~destination:(result / Index (Copy (at index)))
               ~source:(self / Index (Copy (at index)))
               element)
     | Shape (Sum _) ->
         let after = new_block b in
         let cases =
           List.map
             (fun (v : Memory_layout.variant_shape) ->
               let block = new_block b in
               let saved = (b.current, b.statements) in
               start b block;
               let fields =
                 List.map
                   (fun (name, member) ->
                     copied_field t b
                       ~source:(self / Variant_field { variant = v.name; field = name })
                       (name, member))
                   v.fields
               in
               emit b (Assign (result, Build { ty; variant = Some v.name; fields }));
               finish b (Goto after);
               b.current <- fst saved;
               b.statements <- snd saved;
               (v.name, block))
             (variant_shapes t ty)
         in
         finish b (Switch_variant { place = self; cases; default = None });
         start b after
     | Shape (Scalar _) -> emit b (Assign (result, Use (Copy self))));
  (match result_local with
  | Some local -> finish b (Return (Some (Move (at local))))
  | None -> finish b (Return None));
  let parameters = Option.to_list result_pointer @ Option.to_list self_local in
  instance (Copy ty)
    (build b ~parameters
       ~result:
         (match convention with Returned ty -> Some ty | Nothing | Through_pointer _ -> None))
