type t = {
  mutable locals : Lir.local_info list;  (** Most recent first *)
  mutable local_count : int;
  mutable blocks : Lir.basic_block array;  (** With room to spare past [block_count] *)
  mutable block_count : int;
  mutable current : int;
  mutable statements : Lir.statement list;  (** Of the current block, most recent first *)
}

let empty_block : Lir.basic_block = { statements = []; terminator = Unreachable }

let create () =
  {
    locals = [];
    local_count = 0;
    blocks = Array.make 8 empty_block;
    block_count = 0;
    current = 0;
    statements = [];
  }

let local builder ?name ?(borrowed = false) ty =
  builder.locals <- { Lir.ty; name; borrowed } :: builder.locals;
  builder.local_count <- builder.local_count + 1;
  builder.local_count - 1

let local_type builder local = (List.nth builder.locals (builder.local_count - 1 - local)).ty

let block builder =
  if builder.block_count = Array.length builder.blocks then
    builder.blocks <- Array.append builder.blocks (Array.make builder.block_count empty_block);
  builder.block_count <- builder.block_count + 1;
  builder.block_count - 1

let current builder = builder.current

let start builder block =
  builder.current <- block;
  builder.statements <- []

let emit builder statement = builder.statements <- statement :: builder.statements

let finish builder terminator =
  builder.blocks.(builder.current) <- { statements = List.rev builder.statements; terminator };
  builder.statements <- []

let in_block builder block body =
  let current = builder.current and statements = builder.statements in
  start builder block;
  body ();
  builder.current <- current;
  builder.statements <- statements

let at = Lir.local_place

let ( / ) (place : Lir.place) projection : Lir.place =
  { place with projections = place.projections @ [ projection ] }

let usize number = Lir.Constant (Integer (USize, Z.of_int number))

let branch builder value ~yes ~no =
  finish builder (Switch { value; cases = [ (Z.one, yes) ]; default = Some no })

let when_ builder condition then_ =
  let inside = block builder in
  let after = block builder in
  branch builder condition ~yes:inside ~no:after;
  start builder inside;
  then_ ();
  finish builder (Goto after);
  start builder after

let loop builder ?(integer = Memory_layout.USize) ~index_type ~count body =
  let constant number = Lir.Constant (Integer (integer, Z.of_int number)) in
  let index = local builder ~name:"index" index_type in
  let going = local builder (Raw Bool) in
  let test = block builder in
  let inside = block builder in
  let after = block builder in
  emit builder (Assign (at index, Use (constant 0)));
  finish builder (Goto test);
  start builder test;
  emit builder (Assign (at going, Binary (Less, Copy (at index), count)));
  branch builder (Copy (at going)) ~yes:inside ~no:after;
  start builder inside;
  body index;
  emit builder (Assign (at index, Binary (Add, Copy (at index), constant 1)));
  finish builder (Goto test);
  start builder after

let build ?written_result builder ~parameters ~result : Lir.function_ =
  {
    parameters;
    written_result;
    result;
    returns = true;
    locals = Array.of_list (List.rev builder.locals);
    blocks = Array.sub builder.blocks 0 builder.block_count;
    environment = [];
  }
