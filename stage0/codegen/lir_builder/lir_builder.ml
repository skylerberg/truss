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

let local b ?name ?(borrowed = false) ty =
  b.locals <- { Lir.ty; name; borrowed } :: b.locals;
  b.local_count <- b.local_count + 1;
  b.local_count - 1

let local_type b local = (List.nth b.locals (b.local_count - 1 - local)).ty

let block b =
  if b.block_count = Array.length b.blocks then
    b.blocks <- Array.append b.blocks (Array.make b.block_count empty_block);
  b.block_count <- b.block_count + 1;
  b.block_count - 1

let current b = b.current

let start b block =
  b.current <- block;
  b.statements <- []

let emit b statement = b.statements <- statement :: b.statements

let finish b terminator =
  b.blocks.(b.current) <- { statements = List.rev b.statements; terminator };
  b.statements <- []

let aside b block f =
  let current = b.current and statements = b.statements in
  start b block;
  f ();
  b.current <- current;
  b.statements <- statements

let at local : Lir.place = { root = Local local; projections = [] }

let ( / ) (place : Lir.place) projection : Lir.place =
  { place with projections = place.projections @ [ projection ] }

let usize n = Lir.Constant (Integer (USize, Z.of_int n))

let when_ b condition then_ =
  let inside = block b in
  let after = block b in
  finish b (Switch { value = condition; cases = [ (Z.one, inside) ]; default = Some after });
  start b inside;
  then_ ();
  finish b (Goto after);
  start b after

let loop b ~usize:usize_ty ~count body =
  let index = local b ~name:"index" (Value usize_ty) in
  let going = local b (Raw Bool) in
  let test = block b in
  let inside = block b in
  let after = block b in
  emit b (Assign (at index, Use (usize 0)));
  finish b (Goto test);
  start b test;
  emit b (Assign (at going, Binary (Less, Copy (at index), count)));
  finish b (Switch { value = Copy (at going); cases = [ (Z.one, inside) ]; default = Some after });
  start b inside;
  body index;
  emit b (Assign (at index, Binary (Add, Copy (at index), usize 1)));
  finish b (Goto test);
  start b after

let build ?written_result b ~parameters ~result : Lir.function_ =
  {
    parameters;
    written_result;
    result;
    returns = true;
    locals = Array.of_list (List.rev b.locals);
    blocks = Array.sub b.blocks 0 b.block_count;
    environment = [];
  }
