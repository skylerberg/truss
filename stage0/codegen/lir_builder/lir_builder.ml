let bug format = Compiler_bug.bug ~stage:"Lir_builder" format

module Locals = Set.Make (Int)

(* An outlined function: code written as a function of its own, nested in
   the instance, which the code around it runs through its environment. *)
type outlined = {
  parent : int;  (** The function it is written in: 0 for the function being built *)
  nested : int;  (** Its number among the instance's nested functions *)
  parts : Lir.local list;  (** The parent's locals that it is given as parameters *)
  holder : Lir.local;  (** The parent's local that holds its environment *)
  entry : Lir.block;
}

type t = {
  mutable locals : Lir.local_info list;  (** Most recent first *)
  mutable local_count : int;
  mutable blocks : Lir.basic_block array;  (** With room to spare past [block_count] *)
  mutable owners : int array;
      (** The function each block is written in: 0 for the function being built, [n] for the [n]th
          outlined function, -1 for a block not yet started *)
  mutable block_count : int;
  mutable current : int;
  mutable statements : Lir.statement list;  (** Of the current block, most recent first *)
  mutable outlined : outlined list;  (** Most recent first; the [n]th is function [n] *)
  mutable function_ : int;  (** The function being written *)
  mutable built_outlined : (int * Lir.function_) list;
}

let empty_block : Lir.basic_block = { statements = []; terminator = Unreachable }

let create () =
  {
    locals = [];
    local_count = 0;
    blocks = Array.make 8 empty_block;
    owners = Array.make 8 (-1);
    block_count = 0;
    current = 0;
    statements = [];
    outlined = [];
    function_ = 0;
    built_outlined = [];
  }

let local builder ?name ty =
  builder.locals <- { Lir.ty; name } :: builder.locals;
  builder.local_count <- builder.local_count + 1;
  builder.local_count - 1

let local_type builder local = (List.nth builder.locals (builder.local_count - 1 - local)).ty

let block builder =
  if builder.block_count = Array.length builder.blocks then begin
    builder.blocks <- Array.append builder.blocks (Array.make builder.block_count empty_block);
    builder.owners <- Array.append builder.owners (Array.make builder.block_count (-1))
  end;
  builder.block_count <- builder.block_count + 1;
  builder.block_count - 1

let start builder block =
  builder.owners.(block) <- builder.function_;
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

let outline builder ~nested ~parts body =
  let holder = local builder ~name:"environment" (Environment nested) in
  let entry = block builder in
  builder.outlined <-
    { parent = builder.function_; nested; parts; holder; entry } :: builder.outlined;
  let function_ = builder.function_
  and current = builder.current
  and statements = builder.statements in
  builder.function_ <- List.length builder.outlined;
  start builder entry;
  body ();
  builder.function_ <- function_;
  builder.current <- current;
  builder.statements <- statements;
  holder

(* The functions of the code built: the blocks of the function being built,
   and each outlined function.

   A local belongs to the innermost function that every function naming it
   is in, so that a local that one outlined function names alone belongs to
   each of its runs. An outlined function reaches a local of a function
   around it through its environment, which holds the local's address. The
   function that runs it fills the environment once, on entry: the
   addresses do not change, and a loop that runs the function again while
   tasks it spawned earlier read the environment does not write it again,
   which would be a data race. A local that takes no room is never shared:
   each function that names it has its own. *)
let functions ?written_result ~env builder ~parameters =
  let locals = Array.of_list (List.rev builder.locals) in
  let blocks = Array.sub builder.blocks 0 builder.block_count in
  let owners = Array.sub builder.owners 0 builder.block_count in
  let outlined = Array.of_list (List.rev builder.outlined) in
  let count = Array.length outlined + 1 in
  let parent number = outlined.(number - 1).parent in
  let rec depth number = if number = 0 then 0 else 1 + depth (parent number) in
  let rec enclosing first second =
    if first = second then first
    else if depth first >= depth second then enclosing (parent first) second
    else enclosing first (parent second)
  in
  let parts number = if number = 0 then [] else outlined.(number - 1).parts in
  let named = Array.make count Locals.empty in
  let name number local =
    if not (List.mem local (parts number)) then named.(number) <- Locals.add local named.(number)
  in
  Array.iteri
    (fun position (code : Lir.basic_block) ->
      let number = owners.(position) in
      if number >= 0 then begin
        let visitor : Lir.visitor =
          {
            place =
              (fun place ->
                match place.root with Local local -> name number local | Static _ -> ());
            operand = ignore;
          }
        in
        List.iter (Lir.visit_statement visitor) code.statements;
        Lir.visit_terminator visitor code.terminator
      end)
    blocks;
  List.iter (name 0) (parameters @ Option.to_list written_result);
  let home = Hashtbl.create 64 in
  Array.iteri
    (fun number named_here ->
      Locals.iter
        (fun local ->
          Hashtbl.replace home local
            (match Hashtbl.find_opt home local with
            | Some other -> enclosing number other
            | None -> number))
        named_here)
    named;
  (* The locals each function reaches through its environment: those that
     it, or a function outlined from it, names, and that a function around
     it owns. *)
  let captured = Array.make count Locals.empty in
  Array.iteri
    (fun number named_here ->
      Locals.iter
        (fun local ->
          if not (Lir.erased env locals.(local).ty) then
            let owner = Hashtbl.find home local in
            let rec reach number =
              if number <> owner then begin
                captured.(number) <- Locals.add local captured.(number);
                reach (parent number)
              end
            in
            reach number)
        named_here)
    named;
  let captures number =
    List.mapi
      (fun position local -> (local, Printf.sprintf "capture%d" position))
      (Locals.elements captured.(number))
  in
  (* The statements that fill the environments of the functions outlined
     from a function. *)
  let fills number =
    List.concat
      (List.mapi
         (fun index (outlined : outlined) ->
           if outlined.parent <> number then []
           else
             List.map
               (fun (local, field) ->
                 Lir.Assign
                   ( { root = Local outlined.holder; projections = [ Field field ] },
                     Use (Address { place = at local; writable = true }) ))
               (captures (index + 1)))
         (Array.to_list outlined))
  in
  let main_blocks =
    Array.mapi (fun position code -> if owners.(position) <= 0 then code else empty_block) blocks
  in
  if count > 1 then
    main_blocks.(0) <- { (main_blocks.(0)) with statements = fills 0 @ main_blocks.(0).statements };
  let outlined_function number =
    let outlined = outlined.(number - 1) in
    let fresh = ref [] in
    let local (info : Lir.local_info) =
      fresh := info :: !fresh;
      List.length !fresh - 1
    in
    let arrives = local { ty = Raw (Nullable_pointer Opaque); name = Some "environment" } in
    let mapped = Hashtbl.create 16 in
    let parameters =
      List.map
        (fun original ->
          let parameter = local locals.(original) in
          Hashtbl.replace mapped original parameter;
          parameter)
        outlined.parts
    in
    let environment =
      local { ty = Pointer { target = Environment outlined.nested; writable = false }; name = None }
    in
    let captures = captures number in
    let place (written : Lir.place) : Lir.place =
      match written.root with
      | Static _ -> written
      | Local original -> (
          match (Hashtbl.find_opt mapped original, List.assoc_opt original captures) with
          | Some own, _ -> { written with root = Local own }
          | None, Some field ->
              {
                root = Local environment;
                projections = Deref :: Field field :: Deref :: written.projections;
              }
          | None, None ->
              let own = local locals.(original) in
              Hashtbl.replace mapped original own;
              { written with root = Local own })
    in
    let numbers = Hashtbl.create 16 in
    let written =
      List.filter
        (fun position -> owners.(position) = number)
        (List.init (Array.length blocks) Fun.id)
    in
    List.iteri (fun index position -> Hashtbl.replace numbers position (index + 1)) written;
    let block target =
      match Hashtbl.find_opt numbers target with
      | Some mapped -> mapped
      | None -> bug "outlined function %d goes to block %d, outside it" number target
    in
    let rewrite (code : Lir.basic_block) : Lir.basic_block =
      {
        statements = List.map (Lir.map_statement ~place ~block) code.statements;
        terminator = Lir.map_terminator ~place ~block code.terminator;
      }
    in
    let body = List.map (fun position -> rewrite blocks.(position)) written in
    let entry : Lir.basic_block =
      {
        statements =
          Assign (at environment, Use (Copy (at arrives)))
          :: List.map (Lir.map_statement ~place ~block) (fills number);
        terminator = Goto (block outlined.entry);
      }
    in
    ( outlined.nested,
      {
        Lir.parameters = arrives :: parameters;
        written_result = None;
        result = None;
        returns = true;
        locals = Array.of_list (List.rev !fresh);
        blocks = Array.of_list (entry :: body);
        environment =
          List.map
            (fun (original, field) ->
              (field, Lir.Pointer { target = locals.(original).ty; writable = true }))
            captures;
      } )
  in
  (main_blocks, List.init (count - 1) (fun index -> outlined_function (index + 1)))

let build ?written_result ?env builder ~parameters ~result : Lir.function_ =
  let blocks =
    match (builder.outlined, env) with
    | [], _ -> Array.sub builder.blocks 0 builder.block_count
    | _ :: _, Some env ->
        let blocks, outlined = functions ?written_result ~env builder ~parameters in
        builder.built_outlined <- outlined;
        blocks
    | _ :: _, None -> bug "a function with outlined code built without a layout environment"
  in
  {
    parameters;
    written_result;
    result;
    returns = true;
    locals = Array.of_list (List.rev builder.locals);
    blocks;
    environment = [];
  }

let outlined_functions builder = builder.built_outlined
