let bug format = Compiler_bug.bug ~stage:"Outline" format

module Locals = Set.Make (Int)
module Blocks = Set.Make (Int)

let at local : Lir.place = { root = Local local; projections = [] }

(* The fork of the first region that running the function reaches, which
   lies in no other fork's region. *)
let first_fork (f : Lir.function_) =
  List.find_map
    (fun block ->
      List.find_map
        (function
          | Lir.Region { fork; _ } -> Some fork
          | Regions_end { fork } -> bug "fork %d ends before it starts" fork
          | _ -> None)
        f.blocks.(block).statements)
    (Lir.reverse_postorder f.blocks)

let marks fork : Lir.statement -> bool = function
  | Region { fork = other; _ } | Regions_end { fork = other } -> other = fork
  | _ -> false

(* The function's blocks with each mark of the fork first in a block of its
   own making: a block is cut before each mark in it, and each piece but the
   last goes to the next. *)
let cut_at_marks fork (f : Lir.function_) : Lir.basic_block array =
  let added = ref [] in
  let next = ref (Array.length f.blocks) in
  let fresh () =
    incr next;
    !next - 1
  in
  let cut (block : Lir.basic_block) : Lir.basic_block =
    (* Pieces in order, each a mark and what follows it up to the next. *)
    let rec pieces current = function
      | [] -> [ List.rev current ]
      | statement :: rest when marks fork statement && current <> [] ->
          List.rev current :: pieces [ statement ] rest
      | statement :: rest -> pieces (statement :: current) rest
    in
    match pieces [] block.statements with
    | [] | [ _ ] -> block
    | first :: later ->
        let numbered =
          List.rev
            (List.fold_left
               (fun numbered statements -> (fresh (), statements) :: numbered)
               [] later)
        in
        let rec add = function
          | [] -> ()
          | [ (number, statements) ] ->
              added := (number, { Lir.statements; terminator = block.terminator }) :: !added
          | (number, statements) :: ((following, _) :: _ as rest) ->
              added := (number, { Lir.statements; terminator = Goto following }) :: !added;
              add rest
        in
        add numbered;
        { statements = first; terminator = Goto (fst (List.hd numbered)) }
  in
  let blocks = Array.map cut f.blocks in
  let all = Array.make !next { Lir.statements = []; terminator = Unreachable } in
  Array.blit blocks 0 all 0 (Array.length blocks);
  List.iter (fun (number, block) -> all.(number) <- block) !added;
  all

type region = {
  kind : Lir.region;
  start : int;  (** The block its mark is first in *)
  blocks : Blocks.t;
  next : int option;
      (** The block of the next mark, which every way out of the region goes to. A region that
          always fails has no way out. *)
}

(* The fork's regions in order, from the blocks cut at its marks. *)
let regions fork (blocks : Lir.basic_block array) =
  let mark_of block =
    match blocks.(block).statements with
    | statement :: _ when marks fork statement -> Some statement
    | _ -> None
  in
  let region kind start =
    let inside = ref Blocks.empty and next = ref None in
    let rec visit block =
      if not (Blocks.mem block !inside) then begin
        inside := Blocks.add block !inside;
        (match blocks.(block).terminator with
        | Return _ | Yield _ -> bug "a region of fork %d that returns or yields" fork
        | _ -> ());
        List.iter
          (fun successor ->
            if mark_of successor <> None then
              match !next with
              | Some other when other <> successor ->
                  bug "a region of fork %d with two ways out" fork
              | _ -> next := Some successor
            else visit successor)
          (Lir.successors blocks.(block).terminator)
      end
    in
    visit start;
    { kind; start; blocks = !inside; next = !next }
  in
  let first =
    List.find_map
      (fun block ->
        match mark_of block with Some (Region { region; _ }) -> Some (block, region) | _ -> None)
      (Lir.reverse_postorder blocks)
  in
  (* The regions after one that always fails are never reached, in order
     or at once, since a failure ends the run. *)
  let rec from (start, kind) =
    let found = region kind start in
    match Option.map (fun next -> (next, mark_of next)) found.next with
    | Some (next, Some (Region { region; _ })) -> found :: from (next, region)
    | Some (_, Some (Regions_end _)) | None -> [ found ]
    | Some (_, _) -> bug "a region of fork %d that does not end at a mark" fork
  in
  match first with Some first -> from first | None -> bug "fork %d has no region" fork

(* The locals a block names. *)
let block_locals (block : Lir.basic_block) =
  let found = ref Locals.empty in
  let visitor : Lir.visitor =
    {
      place =
        (fun place ->
          match place.root with Local l -> found := Locals.add l !found | Static _ -> ());
      operand = (fun _ -> ());
    }
  in
  List.iter (Lir.visit_statement visitor) block.statements;
  Lir.visit_terminator visitor block.terminator;
  !found

(* The locals a block gives a whole new value. *)
let block_assigns (block : Lir.basic_block) =
  List.fold_left
    (fun found (statement : Lir.statement) ->
      match statement with
      | Assign ({ root = Local l; projections = [] }, _)
      | Call { result = Returned { root = Local l; projections = [] }; _ }
      | Call { result = Written { root = Local l; projections = [] }; _ } ->
          Locals.add l found
      | _ -> found)
    Locals.empty block.statements

let union_over blocks (set : Blocks.t) of_block =
  Blocks.fold (fun block found -> Locals.union (of_block blocks.(block)) found) set Locals.empty

(* Outlines the function's first fork. Gives the function without it and
   the nested functions made of its regions, which take the numbers from
   [first_number] on; or nothing when the function has no fork. *)
let outline_fork env ~first_number (f : Lir.function_) =
  match first_fork f with
  | None -> None
  | Some fork ->
      let blocks = cut_at_marks fork f in
      let regions = regions fork blocks in
      let count = List.length regions in
      let in_a_region =
        List.fold_left (fun all region -> Blocks.union region.blocks all) Blocks.empty regions
      in
      let outside =
        let found = ref (Locals.of_list f.parameters) in
        Array.iteri
          (fun number block ->
            if not (Blocks.mem number in_a_region) then
              found := Locals.union (block_locals block) !found)
          blocks;
        (* A region's start names the locals of its part of the range,
           which are the region's to read, not the code's around it. *)
        !found
      in
      (* The locals that each region's code refers to. The locals of the
         region's own mark are excluded. *)
      let named =
        List.map
          (fun region ->
            union_over blocks region.blocks (fun block ->
                if block == blocks.(region.start) then
                  block_locals { block with statements = List.tl block.statements }
                else block_locals block))
          regions
      in
      let assigned =
        List.map (fun region -> union_over blocks region.blocks block_assigns) regions
      in
      (* No two regions may share a local that one of them gives a whole
         new value: the type checker lets no program do that, so it would
         be a temporary of the compiler's used twice. *)
      List.iteri
        (fun i given ->
          List.iteri
            (fun j used ->
              if i <> j then
                match Locals.choose_opt (Locals.inter given used) with
                | Some local ->
                    bug "local %d is given a value in one region of fork %d and used in another"
                      local fork
                | None -> ())
            named)
        assigned;
      let end_block = (List.nth regions (count - 1)).next in
      let parent_locals = ref (Array.to_list f.locals) in
      let parent_local info =
        parent_locals := !parent_locals @ [ info ];
        List.length !parent_locals - 1
      in
      let made =
        List.mapi
          (fun index region ->
            let number = first_number + index in
            let used = List.nth named index in
            let elsewhere =
              List.fold_left Locals.union outside
                (List.filteri (fun other _ -> other <> index) named)
            in
            let part =
              match region.kind with
              | Chunk { first; last } -> [ first; last ]
              | Task { item; _ } -> [ item ]
              | Branch -> []
            in
            (* The nested function's locals: its environment as it arrives
               and as a pointer to the environment's type, the part of the
               range for a chunk, then each local the region has to
               itself. *)
            let locals = ref [] in
            let local info =
              locals := info :: !locals;
              List.length !locals - 1
            in
            let plain ty : Lir.local_info = { ty; name = None; borrowed = false } in
            let arrives =
              local { (plain (Lir.Raw (Nullable_pointer Opaque))) with name = Some "environment" }
            in
            let part_locals =
              List.map (fun original -> (original, local f.locals.(original))) part
            in
            let environment =
              local (plain (Lir.Pointer { target = Environment number; writable = false }))
            in
            let captured = ref [] in
            let own = Hashtbl.create 16 in
            List.iter (fun (original, mapped) -> Hashtbl.replace own original mapped) part_locals;
            Locals.iter
              (fun original ->
                if not (Hashtbl.mem own original) then
                  let info = f.locals.(original) in
                  if Locals.mem original elsewhere && not (Lir.erased env info.ty) then
                    captured :=
                      (Printf.sprintf "capture%d" (List.length !captured), original) :: !captured
                  else Hashtbl.replace own original (local info))
              used;
            let captured = List.rev !captured in
            let place (p : Lir.place) : Lir.place =
              match p.root with
              | Static _ -> p
              | Local original -> (
                  match Hashtbl.find_opt own original with
                  | Some mapped -> { p with root = Local mapped }
                  | None -> (
                      match List.find_opt (fun (_, l) -> l = original) captured with
                      | Some (name, _) ->
                          {
                            root = Local environment;
                            projections = [ Lir.Deref; Field name; Deref ] @ p.projections;
                          }
                      | None -> bug "local %d of a region is neither its own nor captured" original)
                  )
            in
            (* Block 0 reads the environment, block 1 returns, and the
               region's blocks follow. *)
            let numbers = Hashtbl.create 16 in
            List.iteri
              (fun position block -> Hashtbl.replace numbers block (position + 2))
              (Blocks.elements region.blocks);
            let block target =
              if Some target = region.next then 1
              else
                match Hashtbl.find_opt numbers target with
                | Some mapped -> mapped
                | None -> bug "a region of fork %d goes to block %d, outside it" fork target
            in
            let body =
              List.map
                (fun original ->
                  let { Lir.statements; terminator } = blocks.(original) in
                  let statements =
                    if original = region.start then List.tl statements else statements
                  in
                  {
                    Lir.statements = List.map (Lir.map_statement ~place ~block) statements;
                    terminator = Lir.map_terminator ~place ~block terminator;
                  })
                (Blocks.elements region.blocks)
            in
            let entry : Lir.basic_block =
              {
                statements = [ Assign (at environment, Use (Copy (at arrives))) ];
                terminator = Goto (block region.start);
              }
            in
            let nested : Lir.function_ =
              {
                parameters = arrives :: List.map snd part_locals;
                written_result = None;
                result = None;
                returns = true;
                locals = Array.of_list (List.rev !locals);
                blocks =
                  Array.of_list (entry :: { statements = []; terminator = Return None } :: body);
                environment =
                  List.map
                    (fun (name, original) ->
                      (name, Lir.Pointer { target = f.locals.(original).ty; writable = true }))
                    captured;
              }
            in
            let holder = parent_local (plain (Lir.Environment number)) in
            let fill =
              List.map
                (fun (name, original) ->
                  Lir.Assign
                    ( { root = Local holder; projections = [ Field name ] },
                      Use (Address { place = at original; writable = true }) ))
                captured
            in
            (number, nested, holder, fill, region.kind))
          regions
      in
      let address holder = Lir.Address { place = at holder; writable = false } in
      (* The statements that replace the regions: one fork statement, or
         for task regions, an assignment of each nested function to its
         region's [function_value]. *)
      let replacement : Lir.statement list =
        match made with
        | [ (number, _, holder, _, Chunk { first; last }) ] ->
            [
              Fork_range
                {
                  body = number;
                  environment = address holder;
                  first = Copy (at first);
                  last = Copy (at last);
                };
            ]
        | (_, _, _, _, Task _) :: _ ->
            List.map
              (fun (number, _, holder, _, (kind : Lir.region)) ->
                match kind with
                | Task { function_value; _ } ->
                    Lir.Assign
                      ( at function_value,
                        Function_value { code = Nested number; environment = Some (address holder) }
                      )
                | Branch | Chunk _ -> bug "fork %d mixes task regions with other regions" fork)
              made
        | _ ->
            [
              Fork
                {
                  branches =
                    List.map
                      (fun (number, _, holder, _, (kind : Lir.region)) ->
                        (match kind with
                        | Branch -> ()
                        | Chunk _ | Task _ -> bug "fork %d has a branch among other regions" fork);
                        (number, address holder))
                      made;
                };
            ]
      in
      let start = (List.hd regions).start in
      (* A fork whose last region always fails never ends. *)
      blocks.(start) <-
        {
          statements = List.concat_map (fun (_, _, _, fill, _) -> fill) made @ replacement;
          terminator = (match end_block with Some block -> Goto block | None -> Unreachable);
        };
      Option.iter
        (fun block ->
          blocks.(block) <- { (blocks.(block)) with statements = List.tl blocks.(block).statements })
        end_block;
      Some
        ( { f with locals = Array.of_list !parent_locals; blocks },
          List.map (fun (_, nested, _, _, _) -> nested) made )

let instance env (instance : Lir.t) : Lir.t =
  let nested = ref (Array.to_list instance.nested) in
  (* Outlines every fork of a function, each after the forks around it, and
     the forks of each nested function that makes. *)
  let rec whole (f : Lir.function_) =
    match outline_fork env ~first_number:(List.length !nested) f with
    | None -> f
    | Some (without, made) ->
        let first = List.length !nested in
        nested := !nested @ made;
        List.iteri
          (fun index made ->
            let finished = whole made in
            nested := List.mapi (fun i f -> if i = first + index then finished else f) !nested)
          made;
        whole without
  in
  let main = whole instance.main in
  let count = Array.length instance.nested in
  List.iteri
    (fun index f ->
      if index < count then
        let finished = whole f in
        nested := List.mapi (fun i f -> if i = index then finished else f) !nested)
    (Array.to_list instance.nested);
  { instance with main; nested = Array.of_list !nested }
