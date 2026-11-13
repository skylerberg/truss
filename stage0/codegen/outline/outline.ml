let bug format = Compiler_bug.bug ~stage:"Outline" format

module Locals = Set.Make (Int)
module Blocks = Set.Make (Int)

let at = Lir.local_place

(* The fork of the first region that running the function reaches, which
   lies in no other fork's region. *)
let first_fork (function_ : Lir.function_) =
  List.find_map
    (fun block ->
      List.find_map
        (function
          | Lir.Region { fork; _ } -> Some fork
          | Regions_end { fork } -> bug "fork %d ends before it starts" fork
          | _ -> None)
        function_.blocks.(block).statements)
    (Lir.reverse_postorder function_.blocks)

let marks fork : Lir.statement -> bool = function
  | Region { fork = other; _ } | Regions_end { fork = other } -> other = fork
  | _ -> false

(* The function's blocks with each mark of the fork first in a block of its
   own making: a block is cut before each mark in it, and each piece but the
   last goes to the next. *)
let cut_at_marks fork (function_ : Lir.function_) : Lir.basic_block array =
  let added = ref [] in
  let next = ref (Array.length function_.blocks) in
  let fresh () =
    incr next;
    !next - 1
  in
  let cut (block : Lir.basic_block) : Lir.basic_block =
    (* Pieces in order, each a mark and the statements after it up to the next. *)
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
  let blocks = Array.map cut function_.blocks in
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
    let current = region kind start in
    match Option.map (fun next -> (next, mark_of next)) current.next with
    | Some (next, Some (Region { region; _ })) -> current :: from (next, region)
    | Some (_, Some (Regions_end _)) | None -> [ current ]
    | Some (_, _) -> bug "a region of fork %d that does not end at a mark" fork
  in
  match first with Some first -> from first | None -> bug "fork %d has no region" fork

let block_locals (block : Lir.basic_block) =
  let locals = ref Locals.empty in
  let visitor : Lir.visitor =
    {
      place =
        (fun place ->
          match place.root with Local local -> locals := Locals.add local !locals | Static _ -> ());
      operand = (fun _ -> ());
    }
  in
  List.iter (Lir.visit_statement visitor) block.statements;
  Lir.visit_terminator visitor block.terminator;
  !locals

(* The locals a block gives a whole new value. *)
let block_assigns (block : Lir.basic_block) =
  List.fold_left
    (fun assigned (statement : Lir.statement) ->
      match statement with
      | Assign ({ root = Local local; projections = [] }, _)
      | Call { result = Returned { root = Local local; projections = [] }; _ }
      | Call { result = Written { root = Local local; projections = [] }; _ } ->
          Locals.add local assigned
      | _ -> assigned)
    Locals.empty block.statements

let union_over blocks (set : Blocks.t) of_block =
  Blocks.fold (fun block locals -> Locals.union (of_block blocks.(block)) locals) set Locals.empty

(* Outlines the function's first fork. Gives the function without it and
   the nested functions made of its regions, which take the numbers from
   [first_number] on; or nothing when the function has no fork. *)
let outline_fork env ~first_number (function_ : Lir.function_) =
  match first_fork function_ with
  | None -> None
  | Some fork ->
      let blocks = cut_at_marks fork function_ in
      let regions = regions fork blocks in
      let count = List.length regions in
      let in_a_region =
        List.fold_left (fun all region -> Blocks.union region.blocks all) Blocks.empty regions
      in
      (* The locals of the code around the regions. Only code that can run
         counts: after a loop whose body always fails, the loop's own
         blocks that follow the body cannot, and the locals that they name
         are still the loop's alone. *)
      let outside =
        List.fold_left
          (fun locals number ->
            if Blocks.mem number in_a_region then locals
            else Locals.union (block_locals blocks.(number)) locals)
          (Locals.of_list function_.parameters)
          (Lir.reverse_postorder blocks)
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
        (fun region_index assigned_here ->
          List.iteri
            (fun other_region used ->
              if region_index <> other_region then
                match Locals.choose_opt (Locals.inter assigned_here used) with
                | Some local ->
                    bug "local %d is given a value in one region of fork %d and used in another"
                      local fork
                | None -> ())
            named)
        assigned;
      let end_block = (List.nth regions (count - 1)).next in
      let parent_locals = ref (Array.to_list function_.locals) in
      let parent_local info =
        parent_locals := !parent_locals @ [ info ];
        List.length !parent_locals - 1
      in
      let outlined =
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
              List.map (fun original -> (original, local function_.locals.(original))) part
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
                  let info = function_.locals.(original) in
                  if Locals.mem original elsewhere && not (Lir.erased env info.ty) then
                    captured :=
                      (Printf.sprintf "capture%d" (List.length !captured), original) :: !captured
                  else Hashtbl.replace own original (local info))
              used;
            let captured = List.rev !captured in
            (* The chunks of a fork run at the same time, so one that gave a
               shared local a whole new value would race with the others.
               The type checker lets no program do that, so it would be a
               local of the compiler's that belongs to each run. *)
            (match region.kind with
            | Chunk _ ->
                List.iter
                  (fun (_, original) ->
                    if Locals.mem original (List.nth assigned index) then
                      bug "local %d is given a value in the chunks of fork %d, which share it"
                        original fork)
                  captured
            | Branch | Task _ -> ());
            let place (lir_place : Lir.place) : Lir.place =
              match lir_place.root with
              | Static _ -> lir_place
              | Local original -> (
                  match Hashtbl.find_opt own original with
                  | Some mapped -> { lir_place with root = Local mapped }
                  | None -> (
                      match List.find_opt (fun (_, local) -> local = original) captured with
                      | Some (name, _) ->
                          {
                            root = Local environment;
                            projections = [ Lir.Deref; Field name; Deref ] @ lir_place.projections;
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
                      ( name,
                        Lir.Pointer { target = function_.locals.(original).ty; writable = true } ))
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
        match outlined with
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
              outlined
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
                      outlined;
                };
            ]
      in
      let start = (List.hd regions).start in
      let fills = List.concat_map (fun (_, _, _, fill, _) -> fill) outlined in
      (* The environment of a task region is filled once, at the end of
         the function's entry block. A loop can reach the region again
         while tasks it spawned earlier still read the environment, and
         filling it there again would be a data race. The addresses it
         holds are of this function's locals, which do not change. *)
      let at_entry =
        start <> 0 && match outlined with (_, _, _, _, Task _) :: _ -> true | _ -> false
      in
      if at_entry then
        blocks.(0) <- { (blocks.(0)) with statements = blocks.(0).statements @ fills };
      (* A fork whose last region always fails never ends. *)
      blocks.(start) <-
        {
          statements = (if at_entry then [] else fills) @ replacement;
          terminator = (match end_block with Some block -> Goto block | None -> Unreachable);
        };
      Option.iter
        (fun block ->
          blocks.(block) <- { (blocks.(block)) with statements = List.tl blocks.(block).statements })
        end_block;
      Some
        ( { function_ with locals = Array.of_list !parent_locals; blocks },
          List.map (fun (_, nested, _, _, _) -> nested) outlined )

(* The first loop whose body running the function reaches, which lies in
   no other loop's body: its head, the block that calls the method. *)
let first_loop (function_ : Lir.function_) =
  List.find_opt
    (fun block -> match function_.blocks.(block).terminator with Loop_call _ -> true | _ -> false)
    (Lir.reverse_postorder function_.blocks)

let is_exit loop (block : Lir.basic_block) =
  match block.statements with Loop_exit { loop = other } :: _ -> other = loop | _ -> false

(* Outlines the body of the function's first loop over a method in loop
   form. The body becomes a nested function, numbered [number], that takes
   its environment and its part, and returns whether to go on: it goes on
   where the body reaches its [Loop_next], and where it leaves by an exit,
   it records the exit's number, from 1, in the loop's [exit] and stops.
   The head then calls the method with the body as its last argument, and
   goes on at [after], where the method ended or the body stopped by
   [break], or at the exit the body recorded. *)
let outline_loop env ~number (function_ : Lir.function_) =
  match first_loop function_ with
  | None -> None
  | Some head -> (
      let blocks = function_.blocks in
      match blocks.(head).terminator with
      | Loop_call { loop; target; arguments; go_on; body = entry; after; exit } ->
          let part =
            match blocks.(entry).statements with
            | Loop_body { loop = other; part } :: _ when other = loop -> part
            | _ -> bug "the body of loop %d does not start where its call says" loop
          in
          (* The body's blocks, and the exits it leaves by, in the order
             first reached. *)
          let inside = ref Blocks.empty and exits = ref [] in
          let rec visit block =
            if not (Blocks.mem block !inside) then begin
              inside := Blocks.add block !inside;
              match blocks.(block).terminator with
              | Return _ | Yield _ -> bug "the body of loop %d returns or yields" loop
              | Loop_next { loop = other; _ } when other = loop -> ()
              | terminator ->
                  List.iter
                    (fun successor ->
                      if successor = head then bug "the body of loop %d goes to its head" loop
                      else if is_exit loop blocks.(successor) then
                        begin if not (List.mem successor !exits) then
                          exits := !exits @ [ successor ]
                        end
                      else visit successor)
                    (Lir.successors terminator)
            end
          in
          visit entry;
          let region = !inside and exits = !exits in
          let exit_number block =
            let rec find position = function
              | [] -> bug "block %d is no exit of loop %d" block loop
              | exit_block :: _ when exit_block = block -> position
              | _ :: rest -> find (position + 1) rest
            in
            find 1 exits
          in
          let outside =
            List.fold_left
              (fun locals number ->
                if Blocks.mem number region then locals
                else Locals.union (block_locals blocks.(number)) locals)
              (Locals.add exit (Locals.of_list function_.parameters))
              (Lir.reverse_postorder blocks)
          in
          let named = union_over blocks region block_locals in
          let locals = ref [] in
          let local info =
            locals := info :: !locals;
            List.length !locals - 1
          in
          let plain ty : Lir.local_info = { ty; name = None; borrowed = false } in
          let arrives =
            local { (plain (Lir.Raw (Nullable_pointer Opaque))) with name = Some "environment" }
          in
          let part_local =
            Option.map (fun original -> (original, local function_.locals.(original))) part
          in
          let environment =
            local (plain (Lir.Pointer { target = Environment number; writable = false }))
          in
          let own = Hashtbl.create 16 in
          Option.iter (fun (original, mapped) -> Hashtbl.replace own original mapped) part_local;
          let captured = ref [] in
          Locals.iter
            (fun original ->
              if not (Hashtbl.mem own original) then
                let info = function_.locals.(original) in
                if (Locals.mem original outside || original = exit) && not (Lir.erased env info.ty)
                then
                  captured :=
                    (Printf.sprintf "capture%d" (List.length !captured), original) :: !captured
                else Hashtbl.replace own original (local info))
            (Locals.add exit named);
          let captured = List.rev !captured in
          let place (lir_place : Lir.place) : Lir.place =
            match lir_place.root with
            | Static _ -> lir_place
            | Local original -> (
                match Hashtbl.find_opt own original with
                | Some mapped -> { lir_place with root = Local mapped }
                | None -> (
                    match List.find_opt (fun (_, local) -> local = original) captured with
                    | Some (name, _) ->
                        {
                          root = Local environment;
                          projections = [ Lir.Deref; Field name; Deref ] @ lir_place.projections;
                        }
                    | None ->
                        bug "local %d of the body of loop %d is neither its own nor captured"
                          original loop))
          in
          let go_on_value truth = Some (Lir.Constant (Bool truth)) in
          (* Block 0 reads the environment, then come the body's blocks, then
             one block for each exit, which records it and stops. *)
          let numbers = Hashtbl.create 16 in
          List.iteri
            (fun position block -> Hashtbl.replace numbers block (position + 1))
            (Blocks.elements region);
          let region_count = Blocks.cardinal region in
          let block target =
            match Hashtbl.find_opt numbers target with
            | Some mapped -> mapped
            | None ->
                if List.mem target exits then region_count + exit_number target
                else bug "the body of loop %d goes to block %d, outside it" loop target
          in
          let body =
            List.map
              (fun original ->
                let { Lir.statements; terminator } = blocks.(original) in
                let statements = if original = entry then List.tl statements else statements in
                {
                  Lir.statements = List.map (Lir.map_statement ~place ~block) statements;
                  terminator =
                    (match terminator with
                    | Loop_next { loop = other; _ } when other = loop ->
                        Lir.Return (go_on_value true)
                    | terminator -> Lir.map_terminator ~place ~block terminator);
                })
              (Blocks.elements region)
          in
          let exit_blocks =
            List.map
              (fun exit_block ->
                {
                  Lir.statements =
                    [
                      Assign
                        ( place (at exit),
                          Use (Constant (Integer (UInt32, Z.of_int (exit_number exit_block)))) );
                    ];
                  terminator = Return (go_on_value false);
                })
              exits
          in
          let entry_block : Lir.basic_block =
            {
              statements = [ Assign (at environment, Use (Copy (at arrives))) ];
              terminator = Goto (block entry);
            }
          in
          let nested : Lir.function_ =
            {
              parameters = arrives :: Option.to_list (Option.map snd part_local);
              written_result = None;
              result = Some go_on;
              returns = true;
              locals = Array.of_list (List.rev !locals);
              blocks = Array.of_list ((entry_block :: body) @ exit_blocks);
              environment =
                List.map
                  (fun (name, original) ->
                    (name, Lir.Pointer { target = function_.locals.(original).ty; writable = true }))
                  captured;
            }
          in
          (* The head fills the environment, calls the method with the body,
             and goes on where the body says. *)
          let parent_locals = ref (Array.to_list function_.locals) in
          let parent_local info =
            parent_locals := !parent_locals @ [ info ];
            List.length !parent_locals - 1
          in
          let holder = parent_local (plain (Lir.Environment number)) in
          let body_ty =
            match target with
            | Direct { signature; _ } -> (
                match List.rev signature.parameters with
                | last :: _ -> last
                | [] -> bug "a method in loop form that takes no body")
            | _ -> bug "loop %d calls a method that is not a direct call" loop
          in
          let function_value = parent_local (plain body_ty) in
          let fill =
            List.map
              (fun (name, original) ->
                Lir.Assign
                  ( { root = Local holder; projections = [ Field name ] },
                    Use (Address { place = at original; writable = true }) ))
              captured
          in
          let call : Lir.statement list =
            fill
            @ [
                Assign (at exit, Use (Constant (Integer (UInt32, Z.zero))));
                Assign
                  ( at function_value,
                    Function_value
                      {
                        code = Nested number;
                        environment = Some (Address { place = at holder; writable = false });
                      } );
                Call
                  {
                    target;
                    arguments = arguments @ [ Copy (at function_value) ];
                    result = Discarded;
                  };
              ]
          in
          let blocks = Array.copy blocks in
          blocks.(head) <-
            {
              statements = blocks.(head).statements @ call;
              terminator =
                Switch
                  {
                    value = Copy (at exit);
                    cases =
                      (Z.zero, after)
                      :: List.map
                           (fun exit_block -> (Z.of_int (exit_number exit_block), exit_block))
                           exits;
                    default = None;
                  };
            };
          List.iter
            (fun exit_block ->
              blocks.(exit_block) <-
                { (blocks.(exit_block)) with statements = List.tl blocks.(exit_block).statements })
            exits;
          Some ({ function_ with locals = Array.of_list !parent_locals; blocks }, [ nested ])
      | _ -> bug "a loop head that does not call")

(* Outlines the function's first fork or loop body, the one running the
   function reaches first, which lies in no other's region. *)
let outline_first env ~first_number (function_ : Lir.function_) =
  let order = Lir.reverse_postorder function_.blocks in
  let first matches = List.find_opt matches order in
  let fork_block =
    first (fun block ->
        List.exists
          (function Lir.Region _ -> true | _ -> false)
          function_.blocks.(block).statements)
  in
  let position block =
    let rec find index = function
      | [] -> max_int
      | other :: _ when other = block -> index
      | _ :: rest -> find (index + 1) rest
    in
    find 0 order
  in
  match (fork_block, first_loop function_) with
  | None, None -> None
  | Some fork, Some loop when position loop < position fork ->
      outline_loop env ~number:first_number function_
  | Some _, _ -> outline_fork env ~first_number function_
  | None, Some _ -> outline_loop env ~number:first_number function_

let instance env (instance : Lir.t) : Lir.t =
  let nested = ref (Array.to_list instance.nested) in
  (* Outlines every fork of a function, each after the forks around it, and
     the forks of each nested function that makes. *)
  let rec whole (function_ : Lir.function_) =
    match outline_first env ~first_number:(List.length !nested) function_ with
    | None -> function_
    | Some (without, outlined) ->
        let first = List.length !nested in
        nested := !nested @ outlined;
        List.iteri
          (fun index nested_function ->
            let finished = whole nested_function in
            nested :=
              List.mapi
                (fun region_index function_ ->
                  if region_index = first + index then finished else function_)
                !nested)
          outlined;
        whole without
  in
  let main = whole instance.main in
  let count = Array.length instance.nested in
  List.iteri
    (fun index function_ ->
      if index < count then
        let finished = whole function_ in
        nested :=
          List.mapi
            (fun region_index function_ -> if region_index = index then finished else function_)
            !nested)
    (Array.to_list instance.nested);
  { instance with main; nested = Array.of_list !nested }
