let bug format = Compiler_bug.bug ~stage:"Drops" format

(* A move path: a local and the fields, variant fields, and dereferences
   after it. An element is never moved out, so paths have no indexes. *)
type step = Field of string | Variant of string * string | Deref
type path = { local : int; steps : step list }

let path_of_place (place : Lir.place) =
  match place.root with
  | Static _ -> None
  | Local local ->
      let rec steps acc = function
        | [] -> Some { local; steps = List.rev acc }
        | Lir.Field name :: rest -> steps (Field name :: acc) rest
        | Variant_field { variant; field } :: rest -> steps (Variant (variant, field) :: acc) rest
        | Deref :: rest -> steps (Deref :: acc) rest
        | Index _ :: _ -> None
      in
      steps [] place.projections

let place_of_path path : Lir.place =
  {
    root = Local path.local;
    projections =
      List.map
        (function
          | Field name -> Lir.Field name
          | Variant (variant, field) -> Variant_field { variant; field }
          | Deref -> Deref)
        path.steps;
  }

let rec is_prefix prefix steps =
  match (prefix, steps) with
  | [], _ -> true
  | first_step :: prefix, other_step :: steps -> first_step = other_step && is_prefix prefix steps
  | _ :: _, [] -> false

(* [inner] is [outer] or lies inside it. *)
let is_inside ~outer inner = outer.local = inner.local && is_prefix outer.steps inner.steps

let rec operand_moves (operand : Lir.operand) =
  match operand with
  | Move place | Moved_address place -> place_index_moves place @ [ place ]
  | Copy place | Address { place; _ } -> place_index_moves place
  | Constant _ -> []

and place_index_moves (place : Lir.place) =
  List.concat_map
    (function Lir.Index operand -> operand_moves operand | _ -> [])
    place.projections

let rvalue_moves (rvalue : Lir.rvalue) =
  match rvalue with
  | Use operand | Unary (_, operand) | Convert (operand, _) -> operand_moves operand
  | Binary (_, left, right) -> operand_moves left @ operand_moves right
  | Build { fields; _ } -> List.concat_map (fun (_, operand) -> operand_moves operand) fields
  | Is_variant (place, _) -> place_index_moves place
  | Function_value { environment; _ } -> Option.fold ~none:[] ~some:operand_moves environment

let target_moves target = List.concat_map operand_moves (Lir.target_operands target)

(* A statement's effect on ownership: the places it moves out of, then the
   place it gives a value, then the place it drops. *)
type ownership = { moves : Lir.place list; init : Lir.place option; dropped : Lir.place option }

let statement_effect (statement : Lir.statement) =
  match statement with
  | Assign (place, rvalue) ->
      { moves = place_index_moves place @ rvalue_moves rvalue; init = Some place; dropped = None }
  | Call { target; arguments; result } ->
      {
        moves =
          (target_moves target
          @ List.concat_map operand_moves arguments
          @
          match result with
          | Returned written | Written written -> place_index_moves written
          | Discarded -> []);
        init =
          (match result with
          | Returned written | Written written -> Some written
          | Discarded -> None);
        dropped = None;
      }
  | Drop place -> { moves = place_index_moves place; init = None; dropped = Some place }
  | Free_block _ | Region _ | Regions_end _ -> { moves = []; init = None; dropped = None }
  | Fork _ | Fork_range _ -> bug "a fork, which outlining makes after drops are elaborated"
  | Echo { text; length; _ } ->
      { moves = operand_moves text @ operand_moves length; init = None; dropped = None }

let terminator_moves (terminator : Lir.terminator) =
  match terminator with
  | Switch { value; _ } -> operand_moves value
  | Return value -> Option.fold ~none:[] ~some:operand_moves value
  | Fail { message; length; _ } -> operand_moves message @ operand_moves length
  | Yield { value; _ } -> operand_moves value
  | Switch_variant { place; _ } -> place_index_moves place
  | Goto _ | Unreachable -> []

type analysis = {
  env : Memory_layout.env;
  needs_drop : Ground.ty -> bool;
  environment : int -> (string * Lir.ty) list;
  function_ : Lir.function_;
  paths : path array;  (** Every tracked path *)
  inside : int list array;  (** For each path, the tracked paths within it, itself included *)
}

let path_type analysis path =
  Lir.place_type analysis.env ~environment:analysis.environment analysis.function_
    (place_of_path path)

let path_needs_drop analysis path =
  match path_type analysis path with Some (Value ty) -> analysis.needs_drop ty | _ -> false

let owns analysis path =
  (not analysis.function_.locals.(path.local).borrowed) && path_needs_drop analysis path

(* A path as a message names it: its local, by number and name, and its
   steps. *)
let describe analysis path =
  let local =
    match analysis.function_.locals.(path.local).name with
    | Some name -> Printf.sprintf "local %d (%s)" path.local name
    | None -> Printf.sprintf "local %d" path.local
  in
  List.fold_left
    (fun text step ->
      match step with
      | Field name -> text ^ "." ^ name
      | Variant (variant, field) -> text ^ "." ^ variant ^ "." ^ field
      | Deref -> "*" ^ text)
    local path.steps

let fields_of (layout : Memory_layout.t) =
  match layout.form with Struct fields -> fields | _ -> []

(* An element written gives its whole array a value: lowering writes every
   element of a new array before anything reads it, and elements are never
   moved out. *)
let before_index (place : Lir.place) : Lir.place =
  let rec take = function [] | Lir.Index _ :: _ -> [] | step :: rest -> step :: take rest in
  { place with projections = take place.projections }

(* Tracks every path that is moved, given a value, or dropped, whose type
   has something to drop, and every path around one that holds a value. *)
let analyse env ~needs_drop ~environment (function_ : Lir.function_) =
  let partial = { env; needs_drop; environment; function_; paths = [||]; inside = [||] } in
  let candidates = ref [] in
  let add path = if not (List.mem path !candidates) then candidates := path :: !candidates in
  let consider place =
    match path_of_place place with
    | Some path when owns partial path ->
        let rec ancestors steps =
          add { path with steps };
          match List.rev steps with [] -> () | _ :: rest -> ancestors (List.rev rest)
        in
        ancestors path.steps
    | _ -> ()
  in
  Array.iter
    (fun (block : Lir.basic_block) ->
      List.iter
        (fun statement ->
          let ownership = statement_effect statement in
          List.iter consider ownership.moves;
          Option.iter (fun place -> consider (before_index place)) ownership.init;
          Option.iter consider ownership.dropped)
        block.statements;
      List.iter consider (terminator_moves block.terminator))
    function_.blocks;
  let paths =
    Array.of_list (List.filter (fun path -> owns partial path) (List.sort compare !candidates))
  in
  let inside =
    Array.map
      (fun outer ->
        List.filter_map
          (fun (path_index, inner) -> if is_inside ~outer inner then Some path_index else None)
          (List.mapi (fun path_index path -> (path_index, path)) (Array.to_list paths)))
      paths
  in
  { partial with paths; inside }

let index analysis path =
  let rec find path_index =
    if path_index >= Array.length analysis.paths then None
    else if analysis.paths.(path_index) = path then Some path_index
    else find (path_index + 1)
  in
  find 0

(* For each tracked path, whether it may hold a value and whether it may
   not. *)
type state = { maybe_init : bool array; maybe_uninit : bool array }

let copy_state state =
  { maybe_init = Array.copy state.maybe_init; maybe_uninit = Array.copy state.maybe_uninit }

let join into state =
  let changed = ref false in
  Array.iteri
    (fun path_index holds ->
      if holds && not into.maybe_init.(path_index) then begin
        into.maybe_init.(path_index) <- true;
        changed := true
      end)
    state.maybe_init;
  Array.iteri
    (fun path_index holds ->
      if holds && not into.maybe_uninit.(path_index) then begin
        into.maybe_uninit.(path_index) <- true;
        changed := true
      end)
    state.maybe_uninit;
  !changed

(* The tracked paths that lie within a place. *)
let affected analysis place =
  match path_of_place place with
  | None -> []
  | Some outer ->
      List.filter_map
        (fun (path_index, inner) -> if is_inside ~outer inner then Some path_index else None)
        (List.mapi (fun path_index path -> (path_index, path)) (Array.to_list analysis.paths))

let set_uninit analysis state place =
  List.iter
    (fun path_index ->
      state.maybe_init.(path_index) <- false;
      state.maybe_uninit.(path_index) <- true)
    (affected analysis place)

let definitely_init state path_index =
  state.maybe_init.(path_index) && not state.maybe_uninit.(path_index)

(* A record holds a value once every part of it with something to drop
   does, however it was given them: lowering may fill a new record's fields
   one by one. *)
let rec promote analysis state path =
  match List.rev path.steps with
  | Field _ :: rest -> (
      let parent = { path with steps = List.rev rest } in
      match (index analysis parent, path_type analysis parent) with
      | Some parent_index, Some (Value ty) when not (definitely_init state parent_index) ->
          let is_initialized (field : Memory_layout.field) =
            let inner = { parent with steps = parent.steps @ [ Field field.name ] } in
            (not (owns analysis inner))
            ||
            match index analysis inner with
            | Some inner_index -> definitely_init state inner_index
            | None -> false
          in
          if List.for_all is_initialized (fields_of (Memory_layout.of_type analysis.env ty)) then begin
            state.maybe_init.(parent_index) <- true;
            state.maybe_uninit.(parent_index) <- false;
            promote analysis state parent
          end
      | _ -> ())
  | _ -> ()

(* Giving a place a value gives one to its parts, but not to a pointer's
   target. *)
let set_init analysis state place =
  let place = before_index place in
  let reached =
    match path_of_place place with
    | Some outer ->
        List.filter
          (fun path_index ->
            let inner = analysis.paths.(path_index) in
            not
              (List.mem Deref
                 (List.filteri
                    (fun step_index _ -> step_index >= List.length outer.steps)
                    inner.steps)))
          (affected analysis place)
    | None -> []
  in
  List.iter
    (fun path_index ->
      state.maybe_init.(path_index) <- true;
      state.maybe_uninit.(path_index) <- false)
    reached;
  Option.iter (promote analysis state) (path_of_place place)

let apply analysis state statement =
  let ownership = statement_effect statement in
  List.iter (set_uninit analysis state) ownership.moves;
  Option.iter (set_init analysis state) ownership.init;
  Option.iter (set_uninit analysis state) ownership.dropped

(* On entry, every parameter is initialized, except the result slot. *)
let holds_at_entry analysis path_index =
  let path = analysis.paths.(path_index) in
  List.mem path.local analysis.function_.parameters
  && not (analysis.function_.written_result = Some path.local && path.steps <> [])

let entry_state analysis =
  let count = Array.length analysis.paths in
  {
    maybe_init = Array.init count (holds_at_entry analysis);
    maybe_uninit = Array.init count (fun path_index -> not (holds_at_entry analysis path_index));
  }

(* The state at the start of each block, by iterating to a fixed point. *)
let solve analysis =
  let blocks = analysis.function_.blocks in
  let count = Array.length analysis.paths in
  let empty () = { maybe_init = Array.make count false; maybe_uninit = Array.make count false } in
  let states = Array.init (Array.length blocks) (fun _ -> empty ()) in
  let reached = Array.make (Array.length blocks) false in
  if Array.length blocks > 0 then begin
    states.(0) <- entry_state analysis;
    reached.(0) <- true
  end;
  let changed = ref true in
  while !changed do
    changed := false;
    Array.iteri
      (fun block_index (block : Lir.basic_block) ->
        if reached.(block_index) then begin
          let state = copy_state states.(block_index) in
          List.iter (apply analysis state) block.statements;
          List.iter (set_uninit analysis state) (terminator_moves block.terminator);
          List.iter
            (fun successor ->
              if not reached.(successor) then begin
                reached.(successor) <- true;
                states.(successor) <- copy_state state;
                changed := true
              end
              else if join states.(successor) state then changed := true)
            (Lir.successors block.terminator)
        end)
      blocks
  done;
  (states, reached)

type status = Yes | No | Maybe

let status state path_index =
  match (state.maybe_init.(path_index), state.maybe_uninit.(path_index)) with
  | true, false -> Yes
  | false, _ -> No
  | true, true -> Maybe

type op =
  | Statement of Lir.statement
  | If_flag of int * op list  (** Runs the ops when the path's flag is set *)
  | Switch_on of Lir.place * (string * op list) list * op list

let variant_fields analysis sum variant =
  let block () = fields_of (Memory_layout.block analysis.env sum variant) in
  let of_payload (payload : Memory_layout.t) =
    match payload.form with
    | Scalar (Pointer (Block _)) -> (block (), true)
    | _ -> (fields_of payload, false)
  in
  match (Memory_layout.of_type analysis.env sum).form with
  | Tagged { variants; _ } -> (
      match
        List.find_opt
          (fun (variant_layout : Memory_layout.variant) -> variant_layout.name = variant)
          variants
      with
      | Some variant_layout -> of_payload variant_layout.payload
      | None -> bug "no variant %s" variant)
  | Niche_encoded { dataful; _ } when dataful.name = variant -> of_payload dataful.payload
  | _ -> ([], false)

(* The ops that drop [path]'s owned values in state [s]. [flag] gives the local
   holding a path's drop flag, and records that it needs one. *)
let rec drop_ops analysis state ~flag path =
  match index analysis path with
  | None -> [ Statement (Drop (place_of_path path)) ]
  | Some path_index -> (
      let whole () =
        if
          List.for_all
            (fun other_index -> other_index = path_index || status state other_index = Yes)
            analysis.inside.(path_index)
        then [ Statement (Drop (place_of_path path)) ]
        else open_ops analysis state ~flag path
      in
      match status state path_index with
      | No -> []
      | Yes -> whole ()
      | Maybe -> [ If_flag (flag path_index, whole ()) ])

(* The parts of [path] dropped one by one, when the path holds a value but
   some part of it was moved out. *)
and open_ops analysis state ~flag path =
  let child step =
    let inner = { path with steps = path.steps @ [ step ] } in
    if owns analysis inner then drop_ops analysis state ~flag inner else []
  in
  match path_type analysis path with
  | Some (Value ty) -> (
      match (Memory_layout.of_type analysis.env ty).form with
      | Struct fields ->
          List.concat_map (fun (field : Memory_layout.field) -> child (Field field.name)) fields
      | Tagged _ | Niche_encoded _ -> (
          let depth = List.length path.steps in
          let variants =
            List.sort_uniq compare
              (List.filter_map
                 (fun other_index ->
                   let inner = analysis.paths.(other_index) in
                   match List.nth_opt inner.steps depth with
                   | Some (Variant (inner_variant, _)) -> Some inner_variant
                   | _ -> None)
                 (match index analysis path with
                 | Some path_index -> analysis.inside.(path_index)
                 | None -> []))
          in
          let open_variant variant =
            let fields, indirect = variant_fields analysis ty variant in
            List.concat_map
              (fun (field : Memory_layout.field) -> child (Variant (variant, field.name)))
              fields
            @
            if indirect then [ Statement (Free_block { place = place_of_path path; variant }) ]
            else []
          in
          (* A part of a variant is moved out only of a value that holds
             the variant. So where a part of it holds nothing on every way
             here, the value is that variant. Where a part may still hold
             its value, the value may hold another variant, whose parts
             have nothing to track, and it is asked which it holds. *)
          let certain variant =
            List.exists
              (fun other_index ->
                match List.nth_opt analysis.paths.(other_index).steps depth with
                | Some (Variant (inner_variant, _)) ->
                    inner_variant = variant && status state other_index = No
                | _ -> false)
              (match index analysis path with
              | Some path_index -> analysis.inside.(path_index)
              | None -> [])
          in
          match variants with
          | [] -> [ Statement (Drop (place_of_path path)) ]
          | [ only ] when certain only -> open_variant only
          | variants ->
              [
                Switch_on
                  ( place_of_path path,
                    List.map
                      (fun inner_variant -> (inner_variant, open_variant inner_variant))
                      variants,
                    [ Statement (Drop (place_of_path path)) ] );
              ])
      | _ -> [ Statement (Drop (place_of_path path)) ])
  | _ -> []

(* A part of a place that may hold a value, if any does. *)
let may_own analysis state place =
  List.find_opt (fun path_index -> state.maybe_init.(path_index)) (affected analysis place)

(* A value a function made is the function's to give away or drop: where
   it returns, none of its locals owns a value still. A pointer's target is
   not checked, since it may be the caller's, or a block's. *)
let check_nothing_owned analysis state =
  Array.iteri
    (fun path_index (path : path) ->
      if state.maybe_init.(path_index) && not (List.mem Deref path.steps) then
        bug "%s may still own a value where the function returns" (describe analysis path))
    analysis.paths

type builder = {
  mutable blocks : Lir.basic_block array;
  mutable current : int;
  mutable statements : Lir.statement list;  (** Of the current block, most recent first *)
}

let new_block builder =
  let index = Array.length builder.blocks in
  builder.blocks <- Array.append builder.blocks [| { statements = []; terminator = Unreachable } |];
  index

let finish builder terminator =
  builder.blocks.(builder.current) <- { statements = List.rev builder.statements; terminator };
  builder.statements <- []

let push builder statement = builder.statements <- statement :: builder.statements

let rec emit_ops builder ops =
  List.iter
    (function
      | Statement statement -> push builder statement
      | If_flag (flag, body) ->
          let body_block = new_block builder in
          let after = new_block builder in
          finish builder
            (Switch
               {
                 value = Copy (Lir.local_place flag);
                 cases = [ (Z.one, body_block) ];
                 default = Some after;
               });
          builder.current <- body_block;
          emit_ops builder body;
          finish builder (Goto after);
          builder.current <- after
      | Switch_on (place, cases, default) ->
          let after = new_block builder in
          let case_blocks = List.map (fun (value, ops) -> (value, new_block builder, ops)) cases in
          let default_block = new_block builder in
          finish builder
            (Switch_variant
               {
                 place;
                 cases = List.map (fun (value, target, _) -> (value, target)) case_blocks;
                 default = Some default_block;
               });
          List.iter
            (fun (_, target, ops) ->
              builder.current <- target;
              emit_ops builder ops;
              finish builder (Goto after))
            case_blocks;
          builder.current <- default_block;
          emit_ops builder default;
          finish builder (Goto after);
          builder.current <- after)
    ops

let flag_place = Lir.local_place

let elaborate env ~needs_drop ~environment (function_ : Lir.function_) =
  let analysis = analyse env ~needs_drop ~environment function_ in
  let states, reached = solve analysis in
  (* The rewrite runs twice: first only to learn which paths need a drop
     flag, then for real, keeping each flag up to date wherever its path is
     given a value or moved. *)
  let rewrite ~flags ~flag =
    let builder = { blocks = Array.copy function_.blocks; current = 0; statements = [] } in
    let update s_before s_after =
      List.iter
        (fun (local_index, local) ->
          if
            s_before.maybe_init.(local_index) <> s_after.maybe_init.(local_index)
            || s_before.maybe_uninit.(local_index) <> s_after.maybe_uninit.(local_index)
          then
            push builder
              (Assign (flag_place local, Use (Constant (Bool s_after.maybe_init.(local_index))))))
        flags
    in
    Array.iteri
      (fun block_index (block : Lir.basic_block) ->
        builder.current <- block_index;
        builder.statements <- [];
        (* A flag starts false, as every local starts zeroed, so only the
           flag of a path that holds a value at entry is written there. A
           write at entry would name the flag outside every region, and
           outlining would then share the flag of a region's own local
           among the runs of the region, which is a data race. *)
        if block_index = 0 then
          List.iter
            (fun (local_index, local) ->
              if holds_at_entry analysis local_index then
                push builder (Assign (flag_place local, Use (Constant (Bool true)))))
            flags;
        let state = copy_state states.(block_index) in
        List.iter
          (fun (statement : Lir.statement) ->
            let before = copy_state state in
            let ownership = statement_effect statement in
            match statement with
            | Drop place -> (
                match path_of_place place with
                | Some path when owns analysis path ->
                    emit_ops builder (drop_ops analysis state ~flag path);
                    apply analysis state statement;
                    update before state
                | Some path when not (path_needs_drop analysis path) -> ()
                | Some path when List.mem Deref path.steps ->
                    (* A place that a borrowed local points at, such as one
                       that a lent value holds the address of, is another
                       owner's and always holds a value. *)
                    push builder statement
                | Some path ->
                    bug "a drop of %s, which a borrowed local holds and its owner drops"
                      (describe analysis path)
                | None ->
                    (* An element reached through an index, which always
                       holds a value, since elements are never moved out. *)
                    push builder statement)
            | Assign _ | Call _ ->
                (* A write gives a place a value and drops nothing, so
                   whatever replaces a value drops it first. *)
                let moved = copy_state state in
                List.iter (set_uninit analysis moved) ownership.moves;
                Option.iter
                  (fun destination ->
                    Option.iter
                      (fun local_index ->
                        bug "a write over %s, which may still own a value"
                          (describe analysis analysis.paths.(local_index)))
                      (may_own analysis moved destination))
                  ownership.init;
                push builder statement;
                apply analysis state statement;
                update before state
            | Free_block _ | Echo _ | Region _ | Regions_end _ | Fork _ | Fork_range _ ->
                push builder statement;
                apply analysis state statement;
                update before state)
          block.statements;
        let before = copy_state state in
        List.iter (set_uninit analysis state) (terminator_moves block.terminator);
        update before state;
        (match block.terminator with
        | Return _ when reached.(block_index) -> check_nothing_owned analysis state
        | _ -> ());
        finish builder block.terminator)
      function_.blocks;
    builder
  in
  let needed = ref [] in
  ignore
    (rewrite ~flags:[] ~flag:(fun local_index ->
         if not (List.mem local_index !needed) then needed := local_index :: !needed;
         0));
  let needed = List.sort compare !needed in
  let flag_locals =
    List.mapi (fun count local_index -> (local_index, Array.length function_.locals + count)) needed
  in
  let builder =
    rewrite ~flags:flag_locals ~flag:(fun local_index ->
        match List.assoc_opt local_index flag_locals with
        | Some local -> local
        | None -> bug "a flag nobody asked for")
  in
  let flag_infos =
    List.map (fun _ -> { Lir.ty = Raw Bool; name = Some "owned"; borrowed = false }) flag_locals
  in
  {
    function_ with
    locals = Array.append function_.locals (Array.of_list flag_infos);
    blocks = builder.blocks;
  }
