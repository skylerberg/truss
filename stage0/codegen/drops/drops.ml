let bug format = Printf.ksprintf (fun message -> invalid_arg ("Drops: " ^ message)) format

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
  | a :: prefix, b :: steps -> a = b && is_prefix prefix steps
  | _ :: _, [] -> false

(* [inner] is [outer] or lies inside it. *)
let within ~outer inner = outer.local = inner.local && is_prefix outer.steps inner.steps

(* The places an operand moves out of, in order. *)
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
  | Use o | Unary (_, o) | Convert (o, _) -> operand_moves o
  | Binary (_, a, b) -> operand_moves a @ operand_moves b
  | Build { fields; _ } -> List.concat_map (fun (_, o) -> operand_moves o) fields
  | Is_variant (place, _) -> place_index_moves place
  | Function_value { environment; _ } -> Option.fold ~none:[] ~some:operand_moves environment

let target_moves target = List.concat_map operand_moves (Lir.target_operands target)

(* What a statement does to ownership: the places it moves out of, then the
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
          @ match result with Returned p | Written p -> place_index_moves p | Discarded -> []);
        init = (match result with Returned p | Written p -> Some p | Discarded -> None);
        dropped = None;
      }
  | Drop place -> { moves = place_index_moves place; init = None; dropped = Some place }
  | Free_block _ -> { moves = []; init = None; dropped = None }
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

(* The analysis *)

type analysis = {
  env : Memory_layout.env;
  needs_drop : Ground.ty -> bool;
  environment : int -> (string * Lir.ty) list;
  f : Lir.function_;
  paths : path array;  (** Every tracked path *)
  inside : int list array;  (** For each path, the tracked paths within it, itself included *)
}

let path_type a path = Lir.place_type a.env ~environment:a.environment a.f (place_of_path path)
let owns a path = match path_type a path with Some (Value ty) -> a.needs_drop ty | _ -> false

let fields_of (layout : Memory_layout.t) =
  match layout.form with Struct fields -> fields | _ -> []

(* An element written gives its whole array a value: lowering writes every
   element of a new array before anything reads it, and elements are never
   moved out. *)
let before_index (place : Lir.place) : Lir.place =
  let rec take = function [] | Lir.Index _ :: _ -> [] | p :: rest -> p :: take rest in
  { place with projections = take place.projections }

(* Tracks every path that is moved, given a value, or dropped, whose type
   has something to drop, and every path around one that holds a value. *)
let analyse env ~needs_drop ~environment (f : Lir.function_) =
  let partial = { env; needs_drop; environment; f; paths = [||]; inside = [||] } in
  let found = ref [] in
  let add path = if not (List.mem path !found) then found := path :: !found in
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
    f.blocks;
  let paths =
    Array.of_list (List.filter (fun path -> owns partial path) (List.sort compare !found))
  in
  let inside =
    Array.map
      (fun outer ->
        List.filter_map
          (fun (i, inner) -> if within ~outer inner then Some i else None)
          (List.mapi (fun i p -> (i, p)) (Array.to_list paths)))
      paths
  in
  { partial with paths; inside }

let index a path =
  let rec find i =
    if i >= Array.length a.paths then None else if a.paths.(i) = path then Some i else find (i + 1)
  in
  find 0

(* For each tracked path, whether it may hold a value and whether it may
   not. *)
type state = { maybe_init : bool array; maybe_uninit : bool array }

let copy_state s =
  { maybe_init = Array.copy s.maybe_init; maybe_uninit = Array.copy s.maybe_uninit }

let join into s =
  let changed = ref false in
  Array.iteri
    (fun i v ->
      if v && not into.maybe_init.(i) then begin
        into.maybe_init.(i) <- true;
        changed := true
      end)
    s.maybe_init;
  Array.iteri
    (fun i v ->
      if v && not into.maybe_uninit.(i) then begin
        into.maybe_uninit.(i) <- true;
        changed := true
      end)
    s.maybe_uninit;
  !changed

(* The tracked paths that lie within a place. *)
let affected a place =
  match path_of_place place with
  | None -> []
  | Some outer ->
      List.filter_map
        (fun (i, inner) -> if within ~outer inner then Some i else None)
        (List.mapi (fun i p -> (i, p)) (Array.to_list a.paths))

let set_uninit a s place =
  List.iter
    (fun i ->
      s.maybe_init.(i) <- false;
      s.maybe_uninit.(i) <- true)
    (affected a place)

let definitely_init s i = s.maybe_init.(i) && not s.maybe_uninit.(i)

(* A record holds a value once every part of it with something to drop
   does, however it was given them: lowering may fill a new record's fields
   one by one. *)
let rec promote a s path =
  match List.rev path.steps with
  | Field _ :: rest -> (
      let parent = { path with steps = List.rev rest } in
      match (index a parent, path_type a parent) with
      | Some p, Some (Value ty) when not (definitely_init s p) ->
          let given (field : Memory_layout.field) =
            let inner = { parent with steps = parent.steps @ [ Field field.name ] } in
            (not (owns a inner))
            || match index a inner with Some j -> definitely_init s j | None -> false
          in
          if List.for_all given (fields_of (Memory_layout.of_type a.env ty)) then begin
            s.maybe_init.(p) <- true;
            s.maybe_uninit.(p) <- false;
            promote a s parent
          end
      | _ -> ())
  | _ -> ()

let set_init a s place =
  let place = before_index place in
  List.iter
    (fun i ->
      s.maybe_init.(i) <- true;
      s.maybe_uninit.(i) <- false)
    (affected a place);
  Option.iter (promote a s) (path_of_place place)

let apply a s statement =
  let ownership = statement_effect statement in
  List.iter (set_uninit a s) ownership.moves;
  Option.iter (set_init a s) ownership.init;
  Option.iter (set_uninit a s) ownership.dropped

let entry_state a =
  let n = Array.length a.paths in
  let parameter i = List.mem a.paths.(i).local a.f.parameters in
  { maybe_init = Array.init n parameter; maybe_uninit = Array.init n (fun i -> not (parameter i)) }

(* The state at the start of each block, by iterating to a fixed point. *)
let solve a =
  let blocks = a.f.blocks in
  let n = Array.length a.paths in
  let empty () = { maybe_init = Array.make n false; maybe_uninit = Array.make n false } in
  let states = Array.init (Array.length blocks) (fun _ -> empty ()) in
  let reached = Array.make (Array.length blocks) false in
  if Array.length blocks > 0 then begin
    states.(0) <- entry_state a;
    reached.(0) <- true
  end;
  let changed = ref true in
  while !changed do
    changed := false;
    Array.iteri
      (fun b (block : Lir.basic_block) ->
        if reached.(b) then begin
          let s = copy_state states.(b) in
          List.iter (apply a s) block.statements;
          List.iter (set_uninit a s) (terminator_moves block.terminator);
          List.iter
            (fun successor ->
              if not reached.(successor) then begin
                reached.(successor) <- true;
                states.(successor) <- copy_state s;
                changed := true
              end
              else if join states.(successor) s then changed := true)
            (Lir.successors block.terminator)
        end)
      blocks
  done;
  states

type status = Yes | No | Maybe

let status s i =
  match (s.maybe_init.(i), s.maybe_uninit.(i)) with
  | true, false -> Yes
  | false, _ -> No
  | true, true -> Maybe

(* Elaborating one drop *)

type op =
  | Statement of Lir.statement
  | If_flag of int * op list  (** Runs the ops when the path's flag is set *)
  | Switch_on of Lir.place * (string * op list) list * op list

let variant_fields a sum variant =
  let block () = fields_of (Memory_layout.block a.env sum variant) in
  let of_payload (payload : Memory_layout.t) =
    match payload.form with
    | Scalar (Pointer (Block _)) -> (block (), true)
    | _ -> (fields_of payload, false)
  in
  match (Memory_layout.of_type a.env sum).form with
  | Tagged { variants; _ } -> (
      match List.find_opt (fun (v : Memory_layout.variant) -> v.name = variant) variants with
      | Some v -> of_payload v.payload
      | None -> bug "no variant %s" variant)
  | Niche_encoded { dataful; _ } when dataful.name = variant -> of_payload dataful.payload
  | _ -> ([], false)

(* The ops that drop what [path] owns in state [s]. [flag] gives the local
   holding a path's drop flag, and records that it needs one. *)
let rec drop_ops a s ~flag path =
  match index a path with
  | None -> [ Statement (Drop (place_of_path path)) ]
  | Some i -> (
      let whole () =
        if List.for_all (fun j -> j = i || status s j = Yes) a.inside.(i) then
          [ Statement (Drop (place_of_path path)) ]
        else open_ops a s ~flag path
      in
      match status s i with No -> [] | Yes -> whole () | Maybe -> [ If_flag (flag i, whole ()) ])

(* The parts of [path] dropped one by one, when the path holds a value but
   some part of it was moved out. *)
and open_ops a s ~flag path =
  let child step =
    let inner = { path with steps = path.steps @ [ step ] } in
    if owns a inner then drop_ops a s ~flag inner else []
  in
  match path_type a path with
  | Some (Value ty) -> (
      match (Memory_layout.of_type a.env ty).form with
      | Struct fields ->
          List.concat_map (fun (field : Memory_layout.field) -> child (Field field.name)) fields
      | Tagged _ | Niche_encoded _ -> (
          let depth = List.length path.steps in
          let variants =
            List.sort_uniq compare
              (List.filter_map
                 (fun j ->
                   let inner = a.paths.(j) in
                   match List.nth_opt inner.steps depth with
                   | Some (Variant (v, _)) -> Some v
                   | _ -> None)
                 (match index a path with Some i -> a.inside.(i) | None -> []))
          in
          let open_variant variant =
            let fields, indirect = variant_fields a ty variant in
            List.concat_map
              (fun (field : Memory_layout.field) -> child (Variant (variant, field.name)))
              fields
            @
            if indirect then [ Statement (Free_block { place = place_of_path path; variant }) ]
            else []
          in
          match variants with
          | [ only ] -> open_variant only
          | many ->
              [
                Switch_on
                  ( place_of_path path,
                    List.map (fun v -> (v, open_variant v)) many,
                    [ Statement (Drop (place_of_path path)) ] );
              ])
      | _ -> [ Statement (Drop (place_of_path path)) ])
  | _ -> []

(* Whether any part of a place may hold a value. *)
let may_own a s place = List.exists (fun i -> s.maybe_init.(i)) (affected a place)

(* Rewriting *)

type builder = {
  mutable blocks : Lir.basic_block array;
  mutable current : int;
  mutable statements : Lir.statement list;  (** Of the current block, most recent first *)
  mutable locals : Lir.local_info list;  (** Added locals, most recent first *)
  base_locals : int;
}

let new_block builder =
  let index = Array.length builder.blocks in
  builder.blocks <- Array.append builder.blocks [| { statements = []; terminator = Unreachable } |];
  index

let finish builder terminator =
  builder.blocks.(builder.current) <- { statements = List.rev builder.statements; terminator };
  builder.statements <- []

let push builder statement = builder.statements <- statement :: builder.statements

let new_local builder ty =
  let local = builder.base_locals + List.length builder.locals in
  builder.locals <- { Lir.ty; name = None } :: builder.locals;
  local

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
                 value = Copy { root = Local flag; projections = [] };
                 cases = [ (Z.one, body_block) ];
                 default = Some after;
               });
          builder.current <- body_block;
          emit_ops builder body;
          finish builder (Goto after);
          builder.current <- after
      | Switch_on (place, cases, default) ->
          let after = new_block builder in
          let case_blocks = List.map (fun (v, ops) -> (v, new_block builder, ops)) cases in
          let default_block = new_block builder in
          finish builder
            (Switch_variant
               {
                 place;
                 cases = List.map (fun (v, b, _) -> (v, b)) case_blocks;
                 default = Some default_block;
               });
          List.iter
            (fun (_, b, ops) ->
              builder.current <- b;
              emit_ops builder ops;
              finish builder (Goto after))
            case_blocks;
          builder.current <- default_block;
          emit_ops builder default;
          finish builder (Goto after);
          builder.current <- after)
    ops

let flag_place local : Lir.place = { root = Local local; projections = [] }

let elaborate env ~needs_drop ~environment (f : Lir.function_) =
  let a = analyse env ~needs_drop ~environment f in
  let states = solve a in
  (* The rewrite runs twice: first only to learn which paths need a drop
     flag, then for real, keeping each flag up to date wherever its path is
     given a value or moved. *)
  let rewrite ~flags ~flag =
    let builder =
      {
        blocks = Array.copy f.blocks;
        current = 0;
        statements = [];
        locals = [];
        base_locals = Array.length f.locals + List.length flags;
      }
    in
    let update s_before s_after =
      List.iter
        (fun (i, local) ->
          if
            s_before.maybe_init.(i) <> s_after.maybe_init.(i)
            || s_before.maybe_uninit.(i) <> s_after.maybe_uninit.(i)
          then
            push builder (Assign (flag_place local, Use (Constant (Bool s_after.maybe_init.(i))))))
        flags
    in
    Array.iteri
      (fun b (block : Lir.basic_block) ->
        builder.current <- b;
        builder.statements <- [];
        if b = 0 then
          List.iter
            (fun (i, local) ->
              push builder
                (Assign
                   ( flag_place local,
                     Use (Constant (Bool (List.mem a.paths.(i).local f.parameters))) )))
            flags;
        let s = copy_state states.(b) in
        List.iter
          (fun (statement : Lir.statement) ->
            let before = copy_state s in
            let ownership = statement_effect statement in
            match statement with
            | Drop place -> (
                match path_of_place place with
                | Some path when owns a path ->
                    emit_ops builder (drop_ops a s ~flag path);
                    apply a s statement;
                    update before s
                | Some _ -> ()
                | None ->
                    (* An element reached through an index, which always
                       holds a value, since elements are never moved out. *)
                    push builder statement)
            | Assign _ | Call _ -> (
                let moved = copy_state s in
                List.iter (set_uninit a moved) ownership.moves;
                match ownership.init with
                | Some destination when may_own a moved destination -> (
                    match
                      (path_of_place destination, Lir.place_type env ~environment f destination)
                    with
                    | Some path, Some ty ->
                        let temporary = new_local builder ty in
                        let temporary_place = flag_place temporary in
                        (match statement with
                        | Assign (_, rvalue) -> push builder (Assign (temporary_place, rvalue))
                        | Call call ->
                            let result : Lir.destination =
                              match call.result with
                              | Written _ -> Written temporary_place
                              | _ -> Returned temporary_place
                            in
                            push builder (Call { call with result })
                        | _ -> ());
                        update before moved;
                        emit_ops builder (drop_ops a moved ~flag path);
                        let dropped = copy_state moved in
                        set_uninit a dropped destination;
                        update moved dropped;
                        push builder (Assign (destination, Use (Move temporary_place)));
                        apply a s statement;
                        update dropped s
                    | _ -> bug "an assignment to a place that may own a value but has no path")
                | _ ->
                    push builder statement;
                    apply a s statement;
                    update before s)
            | Free_block _ | Echo _ ->
                push builder statement;
                apply a s statement;
                update before s)
          block.statements;
        let before = copy_state s in
        List.iter (set_uninit a s) (terminator_moves block.terminator);
        update before s;
        finish builder block.terminator)
      f.blocks;
    builder
  in
  let needed = ref [] in
  ignore
    (rewrite ~flags:[] ~flag:(fun i ->
         if not (List.mem i !needed) then needed := i :: !needed;
         0));
  let needed = List.sort compare !needed in
  let flag_locals = List.mapi (fun n i -> (i, Array.length f.locals + n)) needed in
  let builder =
    rewrite ~flags:flag_locals ~flag:(fun i ->
        match List.assoc_opt i flag_locals with
        | Some local -> local
        | None -> bug "a flag nobody asked for")
  in
  let flag_infos = List.map (fun _ -> { Lir.ty = Raw Bool; name = Some "owned" }) flag_locals in
  {
    f with
    locals =
      Array.concat [ f.locals; Array.of_list flag_infos; Array.of_list (List.rev builder.locals) ];
    blocks = builder.blocks;
  }
