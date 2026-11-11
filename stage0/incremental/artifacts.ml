open Nodes
open Edges
open Values
open Update
open Engines

let require_store engine =
  match engine.store with
  | Some store -> store
  | None -> invalid_arg "Incremental: no store is attached"

let record_fact engine store (node : node) reads =
  match node.cell with
  | Result (query, _) when query.saved -> (
      match fingerprint engine node with
      | None -> ()
      | Some value -> (
          let parts =
            List.fold_right
              (fun read found ->
                match (found, key_part engine read) with
                | Some found, Some part -> Some ((read, part) :: found)
                | _ -> None)
              (Lazy.force reads) (Some [])
          in
          match parts with
          | None | Some [] -> ()
          | Some parts ->
              store.add ~kind:"fact" ~key:(fact_key store node parts) value;
              let key = reads_key store node in
              if query.portable && store.find ~kind:"reads" ~key = None then
                store.add ~kind:"reads" ~key
                  (Marshal.to_string
                     (List.map (fun (read, _) -> (name read, key_bytes read)) parts)
                     [])))
  | _ -> ()

let unsaved_nodes engine =
  by_id
    (Hashtbl.fold
       (fun _ (node : node) found -> if node.alive then node :: found else found)
       engine.unsaved [])

let record engine =
  match engine.store with
  | None -> ()
  | Some store ->
      List.iter
        (fun node -> record_fact engine store node (lazy (traced_reads engine node)))
        (unsaved_nodes engine)

(* An artifact: a state, or what changed in one since an earlier artifact.
   Each node is named by its input or query and its key, and what it read
   by places in the artifact's table of such names. *)
type saved_node = {
  saved_name : string;
  saved_key : string;
  saved_value : string option;  (** A fingerprint; [None] for an input that is not set *)
  saved_reads : int list;
  saved_kept : bool;
}

let artifact_header store = "truss artifact " ^ store.version ^ "\n"

type artifact = {
  base : string option;
  saved : saved_node list;
  table : (string * string) array;
  dropped : (string * string) list;
  whole_size : int;
  difference_size : int;
  difference_count : int;
}

(* The same reads in the same order name the same nodes. *)
let same_reads engine reads (base : node) =
  List.map identity reads = List.map identity (traced_reads engine base)

let write ?(full = false) engine =
  let store = require_store engine in
  check_can_change engine;
  sweep engine;
  settle engine;
  let full = full || engine.chain = None in
  let kept (node : node) = node.kept || Hashtbl.mem engine.pinned node.id in
  let candidates =
    if full then begin
      (* What the kept results and the set inputs reach, apart from the
         fixed bases. *)
      let reached = Hashtbl.create 1024 in
      let rec reach (node : node) =
        if (not node.engine.fixed) && not (Hashtbl.mem reached node.id) then begin
          Hashtbl.replace reached node.id node;
          List.iter (fun read -> reach (resolve engine read)) node.reads
        end
      in
      List.iter
        (fun (node : node) ->
          let set =
            match node.cell with Input (_, { slot = Set _ | Stored; _ }) -> true | _ -> false
          in
          if kept node || set then reach node)
        (nodes engine);
      by_id (Hashtbl.fold (fun _ node found -> node :: found) reached [])
    end
    else unsaved_nodes engine
  in
  (* A node that is written must find what it read when the state is
     opened, so a node of the engine's own that the chain does not hold yet
     is written with the first node that read it. *)
  let scheduled = Hashtbl.create 256 in
  List.iter (fun (node : node) -> Hashtbl.replace scheduled node.id ()) candidates;
  let more = Queue.create () in
  let places = Hashtbl.create 256 in
  let table = ref [] in
  let place (read : node) =
    if read.engine == engine && (not read.written) && not (Hashtbl.mem scheduled read.id) then begin
      Hashtbl.replace scheduled read.id ();
      Queue.add read more
    end;
    match Hashtbl.find_opt places read.id with
    | Some place -> place
    | None ->
        let place = Hashtbl.length places in
        Hashtbl.replace places read.id place;
        table := (name read, key_bytes read) :: !table;
        place
  in
  let written (node : node) saved_value saved_reads =
    node.written <- true;
    node.superseding <- not full;
    Some
      {
        saved_name = name node;
        saved_key = key_bytes node;
        saved_value;
        saved_reads;
        saved_kept = kept node;
      }
  in
  let save (node : node) =
    let reads = lazy (traced_reads engine node) in
    if Hashtbl.mem engine.unsaved node.id then record_fact engine store node reads;
    (* A copy that came out as the base's node, reading the same, is the
           base's node, and is not written, unless an earlier difference
           holds another result for it, which this one takes the place of. *)
    let as_base = (not full) && engine.on_whole && not node.superseding in
    let as_below () =
      as_base
      &&
      match node.below with
      | Some base ->
          base.fingerprint = node.fingerprint
          && base.kept = kept node
          && same_reads engine (Lazy.force reads) base
      | None -> false
    in
    match node.cell with
    | Input (_, { slot = Unset; _ }) -> (
        match node.below with
        | Some { cell = Input (_, { slot = Unset; _ }); _ } when as_base -> None
        | _ -> written node None [])
    | Input _ -> (
        match fingerprint engine node with
        | Some value when not (as_below ()) -> written node (Some value) []
        | _ -> None)
    | Result _ -> (
        match fingerprint engine node with
        | Some value ->
            if as_below () then None
            else written node (Some value) (List.map place (Lazy.force reads))
        | None ->
            (* A result with no fingerprint takes the place of an earlier
                   one the chain holds. *)
            if node.written && not full then written node None [] else None)
    | Unfilled -> None
  in
  let first = List.filter_map save candidates in
  let rec rest found =
    match Queue.take_opt more with
    | Some node -> rest (match save node with Some saved -> saved :: found | None -> found)
    | None -> List.rev found
  in
  let saved = first @ rest [] in
  let count = List.length saved in
  let artifact =
    {
      base = (if full then None else engine.chain);
      saved;
      table = Array.of_list (List.rev !table);
      dropped = (if full then [] else List.rev engine.gone);
      whole_size = (if full then count else engine.whole);
      difference_size = (if full then 0 else engine.differences + count);
      difference_count = (if full then 0 else engine.depth + 1);
    }
  in
  let name = store.put (artifact_header store ^ Marshal.to_string artifact []) in
  if full then engine.on_whole <- false;
  engine.chain <- Some name;
  engine.whole <- artifact.whole_size;
  engine.differences <- artifact.difference_size;
  engine.depth <- artifact.difference_count;
  Hashtbl.reset engine.unsaved;
  engine.gone <- [];
  name

type debt = { whole : int; differences : int; depth : int }

let debt (engine : t) =
  { whole = engine.whole; differences = engine.differences; depth = engine.depth }

let artifact (engine : t) = engine.chain

let unwritten (engine : t) =
  engine.chain = None || Hashtbl.length engine.unsaved > 0 || engine.gone <> []

(* An artifact's bytes start with what wrote it. They are marshaled, so
   they mean something only to the same version: read by another, as when
   a compiler collects a store that an earlier build of it wrote to, they
   would be taken for another type's. *)
let read_artifact store bytes : artifact option =
  let header = artifact_header store in
  if String.starts_with ~prefix:header bytes then
    Some (Marshal.from_string bytes (String.length header))
  else None

(* The artifacts from the whole state a chain starts with to its last;
   [None] if the store lacks one, or another version wrote one. *)
let chain_of store name =
  let rec back name found =
    match Option.bind (store.get name) (read_artifact store) with
    | None -> None
    | Some artifact -> (
        let found = (name, artifact) :: found in
        match artifact.base with None -> Some found | Some base -> back base found)
  in
  back name []

let values_in store name =
  match chain_of store name with
  | None -> []
  | Some chain ->
      List.concat_map
        (fun (name, artifact) ->
          name :: List.filter_map (fun (node : saved_node) -> node.saved_value) artifact.saved)
        chain

(* Fills an engine with artifacts' nodes, each the last of its name and key,
   apart from those dropped after. A node of a query this program does not
   declare is left out, and so is one that read a node that cannot be
   found, with everything that read it, since its result could not be
   checked. *)
let fill engine (artifacts : artifact list) =
  let last : (string * string, saved_node * artifact) Hashtbl.t = Hashtbl.create 1024 in
  let order = ref [] in
  let gone = Hashtbl.create 16 in
  List.iter
    (fun (artifact : artifact) ->
      List.iter
        (fun key ->
          Hashtbl.remove last key;
          Hashtbl.replace gone key ())
        artifact.dropped;
      List.iter
        (fun (node : saved_node) ->
          let key = (node.saved_name, node.saved_key) in
          if not (Hashtbl.mem last key) then order := key :: !order;
          Hashtbl.remove gone key;
          Hashtbl.replace last key (node, artifact))
        artifact.saved)
    artifacts;
  (* A node that was dropped is not in the state. Where a base holds it, the
     engine holds its place with nothing in it, so that it is computed if it
     is asked for, and the base's result, which is of an earlier state, is
     never read. *)
  Hashtbl.iter
    (fun (name, key) () ->
      match Hashtbl.find_opt restorers name with
      | Some restorer -> (
          match restorer.find engine ~key with
          | Some (found : node) when found.engine != engine -> (
              match restorer.restore engine ~key with
              | node ->
                  node.written <- true;
                  node.superseding <- true;
                  node.kept <- false
              | exception _ -> ())
          | _ | (exception _) -> ())
      | None -> ())
    gone;
  let made =
    List.filter_map
      (fun key ->
        match Hashtbl.find_opt last key with
        | None -> None
        | Some (saved, artifact) -> (
            match Hashtbl.find_opt restorers saved.saved_name with
            | None -> None
            | Some restorer -> (
                match restorer.restore engine ~key:saved.saved_key with
                | exception _ -> None
                | node ->
                    node.fingerprint <- saved.saved_value;
                    node.kept <- saved.saved_kept;
                    node.written <- true;
                    node.superseding <- true;
                    (match node.cell with
                    | Input (_, cell) ->
                        cell.slot <- (if saved.saved_value = None then Unset else Stored)
                    | Result (_, cell) -> cell.outcome <- None
                    | Unfilled -> ());
                    Some (node, saved, artifact))))
      (List.rev !order)
  in
  let find (artifact : artifact) place =
    let name, key = artifact.table.(place) in
    match Hashtbl.find_opt restorers name with
    | Some restorer -> ( try restorer.find engine ~key with _ -> None)
    | None -> None
  in
  let broken = Hashtbl.create 8 in
  List.iter
    (fun ((node : node), saved, artifact) ->
      let found = List.map (find artifact) saved.saved_reads in
      if List.exists Option.is_none found then Hashtbl.replace broken node.id node
      else begin
        let reads = List.filter_map Fun.id found in
        node.reads <- reads;
        List.iter (fun read -> add_reader engine read node) reads
      end)
    made;
  (* What cannot be checked is left out, with what reads it. One that a base
     also holds keeps its place, with nothing in it, so that the base's
     result, which is of an earlier state, is not read in its stead. *)
  let emptied = Hashtbl.create 8 in
  let rec remove (node : node) =
    if node.alive && not (Hashtbl.mem emptied node.id) then begin
      Hashtbl.replace emptied node.id ();
      let readers = Hashtbl.fold (fun _ reader found -> reader :: found) node.readers [] in
      List.iter (fun read -> remove_reader engine read node) node.reads;
      node.reads <- [];
      node.fingerprint <- None;
      (match node.cell with
      | Input (_, cell) -> cell.slot <- Unset
      | Result (_, cell) -> cell.outcome <- None
      | Unfilled -> ());
      if node.below = None then begin
        node.alive <- false;
        forget engine node;
        Hashtbl.remove engine.own node.id
      end;
      List.iter remove readers
    end
  in
  Hashtbl.iter (fun _ node -> remove node) broken

(* Frozen bases, shared by every engine opened from the same whole state
   over the same bases, and held weakly, so that one no engine uses is
   freed. *)
let shared_bases : (string, t Weak.t) Hashtbl.t = Hashtbl.create 8
let forget_bases () = Hashtbl.reset shared_bases

let frozen_from (store : store) ~bases ~fixed ~name (artifacts : artifact list) =
  let key =
    String.concat ":"
      (store.id :: name :: string_of_bool fixed
      :: List.map (fun (base : t) -> string_of_int base.id) bases)
  in
  let cached =
    match Hashtbl.find_opt shared_bases key with Some weak -> Weak.get weak 0 | None -> None
  in
  match cached with
  | Some engine -> engine
  | None ->
      let engine = create ~bases () in
      attach engine store;
      fill engine artifacts;
      engine.frozen <- true;
      engine.fixed <- fixed;
      let dead =
        Hashtbl.fold
          (fun key weak found -> if Weak.check weak 0 then found else key :: found)
          shared_bases []
      in
      List.iter (Hashtbl.remove shared_bases) dead;
      let weak = Weak.create 1 in
      Weak.set weak 0 (Some engine);
      Hashtbl.replace shared_bases key weak;
      engine

let frozen_of store ~bases ~fixed name =
  match chain_of store name with
  | None -> None
  | Some chain -> Some (frozen_from store ~bases ~fixed ~name (List.map snd chain))

let open_ ?log store ~bases name =
  match chain_of store name with
  | None | Some [] -> None
  | Some ((whole_name, whole) :: differences) ->
      let base = frozen_from store ~bases ~fixed:false ~name:whole_name [ whole ] in
      let engine = create ?log ~bases:(base :: bases) () in
      attach engine store;
      fill engine (List.map snd differences);
      let last = match List.rev differences with (_, last) :: _ -> last | [] -> whole in
      engine.chain <- Some name;
      engine.on_whole <- true;
      engine.whole <- last.whole_size;
      engine.differences <- last.difference_size;
      engine.depth <- last.difference_count;
      Some engine
