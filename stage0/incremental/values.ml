open Nodes
open Edges

let unmarshal bytes = Marshal.from_string bytes 0

(* The fingerprint of an input that is not set. *)
let unset = String.make 32 '\000'

let fingerprint engine (node : node) =
  match node.fingerprint with
  | Some fingerprint -> Some fingerprint
  | None -> (
      match engine.store with
      | None -> None
      | Some store ->
          let bytes =
            match node.cell with
            | Input (_, { slot = Set value; _ }) -> Some (bytes_of value)
            | Result (_, { outcome = Some (Value value); _ }) -> (
                (* A value that holds functions has no bytes. *)
                try Some (bytes_of value) with Invalid_argument _ -> None)
            | _ -> None
          in
          Option.map
            (fun bytes ->
              let fingerprint = if keeps_bytes node then store.put bytes else Blake3.hash bytes in
              node.fingerprint <- Some fingerprint;
              fingerprint)
            bytes)

(* What a fact's key takes of a node: its fingerprint, or that it is an
   input that is not set. *)
let key_part engine (node : node) =
  match node.cell with Input (_, { slot = Unset; _ }) -> Some unset | _ -> fingerprint engine node

let input_value engine (cell : ('key, 'value) input_cell) : 'value option =
  match cell.slot with
  | Unset -> None
  | Set value -> Some value
  | Stored -> (
      match (cell.input_node.fingerprint, engine.store) with
      | Some fingerprint, Some store -> (
          match store.get fingerprint with
          | Some bytes ->
              let value = unmarshal bytes in
              cell.slot <- Set value;
              Some value
          | None -> None)
      | _ -> None)

(* The outcome in memory, reading a stored one. [None] when there is none,
   or the store no longer has it. *)
let load engine (cell : ('key, 'value) result_cell) : 'value outcome option =
  match cell.outcome with
  | Some outcome -> Some outcome
  | None when not (keeps_bytes cell.node) -> None
  | None -> (
      match (cell.node.fingerprint, engine.store) with
      | Some fingerprint, Some store -> (
          match store.get fingerprint with
          | Some bytes ->
              let outcome = Value (unmarshal bytes) in
              cell.outcome <- Some outcome;
              Some outcome
          | None -> None)
      | _ -> None)

let same_exception left right =
  match (left, right) with
  | Cycle _, Cycle _ -> true
  | _ -> ( try left = right with Invalid_argument _ -> false)

let same_outcomes (query : ('key, 'value) query) left right =
  match (left, right) with
  | Value left, Value right -> query.equal left right
  | Raised left, Raised right -> same_exception left right
  | _ -> false

(* What a result read, as a state and a fact record it: each node it read,
   in the order they were first read. A read that has no fingerprint,
   because it raised or its value holds functions, cannot be compared, so
   it is gone through, to what it read in turn. *)
let traced_reads engine (node : node) =
  let seen = Hashtbl.create 16 in
  let found = ref [] in
  let rec visit (read : node) =
    let read = resolve engine read in
    if not (Hashtbl.mem seen read.id) then begin
      Hashtbl.replace seen read.id ();
      if is_input read || fingerprint engine read <> None then found := read :: !found
      else List.iter visit read.reads
    end
  in
  List.iter visit node.reads;
  List.rev !found

(* Whether what read a node recorded the node itself, or what it read. *)
let stops (node : node) =
  is_input node || node.fingerprint <> None
  || match node.cell with Result (_, { outcome = Some (Value _); _ }) -> true | _ -> false

(* A node's reads changed, so every result that recorded its reads through
   it has other reads than it was written with, and is written again. A
   base's result is copied into the engine for that. *)
let resave engine (node : node) =
  if not (stops node) then begin
    let seen = Hashtbl.create 8 in
    let rec above (node : node) =
      List.iter
        (fun (reader : node) ->
          if not (Hashtbl.mem seen reader.id) then begin
            Hashtbl.replace seen reader.id ();
            if stops reader then Hashtbl.replace engine.unsaved reader.id reader else above reader
          end)
        (readers_here engine node ~phase:None)
    in
    above node
  end

let fact_key store (node : node) (parts : (node * string) list) =
  Blake3.hash
    (String.concat ""
       ("fact\000" :: store.version :: "\000" :: identity node
       :: List.concat_map (fun (read, part) -> [ identity read; part ]) parts))

let reads_key store (node : node) =
  Blake3.hash ("reads\000" ^ store.version ^ "\000" ^ identity node)

(* Restoring nodes from a store needs each input and query by name. *)
type restorer = {
  restore : t -> key:string -> node;  (** A node of the engine's own for the key *)
  locate : t -> key:string -> node;  (** The node for the key as the engine sees it, made if none *)
  find : t -> key:string -> node option;
}

let restorers : (string, restorer) Hashtbl.t = Hashtbl.create 64
