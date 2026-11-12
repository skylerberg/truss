open Nodes
open Edges

let unmarshal bytes = Marshal.from_string bytes 0

(* The fingerprint of an input that is not set. *)
let unset = String.make 32 '\000'

(* An exception's bytes: its constructor's name and its arguments. An
   exception is a block whose first field is its constructor, or for one
   with no arguments, the constructor itself, which is how [Printexc] reads
   one too. *)
let exception_bytes (raised : exn) =
  let block = Obj.repr raised in
  let name = Cbor.Text (Printexc.exn_slot_name raised) in
  Cbor.encode
    (if Obj.tag block = Obj.object_tag then Cbor.Array [ name ]
     else
       Cbor.Array
         [
           name;
           Cbor.Bytes
             (bytes_of (Array.init (Obj.size block - 1) (fun index -> Obj.field block (index + 1))));
         ])

(* A fingerprint that equals no other: for an outcome that has no bytes,
   which is then equal only to itself. *)
let random = lazy (Random.State.make_self_init ())
let nonces = ref 0
let derive_nonce = Blake3.derive_key ~context:"truss 2026-11-12 incremental nonce"

let nonce () =
  incr nonces;
  let bits () = Cbor.int (Random.State.bits (Lazy.force random)) in
  derive_nonce (Cbor.encode (Cbor.Array [ Cbor.int !nonces; bits (); bits (); bits () ]))

let forget_fingerprint (node : node) = node.fingerprint <- Unknown

(* A node's fingerprint: the hash of its outcome's bytes. Every input that
   is set and every result that has an outcome has one. A value's bytes are
   put in the store where its query is saved. An exception's bytes are its
   name and arguments, and are never stored: an exception read back would
   not be the one a handler matches. An outcome with no bytes, which is a
   value or an exception that holds a function, is [opaque]: its fingerprint
   is a nonce, so it compares equal to no other computation's, and its
   readers are computed again whenever it is. *)
let derive_exception_fingerprint =
  Blake3.derive_key ~context:"truss 2026-11-12 incremental exception fingerprint"

(* The name of a node's value in the store: the hash of its bytes. [None] for
   a result that raised, or whose value holds functions, or when no store is
   attached. *)
let fingerprint engine (node : node) =
  match node.fingerprint with
  | Hashed { hash; _ } | Opaque hash -> Some hash
  | Unknown -> (
      let set ?(stored = false) hash =
        node.fingerprint <- Hashed { hash; stored };
        Some hash
      in
      let opaque () =
        let nonce = nonce () in
        node.fingerprint <- Opaque nonce;
        Some nonce
      in
      match node.cell with
      | Input (_, { slot = Set value; _ }) -> (
          let bytes = bytes_of value in
          match engine.store with
          | Some store -> set (store.put bytes)
          | None -> set (Blake3.hash bytes))
      | Result (query, { outcome = Some (Value value); _ }) -> (
          match bytes_of value with
          | bytes -> (
              match engine.store with
              | Some store when query.saved -> set ~stored:true (store.put bytes)
              | _ -> set (Blake3.hash bytes))
          | exception Invalid_argument _ -> opaque ())
      | Result (_, { outcome = Some (Raised raised); _ }) -> (
          match exception_bytes raised with
          | bytes -> set (derive_exception_fingerprint bytes)
          | exception Invalid_argument _ -> opaque ())
      | _ -> None)

(* Puts a value's bytes in the store, if its fingerprint was computed
   before the engine had one. *)
let ensure_stored engine (node : node) =
  match (engine.store, node.cell) with
  | Some store, Input (_, { slot = Set value; _ }) -> ignore (store.put (bytes_of value))
  | Some store, Result (query, { outcome = Some (Value value); _ }) when query.saved -> (
      match node.fingerprint with
      | Hashed { hash; stored = false } ->
          ignore (store.put (bytes_of value));
          node.fingerprint <- Hashed { hash; stored = true }
      | Hashed { stored = true; _ } | Opaque _ | Unknown -> ())
  | _ -> ()

(* A node's contribution to a fact's key: its fingerprint, or that it is an
   input that is not set. An opaque node gives none, since its fingerprint
   will never be met again. *)
let key_part engine (node : node) =
  match node.cell with
  | Input (_, { slot = Unset; _ }) -> Some unset
  | _ -> (
      match (fingerprint engine node, node.fingerprint) with
      | Some fingerprint, Hashed _ -> Some fingerprint
      | _ -> None)

let stored_bytes engine (node : node) =
  match (node.fingerprint, engine.store) with
  | Hashed { hash; _ }, Some store -> store.get hash
  | _ -> None

(* An input's value, [None] for one that is not set. An input's value
   comes from the database and cannot be recomputed, so one whose value the store
   no longer has raises [Lost]: read as not set, it would give wrong
   results, which would be kept as facts. *)
let input_value engine (cell : ('key, 'value) input_cell) : 'value option =
  match cell.slot with
  | Unset -> None
  | Set value -> Some value
  | Stored -> (
      match stored_bytes engine cell.input_node with
      | Some bytes ->
          let value = unmarshal bytes in
          cell.slot <- Set value;
          Some value
      | None -> raise (Lost (label cell.input_node)))

(* The outcome in memory, reading a stored one. [None] when there is none,
   or the store no longer has it. *)
let load engine (cell : ('key, 'value) result_cell) : 'value outcome option =
  match cell.outcome with
  | Some outcome -> Some outcome
  | None -> (
      match (cell.node.fingerprint, engine.store) with
      | Hashed { hash; stored = true }, Some store -> (
          match store.get hash with
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

(* A result's dependencies, as the engine sees each node now. *)
let current_reads engine (node : node) = List.map (resolve engine) node.reads

(* The keys a fact and its reads are kept under. The store names each
   result by its kind and key, so these keys need no hash of their own. *)
let fact_key store (node : node) (parts : (node * string) list) =
  Cbor.encode
    (Cbor.Array
       [
         Cbor.Text store.version;
         Cbor.Bytes (identity node);
         Cbor.Array
           (List.map
              (fun (read, part) -> Cbor.Array [ Cbor.Bytes (identity read); Cbor.Bytes part ])
              parts);
       ])

let reads_key store (node : node) =
  Cbor.encode (Cbor.Array [ Cbor.Text store.version; Cbor.Bytes (identity node) ])

(* Restoring nodes from a store needs each input and query by name. *)
type restorer = {
  restore : t -> key:string -> node;  (** A node of the engine's own for the key *)
  locate : t -> key:string -> node;  (** The node for the key as the engine sees it, made if none *)
  find : t -> key:string -> node option;
}

let restorers : (string, restorer) Hashtbl.t = Hashtbl.create 64
