(* Queries with verifying traces. See query.mli.

   Each stored result has the revision it was last checked at,
   [verified_at], and the revision its value last changed at, [changed_at].
   Its trace is a list of dependencies, each a function that brings what it
   read up to date and returns that thing's [changed_at]. A result checked at
   an earlier revision is still valid when every dependency's [changed_at]
   is at most its [verified_at]. *)

type revision = int
type dependency = unit -> revision

(* A frame for each query that is running: the dependencies it has read so
   far, newest first. *)
type frame = { label : string; mutable dependencies : dependency list }

type database = {
  mutable revision : revision;
  mutable frames : frame list;
  mutable log : string list;
}

exception Cycle of string list

let create () = { revision = 1; frames = []; log = [] }

let record database dependency =
  match database.frames with
  | frame :: _ -> frame.dependencies <- dependency :: frame.dependencies
  | [] -> ()

(* Inputs *)

type 'value slot = { mutable value : 'value option; mutable changed : revision }

type ('key, 'value) input = {
  input_name : string;
  input_show : 'key -> string;
  input_equal : 'value -> 'value -> bool;
  slots : ('key, 'value slot) Hashtbl.t;
}

let input ~name ~show ?(equal = ( = )) () =
  { input_name = name; input_show = show; input_equal = equal; slots = Hashtbl.create 64 }

let slot input key =
  match Hashtbl.find_opt input.slots key with
  | Some slot -> slot
  | None ->
      let slot = { value = None; changed = 0 } in
      Hashtbl.replace input.slots key slot;
      slot

let change database slot value =
  database.revision <- database.revision + 1;
  slot.value <- value;
  slot.changed <- database.revision

let set database input key value =
  let slot = slot input key in
  match slot.value with
  | Some old when input.input_equal old value -> ()
  | _ -> change database slot (Some value)

let remove database input key =
  let slot = slot input key in
  match slot.value with None -> () | Some _ -> change database slot None

let find database input key =
  let slot = slot input key in
  record database (fun () -> slot.changed);
  slot.value

let get database input key =
  match find database input key with Some value -> value | None -> raise Not_found

(* Queries *)

type 'value memo = {
  mutable result : 'value;
  mutable verified_at : revision;
  mutable changed_at : revision;
  mutable trace : dependency list;  (** In the order they were read. *)
}

type ('key, 'value) query = {
  name : string;
  show : 'key -> string;
  equal : 'value -> 'value -> bool;
  compute : database -> 'key -> 'value;
  memos : ('key, 'value memo) Hashtbl.t;
  running : ('key, unit) Hashtbl.t;
}

let query ~name ~show ?(equal = ( = )) compute =
  { name; show; equal; compute; memos = Hashtbl.create 64; running = Hashtbl.create 8 }

let label query key = Printf.sprintf "%s(%s)" query.name (query.show key)

(* Runs the query's function in a frame of its own, so what it reads goes
   to its own trace and not to the query that asked for it. *)
let run database query key =
  let this = label query key in
  if Hashtbl.mem query.running key then begin
    let rec cycle acc = function
      | [] -> acc
      | frame :: rest ->
          if frame.label = this then frame.label :: acc else cycle (frame.label :: acc) rest
    in
    raise (Cycle (cycle [] database.frames))
  end;
  database.log <- this :: database.log;
  let frame = { label = this; dependencies = [] } in
  database.frames <- frame :: database.frames;
  Hashtbl.replace query.running key ();
  let finish () =
    Hashtbl.remove query.running key;
    database.frames <- List.tl database.frames
  in
  match query.compute database key with
  | value ->
      finish ();
      (value, List.rev frame.dependencies)
  | exception exception_ ->
      finish ();
      raise exception_

(* Brings the stored result up to date with the current revision. *)
let rec ensure : 'key 'value. database -> ('key, 'value) query -> 'key -> 'value memo =
 fun database query key ->
  match Hashtbl.find_opt query.memos key with
  | Some memo when memo.verified_at = database.revision -> memo
  | Some memo when unchanged memo.verified_at memo.trace ->
      memo.verified_at <- database.revision;
      memo
  | Some memo ->
      let value, trace = run database query key in
      if not (query.equal memo.result value) then begin
        memo.result <- value;
        memo.changed_at <- database.revision
      end;
      memo.verified_at <- database.revision;
      memo.trace <- trace;
      memo
  | None ->
      let value, trace = run database query key in
      let memo =
        { result = value; verified_at = database.revision; changed_at = database.revision; trace }
      in
      Hashtbl.replace query.memos key memo;
      memo

(* Whether nothing in a trace has changed since [verified_at]. Entries are
   checked in the order they were read, and the check stops at the first
   change, since a later entry may not be read at all once an earlier one
   gives a different answer. *)
and unchanged verified_at trace =
  List.for_all (fun dependency -> dependency () <= verified_at) trace

(* A query that catches a [Cycle] has read something that has no stable
   answer, so it records a dependency that always counts as changed, and runs
   again at every revision until the cycle is gone. *)
let demand database query key =
  let memo =
    try ensure database query key
    with Cycle _ as cycle ->
      record database (fun () -> max_int);
      raise cycle
  in
  record database (fun () -> (ensure database query key).changed_at);
  memo.result

let executed database = List.rev database.log
let clear_log database = database.log <- []
