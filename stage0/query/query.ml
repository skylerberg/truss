(* Queries with verifying traces. See query.mli.

   Each stored result has the revision it was last checked at,
   [verified_at], and the revision its outcome last changed at,
   [changed_at]. Its trace is a list of dependencies, each a function that
   brings what it read up to date and returns that thing's [changed_at]. A
   result checked at an earlier revision is still valid when every
   dependency's [changed_at] is at most its [verified_at].

   An outcome is a value or the exception the query raised, so a query that
   fails is stored like one that succeeds, with the trace of what it read,
   and bringing a dependency up to date never raises. *)

type revision = int
type dependency = unit -> revision

(* A frame for each query that is running or whose trace is being checked:
   the dependencies a running query has read so far, newest first. *)
type frame = { label : string; mutable dependencies : dependency list }

type database = {
  id : int;
  mutable revision : revision;
  mutable frames : frame list;
  logging : bool;
  mutable log : string list;
}

exception Cycle of string list

let databases = ref 0

let create ?(log = false) () =
  incr databases;
  { id = !databases; revision = 1; frames = []; logging = log; log = [] }

let record database dependency =
  match database.frames with
  | frame :: _ -> frame.dependencies <- dependency :: frame.dependencies
  | [] -> ()

(* Each input and query keeps a table for each database it is used with, so
   databases never share results. *)
let table tables database =
  match Hashtbl.find_opt tables database.id with
  | Some table -> table
  | None ->
      let table = Hashtbl.create 64 in
      Hashtbl.replace tables database.id table;
      table

(* Inputs *)

type 'value slot = { mutable value : 'value option; mutable changed : revision }

type ('key, 'value) input = {
  input_equal : 'value -> 'value -> bool;
  slots : (int, ('key, 'value slot) Hashtbl.t) Hashtbl.t;
}

let input ~name:_ ~show:_ ?(equal = ( = )) () = { input_equal = equal; slots = Hashtbl.create 4 }

let slot database input key =
  let slots = table input.slots database in
  match Hashtbl.find_opt slots key with
  | Some slot -> slot
  | None ->
      let slot = { value = None; changed = 0 } in
      Hashtbl.replace slots key slot;
      slot

(* A result built while an input changed under it could pass its own trace
   check, so inputs change only between demands. *)
let change database slot value =
  if database.frames <> [] then invalid_arg "Query: an input changed while a query was running";
  database.revision <- database.revision + 1;
  slot.value <- value;
  slot.changed <- database.revision

let set database input key value =
  let slot = slot database input key in
  match slot.value with
  | Some old when input.input_equal old value -> ()
  | _ -> change database slot (Some value)

let remove database input key =
  let slot = slot database input key in
  match slot.value with None -> () | Some _ -> change database slot None

let find database input key =
  let slot = slot database input key in
  record database (fun () -> slot.changed);
  slot.value

let get database input key =
  match find database input key with Some value -> value | None -> raise Not_found

(* Queries *)

type 'value outcome = Value of 'value | Raised of exn

type 'value memo = {
  mutable outcome : 'value outcome;
  mutable verified_at : revision;
  mutable changed_at : revision;
  mutable trace : dependency list;  (** In the order they were read. *)
}

type ('key, 'value) query = {
  name : string;
  show : 'key -> string;
  equal : 'value -> 'value -> bool;
  compute : database -> 'key -> 'value;
  memos : (int, ('key, 'value memo) Hashtbl.t) Hashtbl.t;
  active : (int, ('key, unit) Hashtbl.t) Hashtbl.t;
}

let query ~name ~show ?(equal = ( = )) compute =
  { name; show; equal; compute; memos = Hashtbl.create 4; active = Hashtbl.create 4 }

let label query key = Printf.sprintf "%s(%s)" query.name (query.show key)

let same query left right =
  match (left, right) with
  | Value left, Value right -> query.equal left right
  | Raised left, Raised right -> ( try left = right with Invalid_argument _ -> false)
  | _ -> false

(* Runs [body] with the query marked active for the key, in a frame of its
   own, so what it reads goes to its own trace and not to the query that
   asked for it. A query asked for while it is active, whether running or
   having its trace checked, is a cycle. *)
let in_frame database query key body =
  let this = label query key in
  let active = table query.active database in
  if Hashtbl.mem active key then begin
    let rec cycle acc = function
      | [] -> acc
      | frame :: rest ->
          if frame.label = this then frame.label :: acc else cycle (frame.label :: acc) rest
    in
    raise (Cycle (cycle [] database.frames))
  end;
  let frame = { label = this; dependencies = [] } in
  database.frames <- frame :: database.frames;
  Hashtbl.replace active key ();
  Fun.protect
    ~finally:(fun () ->
      Hashtbl.remove active key;
      database.frames <- List.tl database.frames)
    (fun () -> body frame)

let run database query key =
  in_frame database query key (fun frame ->
      if database.logging then database.log <- label query key :: database.log;
      let outcome =
        match query.compute database key with
        | value -> Value value
        | exception ((Out_of_memory | Stack_overflow) as fatal) -> raise fatal
        | exception exception_ -> Raised exception_
      in
      (outcome, List.rev frame.dependencies))

(* Brings the stored result up to date with the current revision. It raises
   only [Cycle], when the query is already active for the key. *)
let rec ensure : 'key 'value. database -> ('key, 'value) query -> 'key -> 'value memo =
 fun database query key ->
  let memos = table query.memos database in
  match Hashtbl.find_opt memos key with
  | Some memo when memo.verified_at = database.revision -> memo
  | Some memo when in_frame database query key (fun _ -> unchanged memo) ->
      memo.verified_at <- database.revision;
      memo
  | Some memo ->
      let outcome, trace = run database query key in
      if not (same query memo.outcome outcome) then begin
        memo.outcome <- outcome;
        memo.changed_at <- database.revision
      end;
      memo.verified_at <- database.revision;
      memo.trace <- trace;
      memo
  | None ->
      let outcome, trace = run database query key in
      let memo =
        { outcome; verified_at = database.revision; changed_at = database.revision; trace }
      in
      Hashtbl.replace memos key memo;
      memo

(* Whether nothing in a trace has changed since the result was checked.
   Entries are checked in the order they were read, and the check stops at
   the first change, since a later entry may not be read at all once an
   earlier one gives a different answer. *)
and unchanged memo = List.for_all (fun dependency -> dependency () <= memo.verified_at) memo.trace

(* A dependency on a query. A cycle met while checking it counts as a
   change, so the query that read it runs again and meets the cycle in its
   own frame, where it can catch it. *)
let dependency database query key () =
  match ensure database query key with memo -> memo.changed_at | exception Cycle _ -> max_int

(* A query that catches a [Cycle] has read something that has no stable
   answer, so it records a dependency that always counts as changed, and runs
   again at every revision until the cycle is gone. *)
let demand database query key =
  match ensure database query key with
  | memo -> (
      record database (dependency database query key);
      match memo.outcome with Value value -> value | Raised exception_ -> raise exception_)
  | exception (Cycle _ as cycle) ->
      record database (fun () -> max_int);
      raise cycle

let executed database = List.rev database.log
let clear_log database = database.log <- []
