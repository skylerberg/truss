type context = Incremental.context
type subject = Incremental.subject = { path : Path.t; part : string option }
type ('key, 'value) input = ('key, 'value) Incremental.input
type ('key, 'value) query = ('key, 'value) Incremental.query
type phase = int

let declared : (string, unit) Hashtbl.t = Hashtbl.create 16

(* A phase's rank is one more than the highest of the phases it reads, so
   that every phase it reads, directly or not, has a lower one. Inputs are
   before every phase, at rank 0. *)
let phase ~name ~after =
  if Hashtbl.mem declared name then invalid_arg ("Query.phase: two phases are named " ^ name);
  let rank = 1 + List.fold_left max 0 after in
  if rank >= Incremental.phases then invalid_arg ("Query.phase: too many phases before " ^ name);
  Hashtbl.replace declared name ();
  rank

let phase_rank phase = phase
let input = Incremental.input

let query ~name ~show ~phase ?saved ?portable ?equal ?about compute =
  Incremental.query ~name ~show ~phase ?saved ?portable ?equal ?about compute

let find = Incremental.read
let demand = Incremental.demand

exception Cycle = Incremental.Cycle
