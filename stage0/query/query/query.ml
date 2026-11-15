type context = Incremental.context
type part = Incremental.part = Tree | Resolved | Interface | Shape | Signature | Body | Ownership
type subject = Incremental.subject = { path : Path.t; part : part }

let show_part = Incremental.show_part

type ('key, 'value) input = ('key, 'value) Incremental.input
type ('key, 'value) query = ('key, 'value) Incremental.query
type phase = int

let declared : (string, unit) Hashtbl.t = Hashtbl.create 16

let phase ~name ~after =
  if Hashtbl.mem declared name then invalid_arg ("Query.phase: two phases are named " ^ name);
  let rank = 1 + List.fold_left max 0 after in
  if rank >= Incremental.phases then invalid_arg ("Query.phase: too many phases before " ^ name);
  Hashtbl.replace declared name ();
  rank

let input = Incremental.input

let query ~name ~show ~phase ?saved ?portable ?equal ?about compute =
  Incremental.query ~name ~show ~phase ?saved ?portable ?equal ?about compute

let recursive_query ~name ~show ~phase ?saved ?portable ?equal ?about compute =
  let declared = ref None in
  let recursive =
    query ~name ~show ~phase ?saved ?portable ?equal ?about (fun context key ->
        compute (Option.get !declared) context key)
  in
  declared := Some recursive;
  recursive

let find = Incremental.read
let demand = Incremental.demand

exception Cycle = Incremental.Cycle
