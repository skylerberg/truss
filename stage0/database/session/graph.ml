(* What a state's graph answers. Every answer names definitions and parts;
   the engine's nodes stay inside. *)

(* What a node's definition reads of other definitions: its reads, through
   nodes about no definition, to the definitions and parts they reach. *)
let definition_reads engine memo node =
  let own = Option.map (fun (s : Query.subject) -> s.path) (Engine.subject node) in
  let targets = Hashtbl.create 8 in
  let seen = Hashtbl.create 16 in
  let rec walk n =
    List.iter
      (fun read ->
        let identity = Engine.identity read in
        if not (Hashtbl.mem seen identity) then begin
          Hashtbl.replace seen identity ();
          match Engine.subject read with
          | Some subject when Some subject.path <> own ->
              Hashtbl.replace targets (subject.path, Option.value subject.part ~default:"") ()
          | Some _ | None -> (
              if
                (* A fixed base's own lookups are not followed, so a
                   definition is not said to read everything they read. *)
                not (Engine.is_fixed read)
              then
                match Hashtbl.find_opt memo identity with
                | Some reached -> List.iter (fun r -> Hashtbl.replace targets r ()) reached
                | None -> walk read)
        end)
      (Engine.reads engine n)
  in
  walk node;
  Hashtbl.fold (fun r () acc -> r :: acc) targets []

type dependencies = (Path.t, (Path.t * string * string) list) Hashtbl.t

(* For every definition a state holds results about, what it reads of every
   other. *)
let dependencies engine : dependencies =
  let memo = Hashtbl.create 1024 in
  let table = Hashtbl.create 256 in
  List.iter
    (fun node ->
      match Engine.subject node with
      | Some subject ->
          let part = Option.value subject.part ~default:"" in
          let reads = definition_reads engine memo node in
          let previous = Option.value (Hashtbl.find_opt table subject.path) ~default:[] in
          Hashtbl.replace table subject.path
            (List.map (fun (path, read_part) -> (path, part, read_part)) reads @ previous)
      | None -> ())
    (Engine.nodes engine);
  table

let reads (table : dependencies) path = Option.value (Hashtbl.find_opt table path) ~default:[]

let readers (table : dependencies) target =
  Hashtbl.fold
    (fun reader reads acc ->
      List.filter_map
        (fun (path, reader_part, read_part) ->
          if Path.equal path target then Some (reader, reader_part, read_part) else None)
        reads
      @ acc)
    table []
  |> List.sort_uniq compare

type difference = Changed | Added | Same

(* Every node of [mine] that may differ from the same node in [theirs],
   with how it compares. A state holds only what differs from its bases, or
   may, so where the two share a base these are the nodes either holds
   itself; a base that only one has is compared whole. *)
let compare_nodes mine theirs =
  let differs node =
    match Engine.current_in node theirs with
    | None -> Added
    | Some other -> if Engine.same_outcome mine node theirs other then Same else Changed
  in
  let seen = Hashtbl.create 256 in
  let differing = ref [] in
  let add node =
    let identity = Engine.identity node in
    if not (Hashtbl.mem seen identity) then begin
      Hashtbl.replace seen identity ();
      differing := node :: !differing
    end
  in
  List.iter add (Engine.unshared mine theirs);
  List.iter
    (fun other -> Option.iter add (Engine.current_in other mine))
    (Engine.unshared theirs mine);
  List.rev_map (fun node -> (node, differs node)) !differing

(* Every part of a definition that a change between two states could reach,
   in the first, with how it compares with the same part in the second. *)
let changes mine theirs =
  List.filter_map
    (fun (node, difference) ->
      match Engine.subject node with
      | Some (subject : Query.subject) -> Some (subject.path, subject.part, difference)
      | None -> None)
    (compare_nodes mine theirs)

type place = { path : Path.t option; part : string option; label : string }

type overlap =
  | Both_change of place
  | Reads of { this_worktree : bool; change : place; reads : place }

(* Where two states' changes from a common base meet: each node both
   changed, and each node one changed that depends on a node the other changed. *)
let overlaps ~base mine theirs =
  let changed engine =
    List.filter_map
      (fun (node, difference) -> if difference = Same then None else Some node)
      (compare_nodes engine base)
  in
  let mine_changed = changed mine and theirs_changed = changed theirs in
  let by_identity nodes =
    let table = Hashtbl.create 64 in
    List.iter (fun n -> Hashtbl.replace table (Engine.identity n) n) nodes;
    table
  in
  let mine_table = by_identity mine_changed and theirs_table = by_identity theirs_changed in
  let describe node =
    match Engine.subject node with
    | Some subject -> { path = Some subject.path; part = subject.part; label = Engine.label node }
    | None -> { path = None; part = None; label = Engine.label node }
  in
  let both =
    List.filter_map
      (fun node ->
        if Hashtbl.mem theirs_table (Engine.identity node) then Some (Both_change (describe node))
        else None)
      mine_changed
  in
  let reads_other engine changed own_table other_table ~this_worktree =
    List.concat_map
      (fun node ->
        if Engine.subject node = None then []
        else
          List.filter_map
            (fun read ->
              let identity = Engine.identity read in
              match Hashtbl.find_opt other_table identity with
              | Some other when not (Hashtbl.mem own_table identity) ->
                  Some (Reads { this_worktree; change = describe node; reads = describe other })
              | _ -> None)
            (Engine.reads engine node))
      changed
  in
  List.sort_uniq compare
    (both
    @ reads_other mine mine_changed mine_table theirs_table ~this_worktree:true
    @ reads_other theirs theirs_changed theirs_table mine_table ~this_worktree:false)
