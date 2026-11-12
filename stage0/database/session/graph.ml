(* Graph questions about a state. Every answer names definitions and parts;
   the engine's nodes stay inside. *)

type edge = {
  dependent : Path.t;
  dependent_part : string;
  dependency : Path.t;
  dependency_part : string;
}

let part_of (subject : Query.subject) = Option.value subject.part ~default:""

(* The edges from a node about a definition: on each path of reads from the
   node, the first node about another definition. A path passes through
   nodes about no definition and nodes about the same definition, but not
   through a fixed base's nodes, so that a definition does not depend on
   everything the standard library's own queries read. *)
let edges_of_node engine node (subject : Query.subject) =
  let dependencies = Hashtbl.create 8 in
  let visited = Hashtbl.create 16 in
  let rec traverse node =
    List.iter
      (fun read ->
        let identity = Engine.identity read in
        if not (Hashtbl.mem visited identity) then begin
          Hashtbl.replace visited identity ();
          match Engine.subject read with
          | Some read_subject when not (Path.equal read_subject.path subject.path) ->
              Hashtbl.replace dependencies (read_subject.path, part_of read_subject) ()
          | Some _ | None -> if not (Engine.is_fixed read) then traverse read
        end)
      (Engine.reads engine node)
  in
  traverse node;
  Hashtbl.fold
    (fun (dependency, dependency_part) () edges ->
      { dependent = subject.path; dependent_part = part_of subject; dependency; dependency_part }
      :: edges)
    dependencies []

(* The edges from every node about a definition [is_dependent] accepts. *)
let edges_from engine ~is_dependent =
  List.concat_map
    (fun node ->
      match Engine.subject node with
      | Some subject when is_dependent subject.path -> edges_of_node engine node subject
      | Some _ | None -> [])
    (Engine.nodes engine)

let dependencies engine paths =
  let paths = Path.Set.of_list paths in
  List.sort_uniq compare (edges_from engine ~is_dependent:(fun path -> Path.Set.mem path paths))

(* Edges are found from the dependent's nodes, so the dependents of a
   definition take the edges of every definition. *)
let dependents engine = function
  | [] -> []
  | paths ->
      let paths = Path.Set.of_list paths in
      List.filter
        (fun edge -> Path.Set.mem edge.dependency paths)
        (edges_from engine ~is_dependent:(fun _ -> true))
      |> List.sort_uniq compare

(* The definitions each root reaches through edges, the root included.
   A definition's dependencies do not depend on the root that reaches it,
   so roots share them. *)
let reachable engine roots =
  let nodes_about = Hashtbl.create 1024 in
  List.iter
    (fun node ->
      Option.iter
        (fun (subject : Query.subject) -> Hashtbl.add nodes_about subject.path (node, subject))
        (Engine.subject node))
    (Engine.nodes engine);
  let dependencies_of = Hashtbl.create 256 in
  let dependency_paths path =
    match Hashtbl.find_opt dependencies_of path with
    | Some paths -> paths
    | None ->
        let paths =
          List.concat_map
            (fun (node, subject) -> edges_of_node engine node subject)
            (Hashtbl.find_all nodes_about path)
          |> List.map (fun edge -> edge.dependency)
          |> List.sort_uniq Path.compare
        in
        Hashtbl.replace dependencies_of path paths;
        paths
  in
  let rec reach reached path =
    if Path.Set.mem path reached then reached
    else List.fold_left reach (Path.Set.add path reached) (dependency_paths path)
  in
  List.map (reach Path.Set.empty) roots

type difference = Changed | Added | Same

(* Every node of [mine] that may differ from the same node in [theirs],
   with how it compares. A state holds only its differences from its bases, or
   possible ones, so where the two share a base these are the nodes either holds
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
    List.iter (fun visited -> Hashtbl.replace table (Engine.identity visited) visited) nodes;
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
