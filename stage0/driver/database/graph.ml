module Make (Node : Strongly_connected.Node) = struct
  module Table = Hashtbl.Make (Node)

  type component = { id : int; members : Node.t list; mutable is_blocked : bool }

  type t = {
    successors : Node.t list option Table.t;
    reflected : Node.t list Table.t;
    predecessors : unit Table.t Table.t;
    components : component Table.t;
    roots : unit Table.t;
    unreachable_candidates : unit Table.t;
    tracks_blocked : bool;
    mutable next_id : int;
  }

  type group = Blocked | Members of Node.t list
  type update = { touched : Node.t list; removed : Node.t list }

  let create ~tracks_blocked =
    {
      tracks_blocked;
      successors = Table.create 256;
      reflected = Table.create 64;
      predecessors = Table.create 256;
      components = Table.create 256;
      roots = Table.create 64;
      unreachable_candidates = Table.create 64;
      next_id = 0;
    }

  let copy graph =
    let by_id = Hashtbl.create 256 in
    let copied (component : component) =
      match Hashtbl.find_opt by_id component.id with
      | Some copied -> copied
      | None ->
          let copied =
            { id = component.id; members = component.members; is_blocked = component.is_blocked }
          in
          Hashtbl.replace by_id component.id copied;
          copied
    in
    let predecessors = Table.copy graph.predecessors in
    Table.filter_map_inplace (fun _ nodes -> Some (Table.copy nodes)) predecessors;
    let components = Table.copy graph.components in
    Table.filter_map_inplace (fun _ component -> Some (copied component)) components;
    {
      successors = Table.copy graph.successors;
      reflected = Table.copy graph.reflected;
      predecessors;
      components;
      roots = Table.copy graph.roots;
      unreachable_candidates = Table.copy graph.unreachable_candidates;
      tracks_blocked = graph.tracks_blocked;
      next_id = graph.next_id;
    }

  let keys table = Table.fold (fun key _ keys -> key :: keys) table []
  let is_node graph node = Table.mem graph.components node
  let component_of graph node = Table.find graph.components node

  let stored_successors graph node =
    match Table.find_opt graph.successors node with
    | Some (Some successors) -> successors
    | Some None | None -> []

  let edges graph node =
    match Table.find_opt graph.reflected node with
    | Some edges -> edges
    | None -> stored_successors graph node

  let predecessors graph node =
    match Table.find_opt graph.predecessors node with
    | Some predecessors -> keys predecessors
    | None -> []

  let add_predecessor graph node predecessor =
    let predecessors =
      match Table.find_opt graph.predecessors node with
      | Some predecessors -> predecessors
      | None ->
          let predecessors = Table.create 4 in
          Table.replace graph.predecessors node predecessors;
          predecessors
    in
    Table.replace predecessors predecessor ()

  let remove_predecessor graph node predecessor =
    Option.iter
      (fun predecessors -> Table.remove predecessors predecessor)
      (Table.find_opt graph.predecessors node)

  let fresh_component graph members =
    let component = { id = graph.next_id; members; is_blocked = false } in
    graph.next_id <- graph.next_id + 1;
    List.iter (fun member -> Table.replace graph.components member component) members;
    component

  let add_if_new graph node =
    let is_new = not (is_node graph node) in
    if is_new then begin
      ignore (fresh_component graph [ node ]);
      Table.replace graph.unreachable_candidates node ()
    end;
    is_new

  let add_root graph root =
    Table.replace graph.roots root ();
    add_if_new graph root

  let remove_root graph root =
    if Table.mem graph.roots root then begin
      Table.remove graph.roots root;
      Table.replace graph.unreachable_candidates root ()
    end

  let successors graph node = Table.find_opt graph.successors node

  let reflect graph node =
    if not (Table.mem graph.reflected node) then
      Table.replace graph.reflected node (stored_successors graph node)

  let set_successors graph node successors =
    reflect graph node;
    Table.replace graph.successors node successors;
    List.filter (add_if_new graph) (Option.value successors ~default:[])

  let remove_successors graph node =
    if is_node graph node then begin
      reflect graph node;
      Table.remove graph.successors node
    end

  let has_changes graph =
    Table.length graph.reflected > 0 || Table.length graph.unreachable_candidates > 0

  let rec difference left right =
    match (left, right) with
    | [], _ -> []
    | left, [] -> left
    | node :: rest, other :: others ->
        let order = Node.compare node other in
        if order = 0 then difference rest others
        else if order < 0 then node :: difference rest right
        else difference left others

  let neighbors graph next (component : component) =
    let seen = Hashtbl.create 8 in
    List.fold_left
      (fun neighbors member ->
        List.fold_left
          (fun neighbors node ->
            let neighbor = component_of graph node in
            if neighbor.id = component.id || Hashtbl.mem seen neighbor.id then neighbors
            else begin
              Hashtbl.replace seen neighbor.id ();
              neighbor :: neighbors
            end)
          neighbors (next graph member))
      [] component.members

  type search = {
    visited : (int, component) Hashtbl.t;
    mutable frontier : component list;
    list_next : t -> Node.t -> Node.t list;
  }

  let search next start =
    let visited = Hashtbl.create 16 in
    Hashtbl.replace visited start.id start;
    { visited; frontier = [ start ]; list_next = next }

  let step graph ?(within = fun _ -> true) search =
    match search.frontier with
    | [] -> false
    | component :: rest ->
        search.frontier <-
          List.fold_left
            (fun frontier neighbor ->
              if Hashtbl.mem search.visited neighbor.id || not (within neighbor) then frontier
              else begin
                Hashtbl.replace search.visited neighbor.id neighbor;
                neighbor :: frontier
              end)
            rest
            (neighbors graph search.list_next component);
        true

  let reached graph next ~within start =
    let traversal = search next start in
    while step graph ~within:(fun component -> Hashtbl.mem within component.id) traversal do
      ()
    done;
    Hashtbl.fold (fun _ component components -> component :: components) traversal.visited []

  let cycle_through graph ~source ~target =
    let forward = search edges target and backward = search predecessors source in
    let rec exhausted () =
      if not (step graph forward) then `Forward
      else if not (step graph backward) then `Backward
      else exhausted ()
    in
    match exhausted () with
    | `Forward ->
        if Hashtbl.mem forward.visited source.id then
          Some (reached graph predecessors ~within:forward.visited source)
        else None
    | `Backward ->
        if Hashtbl.mem backward.visited target.id then
          Some (reached graph edges ~within:backward.visited target)
        else None

  let has_external_predecessor graph (component : component) =
    List.exists
      (fun member ->
        List.exists
          (fun predecessor -> (component_of graph predecessor).id <> component.id)
          (predecessors graph member))
      component.members

  let unreachable graph candidates =
    let removed = ref [] in
    let rec visit = function
      | [] -> ()
      | node :: rest -> (
          match Table.find_opt graph.components node with
          | Some component
            when (not (List.exists (Table.mem graph.roots) component.members))
                 && not (has_external_predecessor graph component) ->
              let successors =
                List.concat_map (fun member -> edges graph member) component.members
              in
              List.iter
                (fun member ->
                  List.iter
                    (fun successor -> remove_predecessor graph successor member)
                    (edges graph member))
                component.members;
              List.iter
                (fun member ->
                  Table.remove graph.components member;
                  Table.remove graph.successors member;
                  Table.remove graph.predecessors member;
                  Table.remove graph.reflected member;
                  removed := member :: !removed)
                component.members;
              visit (successors @ rest)
          | Some _ | None -> visit rest)
    in
    visit candidates;
    !removed

  let is_unknown graph node =
    match Table.find_opt graph.successors node with
    | Some (Some _) -> false
    | Some None | None -> true

  let blocks graph (component : component) =
    List.exists
      (fun member ->
        is_unknown graph member
        || List.exists
             (fun successor ->
               let other = component_of graph successor in
               other.id <> component.id && other.is_blocked)
             (edges graph member))
      component.members

  let is_current graph (component : component) =
    match component.members with
    | member :: _ -> (
        match Table.find_opt graph.components member with
        | Some current -> current.id = component.id
        | None -> false)
    | [] -> false

  let rec settle graph touch = function
    | [] -> ()
    | (component, is_fresh) :: rest ->
        if is_current graph component then begin
          let is_blocked = blocks graph component in
          let is_flipped = is_blocked <> component.is_blocked in
          if is_flipped then begin
            component.is_blocked <- is_blocked;
            List.iter touch component.members
          end;
          if is_flipped || is_fresh then
            settle graph touch
              (List.map
                 (fun predecessor -> (predecessor, false))
                 (neighbors graph predecessors component)
              @ rest)
          else settle graph touch rest
        end
        else settle graph touch rest

  let update graph =
    let touched = Table.create 64 in
    let touch node = Table.replace touched node () in
    let fresh = ref [] in
    let replace pieces =
      List.iter
        (fun members ->
          List.iter touch members;
          fresh := fresh_component graph members :: !fresh)
        pieces
    in
    let candidates = ref (keys graph.unreachable_candidates) in
    Table.reset graph.unreachable_candidates;
    let changed = List.sort Node.compare (keys graph.reflected) in
    List.iter
      (fun node ->
        let before = List.sort_uniq Node.compare (Table.find graph.reflected node) in
        Table.remove graph.reflected node;
        let after = List.sort_uniq Node.compare (stored_successors graph node) in
        let removed = difference before after and added = difference after before in
        List.iter (fun successor -> remove_predecessor graph successor node) removed;
        List.iter (fun successor -> add_predecessor graph successor node) added;
        touch node;
        let is_with_node successor =
          (component_of graph successor).id = (component_of graph node).id
        in
        if List.exists is_with_node removed then begin
          let split = component_of graph node in
          replace
            (Strongly_connected.find_components
               (module Node)
               ~successors:(fun member ->
                 List.filter
                   (fun successor -> (component_of graph successor).id = split.id)
                   (edges graph member))
               split.members)
        end;
        List.iter
          (fun successor ->
            if not (is_with_node successor) then
              Option.iter
                (fun merged ->
                  replace
                    [
                      List.sort Node.compare
                        (List.concat_map (fun (component : component) -> component.members) merged);
                    ])
                (cycle_through graph ~source:(component_of graph node)
                   ~target:(component_of graph successor)))
          added;
        candidates := removed @ !candidates)
      changed;
    let removed = unreachable graph !candidates in
    if graph.tracks_blocked then
      settle graph touch
        (List.map (fun component -> (component, true)) !fresh
        @ List.filter_map
            (fun node ->
              Option.map
                (fun component -> (component, false))
                (Table.find_opt graph.components node))
            changed);
    { touched = List.sort Node.compare (List.filter (is_node graph) (keys touched)); removed }

  let group graph node =
    match Table.find_opt graph.components node with
    | None -> Members []
    | Some { is_blocked = true; _ } -> Blocked
    | Some { members = [ single ]; _ } ->
        if List.exists (Node.equal single) (stored_successors graph single) then Members [ single ]
        else Members []
    | Some { members; _ } -> Members members
end
