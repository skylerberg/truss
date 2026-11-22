module Make (Node : Strongly_connected.Node) = struct
  module Table = Hashtbl.Make (Node)

  type component = { id : int; members : Node.t list; mutable is_blocked : bool }

  type t = {
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
      reflected = Table.create 64;
      predecessors = Table.create 256;
      components = Table.create 256;
      roots = Table.create 64;
      unreachable_candidates = Table.create 64;
      next_id = 0;
    }

  let copy graph =
    let by_id = Hashtbl.create 256 in
    let copy_component (component : component) =
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
    Table.filter_map_inplace (fun _ component -> Some (copy_component component)) components;
    {
      reflected = Table.copy graph.reflected;
      predecessors;
      components;
      roots = Table.copy graph.roots;
      unreachable_candidates = Table.copy graph.unreachable_candidates;
      tracks_blocked = graph.tracks_blocked;
      next_id = graph.next_id;
    }

  let list_keys table = Table.fold (fun key _ keys -> key :: keys) table []
  let is_node graph node = Table.mem graph.components node
  let list_roots graph = list_keys graph.roots
  let read_component graph node = Table.find graph.components node
  let list_current_successors find_successors node = Option.value (find_successors node) ~default:[]

  let list_edges find_successors graph node =
    match Table.find_opt graph.reflected node with
    | Some edges -> edges
    | None -> list_current_successors find_successors node

  let list_predecessors graph node =
    match Table.find_opt graph.predecessors node with
    | Some predecessors -> list_keys predecessors
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

  let make_component graph members =
    let component = { id = graph.next_id; members; is_blocked = false } in
    graph.next_id <- graph.next_id + 1;
    List.iter (fun member -> Table.replace graph.components member component) members;
    component

  let add_if_new graph node =
    let is_new = not (is_node graph node) in
    if is_new then begin
      ignore (make_component graph [ node ]);
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

  let add_node = add_if_new

  let change_successors graph node ~before ~after =
    if is_node graph node then begin
      if not (Table.mem graph.reflected node) then Table.replace graph.reflected node before;
      List.filter (add_if_new graph) after
    end
    else []

  let has_changes graph =
    Table.length graph.reflected > 0 || Table.length graph.unreachable_candidates > 0

  let rec subtract left right =
    match (left, right) with
    | [], _ -> []
    | left, [] -> left
    | node :: rest, other :: others ->
        let order = Node.compare node other in
        if order = 0 then subtract rest others
        else if order < 0 then node :: subtract rest right
        else subtract left others

  let list_neighbors graph list_next (component : component) =
    let seen = Hashtbl.create 8 in
    List.fold_left
      (fun neighbors member ->
        List.fold_left
          (fun neighbors node ->
            let neighbor = read_component graph node in
            if neighbor.id = component.id || Hashtbl.mem seen neighbor.id then neighbors
            else begin
              Hashtbl.replace seen neighbor.id ();
              neighbor :: neighbors
            end)
          neighbors (list_next graph member))
      [] component.members

  type search = {
    visited : (int, component) Hashtbl.t;
    mutable frontier : component list;
    list_next : t -> Node.t -> Node.t list;
  }

  let start_search list_next start =
    let visited = Hashtbl.create 16 in
    Hashtbl.replace visited start.id start;
    { visited; frontier = [ start ]; list_next }

  let step graph ?(is_inside = fun _ -> true) search =
    match search.frontier with
    | [] -> false
    | component :: rest ->
        search.frontier <-
          List.fold_left
            (fun frontier neighbor ->
              if Hashtbl.mem search.visited neighbor.id || not (is_inside neighbor) then frontier
              else begin
                Hashtbl.replace search.visited neighbor.id neighbor;
                neighbor :: frontier
              end)
            rest
            (list_neighbors graph search.list_next component);
        true

  let list_reached graph list_next ~within start =
    let traversal = start_search list_next start in
    while step graph ~is_inside:(fun component -> Hashtbl.mem within component.id) traversal do
      ()
    done;
    Hashtbl.fold (fun _ component components -> component :: components) traversal.visited []

  let find_cycle_through graph find_successors ~source ~target =
    let list_edges = list_edges find_successors in
    let forward = start_search list_edges target
    and backward = start_search list_predecessors source in
    let rec step_until_exhausted () =
      if not (step graph forward) then `Forward
      else if not (step graph backward) then `Backward
      else step_until_exhausted ()
    in
    match step_until_exhausted () with
    | `Forward ->
        if Hashtbl.mem forward.visited source.id then
          Some (list_reached graph list_predecessors ~within:forward.visited source)
        else None
    | `Backward ->
        if Hashtbl.mem backward.visited target.id then
          Some (list_reached graph list_edges ~within:backward.visited target)
        else None

  let has_external_predecessor graph (component : component) =
    List.exists
      (fun member ->
        List.exists
          (fun predecessor -> (read_component graph predecessor).id <> component.id)
          (list_predecessors graph member))
      component.members

  let list_unreachable graph find_successors candidates =
    let list_edges = list_edges find_successors in
    let removed = ref [] in
    let rec visit = function
      | [] -> ()
      | node :: rest -> (
          match Table.find_opt graph.components node with
          | Some component
            when (not (List.exists (Table.mem graph.roots) component.members))
                 && not (has_external_predecessor graph component) ->
              let successors =
                List.concat_map (fun member -> list_edges graph member) component.members
              in
              List.iter
                (fun member ->
                  List.iter
                    (fun successor -> remove_predecessor graph successor member)
                    (list_edges graph member))
                component.members;
              List.iter
                (fun member ->
                  Table.remove graph.components member;
                  Table.remove graph.predecessors member;
                  Table.remove graph.reflected member;
                  removed := member :: !removed)
                component.members;
              visit (successors @ rest)
          | Some _ | None -> visit rest)
    in
    visit candidates;
    !removed

  let blocks graph find_successors (component : component) =
    List.exists
      (fun member ->
        Option.is_none (find_successors member)
        || List.exists
             (fun successor ->
               let other = read_component graph successor in
               other.id <> component.id && other.is_blocked)
             (list_edges find_successors graph member))
      component.members

  let is_current graph (component : component) =
    match component.members with
    | member :: _ -> (
        match Table.find_opt graph.components member with
        | Some current -> current.id = component.id
        | None -> false)
    | [] -> false

  let rec settle graph find_successors touch = function
    | [] -> ()
    | (component, is_fresh) :: rest ->
        if is_current graph component then begin
          let is_blocked = blocks graph find_successors component in
          let is_flipped = is_blocked <> component.is_blocked in
          if is_flipped then begin
            component.is_blocked <- is_blocked;
            List.iter touch component.members
          end;
          if is_flipped || is_fresh then
            settle graph find_successors touch
              (List.map
                 (fun predecessor -> (predecessor, false))
                 (list_neighbors graph list_predecessors component)
              @ rest)
          else settle graph find_successors touch rest
        end
        else settle graph find_successors touch rest

  let update graph ~find_successors =
    let touched = Table.create 64 in
    let touch node = Table.replace touched node () in
    let fresh = ref [] in
    let replace pieces =
      List.iter
        (fun members ->
          List.iter touch members;
          fresh := make_component graph members :: !fresh)
        pieces
    in
    let candidates = ref (list_keys graph.unreachable_candidates) in
    Table.reset graph.unreachable_candidates;
    let changed = List.sort Node.compare (list_keys graph.reflected) in
    List.iter
      (fun node ->
        let before = List.sort_uniq Node.compare (Table.find graph.reflected node) in
        Table.remove graph.reflected node;
        let after = List.sort_uniq Node.compare (list_current_successors find_successors node) in
        let removed = subtract before after and added = subtract after before in
        List.iter (fun successor -> remove_predecessor graph successor node) removed;
        List.iter (fun successor -> add_predecessor graph successor node) added;
        touch node;
        let is_with_node successor =
          (read_component graph successor).id = (read_component graph node).id
        in
        if List.exists is_with_node removed then begin
          let split = read_component graph node in
          replace
            (Strongly_connected.list_components
               (module Node)
               ~list_successors:(fun member ->
                 List.filter
                   (fun successor -> (read_component graph successor).id = split.id)
                   (list_edges find_successors graph member))
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
                (find_cycle_through graph find_successors ~source:(read_component graph node)
                   ~target:(read_component graph successor)))
          added;
        candidates := removed @ !candidates)
      changed;
    let removed = list_unreachable graph find_successors !candidates in
    if graph.tracks_blocked then
      settle graph find_successors touch
        (List.map (fun component -> (component, true)) !fresh
        @ List.filter_map
            (fun node ->
              Option.map
                (fun component -> (component, false))
                (Table.find_opt graph.components node))
            changed);
    { touched = List.sort Node.compare (List.filter (is_node graph) (list_keys touched)); removed }

  let group graph ~find_successors node =
    match Table.find_opt graph.components node with
    | None -> Members []
    | Some { is_blocked = true; _ } -> Blocked
    | Some { members = [ single ]; _ } ->
        if List.exists (Node.equal single) (list_current_successors find_successors single) then
          Members [ single ]
        else Members []
    | Some { members; _ } -> Members members
end
