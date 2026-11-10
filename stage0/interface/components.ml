(* The strongly connected components of a graph, by Tarjan's algorithm: the
   groups of nodes that reach each other. Whatever is defined by its parts,
   where a part may come back to the whole, is worked out a component at a
   time. Each component is sorted, and a component comes after every other
   one it reaches. [successors] gives only nodes of the graph. *)
let of_graph ~compare ~successors nodes =
  let index = Hashtbl.create 64 and low = Hashtbl.create 64 and on_stack = Hashtbl.create 64 in
  let stack = ref [] and next = ref 0 and found = ref [] in
  let lower node other = Hashtbl.replace low node (min (Hashtbl.find low node) other) in
  let rec visit node =
    Hashtbl.replace index node !next;
    Hashtbl.replace low node !next;
    incr next;
    stack := node :: !stack;
    Hashtbl.replace on_stack node ();
    List.iter
      (fun successor ->
        if not (Hashtbl.mem index successor) then begin
          visit successor;
          lower node (Hashtbl.find low successor)
        end
        else if Hashtbl.mem on_stack successor then lower node (Hashtbl.find index successor))
      (successors node);
    if Hashtbl.find low node = Hashtbl.find index node then begin
      let rec pop members =
        match !stack with
        | top :: rest ->
            stack := rest;
            Hashtbl.remove on_stack top;
            if compare top node = 0 then top :: members else pop (top :: members)
        | [] -> members
      in
      found := List.sort compare (pop []) :: !found
    end
  in
  List.iter (fun node -> if not (Hashtbl.mem index node) then visit node) nodes;
  List.rev !found
