module type Node = sig
  type t

  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
end

module Make (Node : Node) = struct
  module Table = Hashtbl.Make (Node)

  let of_graph ~successors roots =
    let index = Table.create 256 and low = Table.create 256 and on_stack = Table.create 256 in
    let stack = ref [] and next = ref 0 and components = ref [] in
    let work = Stack.create () in
    let enter node =
      Table.replace index node !next;
      Table.replace low node !next;
      incr next;
      stack := node :: !stack;
      Table.replace on_stack node ();
      Stack.push (node, ref (successors node)) work
    in
    let lower node bound = if bound < Table.find low node then Table.replace low node bound in
    let leave node =
      if Table.find low node = Table.find index node then begin
        let rec pop members =
          match !stack with
          | [] -> members
          | top :: rest ->
              stack := rest;
              Table.remove on_stack top;
              if Node.equal top node then top :: members else pop (top :: members)
        in
        components := List.sort Node.compare (pop []) :: !components
      end
    in
    List.iter
      (fun root ->
        if not (Table.mem index root) then begin
          enter root;
          while not (Stack.is_empty work) do
            let node, pending = Stack.top work in
            match !pending with
            | successor :: rest ->
                pending := rest;
                if not (Table.mem index successor) then enter successor
                else if Table.mem on_stack successor then lower node (Table.find index successor)
            | [] ->
                ignore (Stack.pop work);
                if not (Stack.is_empty work) then lower (fst (Stack.top work)) (Table.find low node);
                leave node
          done
        end)
      roots;
    List.rev !components
end
