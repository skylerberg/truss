module type Node = sig
  type t

  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
end

let list_components (type node) (module Node : Node with type t = node) ~list_successors roots =
  let module Table = Hashtbl.Make (Node) in
  let index = Table.create 256 and low_link = Table.create 256 and on_stack = Table.create 256 in
  let stack = ref [] and next_index = ref 0 and components = ref [] in
  let frames = Stack.create () in
  let enter node =
    Table.replace index node !next_index;
    Table.replace low_link node !next_index;
    incr next_index;
    stack := node :: !stack;
    Table.replace on_stack node ();
    Stack.push (node, ref (list_successors node)) frames
  in
  let lower_link node bound =
    if bound < Table.find low_link node then Table.replace low_link node bound
  in
  let leave node =
    if Table.find low_link node = Table.find index node then begin
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
        while not (Stack.is_empty frames) do
          let node, pending = Stack.top frames in
          match !pending with
          | successor :: rest ->
              pending := rest;
              if not (Table.mem index successor) then enter successor
              else if Table.mem on_stack successor then lower_link node (Table.find index successor)
          | [] ->
              ignore (Stack.pop frames);
              if not (Stack.is_empty frames) then
                lower_link (fst (Stack.top frames)) (Table.find low_link node);
              leave node
        done
      end)
    roots;
  List.rev !components
