module Make (Node : Strongly_connected.Node) : sig
  type t
  type group = Blocked | Members of Node.t list
  type update = { touched : Node.t list; removed : Node.t list }

  val create : tracks_blocked:bool -> t
  val copy : t -> t
  val add_root : t -> Node.t -> bool
  val add_node : t -> Node.t -> bool
  val remove_root : t -> Node.t -> unit
  val change_successors : t -> Node.t -> before:Node.t list -> after:Node.t list -> Node.t list
  val is_node : t -> Node.t -> bool
  val has_changes : t -> bool
  val update : t -> find_successors:(Node.t -> Node.t list option) -> update
  val group : t -> find_successors:(Node.t -> Node.t list option) -> Node.t -> group
end
