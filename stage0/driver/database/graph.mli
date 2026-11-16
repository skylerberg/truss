module Make (Node : Strongly_connected.Node) : sig
  type t
  type group = Blocked | Members of Node.t list
  type update = { touched : Node.t list; removed : Node.t list }

  val create : tracks_blocked:bool -> t
  val copy : t -> t
  val add_root : t -> Node.t -> bool
  val remove_root : t -> Node.t -> unit
  val find_successors : t -> Node.t -> Node.t list option option
  val set_successors : t -> Node.t -> Node.t list option -> Node.t list
  val remove_successors : t -> Node.t -> unit
  val has_changes : t -> bool
  val update : t -> update
  val group : t -> Node.t -> group
end
