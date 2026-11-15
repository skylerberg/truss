type t = {
  source : Path.file -> Source.t;
  interface : Interface.Lookups.t;
  mir : Mir.lookups;
  call_edges : Path.t -> Path.t list;
}
