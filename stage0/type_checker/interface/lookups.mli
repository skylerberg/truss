type t = {
  names : Resolve.Names.lookups;
  resolved : Resolve.section -> Resolve.Names.key -> Resolve.resolved option;
  trait_header : Path.t -> Resolve.trait_header option;
  constant_value : Path.t -> Z.t option;
  header : Resolve.Names.key -> Environment.header option;
  lowered_interface : Resolve.Names.key -> Environment.lowered_interface option;
  derived_interface : Path.t -> Types.impl_interface option;
  type_facts : Path.t -> Environment.type_facts option;
  granted : Path.package -> Path.package -> Environment.grant option;
}
