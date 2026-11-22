type t = {
  names : Resolve.Names.lookups;
  read_resolved : Resolve.section -> Resolve.Names.key -> Resolve.resolved;
  find_trait_header : Path.t -> Resolve.trait_header option;
  find_constant_value : Path.t -> Z.t option;
  find_header : Resolve.Names.key -> Environment.header option;
  read_interface : Resolve.Names.key -> Environment.interface;
  read_elaborated_interface : Resolve.Names.key -> Environment.elaborated_interface;
  find_derived_interface : type_:Path.t -> trait:Path.t -> Types.impl_interface option;
  read_type_facts : Path.t -> Environment.type_facts;
  find_grant : Path.package -> Path.package -> Environment.grant option;
}
