type interface =
  | Function_interface of Types.signature
  | Type_interface of Types.type_interface
  | Trait_interface of Types.trait_interface
  | Impl_interface of Types.impl_interface
  | Constant_interface of Types.constant_interface
  | Test_interface of Types.signature
  | Theorem_interface of Types.signature
  | Law_proof_interface of {
      generics : Types.generic list;
      trait : Types.trait_reference;
      law : string;
      for_type : Types.ty;
    }
  | Error_interface of Catalog.reported

type declared_bounds
type known_bounds

type 'bounds scope = {
  self_type : Types.ty option;
  self_trait : Types.trait_reference option;
  self_associated : (string * Types.ty) list;
  self_capabilities : (string * Types.capability_set) list;
  bounds : (Types.parameter * Types.trait_reference list) list;
  broken_parameters : (Types.parameter * Catalog.reported) list;
}

type elaborated_interface = {
  interface : interface;
  diagnostics : Catalog.diagnostic list;
  applications : (Syntax.id * Types.application) list;
  scope : known_bounds scope;
}

type container =
  | Trait_parts of {
      trait_generics : Types.generic list;
      requires : Types.trait_reference list;
      associated_types : Types.associated_type list;
      associated_capabilities : string list;
      laws : (string * (string * Types.ty) list) list;
    }
  | Capability_parts
  | Impl_parts of {
      impl_generics : Types.generic list;
      implements : Types.trait_reference;
      for_type : Types.ty;
      impl_uses : Types.capability_set;
      capability_sets : (string * Types.capability_set) list;
    }

type header = {
  container : container;
  container_scope : declared_bounds scope;
  container_applications : (Syntax.id * Types.application) list;
}

type occurrence = In_place | Indirect | Function_input
type requirement = Never | Requires of Types.ty list
type exposure = Always | If_any of Types.ty list

type type_facts = {
  generics : Types.generic list;
  copyable : requirement;
  plain : requirement;
  view : exposure;
  holds_function : exposure;
  contains : (Types.ty * occurrence) list;
}

type grant = { capabilities : Path.t list; unknown : Grant.capability list }
