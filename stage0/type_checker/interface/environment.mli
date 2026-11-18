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
  | Error_interface of Diagnostic.reported

type scope = {
  self_type : Types.ty option;
  self_trait : Types.trait_reference option;
  self_associated : (string * Types.ty) list;
  self_capabilities : (string * Types.capability_set) list;
  bounds : (Types.parameter * Types.trait_reference list) list;
  broken_parameters : (Types.parameter * Diagnostic.reported) list;
}

type elaborated_interface = {
  interface : interface;
  diagnostics : Diagnostic.in_definition list;
  named : (Syntax.id * Types.ty) list;
  scope : scope;
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
  container_scope : scope;
  container_named : (Syntax.id * Types.ty) list;
}

type occurrence = In_place | Indirect | Function_input
type requirement = Never | Requires of Types.ty list
type exposure = Always | If_any of Types.ty list

type type_facts = {
  copyable : requirement;
  plain : requirement;
  view : exposure;
  holds_function : exposure;
  contains : (Types.ty * occurrence) list;
}

type grant = { capabilities : Path.t list; unknown : string list }
