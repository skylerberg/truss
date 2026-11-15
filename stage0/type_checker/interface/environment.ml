type interface =
  | Function_interface of Types.signature
  | Type_interface of Types.type_interface
  | Trait_interface of Types.trait_interface
  | Impl_interface of Types.impl_interface
  | Constant_interface of Types.constant_interface
  | Test_interface of Types.capability_set
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
}

let empty_scope =
  { self_type = None; self_trait = None; self_associated = []; self_capabilities = []; bounds = [] }

type lowered_interface = {
  interface : interface;
  diagnostics : Syntax.diagnostic list;
  named : (Syntax.span * Types.ty) list;
  scope : scope;
}

type header = {
  container_scope : scope;
  header_generics : Types.generic list;
  header_uses : Types.capability_set;
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

let is_specification = function
  | Function_interface signature -> signature.specification_only
  | Theorem_interface _ | Law_proof_interface _ -> true
  | Type_interface _ | Trait_interface _ | Impl_interface _ | Constant_interface _
  | Test_interface _ | Error_interface _ ->
      false
