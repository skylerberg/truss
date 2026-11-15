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

type lowered_interface = {
  interface : interface;
  diagnostics : Syntax.diagnostic list;
  named : (Syntax.span * Types.ty) list;
  bounds : (Types.parameter * Types.trait_reference list) list;
}

val is_specification : interface -> bool

val lower :
  Query.context ->
  Resolve.Names.key ->
  Syntax.definition ->
  Resolve.resolved ->
  lowered_interface * Lower.context

val lowered_interface : (Resolve.Names.key, lowered_interface option) Query.query
val interface : (Path.t, interface option) Query.query

val in_declared_order :
  Query.context -> Path.t -> variant:string option -> name:('a -> string) -> 'a list -> 'a list

val type_interface : (Path.t, Types.type_interface option) Query.query
val signature : (Path.t, Types.signature option) Query.query

val signature_or_report :
  Query.context -> Path.t -> (Types.signature, Diagnostic.reported) result option

val trait_interface : (Path.t, Types.trait_interface option) Query.query
val impl_interface : (Path.t, Types.impl_interface option) Query.query
val constant_type : (Path.t, Types.ty option) Query.query
