type 'a part = Value of 'a | Failed of Diagnostic.in_definition list | Blocked
type parsed = { tree : Syntax.file; diagnostics : Diagnostic.t list; text : string }

type _ t =
  | Parsed : Path.file -> parsed t
  | Resolved : Resolve.Names.key * Resolve.section -> Resolve.resolved t
  | Grant : Path.package * Path.package -> Interface.Environment.grant t
  | Import_check : Path.file -> Diagnostic.t list t
  | Trait_header : Resolve.Names.key -> Resolve.trait_header t
  | Constant_value : Path.t -> Z.t option t
  | Header : Resolve.Names.key -> Interface.Environment.header t
  | Interface : Resolve.Names.key -> Interface.Environment.elaborated_interface t
  | Derived_interface : { type_ : Path.t; trait : Path.t } -> Types.impl_interface t
  | Type_facts : Path.t -> Interface.Environment.type_facts t
  | Signature_check : Resolve.Names.key -> unit t
  | Contract : Resolve.Names.key -> Core.t t
  | Checked_body : Resolve.Names.key -> Infer.checked t
  | Body_mir : Resolve.Names.key -> Mir.body_part t
  | Contract_mir : Resolve.Names.key -> Mir.contract_part t
  | Generated_mir : Path.t -> (Mir.body_part * Mir.contract_part) t
  | Mir_call_edges : Path.t -> Path.t list t
  | Patterns : Resolve.Names.key -> unit t
  | Usage : Resolve.Names.key -> unit t
  | Ownership : Resolve.Names.key -> (Core.origin * Core.origin) list t
  | Package_check : Path.package * Package_checks.check -> Package_checks.outcome t
  | Proof : Resolve.Names.key -> Prover.proof t
  | Recursion_group : Path.t -> Path.t list t
  | Lowered : Instance.key -> (Compile.lowered, Compile.unsupported) result t
  | Test_key : Instance.key -> (string, Compile.unsupported) result t

type binding = Binding : 'a t * 'a part -> binding

val to_part : 'a t -> Part.stored
val find_type_equality : 'a t -> 'b t -> ('a, 'b) Type.eq option
