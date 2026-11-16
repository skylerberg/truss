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

let to_part : type a. a t -> Part.stored = function
  | Parsed file -> Computed (Parsed file)
  | Resolved (key, section) -> Computed (Resolved (key, section))
  | Grant (package, dependency) -> Computed (Grant (package, dependency))
  | Import_check file -> Computed (Import_check file)
  | Trait_header key -> Computed (Trait_header key)
  | Constant_value path -> Computed (Constant_value path)
  | Header key -> Computed (Header key)
  | Interface key -> Computed (Interface key)
  | Derived_interface { type_; trait } -> Computed (Derived_interface { type_; trait })
  | Type_facts path -> Computed (Type_facts path)
  | Signature_check key -> Computed (Signature_check key)
  | Contract key -> Computed (Contract key)
  | Checked_body key -> Computed (Checked_body key)
  | Body_mir key -> Computed (Body_mir key)
  | Contract_mir key -> Computed (Contract_mir key)
  | Generated_mir path -> Computed (Generated_mir path)
  | Mir_call_edges path -> Computed (Mir_call_edges path)
  | Patterns key -> Computed (Patterns key)
  | Usage key -> Computed (Usage key)
  | Ownership key -> Computed (Ownership key)
  | Package_check (package, check) -> Computed (Package_check (package, check))
  | Proof key -> Computed (Proof key)
  | Recursion_group path -> Recursion_group path
  | Lowered key -> Computed (Lowering (Lowered key))
  | Test_key key -> Computed (Lowering (Test_key key))

let find_type_equality : type a b. a t -> b t -> (a, b) Type.eq option =
 fun left right ->
  match (left, right) with
  | Parsed _, Parsed _ -> Some Equal
  | Resolved _, Resolved _ -> Some Equal
  | Grant _, Grant _ -> Some Equal
  | Import_check _, Import_check _ -> Some Equal
  | Trait_header _, Trait_header _ -> Some Equal
  | Constant_value _, Constant_value _ -> Some Equal
  | Header _, Header _ -> Some Equal
  | Interface _, Interface _ -> Some Equal
  | Derived_interface _, Derived_interface _ -> Some Equal
  | Type_facts _, Type_facts _ -> Some Equal
  | Signature_check _, Signature_check _ -> Some Equal
  | Contract _, Contract _ -> Some Equal
  | Checked_body _, Checked_body _ -> Some Equal
  | Body_mir _, Body_mir _ -> Some Equal
  | Contract_mir _, Contract_mir _ -> Some Equal
  | Generated_mir _, Generated_mir _ -> Some Equal
  | Mir_call_edges _, Mir_call_edges _ -> Some Equal
  | Patterns _, Patterns _ -> Some Equal
  | Usage _, Usage _ -> Some Equal
  | Ownership _, Ownership _ -> Some Equal
  | Package_check _, Package_check _ -> Some Equal
  | Proof _, Proof _ -> Some Equal
  | Recursion_group _, Recursion_group _ -> Some Equal
  | Lowered _, Lowered _ -> Some Equal
  | Test_key _, Test_key _ -> Some Equal
  | _ -> None
