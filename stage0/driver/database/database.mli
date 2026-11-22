type t
type 'value outcome = Value of 'value | Failed | Blocked

exception Unusable of string

val create : ?on_bug:(Compiler_bug.t -> unit) -> ?loaded:string list -> Project.package list -> t
val build_package : loaded:string list -> Project.package -> into:string -> unit
val update : ?on_bug:(Compiler_bug.t -> unit) -> t -> (Path.file * string option) list -> unit

val relayout :
  ?on_bug:(Compiler_bug.t -> unit) -> t -> loaded:string list -> Project.package list -> unit

val open_file :
  ?on_bug:(Compiler_bug.t -> unit) ->
  string ->
  compiler:string ->
  loaded:string list ->
  Project.package list ->
  t

val commit : t -> unit
val close : t -> unit
val close_uncommitted : t -> unit
val copy : t -> t
val merge_packages : string list -> into:string -> unit
val list_package_diagnostics : string -> Path.package -> (Source.t * Diagnostic.t list) list

type checker =
  | Parse
  | Resolve
  | Interface
  | Infer
  | Usage
  | Ownership
  | Package_checks
  | Unexported

val list_file_diagnostics : t -> Path.file -> Diagnostic.t list
val list_dependency_diagnostics : t -> Path.package -> (Source.t * Diagnostic.t list) list
val read_source : t -> Path.file -> Source.t

type proofs

val prove : ?on_bug:(Compiler_bug.t -> unit) -> t -> Path.file list -> proofs
val list_evaluations : proofs -> Prover.Obligation.evaluation list

val decide :
  ?on_bug:(Compiler_bug.t -> unit) ->
  proofs ->
  runs:(Prover.Obligation.evaluation * Prover.Obligation.run) list ->
  Solver.t Lazy.t ->
  unit

type proof_site = { code : string; span : Source.span; shows : string }
type proof_state = { site : proof_site; is_proven : bool; trusts_compiled_code : bool }

val list_proof_states : t -> Path.file -> proof_state list
val list_proof_warnings : t -> Path.file -> Diagnostic.t list
val list_proof_diagnostics : t -> Path.file -> Diagnostic.t list
val list_holes : proofs -> reached:Path.t list -> (Path.file * int * int * Path.t list) list
val make_interface_lookups : t -> Interface.Lookups.t
val read_resolved : t -> Resolve.Names.key -> Resolve.resolved option
val read_checked_body : t -> Resolve.Names.key -> Infer.checked option
val read_parsed : t -> Path.file -> Syntax.file
val find_main : t -> Path.package -> Path.t option

type read = {
  reader : Path.t;
  reader_kind : string;
  read : Path.t;
  read_kind : string;
  is_signature : bool;
}

val list_dependencies : t -> Path.t list -> read list
val list_dependents : t -> Path.t list -> read list

type counts = {
  kind : string;
  computed : int;
  unchanged : int;
  writes : int;
  reads : int;
  distinct_reads : int;
}

val count : (unit -> 'result) -> 'result * counts list

type statement_count = { statement : string; runs : int; steps : int; seconds : float }

val count_statements : (unit -> 'result) -> 'result * statement_count list

type change = { changed : Path.t; kind : string; is_signature : bool }

val list_changes : t -> t -> change list

type manifest_problem =
  | Not_a_capability of { dependency : Path.package; capability : Grant.capability }
  | Unused_dependency of Path.package

val list_manifest_problems : t -> Path.package -> manifest_problem list
val find_code_packages : t -> Path.package -> Path.package list option
val find_lowered_lookups : t -> Path.package list -> (Lowering.lowered_lookups, string) result
val make_name_lookups : t -> Resolve.Names.lookups
val list_definitions_naming : t -> Path.t -> Resolve.Names.key list

module For_testing : sig
  type stage = Kind.stage =
    | Parse
    | Declare
    | Supply
    | Claim_roots
    | Resolve
    | Resolve_grant
    | Check_imports
    | Read_trait_header
    | Evaluate_constant
    | Elaborate_header
    | Elaborate
    | Derive_interface
    | Compute_type_facts
    | Check_signature
    | Check_contract
    | Check_body
    | Build_body_mir
    | Build_contract_mir
    | Generate_mir
    | List_calls
    | Group_recursion
    | Check_usage
    | Check_ownership
    | Check_sealed
    | Check_impl
    | Check_type
    | Check_instantiations
    | Check_tests
    | Check_unexported
    | Check_dependencies
    | Prove
    | Lower
    | Key_tests
    | Decide

  type fact = Kind.fact =
    | Resolved of Resolve.section
    | Grant
    | Trait_header
    | Constant_value
    | Header
    | Interface
    | Elaboration
    | Derived_interface
    | Type_facts
    | Signature_check
    | Contract
    | Body_form
    | Body_tables
    | Run_forever
    | Ownership_modes
    | Body_mir
    | Contract_mir
    | Generated_mir
    | Call_node
    | Callees
    | Recursion_group
    | Usage_check
    | Ownership
    | Unused_dependencies
    | Proof
    | Lowered
    | Test_key

  type lookup = Kind.lookup =
    | Source
    | Packages
    | Files
    | Dependencies
    | Module
    | Entry
    | Entries
    | Imports
    | Declaration
    | Tree
    | Text
    | Place
    | Container
    | Contained
    | Module_declarations
    | File_declarations
    | Package_declarations
    | Members
    | Traits_declaring
    | Impl_index
    | Impls_of_type
    | Impls_of_trait
    | Law_proofs

  type entity = Kind.entity = Definition | Import | Package | Unknown_implementation | Item

  type selection = Kind.selection =
    | Unresolved
    | Import_references
    | Unchecked_bodies
    | Body_uses
    | Instantiations
    | Package_references

  type target = Kind.target =
    | Fact of fact
    | Lookup of lookup
    | Entity of entity
    | Selection of selection

  val stages : stage list
  val show_stage : stage -> string

  type nonrec checker = checker =
    | Parse
    | Resolve
    | Interface
    | Infer
    | Usage
    | Ownership
    | Package_checks
    | Unexported

  val list_diagnostics : checker list -> t -> Path.file -> Diagnostic.t list
  val fragment_checkers : checker list
  val make_unchecked_interface_lookups : t -> Interface.Lookups.t
  val make_mir_lookups : t -> Mir.lookups
  val read_derived_form : t -> Path.t -> Core.t option
  val read_core : t -> Path.t -> (Core.t * Types.substitution) option
  val read_ownership : t -> Resolve.Names.key -> (Core.id list * Core.id list) list outcome
  val list_unread : t -> string list
  val make_proof_lookups : t -> Prover.Lookups.t
  val find_proof : proofs -> Resolve.Names.key -> Prover.proof outcome option

  val list_queries :
    proofs ->
    runs:(Prover.Obligation.evaluation * Prover.Obligation.run) list ->
    (proof_site * string) list

  val lower_roots : ?on_bug:(Compiler_bug.t -> unit) -> t -> unit
  val propagate : ?on_bug:(Compiler_bug.t -> unit) -> t -> unit

  type computed = { stage : stage; id : int }
  type observed = { recomputed : computed list; collected : int list }

  val observe : (unit -> 'result) -> 'result * observed
  val identify_key : Resolve.Names.key -> int
  val identify_path : Path.t -> int
  val identify_file : Path.file -> int
  val identify_module : Path.module_ -> int
  val identify_package : Path.package -> int
  val identify_item : Lowered.Item.t -> int
  val list_reads : t -> stage -> int -> (target * int * string) list
  val with_failing_unit : stage -> int -> (unit -> 'result) -> 'result
  val add_root : t -> Lowered.Item.t -> unit
  val list_differences : t -> t -> (string * int) list
  val list_items : t -> Lowered.Item.t list
  val extend_package : loaded:string -> (Path.file * string) list -> t
end
