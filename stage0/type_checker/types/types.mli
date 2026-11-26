type parameter = { owner : Path.t; name : string }

type ty =
  | Named of { path : Path.t; arguments : argument list }
  | Parameter of parameter
  | Projection of { base : ty; trait : trait_reference; name : string }
  | Function of function_type
  | Never
  | Integer
  | Variable of int
  | Hole
  | Error of Diagnostic.reported

and argument = Type of ty | Value of value

and value =
  | Known of Z.t
  | Value_parameter of parameter
  | Value_variable of int
  | Value_error of Diagnostic.reported

and trait_reference = {
  trait : Path.t;
  trait_arguments : argument list;
  associated : (string * ty) list;
}

and function_type = {
  inputs : (Language.Mode.t * ty) list;
  output : ty;
  uses : capability_set;
  costs : cost list;
}

and result = Returns of ty | Lends of Language.Mode.t * ty

and capability =
  | Built_in of Language.Builtin_capability.t
  | Capability of Path.t
  | Capability_parameter of parameter
  | Capability_projection of { base : ty; trait : trait_reference; name : string }
  | Capability_variable of int
  | Capability_error of Diagnostic.reported
  | Capability_unless of { capability : capability; unless : condition }
  | Capability_unless_values of capability

and condition = bound_condition list
and bound_condition = { subject : ty; bound : trait_reference }
and capability_set = private capability list
and cost = { amortized : bool; resource : resource; bound : cost_bound }

and resource =
  | Metric of Language.Metric.t
  | Calls of { capability : Path.t; method_ : string option }

and cost_bound = Order_of | No_more_than of Z.t | Exactly_cost of Z.t

type associated_kind = Associated_type | Associated_capability_set

type application =
  | Type_application of ty
  | Trait_application of trait_reference
  | Associated_application of {
      base : ty;
      bounds : trait_reference list;
      name : string;
      kind : associated_kind;
    }

val unit : ty
val bool : ty
val make_builtin : ?arguments:argument list -> Language.Builtin_type.t -> ty
val make_self_parameter : Path.t -> parameter
val is_self_parameter : parameter -> bool
val make_named : Path.t -> ty list -> ty
val is_builtin : Language.Builtin_type.t -> ty -> bool
val find_builtin : ty -> Language.Builtin_type.t option
val is_well_known : Well_known.t -> ty -> bool
val find_viewed : ty -> ty option
val strip_view : ty -> ty
val is_view : ty -> bool
val make_view : ty -> ty
val is_viewable : ty -> bool
val erase_views : ty -> ty
val erase_argument_views : argument -> argument
val erase_trait_views : trait_reference -> trait_reference
val find_integer_bits : ty -> (int * bool) option
val find_integer_range : ty -> (Z.t * Z.t) option
val list_value_ranges : ty -> (Z.t * Z.t) list
val is_integer_type : ty -> bool
val signed_integer_types : Language.Builtin_type.t list
val unsigned_integer_types : Language.Builtin_type.t list
val integer_types : Language.Builtin_type.t list
val float_types : Language.Builtin_type.t list
val number_types : Language.Builtin_type.t list
val list_scalar_members : ty -> Language.Builtin_type.t list
val list_fitting_integer_types : Z.t -> Language.Builtin_type.t list
val find_integer_implementors : Path.t -> Language.Builtin_type.t list option
val find_bound_integer_implementors : trait_reference list -> Language.Builtin_type.t list option
val find_sealed_implementors : Path.t -> Language.Builtin_type.t list option
val sealed_traits : Well_known.t list
val is_float_type : ty -> bool
val make_capability_set : capability list -> capability_set
val no_capabilities : capability_set
val union_capabilities : capability_set -> capability_set -> capability_set
val make_capability : Path.t -> capability
val make_condition : condition -> condition
val make_unless : capability -> condition -> capability option
val find_base : capability -> capability
val has_capability : capability -> capability_set -> bool
val may_use : capability -> capability_set -> bool
val find_unless : capability -> capability_set -> condition option

val terminates_when :
  implies:(condition -> condition -> bool) -> condition -> capability_set -> bool

val exists_capability : (capability -> bool) -> capability_set -> bool
val list_capabilities : capability_set -> capability list
val terminates : capability_set -> bool

val intersect_capabilities :
  implies:(condition -> condition -> bool) -> capability_set list -> capability_set

val subtract_capabilities :
  implies:(condition -> condition -> bool) -> capability_set -> capability_set -> capability_set

val is_capability_subset :
  implies:(condition -> condition -> bool) -> capability_set -> capability_set -> bool

val compute_missing_capabilities :
  implies:(condition -> condition -> bool) ->
  required:capability_set ->
  available:capability_set ->
  capability_set

val replace_capabilities : (capability -> capability_set option) -> capability_set -> capability_set

type property = Copyable | Plain | View | Holds_function
type substitution

val no_substitution : substitution
val is_empty_substitution : substitution -> bool
val combine_substitutions : substitution -> substitution -> substitution
val bind_argument : parameter -> argument -> substitution -> substitution
val find_argument : parameter -> substitution -> argument option
val list_type_arguments : substitution -> (parameter * ty) list
val substitute : substitution -> ty -> ty
val substitute_argument : substitution -> argument -> argument
val substitute_trait : substitution -> trait_reference -> trait_reference
val substitute_erased : substitution -> ty -> ty
val substitute_argument_erased : substitution -> argument -> argument
val substitute_trait_erased : substitution -> trait_reference -> trait_reference
val substitute_function : substitution -> function_type -> function_type
val substitute_capabilities : substitution -> capability_set -> capability_set
val substitute_condition : substitution -> condition -> condition

val map_condition_types :
  (ty -> ty) -> (trait_reference -> trait_reference) -> condition -> condition

val map_conditions : (condition -> condition) -> capability_set -> capability_set
val substitute_substitution : substitution -> substitution -> substitution

type evidence =
  | Impl of { impl : Path.t; substitution : substitution }
  | Derived_for_view of { viewed : Path.t; substitution : substitution }
  | Bound

val substitute_evidence : substitution -> evidence -> evidence
val extract_result_type : result -> ty
val find_lent_mode : result -> Language.Mode.t option
val map_argument : (ty -> ty) -> argument -> argument
val map_trait : (ty -> ty) -> trait_reference -> trait_reference

val map_capability_types :
  (ty -> ty) -> (trait_reference -> trait_reference) -> capability_set -> capability_set

val map : ?map_capabilities:(capability_set -> capability_set) -> (ty -> ty option) -> ty -> ty
val exists : ?resolve:(ty -> ty) -> (ty -> bool) -> ty -> bool
val find_specification_only_type : ty -> ty option
val contains_capability_variable : capability_set -> bool
val has_unsolved_capabilities : capability_set -> bool
val equal : ty -> ty -> bool
val is_error : ty -> bool
val is_open_type : ty -> bool
val contains_unsolved : ty -> bool
val is_unsolved_argument : argument -> bool
val has_same_clauses : function_type -> function_type -> bool
val costs_imply : provided:cost list -> required:cost list -> bool
val show : ty -> string
val show_capability : capability -> string
val show_condition : condition -> string
val show_trait : trait_reference -> string
val show_argument : argument -> string
val show_capabilities : capability_set -> string
val show_output : result -> string

type generic_kind = Type_generic of trait_reference list | Value_generic
type generic = { generic : parameter; kind : generic_kind }

val list_generic_arguments : generic list -> argument list
val list_capability_arguments : parameter list -> (string * capability_set) list
val list_bounds : generic list -> parameter -> trait_reference list
val make_substitution : generic list -> argument list -> substitution
val make_capability_substitution : parameter list -> (string * capability_set) list -> substitution

type parameter_info = { name : string; mode : Language.Mode.t; type_ : ty; has_default : bool }

val list_capture_free_parameters : parameter_info list -> string list
val mentions_specification_only_type : parameter_info list -> result -> bool

type modified = { position : int; field_path : string list; is_elements : bool }

type signature = {
  generics : generic list;
  capability_parameters : parameter list;
  receiver : (Language.Mode.t * ty) option;
  parameters : parameter_info list;
  output : result;
  uses : capability_set;
  costs : cost list;
  modifies : modified list;
  specification_only : bool;
  is_update_step : bool;
  capture_free_parameters : string list;
}

val is_field_path_prefix : string list -> string list -> bool
val find_parameter_position : signature -> string -> int option
val read_parameter_at : signature -> int -> parameter_info
val add_receiver : signature -> (Language.Mode.t * ty) option -> signature
val list_modified_parts : signature -> int -> modified list option
val is_part_within : container:modified -> modified -> bool
val show_modified_part : root:string -> modified -> string

type instantiation = {
  type_arguments : argument list;
  capability_arguments : (string * capability_set) list;
}

val no_instantiation : instantiation
val substitute_instantiation : substitution -> instantiation -> instantiation
val make_signature_substitution : signature -> instantiation -> substitution
val make_trait_substitution : generic list -> self:ty -> trait_reference -> substitution
val map_bounds : (trait_reference list -> trait_reference list) -> generic list -> generic list
val map_signature : (ty -> ty) -> signature -> signature
val substitute_signature : substitution -> signature -> signature

val add_impl_generics_and_uses :
  impl_generics:generic list -> impl_uses:capability_set -> signature -> signature

val make_function_type : signature -> function_type option

type field = { field_name : string; field_type : ty; field_has_default : bool }
type variant = { variant_name : string; fields : field list option; indirect : bool }

type shape =
  | Record of field list
  | Sum of variant list
  | Todo_type
  | Builtin_type of Language.Builtin_type.t

type type_interface = {
  type_generics : generic list;
  shape : shape;
  opaque : bool;
  is_tuple : bool;
  derives : Path.t list;
  declares_potential : bool;
}

val instantiate_fields : type_interface -> argument list -> field list option
val instantiate_variants : type_interface -> argument list -> variant list option
val list_field_types : type_interface -> ty list

type associated_type = { associated_name : string; associated_bounds : trait_reference list }
type trait_method = { method_name : string; method_receiver : Path.receiver; provided : bool }

type restated_method = {
  restated_name : string;
  restated_receiver : Path.receiver;
  declared_by : Path.t;
}

type trait_interface = {
  trait_generics : generic list;
  requires : trait_reference list;
  supertraits : trait_reference list;
  associated_types : associated_type list;
  associated_capabilities : string list;
  methods : trait_method list;
  restated : restated_method list;
  laws : (string * (string * ty) list) list;
  is_capability : bool;
}

type impl_interface = {
  impl_generics : generic list;
  implements : trait_reference;
  for_type : ty;
  impl_uses : capability_set;
  capability_sets : (string * capability_set) list;
  impl_methods : (string * Path.receiver) list;
}

val is_implemented_by :
  trait_interface -> trait_method -> name:string -> receiver:Path.receiver -> bool

val find_implementing_receiver :
  trait_interface -> impl_interface -> trait_method -> Path.receiver option

type constant_interface = { constant_type : ty }

val make_trait_reference : arguments:argument list -> Path.t -> trait_reference
val string_type : ty
val find_sequence_element : ty -> ty option
val find_list_of_array : ty -> ty option
val find_specification_sequence_element : ty -> ty option

module For_testing : sig
  val list_arguments : substitution -> (parameter * argument) list
end
