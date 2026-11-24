type recursion =
  | Property of { type_ : Types.ty; property : Types.property }
  | Contents of { type_ : Types.ty }
  | Evidence of { type_ : Types.ty; trait : Types.trait_reference }
  | Capability_set of Types.capability

type count_error = Not_uint64 | Uncomputable
type associated = Associated_type | Associated_capability_set
type kind_mismatch = Value_for_type | Type_for_value

type value_condition =
  | In_capability_method
  | Joined_with_bound
  | Not_panic of Types.capability list

type recipient = Main | Test

type t =
  | Recursion_limit of { limit : int; recursion : recursion }
  | Misplaced_self_type of { at : Core.origin }
  | Self_outside_trait of { at : Core.origin; name : string; associated : associated }
  | Undeclared_associated of {
      at : Core.origin;
      trait : Types.trait_reference;
      name : string;
      associated : associated;
    }
  | Unbounded_associated of {
      at : Core.origin;
      parameter : string;
      name : string;
      associated : associated;
    }
  | Self_defined_capability_set of { at : Core.origin; name : string }
  | Arity of { at : Core.origin; written : string; expected : int; given : int }
  | Head_arity of { at : Core.origin; written : string; expected : int; given : int }
  | Argument_kind of {
      at : Core.origin;
      written : string;
      parameter : string;
      mismatch : kind_mismatch;
    }
  | Arguments_to_parameter of { at : Core.origin; written : string }
  | Count_error of { at : Core.origin; written : string; error : count_error }
  | Trait_as_type of { at : Core.origin; written : string }
  | Capability_as_type of { at : Core.origin; written : string }
  | Head_not_a_type of { at : Core.origin; written : string; kind : Language.Definition_kind.t }
  | Not_a_trait of { at : Core.origin; written : string; is_parameter : bool }
  | Decided_condition of { at : Core.origin; subject : Types.ty }
  | Decided_projection_condition of {
      at : Core.origin;
      subject : Types.ty;
      base : Types.ty;
      trait : Types.trait_reference;
      name : string;
    }
  | Not_a_capability of { at : Core.origin; written : string; is_type_parameter : bool }
  | Calls_not_a_capability of { at : Core.origin; written : string }
  | Calls_through_parameter of { at : Core.origin; name : string }
  | Unknown_capability_method of { at : Core.origin; written : string; method_ : string }
  | Read_only_owning_parameter of {
      at : Core.origin;
      name : Core.origin;
      written : string;
      view : string;
      copy : string;
      takes : string;
    }
  | Time_of_run_forever of { at : Core.origin }
  | Time_of_unbounded_parameter of { at : Core.origin; name : string }
  | Misplaced_value_condition of { at : Core.origin; condition : value_condition }
  | Wrong_value_parameter_type of { at : Core.origin; parameter : string; type_ : Types.ty }
  | Specification_only_field of { at : Core.origin; type_ : Types.ty }
  | Missing_associated_type of { at : Core.origin; name : string; trait : string }
  | Missing_method of { at : Core.origin; name : string; signature : string; trait : string }
  | Implements_built_in_capability of {
      at : Core.origin;
      capability : Language.Builtin_capability.t;
    }
  | Implements_built_in of { at : Core.origin; trait : string }
  | Associated_bound_unmet of {
      at : Core.origin;
      trait : string;
      name : string;
      bound : Types.trait_reference;
      chosen : Types.ty;
    }
  | Extra_associated of { at : Core.origin; trait : string; name : string; associated : associated }
  | Capability_set_defined_twice of { at : Core.origin; name : string }
  | Missing_required_impl of {
      at : Core.origin;
      trait : string;
      required : Types.trait_reference;
      for_type : Types.ty;
    }
  | Uses_on_trait_impl of { at : Core.origin }
  | Mut_self_for_slice of { at : Core.origin; trait : string; for_type : Types.ty }
  | Callback_contract_mismatch of {
      at : Core.origin;
      name : string;
      trait : string;
      parameter : string;
      clauses : string list;
    }
  | Restated_without_own of {
      at : Core.origin;
      trait : string;
      declared_by : Path.t;
      name : string;
      for_type : Types.ty;
    }
  | Undeclared_method of { at : Core.origin; trait : string; name : string }
  | Capability_method_receiver of { at : Core.origin }
  | Overridden_default of { at : Core.origin; trait : string; name : string }
  | Impl_signature_mismatch of {
      at : Core.origin;
      name : string;
      signature : string;
      trait : string;
    }
  | Uses_beyond_impl of { at : Core.origin; name : string }
  | Uses_beyond_trait of { at : Core.origin; name : string; trait : string }
  | Panic_beyond_condition of { at : Core.origin; name : string; trait : string }
  | Bound_unmet of {
      at : Core.origin;
      type_ : Types.ty;
      argument : Types.ty;
      bound : Types.trait_reference;
    }
  | Private_in_public of { at : Core.origin; path : Path.t }
  | Method_outside_package of { at : Core.origin; owner : Path.t; package : Path.package }
  | Method_outside_module of { at : Core.origin; owner : Path.t }
  | System_not_provided of { at : Core.origin; recipient : recipient }
  | No_real_implementation of { at : Core.origin; written : string; recipient : recipient }
  | Main_signature of { at : Core.origin }
  | Duplicate_member of { at : Core.origin; member_kind : string; name : string }
  | Not_derivable of { at : Core.origin; written : string }
  | Derives_inferred of {
      at : Core.origin;
      written : string;
      entry : Core.origin Description.range;
      siblings : Core.origin Description.siblings;
    }
  | Field_not_derivable of { at : Core.origin; written : string }
  | Default_of_sum of { at : Core.origin }
  | Derived_without_equal of { at : Core.origin; written : string }
  | Field_lacks_impl of { at : Core.origin; type_ : Types.ty; written : string }
  | Trait_cycle of { at : Core.origin }
  | Restated_requires of { at : Core.origin; name : string; declared_by : string }
  | Restated_decreases of { at : Core.origin; name : string; declared_by : string }
  | Restated_modifies of { at : Core.origin; name : string; declared_by : string }
  | Indexed_modified_part of { at : Core.origin }
  | Not_a_modified_part of { at : Core.origin }
  | Modified_non_parameter of { at : Core.origin; name : string }
  | Modified_whole_parameter of { at : Core.origin; parameter : string }
  | Read_only_part of { at : Core.origin; parameter : string; fields : string list }
  | Repeated_part of {
      at : Core.origin;
      parameter : string;
      fields : string list;
      container : string list;
      siblings : Core.origin Description.siblings;
    }
  | Fieldless_part of {
      at : Core.origin;
      parameter : string;
      prefix : string list;
      fields : string list;
      type_ : Types.ty;
      has_variants : bool;
    }
  | Opaque_part of { at : Core.origin; type_ : Types.ty }
  | Unknown_part_field of {
      at : Core.origin;
      type_ : Types.ty;
      field : string;
      candidates : string list;
    }
  | Impl_modifies of {
      at : Core.origin;
      name : string;
      parameter : string;
      fields : string list;
      trait : string;
    }
  | Restated_default of { at : Core.origin; name : string; declared_by : string }
  | Restated_body of { at : Core.origin; name : string; declared_by : string }
  | Redeclared_method of {
      at : Core.origin;
      declared_by : string;
      name : string;
      receiver : Path.receiver;
    }
  | Restated_signature of {
      at : Core.origin;
      name : string;
      declared_by : string;
      signature : string;
      uses : Types.capability list;
    }
  | Default_without_body of {
      at : Core.origin;
      type_ : Core.origin;
      default : Core.origin;
      name : string;
    }
  | Proof_bound_unmet of { at : Core.origin; generic : string; bound : Types.trait_reference }
  | Unknown_law of { at : Core.origin; trait : Types.trait_reference; law : string }
  | Law_without_impl of { at : Core.origin; for_type : Types.ty; trait : Types.trait_reference }
