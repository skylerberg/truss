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
type member_kind = Field_member | Variant_member

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
  | Arity of {
      at : Core.origin;
      written : Core.origin Description.range;
      expected : int;
      given : int;
    }
  | Head_arity of {
      at : Core.origin;
      written : Core.origin Description.range;
      expected : int;
      given : int;
    }
  | Argument_kind of {
      at : Core.origin;
      written : Core.origin Description.range;
      parameter : string;
      mismatch : kind_mismatch;
    }
  | Arguments_to_parameter of { at : Core.origin; written : Core.origin Description.range }
  | Count_error of { at : Core.origin; error : count_error }
  | Trait_as_type of { at : Core.origin; written : Core.origin Description.range }
  | Capability_as_type of { at : Core.origin; written : Core.origin Description.range }
  | Head_not_a_type of {
      at : Core.origin;
      written : Core.origin Description.range;
      kind : Language.Definition_kind.t;
    }
  | Not_a_trait of {
      at : Core.origin;
      written : Core.origin Description.range;
      is_parameter : bool;
    }
  | Decided_condition of { at : Core.origin; subject : Types.ty }
  | Decided_projection_condition of {
      at : Core.origin;
      subject : Types.ty;
      base : Types.ty;
      trait : Types.trait_reference;
      name : string;
    }
  | Not_a_capability of {
      at : Core.origin;
      written : Core.origin Description.range;
      is_type_parameter : bool;
    }
  | Calls_not_a_capability of { at : Core.origin; written : Core.origin Description.range }
  | Calls_through_parameter of { at : Core.origin; name : string }
  | Unknown_capability_method of {
      at : Core.origin;
      written : Core.origin Description.range;
      method_ : string;
    }
  | Time_of_run_forever of { at : Core.origin }
  | Time_of_unbounded_parameter of { at : Core.origin; name : string }
  | Misplaced_value_condition of { at : Core.origin; condition : value_condition }
  | Wrong_value_parameter_type of { at : Core.origin; parameter : string; type_ : Types.ty }
  | Specification_only_field of { at : Core.origin; type_ : Types.ty }
  | Missing_associated_type of { at : Core.origin; name : string; trait : Path.t }
  | Missing_method of {
      at : Core.origin;
      name : string;
      signature : Types.signature;
      trait : Path.t;
    }
  | Implements_built_in_capability of {
      at : Core.origin;
      capability : Language.Builtin_capability.t;
    }
  | Implements_built_in of { at : Core.origin; trait : Path.t }
  | Associated_bound_unmet of {
      at : Core.origin;
      trait : Path.t;
      name : string;
      bound : Types.trait_reference;
      chosen : Types.ty;
    }
  | Extra_associated of { at : Core.origin; trait : Path.t; name : string; associated : associated }
  | Capability_set_defined_twice of { at : Core.origin; name : string }
  | Missing_required_impl of {
      at : Core.origin;
      trait : Path.t;
      required : Types.trait_reference;
      for_type : Types.ty;
    }
  | Uses_on_trait_impl of { at : Core.origin }
  | Callback_contract_mismatch of {
      at : Core.origin;
      name : string;
      trait : Path.t;
      parameter : string;
      declaration : Path.key;
      clauses : Core.origin list;
    }
  | Restated_without_own of {
      at : Core.origin;
      trait : Path.t;
      declared_by : Path.t;
      name : string;
      for_type : Types.ty;
    }
  | Undeclared_method of { at : Core.origin; trait : Path.t; name : string }
  | Capability_method_receiver of { at : Core.origin }
  | Overridden_default of { at : Core.origin; trait : Path.t; name : string }
  | Impl_signature_mismatch of {
      at : Core.origin;
      name : string;
      signature : Types.signature;
      trait : Path.t;
    }
  | Uses_beyond_impl of { at : Core.origin; name : string }
  | Uses_beyond_trait of { at : Core.origin; name : string; trait : Path.t }
  | Panic_beyond_condition of { at : Core.origin; name : string; trait : Path.t }
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
  | No_real_implementation of {
      at : Core.origin;
      written : Core.origin Description.range;
      recipient : recipient;
    }
  | Main_signature of { at : Core.origin }
  | Duplicate_member of { at : Core.origin; member_kind : member_kind; name : string }
  | Not_derivable of { at : Core.origin; written : Core.origin Description.range }
  | Derives_inferred of {
      at : Core.origin;
      written : Core.origin Description.range;
      entry : Core.origin Description.range;
      siblings : Core.origin Description.siblings;
    }
  | Field_not_derivable of { at : Core.origin; written : Core.origin Description.range }
  | Potential_not_plain of { at : Core.origin }
  | Default_of_sum of { at : Core.origin }
  | Derived_without_equal of { at : Core.origin; written : Core.origin Description.range }
  | Field_lacks_impl of {
      at : Core.origin;
      type_ : Types.ty;
      written : Core.origin Description.range;
    }
  | Trait_cycle of { at : Core.origin }
  | Restated_requires of { at : Core.origin; name : string; declared_by : Path.t }
  | Restated_decreases of { at : Core.origin; name : string; declared_by : Path.t }
  | Restated_modifies of { at : Core.origin; name : string; declared_by : Path.t }
  | Not_viewable_type of { at : Core.origin; type_ : Types.ty }
  | Indexed_modified_part of { at : Core.origin }
  | Not_a_modified_part of { at : Core.origin }
  | Modified_non_parameter of { at : Core.origin; name : string }
  | Modified_whole_parameter of { at : Core.origin; parameter : string }
  | Read_only_part of { at : Core.origin; parameter : string; part : Types.modified }
  | Repeated_part of {
      at : Core.origin;
      parameter : string;
      part : Types.modified;
      container : Types.modified;
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
  | Part_without_elements of {
      at : Core.origin;
      parameter : string;
      fields : string list;
      type_ : Types.ty;
    }
  | Impl_modifies of {
      at : Core.origin;
      name : string;
      parameter : string;
      part : Types.modified;
      trait : Path.t;
    }
  | Restated_default of { at : Core.origin; name : string; declared_by : Path.t }
  | Restated_body of { at : Core.origin; name : string; declared_by : Path.t }
  | Redeclared_method of {
      at : Core.origin;
      declared_by : Path.t;
      name : string;
      receiver : Path.receiver;
    }
  | Restated_signature of {
      at : Core.origin;
      name : string;
      declared_by : Path.t;
      signature : Types.signature;
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
