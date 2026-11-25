type holder = Own | Of_list of Types.ty

type clash =
  | Same_receiver of { receiver : Path.receiver; trait : Types.trait_reference }
  | Other_package
  | Unwritten of { trait : Types.trait_reference }

type t =
  | Impl_location of { header : Core.origin; trait : Types.trait_reference; for_type : Types.ty }
  | Sealed_trait_impl of {
      header : Core.origin;
      trait : Path.t;
      type_ : Path.t;
      is_floating_point : bool;
    }
  | Method_name_clash of {
      header : Core.origin;
      for_type : Types.ty;
      method_name : string;
      holder : holder;
      clash : clash;
    }
  | Overlapping_impls of {
      header : Core.origin;
      trait : Types.trait_reference;
      for_type : Types.ty;
    }
  | Variant_in_place of { variant : Core.origin }
  | Record_in_place of { header : Core.origin }
  | Associated_type_in_place of { member : Core.origin; name : string; recursive : Types.ty }
  | Function_input_field of { field : Core.origin; type_name : string }
  | Associated_function_input of { member : Core.origin; name : string; recursive : Types.ty }
  | Growing_type of { header : Core.origin }
  | Instantiation_cycle of { header : Core.origin }
  | Duplicate_test of { name : string }
