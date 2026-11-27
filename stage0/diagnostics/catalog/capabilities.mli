type subject =
  | Call of Core.origin
  | Unmeasured_loop
  | Conditionally_measured_loop of Types.condition
  | Failing_operation
  | Concurrent_block
  | Concurrent_for_loop
  | Implementation

type alternative =
  | Add_decreases
  | Add_decreases_or_bound of Types.ty
  | Add_decreases_or_implement of Types.ty

type restriction =
  | Parallel_branch
  | Parallel_for
  | Proof
  | Specification
  | Law
  | Quantifier_body
  | Constant_expression

type declaring_clause =
  | Own_uses
  | Impl_uses
  | Associated_capability_set of { name : string; is_defined : bool; is_named : bool }

type declaration =
  | Declared_by of declaring_clause
  | Fixed_by_trait of { trait : Types.trait_reference; method_name : string }

type granted =
  | Function of Path.t
  | Trait_method of { trait : Path.t; name : string }
  | Implemented_method of { implements : Types.trait_reference; for_type : Types.ty }
  | Provided_implementation of { capability : Path.t; for_type : Types.ty }

type t =
  | Not_granted of {
      at : Core.origin;
      granted : granted;
      package : Path.package;
      capability : Path.t;
    }
  | Lambda_uses of {
      lambda : Core.origin;
      capability : Types.capability;
      use : (Core.origin * subject) option;
    }
  | Must_terminate of {
      at : Core.origin;
      subject : subject;
      restriction : restriction;
      alternative : alternative option;
    }
  | Not_in_restriction of {
      at : Core.origin;
      subject : subject;
      capability : Types.capability;
      restriction : restriction;
      allowed : Types.capability list;
    }
  | Not_available of {
      at : Core.origin;
      subject : subject;
      capability : Types.capability;
      declaration : declaration option;
      can_provide : bool;
      alternative : alternative option;
    }
  | Not_an_implementation of { implementation : Core.origin; type_ : Types.ty }
  | Provide_missing_mut of { implementation : Core.origin }
  | Provide_needless_mut of { implementation : Core.origin; place : Core.origin }
  | Monitor_needs_tasks of { implementation : Core.origin; type_ : Types.ty }
  | Callback_may_deadlock of {
      implementation : Core.origin;
      capability : Path.t;
      method_name : string;
      parameter : string;
    }
