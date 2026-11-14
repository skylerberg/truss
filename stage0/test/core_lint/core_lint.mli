(** A lint of the core form, as GHC's Core Lint is of its Core: the invariants that every core form
    has, which ownership checking, the prover, and code generation rely on. The tests run it on
    every core form they produce.

    Well-formedness:
    - node ids are unique;
    - no type contains an inference variable, a hole, or an error;
    - every generic parameter that appears is declared by the definition or by its enclosing type,
      trait, or impl, and never by a callee;
    - every associated capability set that appears is of a generic parameter or of an associated
      type of one.

    Types:
    - each argument has its parameter's type, and a call has its callee's result type, with the
      call's type arguments substituted;
    - every use of a local has the type of the parameter or the pattern that binds it;
    - an [Operator] and its operands have one built-in type, and a [Compare] compares two values of
      one built-in type: an operator on any other type is a call of a trait method, and an operator
      on a built-in type is never one;
    - a [Construct] lists each field of its record or variant once, each given field with the
      field's type, and then each omitted field, which has a default.

    Calls and modes:
    - a call has one argument per parameter of its callee, in parameter order, each with the
      parameter's mode, and omits only an argument whose parameter has a default;
    - a [mut] parameter receives a place or a slice, an [own] parameter receives a value, and a
      read-only parameter never receives a [Use], which would move or copy the place it borrows,
      except a bound of a [Slice];
    - a place that is assigned, passed [mut], or advanced as a cursor is mutable: it is not a
      constant, and every [Lent] place in it is lent [mut];
    - the expression of a [Lent] place is a call of a lending method;
    - a conversion to [any] records the [impl] or the bound that implements the trait for the
      value's type, and a trait method call is dynamic exactly when its [Self] is an [any] type;
    - a [Yielding_call] is a call of a yielding method, and the [next] of a yielding method's cursor
      is a [Cursor_next], not a call.

    Patterns and bindings:
    - a [let], [match], or [is] on a value binds every name [own];
    - a [let] that binds a mutable local receives a value;
    - a [match] arm has one pattern per scrutinee;
    - the alternatives of a pattern bind the same locals, with the same types and modes.

    Desugaring:
    - the call of a [Slice] takes the slice's base as its first argument, and is a call of
      [slice_range] with a stop or of [slice_from] without one;
    - [Current_target] appears once in each compound assignment, as the first argument of the
      operation that computes the new value, and nowhere else;
    - a lambda captures exactly the locals of the enclosing function that its body reads, in order
      of first use;
    - a construct that no [yield] yields has no field that is a place, and a yielded construct that
      lends a place takes only values of [Plain] types.

    Specifications:
    - a [requires] clause or an [assert] is executable exactly when it has no quantifier, no value
      of type [Integer], no [old] or [result], and no call of a specification-only function;
    - a quantifier in executable code, which includes the assertions of a test, runs as a loop
      ([Over_each]) of a read-only call with one argument, and a quantifier in a specification
      ranges over a mathematical collection ([Over_collection]). *)

val check : Query.context -> Resolve.Names.key -> Core.t -> unit
(** Fails the running test if the definition's core form breaks an invariant. *)

val check_file : Query.context -> Path.file -> int
(** Runs {!check} on every definition of a file that has a core form. Returns the number of such
    definitions. *)

val callee_name : Core.callee -> string
(** The path of a function or a method, [Trait.method] for a trait method, [Capability.method] for a
    capability method, and [intrinsic::operation] for an intrinsic. *)
