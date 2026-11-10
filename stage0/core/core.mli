(** The core form: the type checker's output for one definition.

    The core form is a typed, desugared tree. Ownership checking, the prover, and code generation
    read it instead of the syntax tree. It records every decision the type checker made, so a later
    stage never repeats one:

    - every call names its callee, and lists one argument per parameter, in parameter order;
    - every operator is either a built-in operation or a call of a trait method;
    - syntactic sugar is desugared ([?], compound assignment, [for] over a collection, list
      literals);
    - every expression says whether it denotes a place or a value;
    - every type is fully inferred and normalized.

    If a later stage has to look up which method a name refers to, or inspect the shape of a type to
    decide what a node means, the core form is missing something.

    Every node has an [id], unique within the definition. Later results (such as ownership's) are
    keyed by it. Every node also has an [origin]: the id of the syntax node it was built from.
    Several core nodes can share one origin. Core nodes hold no source spans, so reformatting a
    definition does not change its core form. To show source text for a node, look up its origin in
    [Resolve.Names.spans]. *)

type id = int

type origin = Syntax.id
(** The id of the syntax node a core node was built from. *)

(** A local variable. *)
type local =
  | Named of Syntax.id
      (** A parameter or a pattern binding, identified by the id of the name that declares it. *)
  | Self
  | Synthetic of int
      (** A local introduced by desugaring, numbered from 0 within the definition. For example, [?]
          binds the success value to a synthetic local. *)

(** How a trait method call finds the [impl] it dispatches to. *)
type evidence =
  | Impl of { impl : Path.t; arguments : Types.substitution }
      (** A known [impl], written or derived, with the type arguments for its generic parameters. *)
  | Bound
      (** A trait bound on a generic parameter (or on one of its associated types). The [impl] is
          known only after monomorphization. *)
  | Dynamic  (** Dynamic dispatch through the method table of an [any Trait] value. *)

type callee =
  | Function of { path : Path.t; type_arguments : Types.argument list }
      (** A function, or a method defined directly on a type. For a method, the type arguments of
          the type come first. *)
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      type_arguments : Types.argument list;
          (** Type arguments for the method's own generic parameters. *)
      evidence : evidence;
    }
      (** A method declared by a trait. With [Impl] evidence, the method that runs has the path
          [Method { owner = impl; name; receiver }]. [Infer.core_of_path] gives its body and
          [Interface.Impls.signature] gives its signature, whether the [impl] defines the method or
          inherits the trait's default. *)
  | Capability_method of { capability : Path.t; name : string }
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
      (** A direct call of a [standard::intrinsic] operation. Unlike {!Operator}, the prover does
          not generate overflow or division checks for it. *)
  | Indirect of operand
      (** A call through a function value. If the function value is stored in a place, the operand
          is that place: calling it does not move it. *)

and call = {
  callee : callee;
  arguments : argument list;
      (** One argument per parameter, in parameter order. For a method, the receiver is first. *)
  lends : Types.mode option;
      (** [Some mode] if the callee is a lending method ([lends] in its signature). The result of
          such a call is a place: see {!Lent}. *)
  uses : Types.capability list;
      (** The capabilities this call requires: the callee's [uses] clause, with the callee's
          capability parameters substituted by this call's type arguments. *)
}

and argument =
  | Passed of { mode : Types.mode;  (** The parameter's mode. *) value : operand }
  | Default
      (** The argument was omitted, so the parameter takes its default value. The default expression
          is in the callee's core form. *)

(** An operand is either a place, which is borrowed, or a value. *)
and operand =
  | Place of place
      (** The place itself. It is borrowed, not moved or copied. As an argument, it is borrowed for
          the duration of the call (mutably for a [mut] parameter). As the scrutinee of a [match],
          [is], or [let], the pattern's bindings refer to parts of the place. An [own] parameter
          never receives a [Place]: it receives [Value (Use place)]. *)
  | Value of expression
      (** A value. An [own] parameter takes ownership of it. A read-only parameter borrows it for
          the call. A [mut] parameter receives a [Value] only when the value is a {!Slice}, which is
          a mutable view of part of a place. *)

(** A memory location. Every place has a type: [Local], [Constant], and [Field] carry it, and a
    [Lent] or [Temporary] place has the type of its expression. [Core_walk.place_type] returns it.
*)
and place =
  | Local of { local : local; type_ : Types.ty }
  | Constant of { path : Path.t; type_ : Types.ty }
      (** The static data of a constant. It is read-only. A constant used as a value is a {!Use}
          of this place. *)
  | Field of { base : place; field : string; type_ : Types.ty }
      (** A field of a record. [type_] is the field's type. The fields of a sum type's variant are
          never places of this kind: they are only reachable through pattern bindings. *)
  | Lent of expression
      (** The part of a value that a lending call returns, such as [items[index]] (a call of
          [Index.at]) or [grid.cell(position)]. The expression is a {!Call} whose [lends] is
          [Some _]. The borrow lasts until the end of the enclosing statement. *)
  | Temporary of expression
      (** A value that has no place of its own, stored in a temporary for the enclosing statement so
          that part of it can be accessed, as in [origin().x]. *)

and expression = { id : id; origin : origin; type_ : Types.ty; kind : kind }

and kind =
  (* Literals and simple values *)
  | Integer of Z.t  (** A literal of a built-in integer type, of [Integer], or of [Character]. *)
  | Float of float  (** A float literal, already rounded to the precision of its type. *)
  | Boolean of bool
  | String of string  (** A string literal without interpolation. *)
  | Interpolated of {
      pieces : piece list;
      builder_new : callee;  (** [TextBuilder.new] *)
      builder_write : callee;  (** [TextBuilder.write], used for each {!Text} piece. *)
      builder_finish : callee;  (** [TextBuilder.finish] *)
    }
      (** A string literal with interpolation. The result is the concatenation of the pieces. This
          node will be desugared into the builder calls once the standard library gives them [time]
          clauses. *)
  | Template of { literals : string list; call : expression }
      (** A tagged string, such as [Sql"select ${column}"]. [call] is the call of the tag's
          [from_template] that produces the value; its argument is the constructed [Template]
          record. [literals] are the literal text segments between the interpolated values (one more
          segment than there are values). The prover evaluates the tag's [requires] clauses on them.
      *)
  | Use of place
      (** Reads the value out of a place, consuming it: the value is copied if its type copies
          implicitly ([Plain]), and moved otherwise. Code that only borrows a place receives the
          place as an {!operand} instead, never a [Use]. *)
  | Copy of operand
      (** An explicit [value.copy()] where the compiler implements [Copyable] for the type. *)
  | Function_value of { path : Path.t; type_arguments : Types.argument list }
      (** A reference to a named function or method, used as a value. A variant constructor used as
          a function is desugared to a {!Lambda}. *)
  | Value_parameter of Types.parameter  (** A use of a [USize] generic parameter as a value. *)
  | Lambda of {
      parameters : pattern list;
      captures : local list;
          (** The locals of the enclosing function that the body reads, in order of first use. *)
      body : block;
      result : Types.ty;
    }
  | Construct of { variant : string option; fields : (string * expression option) list }
      (** Constructs a record, or a variant of a sum type; the node's type says which type. [fields]
          lists every field in declaration order. A field with [None] takes its default value, which
          is in the type's core form. A range expression such as [1..5] is desugared to this. *)
  | Collection_literal of { elements : expression list; construction : construction }
      (** An array literal, a set literal, or a specification-only sequence or set. The node's type
          says which. List literals are not this node: they are desugared to calls. *)
  | Map_literal of { entries : (expression * expression) list; construction : construction }
  | Record_update of { base : expression; updates : (string list * expression) list }
      (** [base with (...)]: a copy of the record [base] with some fields replaced. Each update
          gives the path to a field (for a nested field, several names) and the new value. *)
  | Slice of { base : place; start : expression option; stop : expression option; inclusive : bool }
      (** [items[start..stop]]: a view of a range of a list, slice, or array. *)
  (* Calls and operators *)
  | Call of call
  | Operator of { operation : Intrinsic.operation; arguments : expression list }
      (** An arithmetic, bitwise, or shift operation on built-in types. [left + right] and
          [left.add(right)] both produce this node. The prover checks that the operation is defined:
          no overflow, no division by zero, no out-of-range shift. *)
  | Compare of { comparison : comparison; left : expression; right : expression }
      (** A comparison of two values of the same built-in type. In a specification, also a
          comparison of two integers by mathematical value. A comparison of any other type is a
          {!Call} of [Equal.equal], or a {!Matches} on the result of [Ordered.compare]. *)
  | Not of expression
  | And of expression * expression
      (** [&&]. The right operand is evaluated only if the left is true. *)
  | Or of expression * expression
      (** [||]. The right operand is evaluated only if the left is false. *)
  | Implies of expression * expression  (** [==>]. Specifications only. *)
  | Matches of { value : operand; pattern : pattern }
      (** [value is pattern]. Also used for ordering comparisons of non-built-in types:
          [first < second] is [compare(first, second) is Less]. *)
  | Cursor_next of place
      (** Advances the cursor produced by a call of a yielding method. The result is an [Option] of
          the next yielded value. *)
  | Convert of { conversion : conversion; value : expression }
  | To_any of { value : expression; trait : Types.trait_reference; evidence : evidence }
      (** Converts a value to [any Trait]. [evidence] is the [impl] of the trait for the value's
          type. *)
  (* Control flow *)
  | If of { condition : expression; then_ : block; else_ : block option }
  | Match of {
      scrutinees : operand list;
      arms : arm list;
      guards_exhaustive : bool;
          (** True if the last arm is [_ => unreachable] and an earlier arm has a guard. The prover
              must then show that the guards cover every case. *)
    }
  | Block of block
  | Provide of { implementations : implementation list; body : block }
  | Return of expression option
  | Break
  | Continue
  | Todo
  | Unreachable
  | Echo of expression
  (* Specification-only expressions *)
  | Result  (** [result] in an [ensures] clause: the function's return value. *)
  | Old of expression  (** [old(e)]: the value of [e] when the function was called. *)
  | Current_target
      (** The value of the target of the enclosing {!Compound_assign} before the assignment. It
          appears exactly once, as a direct argument of the {!Call} or {!Operator} that computes the
          new value. *)
  | Quantified of { quantifier : Syntax.quantifier; binder : binder; body : expression }
  | Yielded  (** [yielded]: the sequence of values a yielding method has yielded so far. *)
  | Finished  (** [finished]: whether a yielding method has returned. *)
  | Identical of expression * expression  (** [identical(first, second)] *)
  | Cost_function of { function_ : cost_function; arguments : expression list }
      (** A cost function inside a [cost] bound: [log(count)], [power(base, exponent)],
          [time(visit)], or [calls(visit)]. *)

and cost_function = Log | Power | Time | Calls
and comparison = Equal | Not_equal | Less | Less_equal | Greater | Greater_equal

(** One piece of an interpolated string. *)
and piece =
  | Text of string
  | Displayed of { value : operand; display : callee }
      (** An interpolated value, converted to text by [display] (its [Display.display]). The value
          is only borrowed. *)

(** How a collection literal is constructed at run time. *)
and construction =
  | Array  (** An array, constructed in place. *)
  | By_insertion of { empty : callee; insert : callee }
      (** A set or a map: call [empty], then call [insert] for each element. This will be desugared
          into the calls once the standard library has [Set.empty] and [Map.empty]. *)
  | Specification_only
      (** A [Sequence], [FiniteSet], or [FiniteMap]. These exist only in specifications and are
          never constructed at run time. *)

(** An implicit conversion. *)
and conversion =
  | Widen
      (** A function value converted to a function type with more [uses] or weaker [cost] clauses.
          The prover checks that the value's costs imply the expected costs. The value's type is the
          source type and the node's type is the target type. *)
  | To_integer  (** A built-in integer converted to [Integer]. Specifications only. *)
  | From_integer
      (** An [Integer] converted to a built-in integer type. Specifications only. The prover checks
          that the value fits. *)

(** The variable a quantifier binds, and what it ranges over. *)
and binder =
  | Over_type of { local : local; name : string; type_ : Types.ty }  (** [value: Int64] *)
  | Over_range of { pattern : pattern; start : expression; stop : expression; inclusive : bool }
  | Over_collection of { pattern : pattern; collection : expression }

and implementation = {
  origin : origin;
  mode : Types.mode;
  value : operand;
      (** A place (borrowed for the block, mutably if [mode] is [Mut]) or a value (owned by the
          block). *)
  type_ : Types.ty;
  provides : provided list;
      (** Each capability that the implementation's type implements, with the [impl]. *)
}
(** One implementation given to a [provide] block. *)

and provided = { capability : Path.t; impl : Path.t; arguments : Types.substitution }

and block = {
  statements : statement list;
  value : expression option;  (** The block's final expression, which is the block's value. *)
  diverges : bool;
      (** True if control never reaches the end of the block: it always returns, breaks, continues,
          or loops forever. *)
}

and statement = { id : id; origin : origin; kind : statement_kind }

and statement_kind =
  | Let of { pattern : pattern; value : operand; else_ : block option }
      (** [else_] is the block of a [let ... else]. It runs if the pattern does not match, and it
          always diverges. *)
  | Evaluate of expression
  | Assign of { target : place; value : expression }
  | Compound_assign of { target : place; value : expression }
      (** A compound assignment such as [total += step]. [value] computes the new value; inside it,
          {!Current_target} is the target's value before the assignment. The target place is
          evaluated once. *)
  | For of {
      pattern : pattern;
      iteration : iteration;
      clauses : loop_clause list;
      body : block;
      parallel : bool;
    }
  | While of { condition : expression; clauses : loop_clause list; body : block }
  | Parallel of statement list
  | Proof of block
  | Assert of condition
  | Yield of { mode : Types.mode; part : operand }
      (** [yield] in a lending or yielding method. [mode] is the mode in the method's signature. *)

(** What a [for] loop iterates over. *)
and iteration =
  | Integer_range of { start : expression; stop : expression; inclusive : bool }
      (** A range of built-in integers or characters. *)
  | Yielding_call of expression
      (** A {!Call} of a yielding method. [for item in items] is desugared to a call of
          [items.each()] with the loop's mode. *)
  | Cursor of { cursor : place; next : callee option }
      (** An existing cursor, advanced until it is exhausted. [next] is the cursor type's
          [Cursor.next]. It is [None] for the built-in cursor of a yielding method, which is
          advanced as {!Cursor_next} does. *)

and loop_clause =
  | Invariant of expression
  | Decreases of expression list
  | Cost of cost  (** A bound on what the loop has spent so far, checked at every iteration. *)

and cost = {
  origin : origin;  (** The [cost] clause. *)
  amortized : bool;
  resource : resource;
  bound : bound;
}

(** What a [cost] clause counts. *)
and resource = Time | Allocations | Allocated_bytes | Calls of calls_target

(** What a [calls(...)] clause counts calls of. *)
and calls_target =
  | Function_parameter of local  (** Calls through a function-typed parameter. *)
  | Capability of Path.t  (** Calls of any method of a capability. *)
  | Capability_method of Path.t * string  (** Calls of one method of a capability. *)

and bound = Finite | Order_of of expression | At_most of expression | Exactly of expression

and condition = { value : expression; executable : bool }
(** A [requires] clause or an [assert]. [executable] is true if the condition can be evaluated at
    run time. It is false if the condition contains a quantifier, a value of type [Integer], [old],
    [result], or a call of a specification-only function. *)

and arm = { patterns : pattern list; guard : expression option; body : block; origin : origin }
and pattern = { id : id; origin : origin; type_ : Types.ty; kind : pattern_kind }

and pattern_kind =
  | Wildcard
  | Bind of { local : local; name : string; mutable_ : bool; mode : Types.mode }
      (** Binds the matched value to a local. [mode] is [Own] if the binding owns the value, and
          [Read] or [Mut] if it borrows part of the scrutinee. *)
  | Variant of { variant : string; fields : (string * pattern) list }
      (** The fields that the pattern matches, by name, in declaration order. Fields not listed are
          ignored. *)
  | Record of (string * pattern) list
  | Literal of expression
      (** An {!Integer} or {!Boolean} literal, or a constant of a built-in type. The scrutinee is
          compared with it by built-in equality. *)
  | Range of { start : expression; stop : expression; inclusive : bool }
      (** A range of literals or constants. *)
  | Equal_to of { value : expression; equal : callee }
      (** A constant or a string literal, compared by calling [equal] (the type's [Equal.equal]). *)
  | Alternatives of pattern list

(** {1 Definitions} *)

type parameter = {
  local : local;
  name : string;
  mode : Types.mode;
  type_ : Types.ty;
  default : expression option;
  callback_contract : callback_contract option;
}

and callback_contract = { inputs : (local * string) list; requires : expression list }
(** The [requires] clauses of a function-typed parameter that names its inputs, as in
    [transform: (fn(element: Element) -> Output requires ...)]. Every call through the parameter
    must satisfy them. [inputs] are the named inputs, which the clauses can mention. *)

type contract = {
  requires : condition list;
  ensures : expression list;
  decreases : expression list;
  costs : cost list;
}

type law = { name : string; parameters : parameter list; requires : expression list; body : block }

(** The checked content of a definition. *)
type definition =
  | Function of { parameters : parameter list; contract : contract; body : block option }
      (** A function, method, or theorem. [body] is [None] for a trait or capability method that is
          declared without a body. *)
  | Type of {
      defaults : (string option * string * expression) list;
          (** Field defaults: the variant name (for a sum type), the field name, and the default
              expression. *)
      invariants : expression list;
      potential : expression option;
    }
  | Trait of law list
  | Constant of expression
  | Test of block
  | Law_proof of block
  | Empty  (** An [impl] or a capability. Its methods are separate definitions. *)

type t = {
  definition : definition;
  node_count : int;  (** Every node id is less than this. *)
  synthetic_local_count : int;  (** Every [Synthetic] local's number is less than this. *)
}
(** The core form of one definition.

    Three kinds of node carry a proof obligation that the type checker created: a {!From_integer}
    conversion (the value must fit), a {!Widen} conversion (the costs must imply), and a {!Match}
    with [guards_exhaustive] (the guards must cover every case). *)
