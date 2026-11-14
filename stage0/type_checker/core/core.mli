(** The core form: the type checker's output for one definition.

    The core form is a typed, desugared tree. Ownership checking, the prover, and code generation
    read it instead of the syntax tree. It records every decision the type checker made, so a later
    stage never repeats one:

    - every call names its callee, and lists one argument per parameter, in parameter order;
    - every operator is either a built-in operation or a call of a trait method;
    - syntactic sugar is desugared ([?], [for] over a collection, list literals);
    - every expression says whether it denotes a place or a value;
    - every type is fully inferred and normalized.

    If a later stage has to look up which method a name refers to, or inspect the shape of a type to
    decide a node's meaning, the core form is missing something.

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

(** The callee of a call, as each form of code names it. ['indirect] is what a call through a
    function value gives: the core form's operand, the MIR's, or nothing where the caller has the
    value. *)
type 'indirect target =
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
      (** A direct call of a [standard::intrinsic] operation. An integer operation such as [add] or
          [divide] has the obligations of its operator: no overflow and no division by zero. *)
  | Indirect of 'indirect
      (** A call through a function value. If the function value is stored in a place, the operand
          is that place: calling it does not move it. *)

type callee = operand target

and call = {
  callee : callee;
  arguments : argument list;
      (** One argument per parameter, in parameter order. For a method, the receiver is first. *)
  lends : Types.mode option;
      (** [Some mode] if the callee is a lending method ([lends] in its signature). The result of
          such a call is a place: see {!Lent}. *)
  uses : Types.capability_set;
      (** The capabilities this call requires: the callee's [uses] clause, with the callee's
          capability parameters substituted by this call's type arguments. *)
}

and argument =
  | Passed of {
      mode : Types.mode;  (** The parameter's mode. *)
      value : operand;
      mark : mark option;  (** The [mut] or [own] the argument is written with, if any. *)
    }
  | Default
      (** The argument was omitted, so the parameter takes its default value. The default expression
          is in the callee's core form. *)

and mark = { written : origin; marked : origin }
(** A [mut] or [own] mark: [written], the syntax node of the mark with its operand, and [marked],
    the expression after the mark. *)

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
          a mutable view of part of a place. As the scrutinee of a [match], [is], or [let], the
          pattern's bindings own the parts of the value: every binding has the mode [Own]. *)

(** A memory location.

    Every place has a type. [Local], [Constant], and [Field] carry it, and a [Lent] or [Temporary]
    place has the type of its expression. [Core_walk.place_type] returns it.

    Every place has an origin: the id of the syntax node of the place as it is written. A place is
    not a node, so it has no id of its own. [Core_walk.place_origin] returns the origin. *)
and place =
  | Local of { local : local; type_ : Types.ty; origin : origin }
  | Constant of { path : Path.t; type_ : Types.ty; origin : origin }
      (** The static data of a constant. It is read-only. A constant used as a value is a {!Use} of
          this place. *)
  | Field of { base : place; field : string; type_ : Types.ty; origin : origin }
      (** A field of a record. [type_] is the field's type. The fields of a sum type's variant are
          never places of this kind: they are only reachable through pattern bindings. *)
  | Lent of expression
      (** The part of a value that a lending call returns, such as [items[index]] (a call of
          [Index.at]) or [grid.cell(position)]. The expression is a {!Call} whose [lends] is
          [Some _]. The borrow lasts until the end of the enclosing statement, except in the
          condition of an {!If} or a {!While}, where its [binds_lent_part] says how long. *)
  | Temporary of expression
      (** A value that has no place of its own, stored in a temporary for the enclosing statement so
          that part of it can be accessed, as in [origin().x]. *)

and expression = { id : id; origin : origin; type_ : Types.ty; kind : kind }

and kind =
  (* Literals and simple values *)
  | Integer of Z.t  (** A literal of a built-in integer type, of [Integer], or of [Character]. *)
  | Float of float  (** A float literal, already rounded to the precision of its type. *)
  | Boolean of bool
  | String of string
      (** A string literal without interpolation. One with interpolation is a {!Block} of calls: of
          [TextBuilder.new], of [TextBuilder.write] for each piece of text, of the [display] of each
          value, and of [TextBuilder.finish]. *)
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
      captures : capture list;
          (** The locals of the enclosing function that the body reads, in order of first use. The
              lambda borrows them. *)
      body : block;
      result : Types.ty;
    }
  | Construct of { variant : string option; fields : (string * operand option) list }
      (** Constructs a record, or a variant of a sum type; the node's type says which type. [fields]
          has every field once: first the fields that the code gives, in the order written, which is
          the order of evaluation, and then each field with [None], which takes its default value
          from the type's core form. A range expression such as [1..5] is desugared to this.

          A field that is a [Value] is moved into the constructed value. A field that is a [Place]
          is lent to it: the constructed value holds the place's value and does not own it. Only a
          construct that a {!Yield} lends has such a field, or a construct that is a field of one,
          to any depth. The place is lent with the [Yield]'s mode: when a [mut] lend ends, the place
          has the value of the field as the caller left it. A lent construct that lends a place at
          any depth owns nothing, because each of its other fields is a place, a nested construct,
          or a value of a [Plain] type. *)
  | Collection_literal of { elements : expression list; construction : construction }
      (** An array literal, or a specification-only sequence or set. The node's type says which.
          List and set literals are not this node: they are desugared to calls. *)
  | Map_literal of { entries : (expression * expression) list }
      (** A specification-only [FiniteMap]. A [Map] literal is not this node: it is desugared to
          calls. *)
  | Record_update of { base : expression; updates : (string list * expression) list }
      (** [base with (...)]: a copy of the record [base] with some fields replaced. Each update
          gives the path to a field (for a nested field, several names) and the new value. *)
  | Slice of { call : expression }
      (** [base[start..stop]]: a view of a range of a list, a slice, or an array. The view borrows
          [base]: it is some of the elements of that place.

          [call] creates the view. Its first argument is [base], passed as a place, and the only
          occurrence of [base], so a temporary base is evaluated once. With a stop, it is a call of
          the base type's [slice_range] with the start and the exclusive stop; without one, it is a
          call of [slice_from] with the start. A missing start is [0] and an inclusive stop is
          [stop + 1]. The bounds are passed as values. *)
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
  | Convert of { conversion : conversion; value : expression }
  | To_any of { value : expression; trait : Types.trait_reference; evidence : evidence }
      (** Converts a value to [any Trait]. [evidence] is the [impl] of the trait for the value's
          type. *)
  (* Control flow *)
  | If of {
      condition : expression;
      then_ : block;
      else_ : block option;
      binds_lent_part : bool;
          (** The condition calls a lending method and binds a name that may alias the lent part: a
              name bound [mut], or one whose type is a view or is not [Plain]. The condition's lends
              then last until [then_] ends, so that the name cannot dangle. Otherwise they end with
              the condition, every name it binds holds a copy, and [then_] can mutate the lender, as
              in [if counts.get(word) is Some(count) { counts[word] = count + 1 }]. The lends never
              last into [else_]. *)
    }
  | Match of { scrutinees : operand list; arms : arm list }
  | Block of block
  | Provide of { implementations : implementation list; body : block }
  | Return of expression option
  | Break
  | Continue
  | Todo
      (** [todo]: stops the program. A [todo] with no expected type has the type [Never]. The type
          checker does not resolve an operation on such a [todo], or on a local bound to one, so the
          core form replaces the operation: it evaluates the operands and ends in a [Todo]. A use of
          such a local is a [Todo], and a pattern that would bind it is a {!Wildcard}. *)
  | Unreachable
  | Echo of expression
  (* Specification-only expressions *)
  | Result  (** [result] in an [ensures] clause: the function's return value. *)
  | Old of expression  (** [old(e)]: the value of [e] when the function was called. *)
  | Current_target
      (** The value of the target of the enclosing {!Compound_assign} before the assignment, which
          the operator takes as owned. It appears exactly once, as the first argument of the {!Call}
          or {!Operator} that computes the new value. *)
  | Quantified of { quantifier : Syntax.quantifier; binder : binder; body : expression }
  | Yielded
      (** [yielded]: in a loop's clauses, the sequence of the values of the iterations before; in a
          lending method's [ensures], the sequence of its one part, as the caller left it. *)
  | Identical of expression * expression  (** [identical(first, second)] *)
  | Specification_function of { function_ : specification_function; arguments : expression list }
      (** A function that only a specification can call. [log(count)] and [power(base, exponent)]
          are on [Integer], in any specification. [time(visit)] and [calls(visit)] are inside a
          [cost] bound only. *)
  | Method_time of callee
      (** [time(Element.equal)] inside a [cost] bound: a bound on the time of any one call of a
          method of a trait that bounds a type parameter. The callee is a {!Trait_method} whose
          [self_type] is the type parameter and whose evidence is [Bound]. *)

and capture = { local : local; type_ : Types.ty }
and specification_function = Log | Power | Time | Calls
and comparison = Equal | Not_equal | Less | Less_equal | Greater | Greater_equal

(** How a collection literal is constructed. *)
and construction =
  | Array  (** An array, constructed in place. *)
  | Specification_only
      (** A [Sequence] or a [FiniteSet]. These exist only in specifications and are never
          constructed at run time. *)

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

(** The variable that a quantifier binds, and its range. *)
and binder =
  | Over_type of { local : local; name : string; type_ : Types.ty }  (** [value: Int64] *)
  | Over_range of { pattern : pattern; start : expression; stop : expression; inclusive : bool }
  | Over_collection of { pattern : pattern; collection : expression }
      (** The elements of a collection, in a specification. *)
  | Over_elements of { pattern : pattern; elements : elements }
      (** The elements of a collection, in executable code: the quantifier runs as the [for] loop
          over the collection does, and stops at the first counterexample or witness. *)

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
}

and statement = { id : id; origin : origin; kind : statement_kind }

and statement_kind =
  | Let of { pattern : pattern; value : operand; else_ : block option }
      (** [else_] is the block of a [let ... else]. It runs if the pattern does not match, and it
          always diverges. *)
  | Evaluate of expression
  | Assign of { target : place; value : expression }
      (** [value] is evaluated first, then the index keys of [target], and then the new value
          replaces the old one. *)
  | Compound_assign of { target : place; operand : operand; bound : local; value : expression }
      (** A compound assignment such as [total += step]. [operand] is the right operand. It is
          evaluated first, and [bound] is bound to it: to its value, or to the place, which stays
          borrowed until the assignment ends. Then the index keys of [target] are evaluated, once.
          Then [value] computes the new value from {!Current_target} and [bound], and the new value
          replaces the old one.

          The operator takes the old value as owned, so the target holds no value while [value]
          runs. Evaluating the operand first means that no code but the operator runs in that
          window: an early exit in the operand, such as a [?], leaves the target initialized, and
          the operand cannot read or mutate a target that was moved out. *)
  | For of {
      pattern : pattern;
      iteration : iteration;
      clauses : loop_clause list;
      body : block;
      mode : loop_mode;
    }
  | While of {
      condition : expression;
      clauses : loop_clause list;
      body : block;
      binds_lent_part : bool;
          (** As for {!If}: whether the condition's lends last until [body] ends, or end with the
              condition. *)
    }
  | Parallel of statement list
      (** A [parallel] block. Each statement is a branch. A branch uses no capability but [Panic],
          and no early exit leaves one. *)
  | Concurrent of statement list
      (** A [concurrent] block. Each statement is a branch, which runs as a task with the
          capabilities that are available around the block. The block ends when every branch has
          ended. A branch is named by the block's id and its index, from 0 (see {!task}). *)
  | Proof of block
  | Assert of { condition : condition; by_bit_vector : bool }
      (** [by_bit_vector]: proven alone, for every value of the variables it names. *)
  | Yield of { mode : Types.mode; part : operand }
      (** Lends [part], which is the value of a lending method's body or of its [return], with the
          mode in the method's signature. The method ends after it. *)

and loop_mode = Sequential | Parallel_loop | Concurrent_loop

(** A task of [concurrent] code, which an early exit may end before the others of its block or loop.
    The MIR builder finds the tasks each exit ends. The block or the loop is named by its
    statement's origin, which no other statement of the definition has. *)
and task =
  | Branch of { block : origin; index : int }
      (** The branch [index], from 0, of the {!Concurrent} statement with the origin [block]. *)
  | Iteration of { loop : origin }
      (** An iteration of the [concurrent for] loop with the origin [loop]. *)

(** The iteration of a [for] loop. *)
and iteration =
  | Integer_range of { start : expression; stop : expression; inclusive : bool }
      (** A range of built-in integers or characters. *)
  | Elements of elements  (** The elements of a collection, by position. *)
  | Cursor of { cursor : place; next : callee }
      (** A cursor, advanced until it is exhausted. [next] is its type's [Cursor.next]. *)

and elements = {
  count : expression;
      (** The {!Call} of the collection's [count], which is evaluated once, before the first
          iteration. *)
  position : pattern;
      (** A {!Bind} of the position of the iteration: each [USize] from zero up to the count. *)
  element : place;
      (** The {!Lent} place of the {!Call} of the collection's [element] at [position]. It is lent
          for the iteration, and the loop's pattern binds it. *)
}
(** How a loop visits the elements of a collection. The collection is a place that both calls name,
    so it is evaluated once, by the code around the loop. *)

and loop_clause =
  | Invariant of expression
  | Decreases of expression list
  | Cost of cost
      (** A bound on the cost that the loop has incurred so far, checked at every iteration. *)

and cost = {
  origin : origin;  (** The [cost] clause. *)
  amortized : bool;
  resource : resource;
  bound : bound;
}

(** The quantity that a [cost] clause bounds. *)
and resource = Time | Allocations | Allocated_bytes | Calls of calls_target

(** The callee whose calls a [calls(...)] clause counts. *)
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
  | Bind of { local : local; name : string; is_var : bool; mode : Types.mode }
      (** Binds the matched value to a local. [mode] is [Own] if the binding owns the value, and
          [Read] or [Mut] if it borrows part of the scrutinee. *)
  | Variant of { variant : string; fields : (string * pattern) list }
      (** The fields that the pattern matches, by name. Fields not listed are ignored. *)
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
  | Law_proof of { parameters : parameter list; body : block }
      (** The proof of a law for a type. [parameters] are the law's, in the law's order, with [Self]
          and the trait's parameters replaced by the proof's type and trait arguments. The local of
          each is [Synthetic] with the parameter's position, and the body can name them. The locals
          that desugaring makes are numbered after them. *)
  | Empty  (** An [impl] or a capability. Its methods are separate definitions. *)

type t = { definition : definition }
(** The core form of one definition.

    Three kinds of node carry a proof obligation that the type checker created: a {!From_integer}
    conversion (the value must fit), a {!Widen} conversion (the costs must imply), and the
    [_ => unreachable] arm that ends a {!Match} whose guards must cover every case. *)
