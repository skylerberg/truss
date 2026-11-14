(** The MIR: each body of a definition as a control-flow graph of places, values, and explicit
    temporaries, in evaluation order. The builder decides the order of evaluation, the scope of each
    temporary and binding, and the flow of patterns, loops, and early exits once, so every stage
    that reads the MIR agrees on them.

    An expression of a specification is no control-flow graph. A clause, an invariant, a measure,
    and a bound are each a {!formula}: one block whose [if]s, [match]es, short-circuit operators,
    and quantifiers are each one {!Specification} value, so that the prover maps a formula to a term
    by structural recursion and never joins paths to recover a value. Code that never runs, a
    theorem's body, a law's proof, and a [proof] block, is a body, built as a specification: its
    statements can jump, and each functional [if] and [match] in it is one value all the same. Only
    the prover reads either. A statement, a loop, and a contract hold their formulas: no stage after
    the builder reads a core expression. *)

type local = int
type block = int

(** Whether a local is a source binding or a temporary. *)
type local_kind =
  | Source of { local : Core.local; mode : Types.mode; name : string option; is_var : bool }
      (** A parameter, [self], or a local that a pattern or a lambda binds, with the name it is
          written with and whether it is declared with [var]. With [Read] or [Mut], it is the place
          it was bound to, not a copy of it. *)
  | Temporary
      (** A value with no name. It is [Dead] at the end of the statement that makes it, unless it is
          the value of a block, which the enclosing statement reads, or a [let] extends it, which
          makes it [Dead] where the [let]'s bindings are, as the base of a slice that the [let]
          binds is. *)
  | Lent of Types.mode
      (** The part that a lending call lends, or the target of a compound assignment: the place
          itself, until it is [Dead]. *)

type local_info = { kind : local_kind; type_ : Types.ty; origin : Core.origin }

type place = { root : root; projections : projection list }
and root = Local of local | Constant of Path.t

and projection =
  | Field of string
  | Variant_field of { variant : string; field : string }
      (** A field of a variant, where a test has shown that the value holds the variant. *)

type constant = Unit | Integer of Z.t | Float of float | Boolean of bool | String of string

type operand =
  | Use of { place : place; type_ : Types.ty; node : Core.id; origin : Core.origin }
      (** The value at a place, of [type_], copied if the type copies implicitly and moved
          otherwise. [node] is the core node the value is read for. *)
  | Borrow of { place : place; type_ : Types.ty; mode : Types.mode; origin : Core.origin }
      (** The place itself, lent for the operation: read-only, or [mut]. *)
  | Take of { place : place; type_ : Types.ty; origin : Core.origin }
      (** The old value of a compound assignment's target, which the operator takes as owned. The
          statement assigns the target again before any other code runs. *)
  | Constant of { value : constant; type_ : Types.ty }

type callee = operand Core.target
(** A call's callee. An intrinsic called is one that is not a primitive operation: those are
    {!Operation}. *)

type argument =
  | Passed of { mode : Types.mode; value : operand; mode_keyword : Core.mode_keyword option }
  | Default  (** The callee fills in the parameter's default. *)

type call = {
  callee : callee;
  arguments : argument list;  (** One per parameter, in parameter order. *)
  uses : Types.capability_set;
  node : Core.id;  (** The core form's [Call]. *)
  origin : Core.origin;  (** The call's, for diagnostics. *)
}

type capture = { local : Core.local; type_ : Types.ty; place : place }
(** A local that a lambda captures: its core local, its type, and its place in the enclosing body.
*)

type yielded =
  | Part of operand
  | Built of {
      variant : string option;
      fields : (string * yielded option) list;
      type_ : Types.ty;
      node : Core.id;
    }
      (** A constructor of [type_], with every field in evaluation order. [None] takes the field's
          default. [node] is its core node. *)

type provided = {
  mode : Types.mode;
  value : operand;
  type_ : Types.ty;
  provides : Core.provided list;
  origin : Core.origin;
}

(** How long a loan lasts. *)
type loan_duration =
  | Loop_body  (** A loop borrows what it iterates over for its body. *)
  | Provide_body  (** A [provide] block borrows its implementations for its body. *)
  | Rest_of_statement  (** A lending call borrows its receiver until the statement ends. *)
  | Operand_evaluation
      (** An evaluated operand stays borrowed until its operation runs, so that a later operand
          cannot mutate it. *)

(** What a [for] loop iterates over. *)
type iteration =
  | Range of { start : operand; stop : operand; inclusive : bool }
      (** The integers or characters from [start] to [stop], each once. A range of [Character] skips
          the surrogates. *)
  | Pull of { cursor : place; next : callee }
      (** The values a cursor gives until it has none, by its type's [Cursor.next]. *)

type early_exit = {
  resume : block;  (** Where the code after the group goes on, where this exit won *)
  returned : local option;  (** For a [return] with a value, the local the value is in *)
}
(** An early exit that leaves a group of tasks: a [return], [break], or [continue] out of a branch
    of a [concurrent] block or an iteration of a [concurrent for]. *)

type branch = {
  entry : block;
  blocks : block list;  (** Every block of the branch, [entry] first. *)
}
(** A branch of a [parallel] or [concurrent] block. *)

type inlined = {
  method_ : Path.t;
  type_arguments : Types.argument list;  (** The method's, as the instance has them. *)
  call : Core.origin;  (** Where the call is, in the code around it. *)
}
(** A method inlined at a call. *)

(** A connective of a formula. Its right operand is read only where its left operand does not decide
    its value: where the left of [&&] and of [==>] holds, and where the left of [||] does not. *)
type connective = And | Or | Implies

type rvalue =
  | Operand of operand
  | Operation of {
      operation : Intrinsic.operation;
      type_arguments : Types.argument list;
          (** The intrinsic's type arguments: for an operator, the types of its operands. *)
      operands : operand list;
    }
      (** A primitive operation on built-in types, written as an operator or as a call of the
          intrinsic. *)
  | Compare of { comparison : Core.comparison; left : operand; right : operand }
  | Not of operand
  | Construct of { variant : string option; fields : (string * operand option) list }
      (** A record or a variant, with every field in evaluation order. [None] takes the field's
          default. A [Borrow] field lends its place to the value, as a yielded construct does. *)
  | Array of operand list
  | Is_variant of { place : place; variant : string }
  | Convert of { conversion : Core.conversion; value : operand }
  | To_any of { value : operand; trait : Types.trait_reference; evidence : Core.evidence }
  | Copy of operand  (** A [copy()] that the compiler implements. *)
  | Function_value of {
      path : Path.t;
      type_arguments : Types.argument list;
      is_argument : bool;
          (** Whether the function is written as an argument of a call, which checks it against the
              parameter's function type. Anywhere else it is a value whose type keeps none of its
              [requires]. *)
    }
  | Lambda of {
      body : int;
      captures : capture list;
      definition : formula option;
          (** The lambda as a function's definition, where its body is functional, as
              {!definition_of_path} says of a function's: a formula that takes the lambda's
              parameters and reads its captures by their core locals. *)
      value_type : Types.ty option;
          (** The type of the body's value before any conversion to [Integer], which may be narrower
              than the lambda's result type. *)
      is_argument : bool;
          (** Whether the lambda is written as an argument of a call, which reads it with what the
              parameter's function type promises of its arguments. *)
    }
      (** A function value made from a lambda. [body] indexes {!t.lambdas}, and [captures] are in
          the order of its body's {!body.captures}. *)
  | Value_parameter of Types.parameter
  | Specification of specification
      (** An expression that only a specification can hold. No code that runs has one. *)

and specification =
  | Result  (** [result]: the function's return value, in an [ensures]. *)
  | Entry of local
      (** The value that a parameter or [self], by its local, had when the function was called,
          which [old] reads. *)
  | Yielded
      (** [yielded]: in a loop's clauses, the values of the iterations before, and in a lending
          method's [ensures], its part as the caller left it. *)
  | Identical of operand * operand  (** [identical(first, second)] *)
  | Applied of {
      function_ : Core.specification_function;
      arguments : operand list;
      unconverted : Types.ty list;
          (** Each argument's type before it was converted to [Integer], which bounds [log]. *)
    }  (** [log], [power], [time], or [calls], applied. *)
  | Method_time of callee  (** [time(Element.equal)] *)
  | Map of (operand * operand) list  (** A [FiniteMap] literal: each key with its value. *)
  | Quantified of {
      quantifier : Syntax.quantifier;
      range : quantifier_range;
      parameter : local;
      matches : value_block;
      body : value_block;
    }
      (** A quantifier as a formula, over the values of the range that its pattern matches. One
          value of the range is in [parameter]. [matches] tests the pattern against it, binds the
          pattern's names, and gives whether it matches; [body] reads the names and gives the [Bool]
          the quantifier's body gives. *)
  | Conditional of {
      condition : operand;
      then_ : value_block;
      else_ : value_block;
      if_condition : Core.origin option;
          (** The origin of the condition of an [if], as written, which the prover names where it
              shows the case a counterexample takes. [None] for a conditional that the builder makes
              of a pattern. *)
    }
      (** A functional [if] of a specification, as one value: [then_]'s where [condition] holds, and
          [else_]'s where it does not. *)
  | Cases of case list
      (** A functional [match] of a specification, as one value: that of the first case whose tests
          and guard hold. The cases cover every value. *)
  | Connective of { connective : connective; left : operand; right : value_block }
      (** [&&], [||], or [==>] of a specification, as one value. A pattern's tests are an [&&] of
          one test and the tests after it, which read a part only where the test before shows the
          part is there. A name that an [is] in the right operand of [&&] binds is read by the code
          after the [&&], where the [&&] holds, as [x] is in [a && b is Some(x) && x > 0]. *)

(** The values a quantifier ranges over. *)
and case = {
  tests : value_block;  (** Whether the arm's patterns match the scrutinees. *)
  guard : value_block option;  (** The arm's guard, which binds the patterns' names to read them. *)
  value : value_block;  (** The arm's value, which binds the patterns' names to read them. *)
}
(** An arm of a [match] of a specification, for one way its patterns can match: an arm whose
    patterns have alternatives is a case for each. *)

and quantifier_range =
  | Over_type of Types.ty  (** Every value of a type. *)
  | Over_range of { start : operand; stop : operand; inclusive : bool }
  | Over_collection of operand  (** The elements of a collection. *)

and value_block = { statements : statement list; value : operand }
(** A block of a formula: statements that jump nowhere, then the block's value. Its statements read
    the locals of the code around it, and assign locals that only the block reads, but for the names
    that the right operand of an [&&] binds. *)

and formula = {
  parameters : local list;
      (** The locals it takes: the parameters of the function or the lambda it is written for, or
          else each local it reads that nothing in it binds, in the order it first reads them. *)
  locals : local_info array;
  value : value_block;
  type_ : Types.ty;  (** The type of its value. *)
  origin : Core.origin;  (** Where it is written. *)
  lambdas : body array;  (** The bodies of the lambdas written in it. *)
}
(** An expression of a specification, which never runs: a clause, an invariant, a measure, a bound,
    or a functional body read as a definition. It is one {!value_block}, with no control-flow graph:
    an [if], a [match], a short-circuit operator, and a quantifier in it are each one
    {!Specification} value that holds its cases as blocks, so a reader maps it to a term by
    structural recursion. Only the prover reads it. *)

and bound = Finite | Order_of of formula | At_most of formula | Exactly of formula

and cost = {
  origin : Core.origin;  (** The [cost] clause. *)
  amortized : bool;
  resource : Core.resource;
  bound : bound;
}
(** A [cost] clause, with its bound as a formula. *)

and loop_clause =
  | Invariant of formula
  | Decreases of formula list
  | Cost of cost  (** A bound on the cost that the loop has incurred so far. *)

and quantified = {
  quantifier : formula;  (** The quantifier, as the formula it is. *)
  decides : local;  (** The local the loop leaves the quantifier's value in. *)
}
(** A quantifier in code that runs, which is a loop. The prover reads the formula and writes its
    value to [decides], and does not read the loop's body. *)

and loop = {
  clauses : loop_clause list;
  schedule : Core.loop_mode;
  origin : Core.origin;
  quantified : quantified option;
}
(** A loop's clauses, each a formula whose parameters are the locals it reads, and where the loop
    runs a quantifier, the quantifier. *)

and lent_element = {
  element : local;  (** The [Lent] local of the element. *)
  collection : place;
      (** The collection, as the place that holds it at the loop's head, and no temporary that
          borrows it for one iteration. *)
  count : formula;
      (** The call of the collection's [count], which the prover reads: a loop that mutates its
          elements leaves their number as it was. *)
  call : formula;
      (** The element that the collection's [element] lends at the loop's position, which the prover
          reads: a loop that reads its elements was lent these at the positions before. *)
}
(** The element that an iteration of a loop over a collection is lent. *)

and compared = { comparison : Core.comparison; left : formula; right : formula }
(** The condition of a [while] loop that is one comparison of functional operands, from which the
    prover guesses a measure that decreases where the loop writes none. *)

and statement = { kind : statement_kind; origin : Core.origin }

and statement_kind =
  | Assign of { target : place; value : rvalue; node : Core.id option }
      (** [node] is the core expression whose value the assignment computes, where it computes one,
          for the prover's messages. *)
  | Call of { destination : place option; call : call }
  | Lend of { part : local; call : call }
      (** A call of a lending method. The [Lent] local [part] is the part it lends. *)
  | Slice of { destination : place; base : place; call : call }
      (** A call of [slice_range], whose result views [base]. *)
  | Template of { destination : place; literals : string list; call : call }
      (** A tagged string: the call of the tag's [from_template], with the literal texts. *)
  | Live of local list  (** These locals start to hold values here. *)
  | Dead of local list  (** These locals hold nothing from here on. *)
  | Assert of { condition : operand; bit_vector : formula option }
      (** An [assert] that can run. One proven by bit vectors has its condition as a formula too, in
          [bit_vector], which the prover proves of every value of the locals it reads. *)
  | Echo of operand
  | Provide of { provided : provided list; can_use_tasks : bool }
  | Provide_end
  | Loan_start of { loan : int; borrowed : operand; mode : Types.mode; duration : loan_duration }
      (** From here on, what [borrowed] borrows or views is lent with [mode]. *)
  | Loan_end of int list
  | Ghost_assert of { condition : formula; by_bit_vector : bool }
      (** An [assert] that cannot run. Only the prover reads it. *)
  | Matched of { patterns : Core.origin list }
      (** An arm of a [match] whose patterns, by their origins, matched here, before its guard. Only
          the prover reads it, to tell which arm a counterexample takes. *)
  | Proof of t
      (** A [proof] block: a body built as a specification, whose parameters are the locals it
          reads. Its statements can jump, as an [assert] in one arm of an [if] makes them, so it is
          a body and no formula. Only the prover reads it. *)

and terminator =
  | Goto of block
  | Branch of { condition : operand; yes : block; no : block; is_if_condition : bool }
      (** [is_if_condition]: the condition is an [if]'s, as written, which the prover names where it
          shows a path a counterexample takes. *)
  | Switch_variant of { place : place; cases : (string * block) list }
  | For of {
      iteration : iteration;
      part : local;
      lent : lent_element option;
          (** In a loop over the elements of a collection, the element that each iteration is lent.
              [part] is then the element's position. *)
      body : block;
      binding_count : int;
          (** The number of statements at the start of [body] that bind the loop's pattern to
              [part]. The prover runs them to read the loop's clauses, which name what the pattern
              binds. *)
      blocks : block list;  (** Every block of the body, [body] first, nested loops' included. *)
      after : block;
      loop : loop;
    }
  | Fork of { fork : Core.origin; concurrent : bool; branches : branch list; join : block option }
  | Join of { fork : Core.origin; next : block }
      (** The end of a branch of the {!Fork} [fork]. Read in order, [next] runs after it: the next
          branch's entry, or the block's end after the last branch. *)
  | Iteration_end of { loop : block }
      (** The end of an iteration of the enclosing {!For}, the terminator of [loop]. *)
  | Yield of { mode : Types.mode; part : yielded; resume : block }
  | Return of operand option
  | Cancel of {
      task : Core.task;
      task_end : block option;
      winner : local;
      number : int;
      returned : (operand * local) option;
    }
      (** An early exit that leaves [task]: the task cancels its group and ends, at [task_end] for a
          branch of a [concurrent] block, or where its iteration ends. The first task of the group
          to cancel sets [winner] to [number], and moves a value it returns into the local; a later
          one drops that value. The scopes inside the task end before it. *)
  | Resume of { winner : local; exits : early_exit list; next : block }
      (** Where a group of tasks has ended: the [resume] of the exit numbered [winner], counted from
          1 in [exits], where one won, or else [next]. *)
  | Unreachable
  | Written_unreachable
  | Todo  (** A [todo] that is reached stops the program. *)

and natural_loop = {
  loop : loop;
  body : block;
  after : block option;
  compared : compared option;
  blocks : block list;
      (** Every block of the loop, the header first: those the header reaches without leaving by
          [after], and from which the header is reached again. A block that leaves the loop for
          good, as one that ends in a [return] does, is none of them. *)
  condition : block list;
      (** The blocks of the loop's condition, the header first: those of the loop that the header
          reaches before [body]. *)
  exits : block list;
      (** The blocks outside the loop from which [after] is reached, [after] among them. A jump from
          the loop to one of them ends the loop: from a block of the condition, where the condition
          does not hold, and from any other, by a [break]. *)
}
(** A [while] loop, which its header block carries: its clauses, the first block of its body, which
    the loop's condition goes to where it holds, the block it exits to where the condition does not
    hold or a [break] leaves, [None] where no path exits, as from [while true] with no [break], its
    condition where that is a comparison, and its blocks. *)

and basic_block = {
  statements : statement list;
  terminator : terminator;
  terminator_origin : Core.origin;
  header : natural_loop option;  (** The [while] loop this block heads. *)
  inlined : inlined list;
      (** For a block of a method inlined into the body, the methods it was inlined from, innermost
          first. The block's origins are the innermost method's. Empty for the body's own blocks. *)
}

and body = {
  parameters : local list;
  captures : local list;
      (** For a lambda's body, the local of each value it captures, which its {!Lambda} gives, in
          order. *)
  locals : local_info array;
  blocks : basic_block array;  (** The entry is block 0. *)
}

and t = { body : body; lambdas : body array }

type field_default = {
  variant : string option;  (** The field's variant, for a sum type. *)
  field : string;
  type_ : Types.ty;  (** The default's type, in the type's own generic parameters. *)
  value : t;
}

(** The defaults a definition writes, each as a body that takes nothing and returns the value. *)
type defaults =
  | Parameter_defaults of (int * t) list
      (** A function's: each parameter that has a default, by its position among the parameters,
          [self] first, as a call's arguments are numbered. A test and a law's proof have none. *)
  | Field_defaults of field_default list  (** A type's. *)

type requirement = {
  clause : formula;
  code : t option;
      (** The clause as code, where it can run: it holds no quantifier, no value of type [Integer],
          no [old] or [result], and no call of a function for specifications only. A template's
          check and a derived [Deserialize] run it. It is a body that takes what the clause reads, a
          function's parameters or a type's [self], and returns the clause's [Bool]. *)
  names : (Core.local * Core.origin) list;
      (** Each place of the clause that names a local, with the name's origin, in the order written.
          A message that shows the clause at a call writes each argument's text where the clause
          names its parameter. *)
}
(** A [requires] clause, or a type's [invariant]. *)

type callback = {
  inputs : (Core.local * string) list;  (** The named inputs, which the clauses can read. *)
  requires : formula list;
}
(** The [requires] clauses of a function-typed parameter that names its inputs. Every call through
    the parameter must satisfy them. *)

type parameter = {
  local : Core.local;
  name : string;
  mode : Types.mode;
  type_ : Types.ty;
  has_default : bool;  (** Whether a call may leave it out: {!defaults_of_path} holds its default. *)
}
(** A parameter of a function or a method, [self] among them. *)

type contract = {
  parameters : parameter list;
  requires : requirement list;
  ensures : formula list;
  decreases : formula list;
  costs : cost list;
  callbacks : (int * callback) list;
      (** Each function-typed parameter that states clauses, by its position among the parameters,
          [self] first. *)
}
(** What a function's header states, in the order written. Each clause is a formula that takes the
    function's parameters. It reads [result] and a parameter's value on entry as {!Specification}
    values. *)

type type_clauses = { invariants : requirement list; potential : formula option }
(** What a type states of its values: its [invariant] clauses, in the order written, and its
    [cost potential]. Each is a formula that reads [self]. *)

type law = {
  name : string;
  parameters : (Core.local * Types.ty) list;  (** Each parameter's local and type. *)
  requires : formula list;
  states : formula;  (** The [Bool] the law states. *)
}
(** A law of a trait. Each formula's parameters are the law's parameters that it reads. *)

val iter_places_read : (place -> unit) -> value_block -> unit
(** Calls a function on each place that a block of a formula reads: by its statements, by its value,
    and by the blocks that its values hold. *)

val iter_code : ?statement:(statement -> unit) -> ?terminator:(terminator -> unit) -> t -> unit
(** Calls [statement] on every statement and [terminator] on every terminator of a definition's
    code: those of its body, of its lambdas' bodies, of its [proof] blocks, and of every formula
    that a statement, a loop, or a lambda of these holds, with the blocks that a {!Specification}
    value holds. A formula repeats code where it is that code's definition, as a lambda's is, so a
    call may be visited twice. *)

val iter_formula :
  ?statement:(statement -> unit) -> ?terminator:(terminator -> unit) -> formula -> unit
(** As {!iter_code}, for the code of a formula. *)

val operand_type : operand -> Types.ty
(** The type of an operand's value. *)

val canonical : basic_block array -> basic_block array
(** The blocks control can reach from the entry, block 0, in reverse postorder, numbered in that
    order, as the builder leaves a body. *)

val successors : terminator -> block list
(** The blocks a terminator can jump to. *)

val conditional_lends : body -> local list
(** The parts of lending calls whose {!Dead} some path from the entry reaches without passing the
    {!Lend}, as a lend in one arm of a [match] does. A consumer runs the lend's end only where the
    lend ran. *)

val iteration_loop : terminator -> block option
(** The block of the {!For} whose iteration an {!Iteration_end} ends. *)

val block_successors : body -> block -> block list
(** The blocks control goes to from the end of a block: its terminator's {!successors}, and, for the
    end of an iteration, the loop's next iteration and the block after the loop. *)

val is_lowered : Query.context -> Resolve.Names.key -> bool
(** Whether a definition has no error, so that the queries of this module answer for it. *)

val mir : (Resolve.Names.key, t option) Query.query
(** The MIR of a definition's body: a function's, a test's, a theorem's, or a law's proof. It is
    built once for the definition. A body that never runs, a theorem's, a law's proof, or that of a
    function for specifications only, is a specification: its quantifiers are formulas, and it may
    hold {!Specification} values. Only the prover reads such a body. *)

val of_path : (Path.t, t option) Query.query
(** The MIR of the function or method at a path that has code to run, in the generic parameters of
    the definition that writes it, as [Infer.form_origin] names it. A written method has its
    definition's {!mir}, and so does a method that an [impl] inherits from its trait: the default
    method's, which every such [impl] shares. A method of a derived [impl] has the MIR of its
    generated core form. *)

val defaults_of_path : (Path.t, defaults option) Query.query
(** The defaults of the function, method, or type at a path, from the definition that writes them,
    as {!of_path} gives a body's MIR. They are built once for that definition, and are no part of a
    body's MIR: a function has its defaults whether or not it has a body, as a capability's method
    has none, and a caller that reads them reads nothing of the body. [None] for a definition with
    an error, or one that has neither parameters nor fields. *)

val contract_of_path : (Path.t, contract option) Query.query
(** What the header of the function or method at a path states, from the definition that writes it,
    built once. Editing the function's body leaves it equal, so a caller that reads it reads nothing
    of the body. [None] for a definition with an error, or one that is no function. *)

type definition =
  | Functional of formula
      (** The body as a formula whose parameters are the locals it reads, which gives the body's
          value. *)
  | Not_functional
      (** A body that is no definition: it holds a [var], an assignment, a loop, a [return], a [mut]
          argument, or a diverging expression. *)

val definition_of_path : (Path.t, definition option) Query.query
(** The body of the function or method at a path, as a caller in its package reads it. A caller
    reads the body where the body is the callee's semantics, as the body of a trait's or an [impl]'s
    method is. [None] where a caller reads no body: a function's semantics are its contract, so
    editing the function's body proves no caller again. *)

val exported_definition_of_path : (Path.t, definition option) Query.query
(** As {!definition_of_path}, as a caller in another package reads the body. *)

val laws : (Resolve.Names.key, law list) Query.query
(** The laws of a trait, in the order written. *)

val type_clauses_of_path : (Path.t, type_clauses option) Query.query
(** What the type at a path states of its values. [None] for a definition with an error, or one that
    is no type. *)

val is_generated : Query.context -> Path.t -> bool
(** Whether the code of the method at a path is generated for a derived [impl], so that no
    definition writes it. *)

val of_constant : (Path.t, t option) Query.query
(** The MIR of a constant's value: a body that returns it. *)
