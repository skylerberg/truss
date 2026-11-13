(** The MIR: each body of a definition as a control-flow graph of places, values, and explicit
    temporaries, in evaluation order. The builder decides the order of evaluation, the scope of each
    temporary and binding, and the flow of patterns, loops, and early exits once, so every stage
    that reads the MIR agrees on them. Specifications stay core expressions. *)

type local = int
type block = int

(** Whether a local is a source binding or a temporary. *)
type local_kind =
  | Source of { local : Core.local; mode : Types.mode }
      (** A parameter, [self], or a local that a pattern or a lambda binds. With [Read] or [Mut], it
          is the place it was bound to, not a copy of it. *)
  | Temporary
      (** A value with no name. It is [Dead] at the end of the statement that makes it, unless it is
          the value of a block, which the enclosing statement reads. *)
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

type callee =
  | Function of { path : Path.t; type_arguments : Types.argument list }
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      type_arguments : Types.argument list;
      evidence : Core.evidence;
    }
  | Capability_method of { capability : Path.t; name : string }
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
      (** An intrinsic that is not a primitive operation. Those are {!Operation}. *)
  | Indirect of operand

type argument =
  | Passed of { mode : Types.mode; value : operand; mark : Core.mark option }
  | Default  (** The callee fills in the parameter's default. *)

type call = {
  callee : callee;
  arguments : argument list;  (** One per parameter, in parameter order. *)
  uses : Types.capability_set;
  node : Core.id;  (** The core form's [Call]. *)
}

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
  | Function_value of { path : Path.t; type_arguments : Types.argument list }
  | Lambda of { body : int; captures : Core.capture list }
      (** A function value made from a lambda. [body] indexes {!t.lambdas}. *)
  | Value_parameter of Types.parameter

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

type statement = { kind : statement_kind; origin : Core.origin }

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
  | Pull of { destination : place; cursor : place }
      (** The next value of the built-in cursor of a yielding method, an [Option]. *)
  | Live of local list  (** These locals start to hold values here. *)
  | Dead of local list  (** These locals hold nothing from here on. *)
  | Assert of operand  (** An [assert] that can run. *)
  | Echo of operand
  | Provide of { provided : provided list; can_use_tasks : bool }
      (** The start of a [provide] block. [can_use_tasks] says whether its body can use [Tasks], so
          that tasks may call a [mut] implementation at the same time. *)
  | Provide_end
  | Fork_start of { fork : Core.origin; concurrent : bool }
      (** The start of a branch of a [parallel] or [concurrent] block, which [fork] names by its
          statement's origin. *)
  | Fork_end of { fork : Core.origin }  (** The end of the block's last branch. *)
  | Loan_start of { loan : int; borrowed : operand; mode : Types.mode; duration : loan_duration }
      (** From here on, what [borrowed] borrows or views is lent with [mode]. *)
  | Loan_end of int list
  | Ghost_assert of Core.expression  (** An [assert] that cannot run. Only the prover reads it. *)
  | Matched of { patterns : Core.origin list }
      (** An arm of a [match] whose patterns, by their origins, matched here, before its guard. Only
          the prover reads it, to tell which arm a counterexample takes. *)
  | Proof of Core.block  (** Only the prover reads it. *)

type loop = { clauses : Core.loop_clause list; schedule : Core.loop_mode; origin : Core.origin }
(** The clauses of a loop, which its header carries. *)

(** What a [for] loop iterates over. *)
type iteration =
  | Yielding of call  (** The parts a call of a yielding method yields. *)
  | Range of { start : operand; stop : operand; inclusive : bool }
      (** The integers or characters from [start] to [stop], each once. A range of [Character] skips
          the surrogates. *)
  | Pull of { cursor : place; next : callee option }
      (** The values a cursor gives until it has none: the built-in cursor of a yielding method when
          [next] is [None], or else the cursor type's [Cursor.next]. *)

(** Where an early exit from [concurrent] code goes once its tasks end. *)
type task_exit =
  | Exit_return of operand option
  | Exit_to of block
  | Exit_iteration  (** The end of the iteration of the enclosing [For]. *)

type left_task = {
  task : Core.task;
  ends : statement list;
      (** The ends of the scopes between it and the next task, or the exit's target, which run in
          the code around the task once it has ended *)
  task_end : block option;
      (** Where the task's code ends, which the other tasks of its group go on from: the start of
          the next branch of a [concurrent] block, or the block's end. An iteration of a
          [concurrent for] has none. *)
}
(** A task an early exit leaves. *)

type terminator =
  | Goto of block
  | Branch of { condition : operand; yes : block; no : block }
  | Switch_variant of { place : place; cases : (string * block) list }
  | For of { iteration : iteration; part : local; body : block; after : block; loop : loop }
      (** A [for] loop. [body] runs once for each element, which [part] holds, and ends with
          {!Iteration_end} or a jump to [after]. The iterations run one after another, or at once as
          [loop]'s schedule says. *)
  | Iteration_end  (** The end of an iteration of the enclosing {!For}. *)
  | Yield of { mode : Types.mode; part : operand; resume : block }
  | Return of operand option
  | Exit_tasks of { tasks : left_task list; exit : task_exit }
      (** An early exit from [concurrent] code: these tasks end, innermost first, then the exit is
          taken. The exit ends the scopes inside the innermost task before it. *)
  | Unreachable  (** A point the prover shows is never reached. *)
  | Todo  (** A [todo] that is reached stops the program. *)

type natural_loop = { loop : loop; body : block; after : block }
(** A [while] loop, which its header block carries: its clauses, the first block of its body, which
    the loop's condition goes to where it holds, and the block it exits to where the condition does
    not hold or a [break] leaves. *)

type basic_block = {
  statements : statement list;
  terminator : terminator;
  terminator_origin : Core.origin;
  header : natural_loop option;  (** The [while] loop this block heads. *)
}

type body = {
  parameters : local list;
  locals : local_info array;
  blocks : basic_block array;  (** The entry is block 0. *)
}

type t = { body : body; lambdas : body array }

val successors : terminator -> block list
(** The blocks a terminator can jump to. *)

val iteration_loops : body -> (block, block) Hashtbl.t
(** For each block whose terminator ends an iteration, an {!Iteration_end} or an {!Exit_tasks} to
    {!Exit_iteration}, the block of the innermost {!For} whose body it ends. *)

val of_definition : Core.definition -> t option
(** The MIR of a definition whose code runs: a function's, a test's, or a law's proof. *)

val of_path : (Path.t, (t * Types.substitution) option) Query.query
(** The MIR of the function or method at a path that has code to run, with the substitution to apply
    to it, as [Infer.core_of_path] gives the core form: a method of a derived [impl], or one that an
    [impl] inherits from its trait, has the MIR of its generated or inherited core form. *)

val of_expression : ?parameters:Core.parameter list -> Core.expression -> t
(** The MIR of one expression that runs on its own, such as a default or a constant's value: a body
    that returns the expression's value. [parameters] are the locals of the code around that the
    expression reads, such as the template a [requires] clause of a tag's [from_template] checks. *)

val mir : (Resolve.Names.key, t option) Query.query
(** The MIR of a definition whose code runs. The body of a function for specifications only never
    runs, so it has none. *)

val show : t -> string
(** The MIR as text, for tests. *)
