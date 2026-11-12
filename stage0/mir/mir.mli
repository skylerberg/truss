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
  | Use of { place : place; node : Core.id }
      (** The value at a place, copied if its type copies implicitly and moved otherwise. [node] is
          the core node the value is read for. *)
  | Borrow of { place : place; mode : Types.mode }
      (** The place itself, lent for the operation: read-only, or [mut]. *)
  | Constant of constant

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
  uses : Types.capability list;
  node : Core.id;  (** The core form's [Call]. *)
}

type rvalue =
  | Operand of operand
  | Operation of { operation : Intrinsic.operation; operands : operand list }
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

type statement = { kind : statement_kind; origin : Core.origin }

and statement_kind =
  | Assign of { target : place; value : rvalue }
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
  | Provide of provided list
  | Provide_end
  | Fork_start of { fork : int; concurrent : bool }
      (** The start of a branch of a [parallel] or [concurrent] block. *)
  | Fork_end of { fork : int }  (** The end of the block's last branch. *)
  | Ghost_assert of Core.expression  (** An [assert] that cannot run. Only the prover reads it. *)
  | Proof of Core.block  (** Only the prover reads it. *)

type loop = {
  clauses : Core.loop_clause list;
  schedule : Core.loop_mode;
  counter : local option;
      (** The counter of a loop over an integer range, which is at least the range's start and at
          most its stop at the header. *)
  origin : Core.origin;
}
(** The clauses of a loop, which its header carries. *)

(** Where an early exit from [concurrent] code goes once its tasks end. *)
type task_exit = Exit_return of operand option | Exit_to of block

type terminator =
  | Goto of block
  | Branch of { condition : operand; yes : block; no : block }
  | Switch_variant of { place : place; cases : (string * block) list }
  | Each of { call : call; part : local; body : block; after : block; loop : loop }
      (** A [for] loop over a call of a yielding method. [body] runs for each part the callee
          yields, which [part] holds, and ends with {!Iteration_end} or a jump to [after]. *)
  | Iteration_end  (** The end of an iteration of the enclosing {!Each}. *)
  | Yield of { mode : Types.mode; part : operand; resume : block }
  | Return of operand option
  | Exit_tasks of { tasks : Core.task list; exit : task_exit }
      (** An early exit from [concurrent] code: these tasks end, then the exit is taken. *)
  | Unreachable  (** A point the prover shows is never reached. *)
  | Todo  (** A [todo] that is reached stops the program. *)

type basic_block = {
  statements : statement list;
  terminator : terminator;
  terminator_origin : Core.origin;
  header : loop option;  (** The clauses of the natural loop this block heads. *)
}

type body = {
  parameters : local list;
  locals : local_info array;
  blocks : basic_block array;  (** The entry is block 0. *)
}

type t = { body : body; lambdas : body array }

val mir : (Resolve.Names.key, t option) Query.query
(** The MIR of a definition whose code runs. The body of a function for specifications only never
    runs, so it has none. *)

val show : t -> string
(** The MIR as text, for tests. *)
