(** The MIR: each body of a definition as a control-flow graph of places, values, and explicit
    temporaries, in evaluation order. The builder decides the order of evaluation, the scope of each
    temporary and binding, and the flow of patterns, loops, and early exits once, so every stage
    that reads the MIR agrees on them. Specifications stay core expressions. *)

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
  | Lambda of { body : int; captures : capture list; written : Core.expression }
      (** A function value made from a lambda. [body] indexes {!t.lambdas}, and [captures] are in
          the order of its body's {!body.captures}. [written] is the lambda as written, which the
          prover reads as a function's definition. *)
  | Value_parameter of Types.parameter

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
  | Live of local list  (** These locals start to hold values here. *)
  | Dead of local list  (** These locals hold nothing from here on. *)
  | Assert of { condition : operand; bit_vector : Core.expression option }
      (** An [assert] that can run. One proven by bit vectors has its condition as written in
          [bit_vector], which the prover reads as a formula. *)
  | Echo of operand
  | Provide of { provided : provided list; can_use_tasks : bool }
  | Provide_end
  | Loan_start of { loan : int; borrowed : operand; mode : Types.mode; duration : loan_duration }
      (** From here on, what [borrowed] borrows or views is lent with [mode]. *)
  | Loan_end of int list
  | Ghost_assert of { condition : Core.expression; by_bit_vector : bool }
      (** An [assert] that cannot run. Only the prover reads it. *)
  | Matched of { patterns : Core.origin list }
      (** An arm of a [match] whose patterns, by their origins, matched here, before its guard. Only
          the prover reads it, to tell which arm a counterexample takes. *)
  | Proof of Core.block  (** Only the prover reads it. *)

type loop = {
  clauses : Core.loop_clause list;
  schedule : Core.loop_mode;
  origin : Core.origin;
  formula : Core.expression option;
      (** The formula the prover reads for the loop: the quantifier a loop runs, or a [while] loop's
          condition, from which it guesses a measure that decreases. *)
}
(** The clauses of a loop, which its header carries. *)

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

type lent_element = {
  element : local;  (** The [Lent] local of the element. *)
  count : Core.expression;
      (** The call of the collection's [count], which the prover reads: a loop that mutates its
          elements leaves their number as it was. *)
  call : Core.expression;
      (** The call of the collection's [element] at the loop's position, which the prover reads: a
          loop that reads its elements was lent the values of this call at the positions before. *)
}
(** The element that an iteration of a loop over a collection is lent. *)

type terminator =
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

type natural_loop = { loop : loop; body : block; after : block option }
(** A [while] loop, which its header block carries: its clauses, the first block of its body, which
    the loop's condition goes to where it holds, and the block it exits to where the condition does
    not hold or a [break] leaves, [None] where no path exits, as from [while true] with no [break].
*)

type basic_block = {
  statements : statement list;
  terminator : terminator;
  terminator_origin : Core.origin;
  header : natural_loop option;  (** The [while] loop this block heads. *)
  inlined : inlined list;
      (** For a block of a method inlined into the body, the methods it was inlined from, innermost
          first. The block's origins are the innermost method's. Empty for the body's own blocks. *)
}

and inlined = {
  method_ : Path.t;
  type_arguments : Types.argument list;  (** The method's, as the instance has them. *)
  call : Core.origin;  (** Where the call is, in the code around it. *)
}
(** A method inlined at a call. *)

type body = {
  parameters : local list;
  defaults : (local * t) list;
      (** For each parameter with a default, the MIR of the default, which the callee runs where the
          argument is left out. *)
  captures : local list;
      (** For a lambda's body, the local of each value it captures, which its {!Lambda} gives, in
          order. *)
  locals : local_info array;
  blocks : basic_block array;  (** The entry is block 0. *)
}

and t = { body : body; lambdas : body array }

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

val of_definition : Core.definition -> t option
(** The MIR of a definition whose code runs: a function's, a test's, or a law's proof. *)

val of_path : (Path.t, (t * Types.substitution) option) Query.query
(** The MIR of the function or method at a path that has code to run, with the substitution to apply
    to it, as [Infer.core_of_path] gives the core form: a method of a derived [impl], or one that an
    [impl] inherits from its trait, has the MIR of its generated or inherited core form. *)

val of_expression : ?parameters:Core.parameter list -> Core.expression -> t

val mir : (Resolve.Names.key, t option) Query.query
(** The MIR of a definition whose code runs. The body of a function for specifications only never
    runs, so it has none. *)

val of_constant : (Path.t, t option) Query.query
(** The MIR of a constant's value: a body that returns it. *)
