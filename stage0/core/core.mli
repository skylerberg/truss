(** The core form of a definition: what the type checker decided, as a tree.

    The stages after the type checker read this in place of the syntax tree. Everything the checker
    chose is written where it chose it: a call names what it calls and lists its arguments in the
    callee's order, an operator is the call or the built-in operation it means, sugar is the
    construct it stands for, a place is told from a value, and every type is solved and normalized.
    A stage that has to ask again which method a name means, or what shape a type has, has found
    something missing here.

    Every node has an [id], its number within the definition, which later results are keyed by, and
    an [origin], the node of the syntax tree it came from, which is how a diagnostic about it finds
    the text to quote. One syntax node can be the origin of several nodes. *)

type id = int
type origin = Syntax.id

type local =
  | Bound of Syntax.id  (** A parameter or a binding, by the id of the name that binds it. *)
  | Self
  | Made of int
      (** A local the checker made, numbered within the definition: what a [?] found, in the arm
          that gives it back. *)

(** How a trait's [impl] was found. *)
type evidence =
  | Impl of { impl : Path.t; arguments : Types.substitution }  (** A written or derived [impl]. *)
  | Bound
      (** A bound in scope, on a generic parameter or on an associated type of one, which the code's
          instantiation resolves. *)
  | Dynamic  (** Through an [any] value's table. *)
  | Built_in  (** [Copyable] and [Plain], which the compiler implements. *)

type callee =
  | Function of { path : Path.t; type_arguments : Types.argument list }
      (** A function or a type's own method, with its generic arguments, the type head's first. *)
  | Trait_method of {
      trait : Types.trait_reference;
      name : string;
      receiver : Path.receiver;
      self_type : Types.ty;
      type_arguments : Types.argument list;  (** The method's own generic arguments. *)
      evidence : evidence;
    }
      (** A trait's method. With [Impl] evidence, the method at the [impl] is
          [Method { owner = impl; name; receiver }], whose signature and whose body, written there
          or left to the trait, the interface answers for. *)
  | Capability_method of { capability : Path.t; name : string }
  | Intrinsic of { operation : Intrinsic.operation; type_arguments : Types.argument list }
      (** An operation of [standard::intrinsic], called by name: exact when it returns, with nothing
          for the prover to show first. *)
  | Value of expression  (** A function value, called by position. *)

and call = {
  callee : callee;
  arguments : argument list;
      (** One for each parameter, in the callee's order, a method's receiver first. *)
  lends : Types.mode option;
      (** For a lending method, how the part it gives is lent. The part is a place: see [Lent]. *)
  uses : Types.capability list;
      (** The capabilities the call needs, with capability parameters replaced. *)
  capability_arguments : (Types.parameter * Types.capability list) list;
      (** Each capability parameter of the callee, solved. *)
}

and argument = { mode : Types.mode;  (** The parameter's. *) value : operand }

and operand =
  | Place of place
      (** A place, lent to the callee for the call: read-only, or to change for a [mut] parameter.
          An [own] parameter never takes a place; it takes the value there, as [Value (Use place)].
      *)
  | Value of expression
      (** A value: an [own] parameter takes it, and a read-only one sees it for the call. *)
  | Default  (** The parameter's default, which the callee's own core form holds. *)

(** Where a value is. *)
and place =
  | Local of local
  | Field of { base : place; variant : string option; field : string; type_ : Types.ty }
      (** A field of a record, or of the [variant] a pattern or an [is] showed the base to be;
          [type_] is the field's. *)
  | Lent of expression
      (** The part a call of a lending method lends, for the rest of the statement: [items[index]],
          which is [at], and [grid.cell(position)]. The expression is the [Call]. *)
  | Temporary of expression
      (** A value with no place of its own, held for the statement so that a part of it can be
          named: [origin().x]. *)

and expression = { id : id; origin : origin; type_ : Types.ty; kind : kind }

and kind =
  (* Values *)
  | Integer of Z.t  (** Of a built-in integer type, [Integer], or [Character]. *)
  | Float of float  (** Already rounded to its type. *)
  | Boolean of bool
  | String of string  (** A string literal with nothing interpolated. *)
  | Interpolated of piece list
      (** A plain string with interpolations: the text its pieces make, in order. *)
  | Template of {
      from_template : callee;  (** The tag's [FromTemplate.from_template]. *)
      literals : string list;  (** The texts between the parts: one more than there are parts. *)
      parts : expression list;  (** Each already the tag's [Part], through [From] where needed. *)
    }
  | Use of place  (** The value at a place. Whether it is copied or moved is ownership's to say. *)
  | Function_value of { path : Path.t; type_arguments : Types.argument list }
      (** A named function or method as a value. *)
  | Constant of Path.t
  | Generic_value of Types.parameter  (** A [USize] generic parameter. *)
  | Lambda of {
      parameters : pattern list;
      captures : local list;  (** The outer locals it reads, in order. *)
      body : block;
      result : Types.ty;
    }
  | Construct of { variant : string option; fields : (string * operand) list }
      (** A value of a record type or of a variant, of the node's type: every field, in the order
          the type declares them. [Default] is the field's default, which the type's core form
          holds. Never [Place]. *)
  | Collection of expression list
      (** A list, array, or set literal, or a specification's sequence or set: the node's type says
          which. *)
  | Entries of (expression * expression) list  (** A map literal. *)
  | Updated of { base : expression; updates : (string list * expression) list }
      (** [base with (...)]: the record with the field at each path replaced. *)
  | Slice of { base : place; start : expression option; stop : expression option }
      (** [items[start..stop]]: a view of part of a list, a slice, or an array. *)
  (* Calls and operations *)
  | Call of call
  | Operator of { operation : Intrinsic.operation; arguments : expression list }
      (** Arithmetic, a bitwise operator, or a shift on built-in types, however it was written, as
          [left + right] or as [left.add(right)]. The prover shows it defined: that it does not
          overflow, divide by zero, or shift too far. *)
  | Compare of { comparison : comparison; left : expression; right : expression }
      (** A comparison of two values of one built-in type, or in a specification of two integers by
          value. On any other type a comparison is a [Call] of [equal], or of [compare] under a
          [Matches]. *)
  | Not of expression
  | Both of expression * expression  (** [&&]: the right side only when the left holds. *)
  | Either of expression * expression  (** [||] *)
  | Implies of expression * expression  (** [==>], in specifications. *)
  | Matches of { value : expression; pattern : pattern }
      (** [value is pattern], and what [<] asks of the [Ordering] its [compare] gives. *)
  | Convert of { conversion : conversion; value : expression }
  | Any of { value : expression; trait : Types.trait_reference; evidence : evidence }
      (** A value made an [any Trait]. *)
  (* Control *)
  | If of { condition : expression; then_ : block; else_ : block option }
  | Match of {
      scrutinees : expression list;
      arms : arm list;
      guards_cover : bool;
          (** Whether its last arm is [_ => unreachable] after guards, so that the prover shows the
              guards cover. *)
    }
  | Block of block
  | Provide of { implementations : implementation list; body : block }
  | Return of expression option
  | Break
  | Continue
  | Todo
  | Unreachable
  | Echo of expression
  (* Specifications *)
  | Result  (** [result], in an [ensures]. *)
  | Old of expression
  | Updating
      (** In the value of an [Update]: what its target holds before, handed over as owned. *)
  | Quantified of { quantifier : Syntax.quantifier; binder : binder; body : expression }
  | Yielded  (** The parts handed out so far, in order. *)
  | Finished
  | Identical of expression * expression  (** [identical(first, second)] *)
  | Measure of { function_ : measure; arguments : expression list }
      (** [log(count)], [power(base, exponent)], [time(visit)], or [calls(visit)], in a [cost]
          bound. *)

and measure = Log | Power | Time | Calls
and comparison = Equal | Not_equal | Less | Less_equal | Greater | Greater_equal

and piece =
  | Text of string
  | Displayed of { value : expression; display : callee }
      (** A value written out by its [Display]. *)

(** The only conversions, each a node where it happens. *)
and conversion =
  | View
      (** A [List] seen as a [Slice], or a [String] as a [StringSlice], where the view type is
          expected. *)
  | Widen
      (** A function value to a function type with more [uses] or weaker costs. The prover shows the
          costs imply: the value's type is what is given, and the node's what is expected. *)
  | To_integer  (** A built-in integer to [Integer], in specifications. *)
  | From_integer
      (** An [Integer] where a built-in integer is expected, which the prover shows fits. *)

and binder =
  | Over_type of { local : local; name : string; type_ : Types.ty }  (** [value: Int64] *)
  | Over_range of { pattern : pattern; start : expression; stop : expression; inclusive : bool }
  | Over_collection of { pattern : pattern; collection : expression }

and implementation = {
  value : expression;
  provides : provided list;  (** The capabilities its type provides, each with its [impl]. *)
}

and provided = { capability : Path.t; impl : Path.t; arguments : Types.substitution }

and block = {
  statements : statement list;
  value : expression option;  (** What the block gives; none when it gives [Unit] or never ends. *)
}

and statement = { id : id; origin : origin; kind : statement_kind }

and statement_kind =
  | Let of { pattern : pattern; value : expression; otherwise : block option }
      (** [otherwise] is the [else] of a [let] whose pattern can fail; it leaves the block. *)
  | Evaluate of expression
  | Assign of { target : place; value : expression }
  | Update of { target : place; value : expression }
      (** A compound assignment: the target takes [value], in which [Updating] is what the target
          holds before. The target is worked out once. *)
  | For of {
      pattern : pattern;
      drive : drive;
      clauses : loop_clause list;
      body : block;
      parallel : bool;
    }
  | While of { condition : expression; clauses : loop_clause list; body : block }
  | Parallel of statement list
  | Proof of block
  | Assert of expression
  | Yield of { mode : Types.mode; part : operand }
      (** The part a lending or yielding method gives, a place or a value it made, lent as the
          method's signature says. *)

(** What a [for] loop goes over. *)
and drive =
  | Count of { start : expression; stop : expression; inclusive : bool }
      (** A range of built-in integers or characters. *)
  | Each of expression
      (** A [Call] of a yielding method, with the loop's mode: [each] where the loop names a value,
          or the call the loop wrote out. *)
  | Pull of { cursor : expression; next : callee }  (** A cursor, pulled until it ends. *)

and loop_clause =
  | Invariant of expression
  | Decreases of expression list
  | Cost of cost  (** What the loop has spent since it started, at each iteration. *)

and cost = { amortized : bool; resource : Syntax.resource; bound : bound }
and bound = Finite | Order_of of expression | At_most of expression | Exactly of expression
and arm = { patterns : pattern list; guard : expression option; body : block; origin : origin }
and pattern = { id : id; origin : origin; type_ : Types.ty; kind : pattern_kind }

and pattern_kind =
  | Anything
  | Bind of { local : local; name : string; mutable_ : bool; mode : Types.mode }
      (** [mode] is how the binding holds what it matched: its own, or a part lent to it. *)
  | Variant of { variant : string; fields : (string * pattern) list }
      (** The fields it looks at, by name, in the order the variant declares them. *)
  | Record of (string * pattern) list
  | Literal of expression  (** An [Integer] or a [Boolean] node, compared as built-in values. *)
  | Within of { start : expression; stop : expression; inclusive : bool }
      (** A range of literals or constants. *)
  | Equals of { value : expression; equal : callee }
      (** A constant or a string, compared with the type's [Equal]. *)
  | Alternatives of pattern list

(** A definition's parts, each checked on its own. *)

type parameter = {
  local : local;
  name : string;
  mode : Types.mode;
  type_ : Types.ty;
  default : expression option;
  accepts : accepts option;
}

and accepts = { inputs : (local * string) list; requires : expression list }
(** What a parameter of a function type requires of each call through it, when the type names its
    inputs: [transform: (fn(element: Element) -> Output requires ...)]. *)

type contract = {
  requires : expression list;
  ensures : expression list;
  decreases : expression list;
  costs : cost list;
}

type law = { name : string; parameters : parameter list; requires : expression list; body : block }

type parts =
  | Function of { parameters : parameter list; contract : contract; body : block option }
      (** A function, a method, or a theorem; [body] is absent for a method a trait or a capability
          only declares. *)
  | Type of {
      defaults : (string option * string * expression) list;
          (** Each field's default, by its variant, if it is in one, and its name. *)
      invariants : expression list;
      potential : expression option;
    }
  | Trait of law list
  | Constant of expression
  | Test of block
  | Law_proof of block
  | Nothing  (** An [impl] or a capability, which holds only its methods. *)

(** Two parts of one collection lent side by side, which the prover shows do not overlap. Every
    other obligation is a node: [From_integer], [Widen], and a [Match] whose guards must cover. *)
type obligation = Disjoint of { first : id; second : id }

type t = {
  parts : parts;
  nodes : int;  (** One more than the largest id. *)
  made : int;  (** How many locals the checker made. *)
  obligations : obligation list;
}
