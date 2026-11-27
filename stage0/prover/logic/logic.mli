type sort = Int | Bool | Float of int * int | Type_sort of Types.ty | Function_sort of int
type evaluation = Constant_value of Path.t | Assertion of { definition : Path.t; condition : int }

module Symbol : sig
  type 'term t =
    | Variable of { label : string; numbers : int list }
    | Function of { callee : Path.t; type_arguments : Types.argument list }
    | Limited of { callee : Path.t; type_arguments : Types.argument list }
    | Function_value of { callee : Path.t; type_arguments : Types.argument list }
    | Constant of { path : Path.t; type_arguments : Types.argument list }
    | Evaluated of evaluation
    | Generic_value of { owner : Path.t; name : string }
    | Literal of { type_ : Types.ty; value : Language.Literal.t }
    | Named_term of 'term
    | Lambda of { sorts : sort list; definition : 'term }
    | Lifted of 'term t
    | Unspecified of 'term t
    | Constructor of { type_ : Types.ty; variant : string option }
    | Field of { type_ : Types.ty; variant : string option; field : string }
    | Unit
    | Apply of sort list
    | Callback_ensures of sort list
    | Equal of Types.ty
    | Valid of Types.ty
    | Rank of Types.ty
    | Capacity of Types.ty
    | Range_of of Types.ty
    | Model of Types.ty
    | Sequence_range of Types.ty
    | Slack of Types.ty
    | Potential of Types.ty
    | Potential_measure of Types.ty
    | Block_bytes of { type_ : Types.ty; variant : string option }
    | Callback_cost of { metric : Language.Metric.t; sort : sort }
    | Method_cost of {
        metric : Language.Metric.t;
        method_ : Path.t;
        trait_arguments : Types.argument list;
        self_type : Types.ty;
      }
    | Opaque_operation of {
        operation : Intrinsic.scalar;
        type_ : Types.ty;
        integer : (int * bool) option;
      }
    | Bit_count of { count : Intrinsic.scalar; width : int }
    | System of Intrinsic.runtime
    | Libc_number of Libc.number
    | Handle_descriptor
    | Compare_bytes_order
    | Cost_most
    | Integer_log
    | Integer_power
end

type rounding_mode = Nearest_ties_to_even | Toward_positive | Toward_negative | Toward_zero

type operator =
  | Not
  | And
  | Or
  | Implies
  | Equal
  | Ite
  | Negate
  | Add
  | Subtract
  | Multiply
  | Div
  | Mod
  | Power
  | Less
  | Less_equal
  | Greater
  | Greater_equal
  | To_real
  | Int2bv of { width : int }
  | Bv2nat
  | Bvnot
  | Bvand
  | Bvor
  | Bvxor
  | Bvshl
  | Bvlshr
  | Bvashr
  | Bvsub
  | Concat
  | Extract of { high : int; low : int }
  | Fp
  | Fp_neg
  | Fp_add of rounding_mode
  | Fp_sub of rounding_mode
  | Fp_mul of rounding_mode
  | Fp_div of rounding_mode
  | Fp_fma of rounding_mode
  | Fp_sqrt of rounding_mode
  | Fp_round_to_integral of rounding_mode
  | Fp_eq
  | Fp_lt
  | Fp_leq
  | Fp_is_nan
  | To_fp of { exponent : int; significand : int; rounding_mode : rounding_mode option }
  | Fp_to_sbv of { width : int; rounding_mode : rounding_mode }
  | Fp_to_ubv of { width : int; rounding_mode : rounding_mode }

type term =
  | Symbol of symbol
  | Integer of Z.t
  | Boolean of bool
  | Bits of int * Z.t
  | Apply of symbol * term list
  | Is of symbol * term
  | Operation of operator * term list
  | Forall of (symbol * sort) list * term list * term
  | Exists of (symbol * sort) list * term

and symbol = term Symbol.t

type declaration =
  | Constant of symbol * sort
  | Function of symbol * sort list * sort
  | Definition of { symbol : symbol; parameters : (symbol * sort) list; result : sort; body : term }
  | Datatype of Types.ty * (symbol * (symbol * sort) list) list

type query = { declarations : declaration list; facts : term list; goal : term }

val list_arguments : term -> term list
val map_arguments : (term -> term) -> term -> term
val int : int -> term
val ( &&& ) : term -> term -> term
val ( ||| ) : term -> term -> term
val ( ==> ) : term -> term -> term
val not_ : term -> term
val equal : term -> term -> term
val ite : term -> term -> term -> term
val negate : term -> term
val add : term -> term -> term
val subtract : term -> term -> term
val multiply : term -> term -> term
val larger : term -> term -> term
val at_least_zero : term -> term
val linearize : term -> (term * Z.t) list * Z.t
val combine_linear : (term * Z.t) list * Z.t -> term
val normalize_linear : term -> term
val less : term -> term -> term
val less_equal : term -> term -> term
val greater : term -> term -> term
val greater_equal : term -> term -> term
val conjunction : term list -> term
val disjunction : term list -> term
val truncated_divide : term -> term -> term
val truncated_remainder : term -> term -> term
val integer_of_bits : is_signed:bool -> width:int -> term -> term
val mentions : symbol list -> term -> bool
val decreases_lexicographically : term list -> term list -> term
val is_refuted : term -> bool
val is_valid : term -> bool
val list_free_constants : term -> symbol list
val has_quantifier : term -> bool
val remove_quantified_facts : query -> query
val forall : ?trigger:term list -> (symbol * sort) list * term -> term
val substitute : (symbol * term) list -> term -> term
val replace : from:term -> into:term -> term -> term
val has_untriggered_fact : ?is_counted:(term -> bool) -> query -> bool
val hash_term : term -> int

val prune :
  find_signature:(symbol -> (sort list * sort) option) ->
  list_axioms:(symbol -> term list) ->
  query ->
  query

val declare_derived :
  find_signature:(symbol -> (sort list * sort) option) ->
  list_constructors:(Types.ty -> (symbol * (symbol * sort) list) list option) ->
  query ->
  query

val list_conjunct_queries : query -> query list
val show_term : term -> string
val show_query : query -> string
