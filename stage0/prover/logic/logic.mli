type sort = Int | Bool | Float of int * int | Type_sort of Types.ty | Function_sort of int

module Symbol : sig
  type 'term t =
    | Variable of { label : string; numbers : int list }
    | Function of { callee : Path.t; instance : Types.argument list }
    | Limited of { callee : Path.t; instance : Types.argument list }
    | Function_value of { callee : Path.t; instance : Types.argument list }
    | Constant of Path.t
    | Generic_value of { owner : Path.t; name : string }
    | Text_literal of { type_ : Types.ty; text : string }
    | Named_term of 'term
    | Lambda of { sorts : sort list; definition : 'term }
    | Lifted of 'term t
    | Unspecified of 'term t
    | Constructor of { type_ : Types.ty; variant : string option }
    | Field of { type_ : Types.ty; variant : string option; field : string }
    | Unit
    | Apply of sort list
    | Equal of Types.ty
    | Valid of Types.ty
    | Rank of Types.ty
    | Capacity of Types.ty
    | Model of Types.ty
    | Slack of Types.ty
    | Potential of Types.ty
    | Potential_measure of Types.ty
    | Block_bytes of { type_ : Types.ty; variant : string option }
    | Callback_cost of { metric : Metric.t; sort : sort }
    | Method_cost of {
        metric : Metric.t;
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
    | Cost_log
    | Cost_power
    | Reached of int
    | Condition of int
end

type term =
  | Symbol of symbol
  | Integer of Z.t
  | Boolean of bool
  | Bits of int * Z.t
  | Apply of symbol * term list
  | Is of symbol * term
  | Operation of string * term list
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
val conjunction : term list -> term
val disjunction : term list -> term
val truncated_divide : term -> term -> term
val truncated_remainder : term -> term -> term
val integer_of_bits : is_signed:bool -> width:int -> term -> term
val mentions : symbol list -> term -> bool
val list_free_constants : term -> symbol list
val has_quantifier : term -> bool
val forall : ?trigger:term list -> (symbol * sort) list * term -> term
val substitute : (symbol * term) list -> term -> term
val replace : from:term -> into:term -> term -> term
val has_untriggered_fact : query -> bool
val prune : query -> query
val show_query : ?cardinality_bound:int -> query -> string
val has_uninterpreted_sort : query -> bool

type rendering

val render : query -> rendering
val rendered_text : rendering -> string
val render_term : rendering -> term -> string option
val list_symbols : rendering -> (symbol * string) list
val list_members : query -> (string * (symbol * symbol list)) list
val hash : string -> string
val show_symbol : symbol -> string
