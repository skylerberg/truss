type sort = Int | Bool | Float of int * int | Uninterpreted of string

module Symbol : sig
  type 'term t =
    | Variable of { label : string; numbers : int list }
    | Function of { callee : Path.t; instance : string list }
    | Limited of { callee : Path.t; instance : string list }
    | Function_value of { callee : Path.t; instance : string list }
    | Constant of Path.t
    | Generic_value of { owner : Path.t; name : string }
    | Text_literal of { type_key : string; text : string }
    | Named_term of 'term
    | Lambda of { sorts : sort list; definition : 'term }
    | Lifted of 'term t
    | Constructor of { type_key : string; type_name : string; variant : string option }
    | Field of { type_key : string; variant : string option; field : string }
    | Unit
    | Apply of sort list
    | Equal of string
    | Valid of string
    | Rank of string
    | Capacity of string
    | Model of string
    | Slack of string
    | Potential of string
    | Potential_measure of string
    | Block_bytes of { type_key : string; variant : string option }
    | Time of sort
    | Method_time of { method_ : Path.t; self_type : string }
    | Opaque_operation of { operation : string; type_key : string; integer : (int * bool) option }
    | Bit_count of { count : string; width : int }
    | System of string
    | Libc_number of string
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
  | Datatype of string * (symbol * (symbol * sort) list) list

type query = { declarations : declaration list; facts : term list; goal : term }

val arguments : term -> term list
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
val mentions : symbol list -> term -> bool
val free_constants : term -> symbol list
val has_quantifier : term -> bool
val forall : ?trigger:term list -> (symbol * sort) list * term -> term
val substitute : (symbol * term) list -> term -> term
val replace : from:term -> into:term -> term -> term
val has_untriggered_fact : query -> bool
val prune : query -> query
val text : query -> string

type rendering

val render : query -> rendering
val rendered_text : rendering -> string
val term_text : rendering -> term -> string option
val symbols : rendering -> (symbol * string) list
val members : query -> (string * (symbol * symbol list)) list
val hash : string -> string
val show_symbol : symbol -> string
