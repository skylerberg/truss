type limit = Minimum | Maximum

type t =
  | Name of string
  | Integer of Z.t
  | Boolean of bool
  | Field of { receiver : t; field : string }
  | Limit of { type_ : Types.ty; limit : limit }
  | Negated of t
  | Sum of t list
  | Product of t list
  | Difference of t * t
  | Quotient of t * t
  | Compared of { left : t; comparison : Language.Comparison.t; right : t }
  | Not of t
  | All of t list
  | Any of t list
  | Implies of { premise : t; conclusion : t }
