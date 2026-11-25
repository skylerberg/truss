type t =
  | Integer of Z.t
  | Boolean of bool
  | Text of string
  | Constructed of { type_ : Path.t; variant : string option; fields : (string * t) list }

type outcome = Known of t | Calls_function | Depends_on_itself | Unevaluated
