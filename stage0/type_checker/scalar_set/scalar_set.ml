type member =
  | Int8
  | Int16
  | Int32
  | Int64
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | Float32
  | Float64
  | Integer
  | Character

type t = int

let all_members =
  [ Int8; Int16; Int32; Int64; UInt8; UInt16; UInt32; UInt64; Float32; Float64; Integer; Character ]

let read_bit member =
  let rec find position = function
    | [] -> invalid_arg "Scalar_set.read_bit"
    | first :: rest -> if first = member then 1 lsl position else find (position + 1) rest
  in
  find 0 all_members

let empty = 0
let make members = List.fold_left (fun set member -> set lor read_bit member) empty members
let mem member set = set land read_bit member <> 0
let list_members set = List.filter (fun member -> mem member set) all_members
let inter = ( land )
let union = ( lor )
let is_empty set = set = empty
let is_subset set ~of_ = set land lnot of_ = empty
let equal = Int.equal
let find_single set = match list_members set with [ member ] -> Some member | _ -> None
let signed_integers = make [ Int8; Int16; Int32; Int64 ]
let unsigned_integers = make [ UInt8; UInt16; UInt32; UInt64 ]
let fixed_width_integers = union signed_integers unsigned_integers
let floats = make [ Float32; Float64 ]
let code_numbers = union fixed_width_integers floats
let negatable = union signed_integers (union floats (make [ Integer ]))

let convert_to_builtin : member -> Intrinsic.builtin = function
  | Int8 -> Int8
  | Int16 -> Int16
  | Int32 -> Int32
  | Int64 -> Int64
  | UInt8 -> UInt8
  | UInt16 -> UInt16
  | UInt32 -> UInt32
  | UInt64 -> UInt64
  | Float32 -> Float32
  | Float64 -> Float64
  | Integer -> Integer
  | Character -> Character

let make_type = function
  | Integer -> Types.Integer
  | member -> Types.make_builtin (convert_to_builtin member)

let find_member (type_ : Types.ty) =
  match type_ with
  | Types.Integer -> Some Integer
  | _ ->
      Option.bind (Types.find_builtin type_) (fun builtin ->
          List.find_opt (fun member -> convert_to_builtin member = builtin) all_members)

let find_range member =
  if mem member fixed_width_integers then Types.find_integer_range (make_type member) else None

let find_common_range set =
  List.fold_left
    (fun common member ->
      match (common, find_range member) with
      | Some (low, high), Some (other_low, other_high) ->
          Some (Z.max low other_low, Z.min high other_high)
      | None, range | range, None -> range)
    None (list_members set)

let list_fitting_integers value =
  make
    (Integer
    :: List.filter
         (fun member ->
           match find_range member with
           | Some (low, high) -> Z.geq value low && Z.leq value high
           | None -> false)
         (list_members fixed_width_integers))

let find_sealed_implementors trait =
  if Well_known.is Signed_integer trait then Some signed_integers
  else if Well_known.is Unsigned_integer trait then Some unsigned_integers
  else if Well_known.is Fixed_width_integer trait then Some fixed_width_integers
  else if Well_known.is Floating_point trait then Some floats
  else None

let find_bound_implementors (bounds : Types.trait_reference list) =
  List.fold_left
    (fun implementors (bound : Types.trait_reference) ->
      match (implementors, find_sealed_implementors bound.trait) with
      | Some implementors, Some these -> Some (inter implementors these)
      | None, these | these, None -> these)
    None bounds

let choose_default set =
  List.find_opt (fun member -> mem member set) [ Integer; Int64; UInt64; Float64 ]

let describe set =
  match find_single set with
  | Some member -> Printf.sprintf "`%s`" (Types.show (make_type member))
  | None ->
      if is_subset set ~of_:floats then "a float"
      else if is_subset set ~of_:unsigned_integers then "an unsigned integer"
      else if is_subset set ~of_:(union signed_integers (make [ Integer ])) then "a signed integer"
      else if is_subset set ~of_:(union fixed_width_integers (make [ Integer ])) then "an integer"
      else "a number"
