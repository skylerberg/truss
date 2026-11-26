let find_signature : Logic.symbol -> (Logic.sort list * Logic.sort) option = function
  | Apply sorts -> (
      match List.rev sorts with output :: inputs -> Some (List.rev inputs, output) | [] -> None)
  | Callback_ensures sorts -> Some (sorts, Bool)
  | Equal ty ->
      let sort = Encoding.sort_of ty in
      Some ([ sort; sort ], Bool)
  | Valid ty -> Some ([ Encoding.sort_of ty ], Bool)
  | Rank ty | Capacity ty | Slack ty | Potential ty -> Some ([ Encoding.sort_of ty ], Int)
  | Model (Named { arguments = [ Type element ]; _ } as ty) ->
      Some ([ Encoding.sort_of ty ], Encoding.sort_of (Encoding.make_sequence_type element))
  | Sequence_range element ->
      let sequence = Encoding.sort_of (Encoding.make_sequence_type element) in
      Some ([ sequence; Int; Int ], sequence)
  | Compare_bytes_order ->
      let bytes = Encoding.sort_of (Encoding.make_sequence_type (Types.make_builtin UInt8)) in
      Some ([ bytes; bytes ], Int)
  | Handle_descriptor -> Some ([ Encoding.sort_of (Types.make_builtin Handle) ], Int)
  | Callback_cost { sort; _ } -> Some ([ sort ], Int)
  | Bit_count _ | Integer_log -> Some ([ Int ], Int)
  | Integer_power -> Some ([ Int; Int ], Int)
  | Potential_measure _ -> Some ([], Function_sort 1)
  | Literal { type_; _ } -> Some ([], Encoding.sort_of type_)
  | Block_bytes _ | Method_cost _ | Libc_number _ | Generic_value _ -> Some ([], Int)
  | System _ -> Some ([], Bool)
  | Model _ | Variable _ | Function _ | Limited _ | Function_value _ | Constant _ | Evaluated _
  | Named_term _ | Lambda _ | Lifted _ | Unspecified _ | Constructor _ | Field _ | Unit | Range_of _
  | Opaque_operation _ | Cost_most ->
      None
