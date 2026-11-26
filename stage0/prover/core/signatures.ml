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

let list_axioms : Logic.symbol -> Logic.term list = function
  | Rank ty as symbol ->
      let each = Logic.Symbol.Variable { label = "ranked.value"; numbers = [] } in
      [
        Logic.forall
          ( [ (each, Encoding.sort_of ty) ],
            Logic.less_equal (Logic.int 0) (Logic.Apply (symbol, [ Logic.Symbol each ])) );
      ]
  | Generic_value _ as symbol ->
      [ Encoding.make_in_range (Types.make_builtin UInt64) (Logic.Symbol symbol) ]
  | Libc_number number as symbol ->
      [
        Encoding.make_in_range
          (Types.make_builtin (Intrinsic.convert_libc_scalar (Libc.classify_number number)))
          (Logic.Symbol symbol);
      ]
  | System runtime as symbol ->
      let alternatives : Intrinsic.runtime list =
        match runtime with
        | System_is_os _ -> List.map (fun os -> Intrinsic.System_is_os os) Libc.oses
        | System_is_architecture _ ->
            List.map
              (fun architecture -> Intrinsic.System_is_architecture architecture)
              Libc.architectures
        | _ -> []
      in
      List.filter_map
        (fun other ->
          if other = runtime then None
          else Some Logic.(not_ (Symbol symbol &&& Symbol (Logic.Symbol.System other))))
        alternatives
  | Block_bytes _ as symbol -> [ Logic.less_equal (Logic.int 1) (Logic.Symbol symbol) ]
  | Compare_bytes_order as symbol ->
      let bytes = Encoding.sort_of (Encoding.make_sequence_type (Types.make_builtin UInt8)) in
      let variable label = Logic.Symbol.Variable { label; numbers = [] } in
      let first = variable "bytes.first"
      and second = variable "bytes.second"
      and third = variable "bytes.third" in
      let order left right = Logic.Apply (symbol, [ Logic.Symbol left; Logic.Symbol right ]) in
      let over names body = Logic.forall (List.map (fun name -> (name, bytes)) names, body) in
      [
        over [ first; second; third ]
          Logic.(
            less (order first second) (int 0)
            &&& less (order second third) (int 0)
            ==> less (order first third) (int 0));
        over [ first ] (Logic.equal (order first first) (Logic.int 0));
        over [ first; second ]
          Logic.(
            less_equal (int (-1)) (order first second)
            &&& less_equal (order first second) (int 1)
            &&& (equal (order first second) (int 0) ==> equal (Symbol first) (Symbol second))
            &&& equal (order second first) (negate (order first second)));
      ]
  | _ -> []
