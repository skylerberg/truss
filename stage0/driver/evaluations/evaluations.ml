let rec make_value : Lowered.static_value -> Prover.Obligation.value = function
  | Static_scalar (Bool holds) -> Boolean holds
  | Static_scalar (Integer (_, number)) -> Integer number
  | Static_scalar (Character scalar) -> Integer (Z.of_int scalar)
  | Static_scalar (Float32 bits) -> Float (Int32.float_of_bits bits)
  | Static_scalar (Float64 bits) -> Float (Int64.float_of_bits bits)
  | Static_scalar _ ->
      Compiler_bug.raise_bug ~stage:"Evaluations" "an evaluation gave a scalar that is no value"
  | Static_record fields -> Constructed { variant = None; fields = make_fields fields }
  | Static_variant (variant, fields) ->
      Constructed { variant = Some variant; fields = make_fields fields }
  | Static_array elements | Static_storage { elements; _ } | Static_view { elements; _ } ->
      Elements (List.map make_value elements)

and make_fields fields = List.map (fun (name, value) -> (name, make_value value)) fields

let make_run : Lowered.static_value Backend.ran -> Prover.Obligation.run = function
  | Ran value -> Evaluated (make_value value)
  | Unfinished report -> Unfinished report
  | Stopped report -> Failed report

let run backend evaluations =
  List.combine evaluations
    (List.map make_run
       (Backend.evaluate backend
          (List.map
             (function
               | Prover.Obligation.Constant_value path -> Lowered.Item.Constant path
               | Assertion { definition; condition } -> Assertion { definition; condition })
             evaluations)))
