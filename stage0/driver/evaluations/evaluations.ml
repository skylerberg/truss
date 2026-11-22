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

let make_run : (Lowered.static_value Backend.ran, string) result -> Prover.Obligation.run = function
  | Ok (Ran value) -> Evaluated (make_value value)
  | Ok (Unfinished report) -> Unfinished report
  | Ok (Stopped report) | Error report -> Failed report

let run backend evaluations =
  List.map
    (fun (evaluation : Prover.Obligation.evaluation) ->
      ( evaluation,
        make_run
          (Backend.evaluate backend
             (match evaluation with
             | Constant_value path -> Constant path
             | Assertion { definition; condition } -> Assertion { definition; condition })) ))
    evaluations
