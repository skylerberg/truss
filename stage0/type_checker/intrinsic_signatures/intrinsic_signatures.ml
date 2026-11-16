let parameter operation name : Types.parameter =
  { owner = Intrinsic.operation_path operation; name }

let storage element =
  Types.Named { path = Intrinsic.builtin_path Storage; arguments = [ Types.Type element ] }

let view element =
  Types.Named { path = Intrinsic.builtin_path View; arguments = [ Types.Type element ] }

let libc_scalar scalar = Types.make_builtin (Intrinsic.libc_builtin scalar)

let sequence element =
  Types.Named { path = Well_known.path Sequence; arguments = [ Types.Type element ] }

let signature (operation : Intrinsic.operation) : Types.signature =
  let generic name = { Types.generic = parameter operation name; kind = Type_generic [] } in
  let bounded known name =
    {
      Types.generic = parameter operation name;
      kind =
        Type_generic [ { trait = Well_known.path known; trait_arguments = []; associated = [] } ];
    }
  in
  let parameter_type name = Types.Parameter (parameter operation name) in
  let input ?(mode = Types.Read) name type_ = { Types.name; mode; type_; has_default = false } in
  let make ?(generics = []) ?(output = Types.Returns Types.unit) parameters : Types.signature =
    {
      generics = List.map generic generics;
      receiver = None;
      parameters;
      output;
      uses = Types.no_capabilities;
      terminates = true;
      specification_only = false;
      capture_free_parameters = [];
    }
  in
  let value = parameter_type "Value" and element = parameter_type "Element" in
  let uint64 = Types.make_builtin UInt64 and bool = Types.bool in
  let binary output =
    make ~generics:[ "Value" ] ~output:(Returns output) [ input "left" value; input "right" value ]
  in
  let unary output = make ~generics:[ "Value" ] ~output:(Returns output) [ input "value" value ] in
  let over_array ~output parameters =
    let count = parameter operation "count" in
    let array =
      Types.Named
        {
          path = Intrinsic.builtin_path Array;
          arguments = [ Types.Type element; Types.Value (Value_parameter count) ];
        }
    in
    {
      (make ~output:(output array) (parameters array)) with
      generics = [ generic "Element"; { Types.generic = count; kind = Value_generic } ];
    }
  in
  let work_item = Types.make_builtin UInt64 in
  let work =
    Types.Function
      {
        inputs = [ (Read, work_item) ];
        output = Types.unit;
        uses = Types.no_capabilities;
        costs = [];
      }
  in
  let with_storage ?(mode = Types.Read) ?(output = Types.Returns Types.unit) rest =
    make ~generics:[ "Element" ] ~output (input ~mode "storage" (storage element) :: rest)
  in
  let with_plain_storage rest =
    { (with_storage ~mode:Mut rest) with generics = [ bounded Plain "Element" ] }
  in
  match operation with
  | Add | Subtract | Multiply | Divide | Remainder | Wrapping_add | Wrapping_subtract
  | Wrapping_multiply | Bit_and | Bit_or | Bit_xor | Multiply_high ->
      binary value
  | Add_overflows | Subtract_overflows | Multiply_overflows | Equal | Less | Ieee_equal | Ieee_less
    ->
      binary bool
  | Negate | Complement | Square_root | Floor | Ceiling | Truncate | Round_to_even | Swap_bytes ->
      unary value
  | Is_nan -> unary bool
  | Leading_zeros | Trailing_zeros | Count_ones -> unary uint64
  | Shift_left | Shift_right ->
      make ~generics:[ "Value"; "Amount" ] ~output:(Returns value)
        [ input "value" value; input "amount" (parameter_type "Amount") ]
  | Rotate_left | Rotate_right ->
      make ~generics:[ "Value" ] ~output:(Returns value)
        [ input "value" value; input "amount" uint64 ]
  | Convert ->
      make ~generics:[ "Source"; "Target" ]
        ~output:(Returns (parameter_type "Target"))
        [ input "value" (parameter_type "Source") ]
  | Fits ->
      make ~generics:[ "Source"; "Target" ] ~output:(Returns bool)
        [ input "value" (parameter_type "Source") ]
  | Fused_multiply_add ->
      make ~generics:[ "Value" ] ~output:(Returns value)
        [ input "value" value; input "multiplier" value; input "addend" value ]
  | To_bits ->
      make ~generics:[ "Value"; "Bits" ]
        ~output:(Returns (parameter_type "Bits"))
        [ input "value" value ]
  | From_bits ->
      make ~generics:[ "Bits"; "Value" ] ~output:(Returns value)
        [ input "bits" (parameter_type "Bits") ]
  | Compare_bytes ->
      make
        ~output:(Returns (Types.make_builtin Int8))
        [
          input "left" (view (Types.make_builtin UInt8));
          input "right" (view (Types.make_builtin UInt8));
        ]
  | Storage_empty -> make ~generics:[ "Element" ] ~output:(Returns (storage element)) []
  | Storage_with_capacity ->
      make ~generics:[ "Element" ] ~output:(Returns (storage element)) [ input "capacity" uint64 ]
  | Storage_length | Storage_capacity -> with_storage ~output:(Returns uint64) []
  | Storage_set_capacity -> with_storage ~mode:Mut [ input "capacity" uint64 ]
  | Storage_lengthen -> with_plain_storage [ input "by" uint64 ]
  | Storage_shorten -> with_plain_storage [ input "length" uint64 ]
  | Storage_push -> with_storage ~mode:Mut [ input ~mode:Own "value" element ]
  | Storage_pop -> with_storage ~mode:Mut ~output:(Returns element) []
  | Storage_insert ->
      with_storage ~mode:Mut [ input "index" uint64; input ~mode:Own "value" element ]
  | Storage_remove -> with_storage ~mode:Mut ~output:(Returns element) [ input "index" uint64 ]
  | Storage_swap -> with_storage ~mode:Mut [ input "first" uint64; input "second" uint64 ]
  | Storage_from_array ->
      over_array
        ~output:(fun _ -> Returns (storage element))
        (fun array -> [ input ~mode:Own "array" array ])
  | Array_from_storage ->
      over_array
        ~output:(fun array -> Returns array)
        (fun _ -> [ input ~mode:Own "storage" (storage element) ])
  | Array_view ->
      over_array ~output:(fun _ -> Returns (view element)) (fun array -> [ input "array" array ])
  | Array_at_mut ->
      over_array
        ~output:(fun _ -> Lends (Mut, element))
        (fun array -> [ input ~mode:Mut "array" array; input "index" uint64 ])
  | Storage_at -> with_storage ~output:(Lends (Read, element)) [ input "index" uint64 ]
  | Storage_at_mut -> with_storage ~mode:Mut ~output:(Lends (Mut, element)) [ input "index" uint64 ]
  | Storage_view -> with_storage ~output:(Returns (view element)) []
  | View_length ->
      make ~generics:[ "Element" ] ~output:(Returns uint64) [ input "view" (view element) ]
  | View_at ->
      make ~generics:[ "Element" ]
        ~output:(Lends (Read, element))
        [ input "view" (view element); input "index" uint64 ]
  | View_at_mut ->
      make ~generics:[ "Element" ]
        ~output:(Lends (Mut, element))
        [ input ~mode:Mut "view" (view element); input "index" uint64 ]
  | View_swap ->
      make ~generics:[ "Element" ]
        [ input ~mode:Mut "view" (view element); input "first" uint64; input "second" uint64 ]
  | View_slice ->
      make ~generics:[ "Element" ]
        ~output:(Returns (view element))
        [ input "view" (view element); input "start" uint64; input "stop" uint64 ]
  | Storage_model ->
      { (with_storage ~output:(Returns (sequence element)) []) with specification_only = true }
  | Array_model ->
      {
        (over_array
           ~output:(fun _ -> Returns (sequence element))
           (fun array -> [ input "array" array ]))
        with
        specification_only = true;
      }
  | View_model ->
      {
        (make ~generics:[ "Element" ]
           ~output:(Returns (sequence element))
           [ input "view" (view element) ])
        with
        specification_only = true;
      }
  | View_address ->
      make ~generics:[ "Element" ] ~output:(Returns uint64) [ input "view" (view element) ]
  | Crash ->
      make ~output:(Returns Types.Never)
        [ input "message" (Types.Named { path = Well_known.path String_slice; arguments = [] }) ]
  | Handle_from ->
      make
        ~output:(Returns (Types.make_builtin Handle))
        [ input "descriptor" (Types.make_builtin Int32) ]
  | Handle_descriptor ->
      make
        ~output:(Returns (Types.make_builtin Int32))
        [ input "handle" (Types.make_builtin Handle) ]
  | Handle_release ->
      make
        ~output:(Returns (Types.make_builtin Int32))
        [ input ~mode:Own "handle" (Types.make_builtin Handle) ]
  | Run_test -> make [ input "index" (Types.make_builtin UInt32) ]
  | Coroutine_start ->
      {
        (make ~output:(Returns uint64) [ input ~mode:Own "work" work; input "item" work_item ]) with
        capture_free_parameters = [ "work" ];
      }
  | Tasks_spawn ->
      {
        (make ~output:(Returns bool)
           [ input "group" work_item; input ~mode:Own "work" work; input "item" work_item ])
        with
        capture_free_parameters = [ "work" ];
      }
  | Holds_invariant ->
      make ~generics:[ "Value" ] ~output:(Returns bool)
        [ input "value" value; input "clause" uint64 ]
  | Shared_new | Shared_update | Shared_key -> (
      let shared =
        Types.Named { path = Intrinsic.builtin_path Shared; arguments = [ Types.Type value ] }
      in
      match operation with
      | Shared_new ->
          {
            (make ~output:(Returns shared) [ input ~mode:Own "value" value ]) with
            generics = [ bounded Storable "Value" ];
          }
      | Shared_update ->
          let change : Types.function_type =
            {
              inputs = [ (Mut, value); (Own, parameter_type "Input") ];
              output = parameter_type "Result";
              uses = Types.no_capabilities;
              costs = [];
            }
          in
          {
            (make
               ~output:(Returns (parameter_type "Result"))
               [
                 input "shared" shared;
                 input ~mode:Own "input" (parameter_type "Input");
                 input "change" (Types.Function change);
               ])
            with
            generics = [ bounded Storable "Value"; generic "Input"; bounded Storable "Result" ];
          }
      | _ ->
          {
            (make ~output:(Returns (Types.make_builtin UInt64)) [ input "shared" shared ]) with
            generics = [ bounded Storable "Value" ];
          })
  | Coroutine_resume -> make ~output:(Returns bool) [ input "coroutine" uint64 ]
  | Coroutine_suspend -> make []
  | Report_tests_to -> make [ input "descriptor" (Types.make_builtin Int32) ]
  | Live_blocks -> make ~output:(Returns uint64) []
  | Environment_entry ->
      make
        ~output:(Returns (view (Types.make_builtin UInt8)))
        [ input "index" uint64; input ~mode:Mut "is_present" bool ]
  | System_is_os _ | System_is_architecture _ -> make ~output:(Returns bool) []
  | Libc function_ ->
      let { Libc.parameters; result; _ } = Libc.signature function_ in
      let presence = match result with Text -> [ input ~mode:Mut "is_present" bool ] | _ -> [] in
      make
        ~output:
          (Returns
             (match result with
             | Returns scalar | Points_at scalar -> libc_scalar scalar
             | Text -> view (Types.make_builtin UInt8)
             | Never -> Types.Never))
        (List.concat_map
           (fun (name, (passes : Libc.passes)) ->
             match passes with
             | Value scalar -> [ input name (libc_scalar scalar) ]
             | Elements (scalar, _) -> [ input name (view (libc_scalar scalar)) ]
             | Room (scalar, _) | Elements_to_change (scalar, _) ->
                 [ input ~mode:Mut name (storage (libc_scalar scalar)) ]
             | Written (scalar, names) ->
                 List.map (fun name -> input ~mode:Mut name (libc_scalar scalar)) names
             | Always _ | Fixed _ -> [])
           parameters
        @ presence)
  | Libc_number number -> make ~output:(Returns (libc_scalar (Libc.number_type number))) []

type time = Constant_time | Linear_in of int | Unbounded_time
type amount = Argument of int | Generic of string
type allocations = No_allocations | One_if_positive of amount | Unknown_allocations
type cost = { time : time; allocations : allocations }

let cost (operation : Intrinsic.operation) =
  match operation with
  | Add | Subtract | Multiply | Divide | Remainder | Negate | Wrapping_add | Wrapping_subtract
  | Wrapping_multiply | Add_overflows | Subtract_overflows | Multiply_overflows | Equal | Less
  | Ieee_equal | Ieee_less | Bit_and | Bit_or | Bit_xor | Complement | Shift_left | Shift_right
  | Convert | Fits | Square_root | Fused_multiply_add | Floor | Ceiling | Truncate | Round_to_even
  | To_bits | From_bits | Is_nan | Leading_zeros | Trailing_zeros | Count_ones | Swap_bytes
  | Rotate_left | Rotate_right | Multiply_high | Storage_empty | Storage_length | Storage_capacity
  | Storage_pop | Storage_swap | Storage_at | Storage_at_mut | Storage_view | View_length | View_at
  | View_at_mut | View_swap | View_slice | View_address | Array_view | Array_at_mut
  | Array_from_storage | Storage_model | View_model | Array_model | Crash | Storage_lengthen
  | Storage_shorten | Storage_push | Handle_from | Handle_descriptor | Handle_release
  | Report_tests_to | Live_blocks | Libc_number _ | System_is_os _ | System_is_architecture _ ->
      { time = Constant_time; allocations = No_allocations }
  | Holds_invariant -> { time = Unbounded_time; allocations = Unknown_allocations }
  | Compare_bytes | Storage_remove | Storage_insert | Environment_entry ->
      { time = Linear_in 0; allocations = No_allocations }
  | Storage_set_capacity -> { time = Linear_in 0; allocations = Unknown_allocations }
  | Storage_with_capacity -> { time = Constant_time; allocations = One_if_positive (Argument 0) }
  | Storage_from_array -> { time = Constant_time; allocations = One_if_positive (Generic "count") }
  | Run_test | Libc _ | Coroutine_start | Coroutine_resume | Coroutine_suspend | Tasks_spawn
  | Shared_new | Shared_update | Shared_key ->
      { time = Unbounded_time; allocations = Unknown_allocations }
