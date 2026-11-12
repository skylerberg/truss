(* The signatures of [standard::intrinsic]'s operations. Arithmetic and
   comparison are generic over the built-in number type, which code generation
   sees after monomorphization. *)
let parameter operation name : Types.parameter =
  { owner = Intrinsic.operation_path operation; name }

let storage element =
  Types.Named { path = Intrinsic.builtin_path Storage; arguments = [ Types.Type element ] }

let view element =
  Types.Named { path = Intrinsic.builtin_path View; arguments = [ Types.Type element ] }

let libc_scalar scalar = Types.builtin (Intrinsic.libc_builtin scalar)

let sequence element =
  Types.Named { path = Well_known.path Sequence; arguments = [ Types.Type element ] }

let signature (operation : Intrinsic.operation) : Types.signature =
  let generic name = { Types.generic = parameter operation name; kind = Type_generic [] } in
  let parameter_type name = Types.Parameter (parameter operation name) in
  let input ?(mode = Types.Read) name type_ = { Types.name; mode; type_; has_default = false } in
  let make ?(generics = []) ?(output = Types.Returns Types.unit) parameters : Types.signature =
    {
      generics = List.map generic generics;
      receiver = None;
      parameters;
      output;
      uses = [];
      terminates = true;
      specification_only = false;
      stores_functions = [];
      transparent = false;
    }
  in
  let value = parameter_type "Value" and element = parameter_type "Element" in
  let usize = Types.builtin USize and bool = Types.bool in
  let binary output =
    make ~generics:[ "Value" ] ~output:(Returns output) [ input "left" value; input "right" value ]
  in
  let unary output = make ~generics:[ "Value" ] ~output:(Returns output) [ input "value" value ] in
  (* An operation on an [Array[Element, count]], generic over both. *)
  let over_array ?(output = fun _ -> Types.Returns Types.unit) parameters =
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
  (* The work a coroutine or a task runs: a function of one [UInt64]. *)
  let work_item = Types.builtin UInt64 in
  let work =
    Types.Function
      { inputs = [ (Read, work_item) ]; output = Returns Types.unit; uses = []; costs = [] }
  in
  let with_storage ?(mode = Types.Read) ?(output = Types.Returns Types.unit) rest =
    make ~generics:[ "Element" ] ~output (input ~mode "storage" (storage element) :: rest)
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
  | Leading_zeros | Trailing_zeros | Count_ones -> unary usize
  | Shift_left | Shift_right ->
      make ~generics:[ "Value"; "Amount" ] ~output:(Returns value)
        [ input "value" value; input "amount" (parameter_type "Amount") ]
  | Rotate_left | Rotate_right ->
      make ~generics:[ "Value" ] ~output:(Returns value)
        [ input "value" value; input "amount" usize ]
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
        ~output:(Returns (Types.builtin Int8))
        [ input "left" (view (Types.builtin UInt8)); input "right" (view (Types.builtin UInt8)) ]
  | Storage_empty -> make ~generics:[ "Element" ] ~output:(Returns (storage element)) []
  | Storage_with_capacity ->
      make ~generics:[ "Element" ] ~output:(Returns (storage element)) [ input "capacity" usize ]
  | Storage_length | Storage_capacity -> with_storage ~output:(Returns usize) []
  | Storage_set_capacity -> with_storage ~mode:Mut [ input "capacity" usize ]
  | Storage_lengthen -> with_storage ~mode:Mut [ input "by" usize ]
  | Storage_shorten ->
      (* Only elements with nothing to drop can be forgotten. *)
      let plain : Types.trait_reference =
        { trait = Well_known.path Plain; trait_arguments = []; associated = [] }
      in
      {
        (with_storage ~mode:Mut [ input "length" usize ]) with
        generics =
          [ { Types.generic = parameter operation "Element"; kind = Type_generic [ plain ] } ];
      }
  | Storage_push -> with_storage ~mode:Mut [ input ~mode:Own "value" element ]
  | Storage_pop -> with_storage ~mode:Mut ~output:(Returns element) []
  | Storage_insert ->
      with_storage ~mode:Mut [ input "index" usize; input ~mode:Own "value" element ]
  | Storage_remove -> with_storage ~mode:Mut ~output:(Returns element) [ input "index" usize ]
  | Storage_swap -> with_storage ~mode:Mut [ input "first" usize; input "second" usize ]
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
        (fun array -> [ input ~mode:Mut "array" array; input "index" usize ])
  | Storage_at -> with_storage ~output:(Lends (Read, element)) [ input "index" usize ]
  | Storage_at_mut -> with_storage ~mode:Mut ~output:(Lends (Mut, element)) [ input "index" usize ]
  | Storage_view -> with_storage ~output:(Returns (view element)) []
  | Storage_view_mut -> with_storage ~mode:Mut ~output:(Returns (view element)) []
  | View_length ->
      make ~generics:[ "Element" ] ~output:(Returns usize) [ input "view" (view element) ]
  | View_at ->
      make ~generics:[ "Element" ]
        ~output:(Lends (Read, element))
        [ input "view" (view element); input "index" usize ]
  | View_at_mut ->
      make ~generics:[ "Element" ]
        ~output:(Lends (Mut, element))
        [ input ~mode:Mut "view" (view element); input "index" usize ]
  | View_swap ->
      make ~generics:[ "Element" ]
        [ input ~mode:Mut "view" (view element); input "first" usize; input "second" usize ]
  | Storage_take_view -> with_storage ~mode:Mut [ input "view" (view element); input "start" usize ]
  | View_take_view ->
      make ~generics:[ "Element" ]
        [ input ~mode:Mut "view" (view element); input "part" (view element); input "start" usize ]
  | Array_take_view ->
      over_array (fun array ->
          [ input ~mode:Mut "array" array; input "view" (view element); input "start" usize ])
  | View_slice ->
      make ~generics:[ "Element" ]
        ~output:(Returns (view element))
        [ input "view" (view element); input "start" usize; input "stop" usize ]
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
      make ~generics:[ "Element" ] ~output:(Returns usize) [ input "view" (view element) ]
  | Crash ->
      make ~output:(Returns Types.Never)
        [ input "message" (Types.Named { path = Well_known.path String_slice; arguments = [] }) ]
  | Handle_from ->
      make ~output:(Returns (Types.builtin Handle)) [ input "descriptor" (Types.builtin Int32) ]
  | Handle_descriptor ->
      make ~output:(Returns (Types.builtin Int32)) [ input "handle" (Types.builtin Handle) ]
  | Handle_release ->
      make
        ~output:(Returns (Types.builtin Int32))
        [ input ~mode:Own "handle" (Types.builtin Handle) ]
  | Run_test -> make [ input "index" (Types.builtin UInt32) ]
  | Coroutine_start ->
      {
        (make ~output:(Returns usize) [ input ~mode:Own "work" work; input "item" work_item ]) with
        stores_functions = [ "work" ];
      }
  | Tasks_spawn ->
      {
        (make ~output:(Returns bool)
           [ input "group" work_item; input ~mode:Own "work" work; input "item" work_item ])
        with
        stores_functions = [ "work" ];
      }
  | Shared_new | Shared_update | Shared_key -> (
      let storable : Types.trait_reference =
        { trait = Well_known.path Storable; trait_arguments = []; associated = [] }
      in
      let bounded name =
        { Types.generic = parameter operation name; kind = Type_generic [ storable ] }
      in
      let shared =
        Types.Named { path = Intrinsic.builtin_path Shared; arguments = [ Types.Type value ] }
      in
      match operation with
      | Shared_new ->
          {
            (make ~output:(Returns shared) [ input ~mode:Own "value" value ]) with
            generics = [ bounded "Value" ];
          }
      | Shared_update ->
          let change : Types.function_type =
            {
              inputs = [ (Mut, value); (Own, parameter_type "Input") ];
              output = Returns (parameter_type "Result");
              uses = [];
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
            generics = [ bounded "Value"; generic "Input"; bounded "Result" ];
          }
      | _ ->
          {
            (make ~output:(Returns (Types.builtin UInt64)) [ input "shared" shared ]) with
            generics = [ bounded "Value" ];
          })
  | Coroutine_resume -> make ~output:(Returns bool) [ input "coroutine" usize ]
  | Coroutine_suspend -> make []
  | Report_tests_to -> make [ input "descriptor" (Types.builtin Int32) ]
  | Live_blocks -> make ~output:(Returns usize) []
  | Environment_entry ->
      make
        ~output:(Returns (view (Types.builtin UInt8)))
        [ input "index" usize; input ~mode:Mut "is_present" bool ]
  | System_is_os _ | System_is_architecture _ -> make ~output:(Returns bool) []
  | Libc function_ ->
      let { Libc.parameters; result; _ } = Libc.signature function_ in
      let presence = match result with Text -> [ input ~mode:Mut "is_present" bool ] | _ -> [] in
      make
        ~output:
          (Returns
             (match result with
             | Returns scalar | Points_at scalar -> libc_scalar scalar
             | Text -> view (Types.builtin UInt8)
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

(* What each operation costs, as the prover trusts it. Arithmetic, and
   reading or swapping in place, take a fixed number of steps and allocate
   nothing. Making a storage with room for some elements takes a fixed
   number of steps and allocates one block, unless the room is for none. Moving or comparing the elements of a storage or a view, as
   giving a storage a new capacity moves them, takes steps in proportion to
   its length. Running a test and reaching the system may do more, and are
   known by no bound. *)
let cost (operation : Intrinsic.operation) =
  match operation with
  | Add | Subtract | Multiply | Divide | Remainder | Negate | Wrapping_add | Wrapping_subtract
  | Wrapping_multiply | Add_overflows | Subtract_overflows | Multiply_overflows | Equal | Less
  | Ieee_equal | Ieee_less | Bit_and | Bit_or | Bit_xor | Complement | Shift_left | Shift_right
  | Convert | Fits | Square_root | Fused_multiply_add | Floor | Ceiling | Truncate | Round_to_even
  | To_bits | From_bits | Is_nan | Leading_zeros | Trailing_zeros | Count_ones | Swap_bytes
  | Rotate_left | Rotate_right | Multiply_high | Storage_empty | Storage_length | Storage_capacity
  | Storage_pop | Storage_swap | Storage_at | Storage_at_mut | Storage_view | Storage_view_mut
  | View_length | View_at | View_at_mut | View_swap | Storage_take_view | View_take_view
  | Array_take_view | View_slice | View_address | Array_view | Array_at_mut | Array_from_storage
  | Storage_model | View_model | Array_model | Crash | Storage_lengthen | Storage_shorten
  | Storage_push | Handle_from | Handle_descriptor | Handle_release | Report_tests_to | Live_blocks
  | Libc_number _ | System_is_os _ | System_is_architecture _ ->
      { time = Constant_time; allocations = No_allocations }
  | Compare_bytes | Storage_remove | Storage_insert | Environment_entry ->
      { time = Linear_in 0; allocations = No_allocations }
  | Storage_set_capacity -> { time = Linear_in 0; allocations = Unknown_allocations }
  | Storage_with_capacity -> { time = Constant_time; allocations = One_if_positive (Argument 0) }
  | Storage_from_array -> { time = Constant_time; allocations = One_if_positive (Generic "count") }
  | Run_test | Libc _ | Coroutine_start | Coroutine_resume | Coroutine_suspend | Tasks_spawn
  | Shared_new | Shared_update | Shared_key ->
      { time = Unbounded_time; allocations = Unknown_allocations }
