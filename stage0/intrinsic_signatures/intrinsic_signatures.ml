(* The signatures of [standard::intrinsic]'s operations. Arithmetic and
   comparison are generic over the built-in number type, which code generation
   sees after monomorphization. *)

module T = Types

let parameter operation name : T.parameter = { owner = Intrinsic.operation_path operation; name }
let text name : Path.t = Top { module_ = { package = "standard"; modules = [ "text" ] }; name }

let storage element =
  T.Named { path = Intrinsic.builtin_path Storage; arguments = [ T.Type element ] }

let view element = T.Named { path = Intrinsic.builtin_path View; arguments = [ T.Type element ] }

let sequence element =
  T.Named
    {
      path =
        Top { module_ = { package = "standard"; modules = [ "specification" ] }; name = "Sequence" };
      arguments = [ T.Type element ];
    }

let signature (operation : Intrinsic.operation) : T.signature =
  let generic name = { T.generic = parameter operation name; kind = Type_generic [] } in
  let p name = T.Parameter (parameter operation name) in
  let input ?(mode = T.Read) name type_ = { T.name; mode; type_; has_default = false } in
  let make ?(generics = []) ?(output = T.Returns T.unit) parameters : T.signature =
    {
      generics = List.map generic generics;
      receiver = None;
      parameters;
      output;
      uses = [];
      terminates = true;
      specification_only = false;
      stores_functions = [];
    }
  in
  let value = p "Value" and element = p "Element" in
  let usize = T.builtin USize and bool = T.bool in
  let binary output =
    make ~generics:[ "Value" ] ~output:(Returns output) [ input "left" value; input "right" value ]
  in
  let unary output = make ~generics:[ "Value" ] ~output:(Returns output) [ input "value" value ] in
  let with_storage ?(mode = T.Read) ?(output = T.Returns T.unit) rest =
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
        [ input "value" value; input "amount" (p "Amount") ]
  | Rotate_left | Rotate_right ->
      make ~generics:[ "Value" ] ~output:(Returns value)
        [ input "value" value; input "amount" usize ]
  | Convert ->
      make ~generics:[ "Source"; "Target" ]
        ~output:(Returns (p "Target"))
        [ input "value" (p "Source") ]
  | Fits ->
      make ~generics:[ "Source"; "Target" ] ~output:(Returns bool) [ input "value" (p "Source") ]
  | Fused_multiply_add ->
      make ~generics:[ "Value" ] ~output:(Returns value)
        [ input "value" value; input "multiplier" value; input "addend" value ]
  | To_bits ->
      make ~generics:[ "Value"; "Bits" ] ~output:(Returns (p "Bits")) [ input "value" value ]
  | From_bits ->
      make ~generics:[ "Bits"; "Value" ] ~output:(Returns value) [ input "bits" (p "Bits") ]
  | Compare_bytes ->
      make
        ~output:(Returns (T.builtin Int8))
        [ input "left" (view (T.builtin UInt8)); input "right" (view (T.builtin UInt8)) ]
  | Storage_empty -> make ~generics:[ "Element" ] ~output:(Returns (storage element)) []
  | Storage_with_capacity ->
      make ~generics:[ "Element" ] ~output:(Returns (storage element)) [ input "capacity" usize ]
  | Storage_length | Storage_capacity -> with_storage ~output:(Returns usize) []
  | Storage_reserve -> with_storage ~mode:Mut [ input "additional" usize ]
  | Storage_push -> with_storage ~mode:Mut [ input ~mode:Own "value" element ]
  | Storage_pop -> with_storage ~mode:Mut ~output:(Returns element) []
  | Storage_insert ->
      with_storage ~mode:Mut [ input "index" usize; input ~mode:Own "value" element ]
  | Storage_remove -> with_storage ~mode:Mut ~output:(Returns element) [ input "index" usize ]
  | Storage_swap -> with_storage ~mode:Mut [ input "first" usize; input "second" usize ]
  | Storage_at -> with_storage ~output:(Lends (Read, element)) [ input "index" usize ]
  | Storage_at_mut -> with_storage ~mode:Mut ~output:(Lends (Mut, element)) [ input "index" usize ]
  | Storage_view -> with_storage ~output:(Returns (view element)) []
  | View_length ->
      make ~generics:[ "Element" ] ~output:(Returns usize) [ input "view" (view element) ]
  | View_at ->
      make ~generics:[ "Element" ]
        ~output:(Lends (Read, element))
        [ input "view" (view element); input "index" usize ]
  | View_slice ->
      make ~generics:[ "Element" ]
        ~output:(Returns (view element))
        [ input "view" (view element); input "start" usize; input "stop" usize ]
  | Storage_model ->
      { (with_storage ~output:(Returns (sequence element)) []) with specification_only = true }
  | View_model ->
      {
        (make ~generics:[ "Element" ]
           ~output:(Returns (sequence element))
           [ input "view" (view element) ])
        with
        specification_only = true;
      }
  | Crash ->
      make ~output:(Returns T.Never)
        [ input "message" (T.Named { path = text "StringSlice"; arguments = [] }) ]
  | Write_bytes ->
      make
        ~output:(Returns (T.builtin ISize))
        [ input "descriptor" (T.builtin Int32); input "bytes" (view (T.builtin UInt8)) ]
  | Read_bytes ->
      make
        ~output:(Returns (T.builtin ISize))
        [
          input "descriptor" (T.builtin Int32);
          input ~mode:Mut "buffer" (storage (T.builtin UInt8));
          input "count" usize;
        ]
  | Write_float ->
      make ~generics:[ "Value" ]
        [ input ~mode:Mut "buffer" (storage (T.builtin UInt8)); input "value" value ]
  | Open_file ->
      make
        ~output:(Returns (T.Named { path = Intrinsic.builtin_path Handle; arguments = [] }))
        [
          input "path" (view (T.builtin UInt8));
          input "flags" (T.builtin Int32);
          input ~mode:Mut "error" (T.builtin Int32);
        ]
  | Handle_read ->
      make
        ~output:(Returns (T.builtin ISize))
        [
          input ~mode:Mut "handle"
            (T.Named { path = Intrinsic.builtin_path Handle; arguments = [] });
          input ~mode:Mut "buffer" (storage (T.builtin UInt8));
          input "count" usize;
        ]
  | Handle_write ->
      make
        ~output:(Returns (T.builtin ISize))
        [
          input ~mode:Mut "handle"
            (T.Named { path = Intrinsic.builtin_path Handle; arguments = [] });
          input "bytes" (view (T.builtin UInt8));
        ]
  | Environment_variable ->
      make ~output:(Returns bool)
        [
          input "name" (view (T.builtin UInt8));
          input ~mode:Mut "buffer" (storage (T.builtin UInt8));
        ]
  | Run_process ->
      make
        ~output:(Returns (T.builtin Int32))
        [
          input "program" (view (T.builtin UInt8));
          input "arguments" (view (T.builtin UInt8));
          input ~mode:Mut "error" (T.builtin Int32);
        ]
  | Clock_now -> make ~output:(Returns (T.builtin Int64)) []
  | Random_fill ->
      make [ input ~mode:Mut "buffer" (storage (T.builtin UInt8)); input "count" usize ]

type time = Constant_time | Linear_in of int | Unbounded_time
type cost = { time : time; allocation_free : bool }

(* What each operation costs, as the prover trusts it: arithmetic and
   reading or swapping in place take a fixed number of steps and allocate
   nothing; moving or comparing the elements of a storage or a view takes
   steps in proportion to its length; anything else that grows storage, or
   reaches the system, may do more, and is known by no bound. *)
let cost (operation : Intrinsic.operation) =
  match operation with
  | Add | Subtract | Multiply | Divide | Remainder | Negate | Wrapping_add | Wrapping_subtract
  | Wrapping_multiply | Add_overflows | Subtract_overflows | Multiply_overflows | Equal | Less
  | Ieee_equal | Ieee_less | Bit_and | Bit_or | Bit_xor | Complement | Shift_left | Shift_right
  | Convert | Fits | Square_root | Fused_multiply_add | Floor | Ceiling | Truncate | Round_to_even
  | To_bits | From_bits | Is_nan | Leading_zeros | Trailing_zeros | Count_ones | Swap_bytes
  | Rotate_left | Rotate_right | Multiply_high | Storage_empty | Storage_length | Storage_capacity
  | Storage_pop | Storage_swap | Storage_at | Storage_at_mut | Storage_view | View_length | View_at
  | View_slice | Storage_model | View_model | Crash ->
      { time = Constant_time; allocation_free = true }
  | Compare_bytes | Storage_remove -> { time = Linear_in 0; allocation_free = true }
  | Storage_insert -> { time = Linear_in 0; allocation_free = false }
  | Storage_with_capacity | Storage_reserve | Storage_push | Write_bytes | Read_bytes | Write_float
  | Open_file | Handle_read | Handle_write | Environment_variable | Run_process | Clock_now
  | Random_fill ->
      { time = Unbounded_time; allocation_free = false }
