let make_sequence_range (environment : State.environment) query element sequence ~start ~stop =
  let sequence_sort = Encoding.sort_of (Encoding.make_sequence_type element) in
  let symbol = Logic.Symbol.Sequence_range element in
  let range_of whole low high = Logic.Apply (symbol, [ whole; low; high ]) in
  Query.run_once query (Range_elements element) (fun () ->
      let variable label = Logic.Symbol.Variable { label; numbers = [] } in
      let whole = variable "range.whole"
      and low = variable "range.start"
      and high = variable "range.stop"
      and position = variable "range.position" in
      let bound = [ (whole, sequence_sort); (low, Logic.Int); (high, Logic.Int) ] in
      let whole_term = Logic.Symbol whole
      and low_term = Logic.Symbol low
      and high_term = Logic.Symbol high
      and position_term = Logic.Symbol position in
      let range = range_of whole_term low_term high_term in
      let length = Models.make_sequence_length element in
      let count = Logic.subtract high_term low_term in
      let is_within =
        Logic.(
          less_equal (int 0) low_term
          &&& less_equal low_term high_term
          &&& less_equal high_term (length whole_term))
      in
      Query.add_fact query
        (Logic.forall ~trigger:[ range ] (bound, Logic.(is_within ==> equal (length range) count)));
      (match
         ( Models.index_sequence environment query element range position_term,
           Models.index_sequence environment query element whole_term
             (Logic.add low_term position_term) )
       with
      | Some inside, Some outside ->
          Query.add_fact query
            (Logic.forall ~trigger:[ inside ]
               ( bound @ [ (position, Logic.Int) ],
                 Logic.(
                   is_within
                   &&& less_equal (int 0) position_term
                   &&& less position_term count ==> equal inside outside) ))
      | _ -> ());
      match
        ( Models.index_sequence environment query element whole_term position_term,
          Models.index_sequence environment query element range
            (Logic.subtract position_term low_term) )
      with
      | Some outside, Some inside ->
          Query.add_fact query
            (Logic.forall ~trigger:[ range; outside ]
               ( bound @ [ (position, Logic.Int) ],
                 Logic.(
                   is_within &&& less_equal low_term position_term &&& less position_term high_term
                   ==> equal outside inside) ))
      | _ -> ());
  range_of sequence start stop

let apply_range (frame : State.frame) ~node (site : Invocation.site) ~(base_type : Types.ty)
    ~collection ~low ~high =
  let location = Facts.locate frame site.origin in
  let element =
    match base_type with
    | Types.Named { arguments = Types.Type element :: _; _ } -> element
    | _ when Types.is_well_known String base_type -> Types.make_builtin UInt8
    | _ -> Facts.raise_unsupported location (Range_of base_type)
  in
  let is_sequence =
    match base_type with
    | Types.Named { path; _ } -> Path.equal path Encoding.sequence_path
    | _ -> false
  in
  let model =
    if is_sequence then collection
    else
      match Models.find_model frame.environment frame.query base_type collection ~element with
      | Some model -> model
      | None -> Facts.raise_unsupported location (Range_of base_type)
  in
  let length = Models.make_sequence_length element model in
  let is_whole =
    match (low, high) with Logic.Integer start, None -> Z.equal start Z.zero | _ -> false
  in
  let high =
    match high with
    | Some high -> high
    | None ->
        Facts.assume frame (Logic.less_equal (Logic.int 0) length);
        length
  in
  if not is_whole then
    Obligations.oblige frame location
      (Out_of_bounds { at = Facts.quote frame.source site.origin })
      Logic.(less_equal (int 0) low &&& less_equal low high &&& less_equal high length);
  let range =
    if is_whole then model
    else make_sequence_range frame.environment frame.query element model ~start:low ~stop:high
  in
  if is_sequence then (frame, range, low, high)
  else begin
    Validity.note_place frame ~node ~origin:site.origin (Run (low, high));
    let range_type_of_site = Encoding.substitute_type frame site.type_ in
    let symbol = Logic.Symbol.Range_of base_type in
    Query.declare frame.query
      (Logic.Function
         ( symbol,
           [ Encoding.sort_of base_type; Logic.Int; Logic.Int ],
           Encoding.sort_of range_type_of_site ));
    let viewed = Logic.Apply (symbol, [ collection; low; high ]) in
    Facts.assume frame (Encoding.make_in_range range_type_of_site viewed);
    (match Models.find_model frame.environment frame.query range_type_of_site viewed ~element with
    | Some viewed_model -> Facts.assume frame (Logic.equal viewed_model range)
    | None -> ());
    (frame, viewed, low, high)
  end

let index_element (environment : State.environment) query element term index =
  match Models.index_sequence environment query element term index with
  | Some term -> term
  | None -> Facts.raise_unsupported Whole_definition Sequence_elements

let assume_unchanged_outside (frame : State.frame) element ~before ~after ~start ~stop =
  let length sequence = Models.make_sequence_length element sequence in
  let at = index_element frame.environment frame.query element in
  let limit = Query.make_fresh_name frame.query "index" in
  let index = Logic.Symbol limit in
  Facts.assume frame (Logic.equal (length after) (length before));
  Facts.assume frame
    (Logic.forall
       ( [ (limit, Logic.Int) ],
         Logic.(
           less_equal (int 0) index
           &&& less index (length before)
           ==> (less_equal start index &&& less index stop
               ||| equal (at after index) (at before index))) ))

let make_handle_descriptor handle = Logic.Apply (Logic.Symbol.Handle_descriptor, [ handle ])
let make_libc_number (number : Libc.number) = Logic.Symbol (Logic.Symbol.Libc_number number)

let make_buffer_capacity element term =
  Logic.Apply
    (Logic.Symbol.Capacity (Types.make_builtin Storage ~arguments:[ Type element ]), [ term ])

let make_buffer_model (builtin : Language.Builtin_type.t) element term =
  Logic.Apply (Logic.Symbol.Model (Types.make_builtin builtin ~arguments:[ Type element ]), [ term ])

let call_libc (frame : State.frame) ~(site : Invocation.site) (function_ : Libc.function_) operands
    ~changed known =
  let { Libc.parameters; at_most; _ } = Libc.make_signature function_ in
  let arguments =
    List.concat_map
      (fun (name, (passes : Libc.passes)) ->
        match passes with
        | Value _ | Elements _ | Room _ | Elements_to_change _ -> [ (name, Some passes) ]
        | Written (_, names) -> List.map (fun name -> (name, None)) names
        | Always _ | Fixed _ -> [])
      parameters
  in
  let find_value name =
    List.find_map
      (fun (position, (named, _)) -> if named = name then List.nth_opt operands position else None)
      (List.mapi (fun position argument -> (position, argument)) arguments)
  in
  let count (extent : Libc.extent) =
    match extent with
    | Counted { by; each } ->
        Option.map
          (fun value -> if each = 1 then value else Logic.multiply (Logic.int each) value)
          (find_value by)
    | Exactly elements -> Some (Logic.int elements)
    | Number number -> Some (make_libc_number number)
    | Through_zero -> None
  in
  let require requirement condition =
    Obligations.oblige frame (Facts.locate frame site.origin)
      (Intrinsic_requirement { at = Facts.quote frame.source site.origin; requirement })
      condition
  in
  let make_element_type scalar = Types.make_builtin (Intrinsic.convert_libc_scalar scalar) in
  let length element sequence = Models.make_sequence_length element sequence in
  List.iteri
    (fun position (_, passes) ->
      match (passes, List.nth_opt operands position, List.nth_opt changed position) with
      | ( Some ((Libc.Room (scalar, extent) | Elements_to_change (scalar, extent)) as passes),
          Some before,
          Some after ) -> (
          let element = make_element_type scalar in
          let model term = make_buffer_model Storage element term in
          let capacity term = make_buffer_capacity element term in
          Facts.assume frame
            Logic.(
              equal (length element (model after)) (length element (model before))
              &&& equal (capacity after) (capacity before));
          match (passes, count extent) with
          | Room _, counted ->
              Facts.assume frame (Logic.equal (model after) (model before));
              Option.iter
                (fun counted ->
                  require Room_written
                    (Logic.less_equal
                       (Logic.add (length element (model before)) counted)
                       (capacity before)))
                counted
          | _, Some counted ->
              require Elements_mutated (Logic.less_equal counted (length element (model before)))
          | _, None -> ())
      | Some (Libc.Elements (scalar, extent)), Some view, _ -> (
          let element = make_element_type scalar in
          let elements = make_buffer_model Storage element view in
          match count extent with
          | Some counted ->
              require Elements_read (Logic.less_equal counted (length element elements))
          | None ->
              let last = Logic.subtract (length element elements) (Logic.int 1) in
              require Ends_with_zero
                Logic.(
                  greater_equal (length element elements) (int 1)
                  &&&
                  match
                    Models.index_sequence frame.environment frame.query element elements last
                  with
                  | Some last_element -> equal last_element (int 0)
                  | None -> Boolean false))
      | _ -> ())
    arguments;
  (match Option.bind at_most find_value with
  | Some bound -> Facts.assume frame Logic.(greater_equal known (int 0) ==> less_equal known bound)
  | None -> ());
  known

let measure_type element : Types.function_type =
  {
    inputs = [ (Language.Mode.Read, element) ];
    output = Types.Integer;
    uses = Types.no_capabilities;
    costs = [];
  }

let make_sequence_sum element term measure =
  let symbol =
    Logic.Symbol.Function
      { callee = Well_known.make_method_path Sequence_sum; type_arguments = [ Types.Type element ] }
  in
  Logic.Apply (symbol, [ term; measure ])

let make_each_sum query element relation =
  let measure = Query.make_fresh_name query "measure" in
  Logic.forall
    ( [ (measure, Encoding.sort_of (Types.Function (measure_type element))) ],
      relation
        (fun sequence -> make_sequence_sum element sequence (Logic.Symbol measure))
        (fun value ->
          Callbacks.apply_function (measure_type element) (Logic.Symbol measure) [ value ]) )

let make_empty_sequence (frame : State.frame) element =
  let empty =
    Facts.declare_fresh frame "parts" (Encoding.sort_of (Encoding.make_sequence_type element))
  in
  Facts.assume frame (Logic.equal (Models.make_sequence_length element empty) (Logic.int 0));
  Facts.assume frame
    (make_each_sum frame.query element (fun sum _ -> Logic.equal (sum empty) (Logic.int 0)));
  empty

let append_element (frame : State.frame) element shorter appended =
  let longer =
    Facts.declare_fresh frame "parts" (Encoding.sort_of (Encoding.make_sequence_type element))
  in
  let length = Models.make_sequence_length element shorter in
  Facts.assume frame
    Logic.(
      greater_equal length (int 0)
      &&& equal (Models.make_sequence_length element longer) (add length (int 1)));
  (match
     (Models.index_sequence frame.environment frame.query element longer length, frame.bound)
   with
  | Some last, _ -> Facts.assume frame (Logic.equal last appended)
  | None, _ -> ());
  let index = Query.make_fresh_name frame.query "index" in
  (match
     ( Models.index_sequence frame.environment frame.query element longer (Logic.Symbol index),
       Models.index_sequence frame.environment frame.query element shorter (Logic.Symbol index) )
   with
  | Some after, Some before ->
      Facts.assume frame
        (Logic.forall
           ( [ (index, Logic.Int) ],
             Logic.(
               less_equal (int 0) (Symbol index)
               &&& less (Symbol index) length ==> equal after before) ))
  | _ -> ());
  let measure = Query.make_fresh_name frame.query "measure" in
  Facts.assume frame
    (Logic.forall
       ( [ (measure, Encoding.sort_of (Types.Function (measure_type element))) ],
         Logic.equal
           (make_sequence_sum element longer (Logic.Symbol measure))
           (Logic.add
              (make_sequence_sum element shorter (Logic.Symbol measure))
              (Callbacks.apply_function (measure_type element) (Logic.Symbol measure) [ appended ]))
       ));
  longer

let make_byte_order left right = Logic.Apply (Logic.Symbol.Compare_bytes_order, [ left; right ])

let find_scalar_bytes element : int option =
  match Types.find_builtin element with
  | Some (Int8 | UInt8 | Bool) -> Some 1
  | Some (Int16 | UInt16) -> Some 2
  | Some (Int32 | UInt32 | Float32 | Character) -> Some 4
  | Some (Int64 | UInt64 | Float64) -> Some 8
  | _ -> None

let make_length_in_range value =
  Logic.(less_equal (int 0) value &&& Encoding.make_in_range (Types.make_builtin Int64) value)

let model_buffer (frame : State.frame) (builtin : Language.Builtin_type.t) element term =
  let sequence = make_buffer_model builtin element term in
  Facts.assume frame (make_length_in_range (Models.make_sequence_length element sequence));
  sequence

let model_storage (frame : State.frame) element term =
  let sequence = model_buffer frame Storage element term in
  let capacity = make_buffer_capacity element term in
  Facts.assume frame
    Logic.(
      less_equal (Models.make_sequence_length element sequence) capacity
      &&& make_length_in_range capacity);
  sequence

let require_precondition (frame : State.frame) (site : Invocation.site) requirement condition =
  if frame.makes_obligations then
    Obligations.oblige frame (Facts.locate frame site.origin)
      (Intrinsic_requirement { at = Facts.quote frame.source site.origin; requirement })
      condition;
  Facts.restrict_unless_proven frame condition

let translate_buffer_operation (frame : State.frame) ~(site : Invocation.site)
    (operation : Intrinsic.buffer) element (values : State.passed list) ~changed result_type known =
  let read_passed position =
    match List.nth_opt values position with
    | Some passed -> passed
    | None ->
        Facts.raise_bug "`%s` without operand %d"
          (Intrinsic.show_operation (Buffer operation))
          position
  in
  let read_operand position = (read_passed position).term in
  let length sequence = Models.make_sequence_length element sequence in
  let capacity term = make_buffer_capacity element term in
  let storage = model_storage frame element in
  let require ?(requirement = Catalog.Prover.Room_written) condition =
    require_precondition frame site requirement condition
  in
  let at = index_element frame.environment frame.query element in
  let make_index_name () = Query.make_fresh_name frame.query "index" in
  let in_interval index low high = Logic.(less_equal low index &&& less index high) in
  let all name low high body =
    Logic.forall ([ (name, Logic.Int) ], Logic.(in_interval (Symbol name) low high ==> body))
  in
  let read_changed_storage () = storage (List.hd changed) in
  match operation with
  | Storage_model -> storage (read_operand 0)
  | Array_model ->
      let array = read_passed 0 in
      Models.make_array_model frame array.type_ array.term
  | Storage_length -> length (storage (read_operand 0))
  | Storage_capacity ->
      let buffer = read_operand 0 in
      ignore (storage buffer);
      capacity buffer
  | Storage_lengthen ->
      if
        Option.is_none (Types.find_integer_bits element)
        && Option.is_none (Encoding.find_float_format element)
      then
        Facts.raise_bug "`storage_lengthen` over `%s`, which has bit patterns that are no value"
          (Types.show element);
      let buffer = read_operand 0 and by = read_operand 1 in
      let before = storage buffer and after = read_changed_storage () in
      let defined = require (Logic.less_equal (Logic.add (length before) by) (capacity buffer)) in
      Facts.assume defined (Logic.equal (capacity (List.hd changed)) (capacity buffer));
      let limit = make_index_name () in
      Facts.assume defined (Logic.equal (length after) (Logic.add (length before) by));
      Facts.assume defined
        (all limit (Logic.int 0) (length before)
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      known
  | Compare_bytes -> make_byte_order (storage (read_operand 0)) (storage (read_operand 1))
  | Storage_range ->
      let start = read_operand 1 and stop = read_operand 2 in
      let whole = storage (read_operand 0) and part = storage known in
      let defined =
        require ~requirement:Range_within_storage
          Logic.(
            less_equal (int 0) start &&& less_equal start stop &&& less_equal stop (length whole))
      in
      let limit = make_index_name () in
      Facts.assume defined (Logic.equal (length part) (Logic.subtract stop start));
      Facts.assume defined
        (all limit (Logic.int 0) (length part)
           (Logic.equal (at part (Logic.Symbol limit))
              (at whole (Logic.add start (Logic.Symbol limit)))));
      known
  | Storage_as ->
      let built =
        Logic.Apply (Encoding.make_constructor_symbol result_type None, [ read_operand 0 ])
      in
      Validity.check_valid frame (Facts.locate frame site.origin) result_type built ~deep:false
        ~moment:Built_here;
      built
  | Storage_address -> (
      match find_scalar_bytes element with
      | Some bytes ->
          let length =
            Models.make_sequence_length element (make_buffer_model Storage element (read_operand 0))
          in
          Facts.assume frame
            Logic.(
              less_equal (add known (multiply (int bytes) length)) (Integer (Z.shift_left Z.one 64))
              &&& (greater length (int 0) ==> greater_equal known (int 1)));
          known
      | None -> known)
  | Storage_empty | Storage_with_capacity | Storage_set_capacity | Storage_shorten | Storage_push
  | Storage_pop | Storage_insert | Storage_remove | Storage_swap | Storage_from_array
  | Array_from_storage | Find_byte ->
      Facts.raise_bug "`%s`, whose semantics is its contract, read as a term"
        (Intrinsic.show_operation (Buffer operation))

let translate_lend (frame : State.frame) ~(site : Invocation.site) (lend : Intrinsic.lend) types
    (values : State.passed list) =
  match (types, values) with
  | element :: _, [ container; index ] ->
      let sequence = match lend with Storage_at -> model_storage frame element container.term in
      let (_ : State.frame) =
        require_precondition frame site Element_at_index
          Logic.(
            less_equal (int 0) index.term
            &&& less index.term (Models.make_sequence_length element sequence))
      in
      index_element frame.environment frame.query element sequence index.term
  | _ ->
      Facts.raise_bug "`%s` without an element type, a container, and an index"
        (Intrinsic.show_operation (Lend lend))

let read_invariant (frame : State.frame) (values : State.passed list) result_type =
  match values with
  | [ subject; clause ] -> (
      match (clause.term, Validity.find_invariants frame.environment subject.type_) with
      | Logic.Integer index, Some (source, written) -> (
          match List.nth_opt written (Z.to_int index) with
          | Some invariant ->
              let inner =
                Validity.make_type_frame frame source subject.type_ ~self:(Some subject.term)
              in
              snd (Validity.read_specification inner invariant)
          | None -> Encoding.arrive frame "holds" result_type)
      | _ -> Encoding.arrive frame "holds" result_type)
  | _ -> Encoding.arrive frame "holds" result_type

let translate_runtime (frame : State.frame) ~(site : Invocation.site) (runtime : Intrinsic.runtime)
    (values : State.passed list) ~changed result_type known =
  let operands = List.map (fun (passed : State.passed) -> passed.term) values in
  match runtime with
  | Holds_invariant -> read_invariant frame values result_type
  | Shared_update ->
      Validity.assume_valid frame result_type (Lazy.force known);
      Lazy.force known
  | Libc function_ -> call_libc frame ~site function_ operands ~changed (Lazy.force known)
  | Libc_number number -> make_libc_number number
  | System_is_os _ | System_is_architecture _ -> Logic.Symbol (Logic.Symbol.System runtime)
  | Environment_entry ->
      let byte = Types.make_builtin UInt8 in
      let model = make_buffer_model Storage byte (Lazy.force known) in
      let length = Models.make_sequence_length byte model in
      (match
         Models.index_sequence frame.environment frame.query byte model
           (Logic.Symbol (Query.make_variable "entry.index"))
       with
      | Some at ->
          Facts.assume frame
            (Logic.forall
               ( [ (Query.make_variable "entry.index", Logic.Int) ],
                 Logic.(
                   less_equal (int 0) (Symbol (Query.make_variable "entry.index"))
                   &&& less (Symbol (Query.make_variable "entry.index")) length
                   ==> not_ (equal at (int 0))) ))
      | None -> ());
      Lazy.force known
  | Handle_from -> (
      match operands with
      | [ descriptor ] ->
          Facts.assume frame (Logic.equal (make_handle_descriptor (Lazy.force known)) descriptor);
          Lazy.force known
      | _ -> Lazy.force known)
  | Handle_descriptor -> (
      match operands with
      | [ handle ] ->
          let descriptor = make_handle_descriptor handle in
          Facts.assume frame (Encoding.make_in_range (Types.make_builtin Int32) descriptor);
          descriptor
      | _ -> Lazy.force known)
  | Crash | Handle_release | Run_test | Report_tests_to | Live_blocks | Coroutine_start
  | Coroutine_resume | Coroutine_suspend | Tasks_spawn | Shared_new | Shared_key ->
      Lazy.force known

let translate_intrinsic (frame : State.frame) ~(site : Invocation.site)
    (operation : Intrinsic.operation) types (values : State.passed list) ~changed result_type =
  let known = lazy (Encoding.arrive frame "result" result_type) in
  match operation with
  | Scalar scalar ->
      Operations.translate_primitive_operation frame ~site scalar types
        (List.map (fun (passed : State.passed) -> passed.term) values)
        ~arguments:(List.map (fun (passed : State.passed) -> passed.origin) values)
        ~fallback:(fun () -> Lazy.force known)
  | Buffer buffer ->
      let element =
        match (buffer, types) with
        | (Compare_bytes | Find_byte), _ -> Types.make_builtin UInt8
        | _, element :: _ -> element
        | _, [] -> Facts.raise_bug "`%s` has no element type" (Intrinsic.show_operation operation)
      in
      translate_buffer_operation frame ~site buffer element values ~changed result_type
        (Lazy.force known)
  | Lend lend -> translate_lend frame ~site lend types values
  | Runtime runtime -> translate_runtime frame ~site runtime values ~changed result_type known

let replace_element (frame : State.frame) element ~before ~after index part =
  let length sequence = Models.make_sequence_length element sequence in
  let at = index_element frame.environment frame.query element in
  let limit = Query.make_fresh_name frame.query "index" in
  Facts.assume frame
    (Logic.conjunction
       [ Logic.equal (length after) (length before); Logic.equal (at after index) part ]);
  Facts.assume frame
    (Logic.forall
       ( [ (limit, Logic.Int) ],
         Logic.(
           less_equal (int 0) (Symbol limit)
           &&& less (Symbol limit) (length before)
           &&& not_ (equal (Symbol limit) index)
           ==> equal (at after (Symbol limit)) (at before (Symbol limit))) ))

let keeps_potential : Intrinsic.operation -> bool = function
  | Scalar _ | Lend _
  | Buffer
      ( Storage_swap | Compare_bytes | Find_byte | Storage_length | Storage_capacity | Storage_range
      | Storage_as | Storage_model | Array_model | Storage_address )
  | Runtime
      ( Crash | Handle_from | Handle_descriptor | Run_test | Report_tests_to | Live_blocks
      | Environment_entry | Coroutine_resume | Coroutine_suspend | Holds_invariant | Shared_key
      | System_is_os _ | System_is_architecture _ | Libc_number _ ) ->
      true
  | Buffer
      ( Storage_empty | Storage_with_capacity | Storage_set_capacity | Storage_lengthen
      | Storage_shorten | Storage_push | Storage_pop | Storage_insert | Storage_remove
      | Storage_from_array | Array_from_storage )
  | Runtime (Handle_release | Coroutine_start | Tasks_spawn | Shared_new | Shared_update | Libc _)
    ->
      false

let make_buffer_slack (ty : Types.ty) term = Logic.Apply (Logic.Symbol.Slack ty, [ term ])

let find_sequence_element (frame : State.frame) (sequence : Types.ty) =
  match Types.strip_view sequence with
  | Types.Named { arguments = Types.Type element :: _; _ } -> Encoding.substitute_type frame element
  | text when Types.is_well_known String text -> Types.make_builtin UInt8
  | _ -> Facts.raise_bug "an element of `%s`, which is no sequence" (Types.show sequence)

let find_sequence_model (frame : State.frame) (sequence : Types.ty) term =
  match sequence with
  | Types.Named { path; _ } when Well_known.find_builtin_type path = Some Array ->
      Models.make_array_model frame sequence term
  | _ -> (
      match
        Models.find_model frame.environment frame.query sequence term
          ~element:(find_sequence_element frame sequence)
      with
      | Some model -> model
      | None -> Facts.raise_unsupported Whole_definition (Elements_of sequence))

let oblige_in_bounds (frame : State.frame) ~origin condition =
  Obligations.oblige frame (Facts.locate frame origin)
    (Out_of_bounds { at = Facts.quote frame.source origin })
    condition

let read_sequence_element (frame : State.frame) (sequence : Types.ty) term index ~node ~origin =
  let element = find_sequence_element frame sequence in
  let model = find_sequence_model frame sequence term in
  let is_in_bounds =
    Logic.(less_equal (int 0) index &&& less index (Models.make_sequence_length element model))
  in
  oblige_in_bounds frame ~origin is_in_bounds;
  Validity.note_place frame ~node ~origin (One index);
  let read = index_element frame.environment frame.query element model index in
  let defined = Facts.restrict_unless_proven frame is_in_bounds in
  Facts.assume defined (Encoding.make_in_range element read);
  Validity.assume_valid defined element read;
  read

let write_sequence (frame : State.frame) (sequence : Types.ty) before ~write_model =
  let element = find_sequence_element frame sequence in
  let after =
    match (sequence, Encoding.find_constructors frame.environment sequence) with
    | Types.Named { path; _ }, _ when Well_known.find_builtin_type path = Some Array ->
        let after = Encoding.arrive frame "changed" sequence in
        write_model
          ~before:(Models.make_array_model frame sequence before)
          ~after:(Models.make_array_model frame sequence after);
        after
    | _, Some [ (None, [ (field, buffer_type) ]) ] ->
        let buffer = Encoding.select_field frame.environment sequence None field before in
        let written = Encoding.arrive frame "changed" buffer_type in
        if not (Types.is_builtin Storage buffer_type) then
          Facts.raise_bug "the field of `%s` is no buffer" (Types.show sequence);
        write_model
          ~before:(make_buffer_model Storage element buffer)
          ~after:(make_buffer_model Storage element written);
        Facts.assume frame
          (Logic.equal (make_buffer_capacity element written) (make_buffer_capacity element buffer));
        let after = Logic.Apply (Encoding.make_constructor_symbol sequence None, [ written ]) in
        write_model
          ~before:(find_sequence_model frame sequence before)
          ~after:(find_sequence_model frame sequence after);
        after
    | _, None ->
        let after = Encoding.arrive frame "changed" sequence in
        write_model
          ~before:(find_sequence_model frame sequence before)
          ~after:(find_sequence_model frame sequence after);
        Facts.assume frame
          (Logic.equal (make_buffer_slack sequence after) (make_buffer_slack sequence before));
        after
    | _, Some _ -> Facts.raise_bug "a sequence `%s` with more than one field" (Types.show sequence)
  in
  Validity.assume_valid frame sequence after;
  after

let write_sequence_element (frame : State.frame) (sequence : Types.ty) before index part =
  let element = find_sequence_element frame sequence in
  write_sequence frame sequence before ~write_model:(fun ~before ~after ->
      replace_element frame element ~before ~after index part)

let write_sequence_range (frame : State.frame) (sequence : Types.ty) before ~start ~stop
    ~(range_type : Types.ty) range =
  let element = find_sequence_element frame sequence in
  let range_model = find_sequence_model frame range_type range in
  write_sequence frame sequence before ~write_model:(fun ~before ~after ->
      assume_unchanged_outside frame element ~before ~after ~start ~stop;
      Facts.assume frame
        (Logic.equal
           (make_sequence_range frame.environment frame.query element after ~start ~stop)
           range_model);
      let replaced =
        make_sequence_range frame.environment frame.query element before ~start ~stop
      in
      Facts.assume frame
        (make_each_sum frame.query element (fun sum _ ->
             Logic.equal
               (Logic.add (sum after) (sum replaced))
               (Logic.add (sum before) (sum range_model)))))

let replace_elements (frame : State.frame) (sequence : Types.ty) before =
  let element = find_sequence_element frame sequence in
  let keep_length ~before ~after =
    Facts.assume frame
      (Logic.equal
         (Models.make_sequence_length element after)
         (Models.make_sequence_length element before))
  in
  if Types.is_builtin Storage sequence then begin
    let after = Encoding.arrive frame "changed" sequence in
    keep_length
      ~before:(make_buffer_model Storage element before)
      ~after:(make_buffer_model Storage element after);
    Facts.assume frame
      (Logic.equal (make_buffer_capacity element after) (make_buffer_capacity element before));
    after
  end
  else write_sequence frame sequence before ~write_model:keep_length
