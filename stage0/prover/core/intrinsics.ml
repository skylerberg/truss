let make_sequence_range context element sequence ~start ~stop =
  let sequence_sort = Facts.declare_sort context (Models.make_sequence_type element) in
  let symbol = Logic.Symbol.Sequence_range element in
  Facts.declare context
    (Logic.Function (symbol, [ sequence_sort; Logic.Int; Logic.Int ], sequence_sort));
  let range_of whole low high = Logic.Apply (symbol, [ whole; low; high ]) in
  Facts.run_once context (Range_elements element) (fun () ->
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
      let length = Models.make_sequence_length context element in
      let count = Logic.subtract high_term low_term in
      let is_within =
        Logic.(
          less_equal (int 0) low_term
          &&& less_equal low_term high_term
          &&& less_equal high_term (length whole_term))
      in
      Facts.add_fact context
        (Logic.forall ~trigger:[ range ] (bound, Logic.(is_within ==> equal (length range) count)));
      (match
         ( Models.index_sequence context element range position_term,
           Models.index_sequence context element whole_term (Logic.add low_term position_term) )
       with
      | Some inside, Some outside ->
          Facts.add_fact context
            (Logic.forall ~trigger:[ inside ]
               ( bound @ [ (position, Logic.Int) ],
                 Logic.(
                   is_within
                   &&& less_equal (int 0) position_term
                   &&& less position_term count ==> equal inside outside) ))
      | _ -> ());
      match
        ( Models.index_sequence context element whole_term position_term,
          Models.index_sequence context element range (Logic.subtract position_term low_term) )
      with
      | Some outside, Some inside ->
          Facts.add_fact context
            (Logic.forall ~trigger:[ range; outside ]
               ( bound @ [ (position, Logic.Int) ],
                 Logic.(
                   is_within &&& less_equal low_term position_term &&& less position_term high_term
                   ==> equal outside inside) ))
      | _ -> ());
  range_of sequence start stop

let apply_slice context (frame : State.frame) ~node (site : Invocation.site) ~(base_type : Types.ty)
    ~collection ~low ~high =
  let location = Facts.locate context frame.source site.origin in
  let element =
    match base_type with
    | Types.Named { arguments = Types.Type element :: _; _ } -> element
    | _ -> Facts.raise_unsupported location "a slice of `%s`" (Types.show base_type)
  in
  let is_sequence =
    match base_type with
    | Types.Named { path; _ } -> Path.equal path Models.sequence_path
    | _ -> false
  in
  let model =
    if is_sequence then collection
    else
      match Models.find_model context base_type collection ~element with
      | Some model -> model
      | None -> Facts.raise_unsupported location "a slice of `%s`" (Types.show base_type)
  in
  let length = Models.make_sequence_length context element model in
  let is_whole =
    match (low, high) with Logic.Integer start, None -> Z.equal start Z.zero | _ -> false
  in
  let high =
    match high with
    | Some high -> high
    | None ->
        Facts.assume context frame (Logic.less_equal (Logic.int 0) length);
        length
  in
  if not is_whole then
    Facts.oblige context frame Out_of_bounds location
      [ Text "`"; Facts.quote frame.source site.origin; Text "` may not be within the collection." ]
      Logic.(less_equal (int 0) low &&& less_equal low high &&& less_equal high length);
  let range = make_sequence_range context element model ~start:low ~stop:high in
  if is_sequence then (frame, range, low, high)
  else begin
    Validity.note_place context frame ~node ~origin:site.origin (Run (low, high));
    let slice_type = Facts.substitute_type context frame site.type_ in
    let symbol = Logic.Symbol.Slice_of base_type in
    Facts.declare context
      (Logic.Function
         ( symbol,
           [ Facts.declare_sort context base_type; Logic.Int; Logic.Int ],
           Facts.declare_sort context slice_type ));
    let viewed = Logic.Apply (symbol, [ collection; low; high ]) in
    Facts.assume context frame (Facts.make_in_range slice_type viewed);
    (match Models.find_model context slice_type viewed ~element with
    | Some viewed_model -> Facts.assume context frame (Logic.equal viewed_model range)
    | None -> ());
    (frame, viewed, low, high)
  end

let index_element context element term index =
  match Models.index_sequence context element term index with
  | Some term -> term
  | None -> Facts.raise_unsupported Whole_definition "the elements of a sequence"

let assume_unchanged_outside context frame element ~before ~after ~start ~stop =
  let length sequence = Models.make_sequence_length context element sequence in
  let at = index_element context element in
  let limit = Facts.make_fresh_name context "index" in
  let index = Logic.Symbol limit in
  Facts.assume context frame (Logic.equal (length after) (length before));
  Facts.assume context frame
    (Logic.forall
       ( [ (limit, Logic.Int) ],
         Logic.(
           less_equal (int 0) index
           &&& less index (length before)
           ==> (less_equal start index &&& less index stop
               ||| equal (at after index) (at before index))) ))

let handle_descriptor context handle =
  let handle_sort = Facts.declare_sort context (Types.make_builtin Handle) in
  Facts.declare context
    (Logic.Function (Logic.Symbol.Handle_descriptor, [ handle_sort ], Logic.Int));
  Logic.Apply (Logic.Symbol.Handle_descriptor, [ handle ])

let declare_libc_number context frame (number : Libc.number) =
  let symbol = Logic.Symbol.Libc_number number in
  Facts.declare context (Logic.Constant (symbol, Logic.Int));
  let term = Logic.Symbol symbol in
  Facts.assume context frame
    (Facts.make_in_range
       (Types.make_builtin (Intrinsic.convert_libc_scalar (Libc.classify_number number)))
       term);
  term

let make_buffer_capacity context element term =
  let ty = Types.make_builtin Storage ~arguments:[ Type element ] in
  let symbol = Logic.Symbol.Capacity ty in
  Facts.declare context (Logic.Function (symbol, [ Facts.declare_sort context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

let make_buffer_model context (builtin : Language.Builtin_type.t) element term =
  let ty = Types.make_builtin builtin ~arguments:[ Type element ] in
  let symbol = Logic.Symbol.Model ty in
  Facts.declare context
    (Logic.Function
       ( symbol,
         [ Facts.declare_sort context ty ],
         Facts.declare_sort context (Models.make_sequence_type element) ));
  Logic.Apply (symbol, [ term ])

let call_libc context frame ~(site : Invocation.site) (function_ : Libc.function_) operands ~changed
    known =
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
    | Number number -> Some (declare_libc_number context frame number)
    | Through_zero -> None
  in
  let require requirement condition =
    Facts.oblige context frame Requires
      (Facts.locate context frame.source site.origin)
      [
        Text "`";
        Facts.quote frame.source site.origin;
        Text (Printf.sprintf "` may not %s." requirement);
      ]
      condition
  in
  let make_element_type scalar = Types.make_builtin (Intrinsic.convert_libc_scalar scalar) in
  let length element sequence = Models.make_sequence_length context element sequence in
  List.iteri
    (fun position (_, passes) ->
      match (passes, List.nth_opt operands position, List.nth_opt changed position) with
      | ( Some ((Libc.Room (scalar, extent) | Elements_to_change (scalar, extent)) as passes),
          Some before,
          Some after ) -> (
          let element = make_element_type scalar in
          let model term = make_buffer_model context Storage element term in
          let capacity term = make_buffer_capacity context element term in
          Facts.assume context frame
            Logic.(
              equal (length element (model after)) (length element (model before))
              &&& equal (capacity after) (capacity before));
          match (passes, count extent) with
          | Room _, counted ->
              Facts.assume context frame (Logic.equal (model after) (model before));
              Option.iter
                (fun counted ->
                  require "have the room it writes into"
                    (Logic.less_equal
                       (Logic.add (length element (model before)) counted)
                       (capacity before)))
                counted
          | _, Some counted ->
              require "have the elements it mutates"
                (Logic.less_equal counted (length element (model before)))
          | _, None -> ())
      | Some (Libc.Elements (scalar, extent)), Some view, _ -> (
          let element = make_element_type scalar in
          let elements = make_buffer_model context View element view in
          match count extent with
          | Some counted ->
              require "have the elements it reads"
                (Logic.less_equal counted (length element elements))
          | None ->
              let last = Logic.subtract (length element elements) (Logic.int 1) in
              require "end with a zero, which it reads up to"
                Logic.(
                  greater_equal (length element elements) (int 1)
                  &&&
                  match Models.index_sequence context element elements last with
                  | Some last_element -> equal last_element (int 0)
                  | None -> Boolean false))
      | _ -> ())
    arguments;
  (match Option.bind at_most find_value with
  | Some bound ->
      Facts.assume context frame Logic.(greater_equal known (int 0) ==> less_equal known bound)
  | None -> ());
  known

let measure_type element : Types.function_type =
  {
    inputs = [ (Language.Mode.Read, element) ];
    output = Types.Integer;
    uses = Types.no_capabilities;
    costs = [];
  }

let make_sequence_sum context element term measure =
  let symbol =
    Logic.Symbol.Function
      { callee = Well_known.make_method_path Sequence_sum; type_arguments = [ Types.Type element ] }
  in
  Facts.declare context
    (Logic.Function
       ( symbol,
         [
           Facts.declare_sort context (Models.make_sequence_type element);
           Facts.declare_sort context (Types.Function (measure_type element));
         ],
         Logic.Int ));
  Logic.Apply (symbol, [ term; measure ])

let make_each_sum context element relation =
  let measure = Facts.make_fresh_name context "measure" in
  Logic.forall
    ( [ (measure, Facts.declare_sort context (Types.Function (measure_type element))) ],
      relation
        (fun sequence -> make_sequence_sum context element sequence (Logic.Symbol measure))
        (fun value ->
          Lambdas.apply_function context (measure_type element) (Logic.Symbol measure) [ value ]) )

let make_empty_parts context frame element =
  let parts =
    Facts.declare_fresh context frame "parts"
      (Facts.declare_sort context (Models.make_sequence_type element))
  in
  Facts.assume context frame
    (Logic.equal (Models.make_sequence_length context element parts) (Logic.int 0));
  Facts.assume context frame
    (make_each_sum context element (fun sum _ -> Logic.equal (sum parts) Costs.zero));
  parts

let append_part context frame element parts part =
  let longer =
    Facts.declare_fresh context frame "parts"
      (Facts.declare_sort context (Models.make_sequence_type element))
  in
  let length = Models.make_sequence_length context element parts in
  Facts.assume context frame
    Logic.(
      greater_equal length (int 0)
      &&& equal (Models.make_sequence_length context element longer) (add length (int 1)));
  (match (Models.index_sequence context element longer length, frame.bound) with
  | Some last, _ -> Facts.assume context frame (Logic.equal last part)
  | None, _ -> ());
  let index = Facts.make_fresh_name context "index" in
  (match
     ( Models.index_sequence context element longer (Logic.Symbol index),
       Models.index_sequence context element parts (Logic.Symbol index) )
   with
  | Some after, Some before ->
      Facts.assume context frame
        (Logic.forall
           ( [ (index, Logic.Int) ],
             Logic.(
               less_equal (int 0) (Symbol index)
               &&& less (Symbol index) length ==> equal after before) ))
  | _ -> ());
  let measure = Facts.make_fresh_name context "measure" in
  Facts.assume context frame
    (Logic.forall
       ( [ (measure, Facts.declare_sort context (Types.Function (measure_type element))) ],
         Logic.equal
           (make_sequence_sum context element longer (Logic.Symbol measure))
           (Logic.add
              (make_sequence_sum context element parts (Logic.Symbol measure))
              (Lambdas.apply_function context (measure_type element) (Logic.Symbol measure) [ part ]))
       ));
  longer

let make_byte_order context left right =
  let sequence =
    Facts.declare_sort context (Models.make_sequence_type (Types.make_builtin UInt8))
  in
  let symbol = Logic.Symbol.Compare_bytes_order in
  let first = not (Tables.Symbol_table.mem context.declared symbol) in
  Facts.declare context (Logic.Function (symbol, [ sequence; sequence ], Logic.Int));
  let order first_term second_term = Logic.Apply (symbol, [ first_term; second_term ]) in
  if first then begin
    let first_term = Logic.Symbol (Facts.make_variable "bytes.first")
    and second_term = Logic.Symbol (Facts.make_variable "bytes.second")
    and third_term = Logic.Symbol (Facts.make_variable "bytes.third") in
    let over names body = Logic.forall (List.map (fun name -> (name, sequence)) names, body) in
    List.iter (Facts.add_fact context)
      (List.rev
         [
           over
             [ Facts.make_variable "bytes.first"; Facts.make_variable "bytes.second" ]
             Logic.(
               less_equal (int (-1)) (order first_term second_term)
               &&& less_equal (order first_term second_term) (int 1)
               &&& (equal (order first_term second_term) (int 0) ==> equal first_term second_term)
               &&& equal (order second_term first_term) (negate (order first_term second_term)));
           over
             [ Facts.make_variable "bytes.first" ]
             (Logic.equal (order first_term first_term) (Logic.int 0));
           over
             [
               Facts.make_variable "bytes.first";
               Facts.make_variable "bytes.second";
               Facts.make_variable "bytes.third";
             ]
             Logic.(
               less (order first_term second_term) (int 0)
               &&& less (order second_term third_term) (int 0)
               ==> less (order first_term third_term) (int 0));
         ])
  end;
  order left right

let find_scalar_bytes element : int option =
  match Types.find_builtin element with
  | Some (Int8 | UInt8 | Bool) -> Some 1
  | Some (Int16 | UInt16) -> Some 2
  | Some (Int32 | UInt32 | Float32 | Character) -> Some 4
  | Some (Int64 | UInt64 | Float64) -> Some 8
  | _ -> None

let make_length_in_range value =
  Logic.(less_equal (int 0) value &&& Facts.make_in_range (Types.make_builtin Int64) value)

let model_buffer context frame (builtin : Language.Builtin_type.t) element term =
  let sequence = make_buffer_model context builtin element term in
  Facts.assume context frame
    (make_length_in_range (Models.make_sequence_length context element sequence));
  sequence

let model_storage context frame element term =
  let sequence = model_buffer context frame Storage element term in
  let capacity = make_buffer_capacity context element term in
  Facts.assume context frame
    Logic.(
      less_equal (Models.make_sequence_length context element sequence) capacity
      &&& make_length_in_range capacity);
  sequence

let require_precondition context (frame : State.frame) (site : Invocation.site) requirement
    condition =
  if frame.makes_obligations then
    Facts.oblige context frame Requires
      (Facts.locate context frame.source site.origin)
      [
        Text "`";
        Facts.quote frame.source site.origin;
        Text (Printf.sprintf "` may not %s." requirement);
      ]
      condition
  else Facts.assume context frame condition

let require_element context frame site element index sequence =
  require_precondition context frame site "have an element at its index"
    Logic.(
      less_equal (int 0) index &&& less index (Models.make_sequence_length context element sequence))

let translate_buffer_operation context frame ~(site : Invocation.site)
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
  let read_array_count (array_type : Types.ty) =
    match array_type with
    | Types.Named { arguments = [ _; Types.Value count ]; _ } ->
        Models.make_value_term context frame count
    | _ ->
        Facts.raise_bug "`%s` on `%s`, which has no count"
          (Intrinsic.show_operation (Buffer operation))
          (Types.show array_type)
  in
  let length sequence = Models.make_sequence_length context element sequence in
  let view = model_buffer context frame View element in
  let capacity term = make_buffer_capacity context element term in
  let storage = model_storage context frame element in
  let require ?(requirement = "have the room it writes into") condition =
    require_precondition context frame site requirement condition
  in
  let assume_capacity_kept () =
    Facts.assume context frame
      (Logic.equal (capacity (List.hd changed)) (capacity (read_operand 0)))
  in
  let at = index_element context element in
  let make_index_name () = Facts.make_fresh_name context "index" in
  let in_interval index low high = Logic.(less_equal low index &&& less index high) in
  let all name low high body =
    Logic.forall ([ (name, Logic.Int) ], Logic.(in_interval (Symbol name) low high ==> body))
  in
  let in_bounds index sequence = in_interval index (Logic.int 0) (length sequence) in
  let each_sum = make_each_sum context element in
  let read_changed_storage () = storage (List.hd changed) in
  let assume_swapped before after =
    let first = read_operand 1 and second = read_operand 2 in
    require ~requirement:"have elements at both of its indexes"
      Logic.(in_bounds first before &&& in_bounds second before);
    let limit = make_index_name () in
    Facts.assume context frame
      (Logic.conjunction
         [
           Logic.equal (length after) (length before);
           Logic.equal (at after first) (at before second);
           Logic.equal (at after second) (at before first);
         ]);
    Facts.assume context frame
      (all limit (Logic.int 0) (length before)
         Logic.(
           not_ (equal (Symbol limit) first)
           &&& not_ (equal (Symbol limit) second)
           ==> equal (at after (Symbol limit)) (at before (Symbol limit))));
    Facts.assume context frame (each_sum (fun sum _ -> Logic.equal (sum after) (sum before)));
    known
  in
  match operation with
  | Storage_model -> storage (read_operand 0)
  | View_model -> view (read_operand 0)
  | Array_model ->
      let array = read_passed 0 in
      Models.make_array_model context frame array.type_ array.term
  | Storage_empty ->
      Facts.assume context frame (Logic.equal (length (storage known)) (Logic.int 0));
      known
  | Storage_with_capacity ->
      Facts.assume context frame
        Logic.(equal (length (storage known)) (int 0) &&& equal (capacity known) (read_operand 0));
      known
  | Storage_length -> length (storage (read_operand 0))
  | View_length -> length (view (read_operand 0))
  | Storage_capacity ->
      let buffer = read_operand 0 in
      ignore (storage buffer);
      capacity buffer
  | Storage_set_capacity ->
      let buffer = read_operand 0 and room = read_operand 1 in
      require (Logic.greater_equal room (length (storage buffer)));
      Facts.assume context frame (Logic.equal (read_changed_storage ()) (storage buffer));
      Facts.assume context frame (Logic.equal (capacity (List.hd changed)) room);
      known
  | Storage_lengthen ->
      let buffer = read_operand 0 and by = read_operand 1 in
      let before = storage buffer and after = read_changed_storage () in
      require (Logic.less_equal (Logic.add (length before) by) (capacity buffer));
      assume_capacity_kept ();
      let limit = make_index_name () in
      Facts.assume context frame (Logic.equal (length after) (Logic.add (length before) by));
      Facts.assume context frame
        (all limit (Logic.int 0) (length before)
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      known
  | Storage_shorten ->
      let shorter = read_operand 1 in
      let before = storage (read_operand 0) and after = read_changed_storage () in
      require ~requirement:"be given a length at most the storage's"
        (Logic.less_equal shorter (length before));
      assume_capacity_kept ();
      let limit = make_index_name () in
      Facts.assume context frame (Logic.equal (length after) shorter);
      Facts.assume context frame
        (all limit (Logic.int 0) shorter
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      known
  | Storage_push ->
      let buffer = read_operand 0 in
      require (Logic.less (length (storage buffer)) (capacity buffer));
      assume_capacity_kept ();
      let longer = append_part context frame element (storage buffer) (read_operand 1) in
      Facts.assume context frame (Logic.equal (read_changed_storage ()) longer);
      known
  | Storage_pop ->
      let buffer = read_operand 0 in
      require ~requirement:"have an element to pop"
        (Logic.greater (length (storage buffer)) (Logic.int 0));
      assume_capacity_kept ();
      let longer = append_part context frame element (read_changed_storage ()) known in
      Facts.assume context frame (Logic.equal (storage buffer) longer);
      known
  | Storage_insert ->
      let buffer = read_operand 0 and index = read_operand 1 and value = read_operand 2 in
      let before = storage buffer and after = read_changed_storage () in
      require ~requirement:"be given an index at most the storage's length"
        Logic.(less_equal (int 0) index &&& less_equal index (length before));
      require (Logic.less (length before) (capacity buffer));
      assume_capacity_kept ();
      let limit = make_index_name () in
      Facts.assume context frame
        (Logic.conjunction
           [
             Logic.equal (length after) (Logic.add (length before) (Logic.int 1));
             Logic.equal (at after index) value;
           ]);
      Facts.assume context frame
        (all limit (Logic.int 0) index
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      let limit = make_index_name () in
      Facts.assume context frame
        (all limit index (length before)
           (Logic.equal
              (at after (Logic.add (Logic.Symbol limit) (Logic.int 1)))
              (at before (Logic.Symbol limit))));
      let limit = make_index_name () in
      Facts.assume context frame
        (all limit
           (Logic.add index (Logic.int 1))
           (length after)
           (Logic.equal (at after (Logic.Symbol limit))
              (at before (Logic.subtract (Logic.Symbol limit) (Logic.int 1)))));
      Facts.assume context frame
        (each_sum (fun sum measure ->
             Logic.equal (sum after) (Logic.add (sum before) (measure value))));
      known
  | Storage_remove ->
      let index = read_operand 1 in
      assume_capacity_kept ();
      let before = storage (read_operand 0) and after = read_changed_storage () in
      require_element context frame site element index before;
      let limit = make_index_name () in
      Facts.assume context frame
        (Logic.conjunction
           [
             Logic.equal (length after) (Logic.subtract (length before) (Logic.int 1));
             Logic.equal known (at before index);
           ]);
      Facts.assume context frame
        (all limit (Logic.int 0) index
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      let limit = make_index_name () in
      Facts.assume context frame
        (all limit index (length after)
           (Logic.equal (at after (Logic.Symbol limit))
              (at before (Logic.add (Logic.Symbol limit) (Logic.int 1)))));
      Facts.assume context frame
        (each_sum (fun sum measure ->
             Logic.equal (sum before) (Logic.add (sum after) (measure known))));
      known
  | Storage_swap ->
      assume_capacity_kept ();
      assume_swapped (storage (read_operand 0)) (read_changed_storage ())
  | View_swap -> assume_swapped (view (read_operand 0)) (view (List.hd changed))
  | Storage_view ->
      Facts.assume context frame (Logic.equal (view known) (storage (read_operand 0)));
      known
  | Compare_bytes -> make_byte_order context (view (read_operand 0)) (view (read_operand 1))
  | Find_byte ->
      let bytes = view (read_operand 0) and byte = read_operand 1 in
      let limit = make_index_name () in
      Facts.assume context frame
        Logic.(
          less_equal (int 0) known
          &&& less_equal known (length bytes)
          &&& (less known (length bytes) ==> equal (at bytes known) byte));
      Facts.assume context frame
        (all limit (Logic.int 0) known Logic.(not_ (equal (at bytes (Symbol limit)) byte)));
      known
  | View_slice ->
      let start = read_operand 1 and stop = read_operand 2 in
      let whole = view (read_operand 0) and part = view known in
      require ~requirement:"be given a range within the view"
        Logic.(
          less_equal (int 0) start &&& less_equal start stop &&& less_equal stop (length whole));
      let limit = make_index_name () in
      Facts.assume context frame (Logic.equal (length part) (Logic.subtract stop start));
      Facts.assume context frame
        (all limit (Logic.int 0) (length part)
           (Logic.equal (at part (Logic.Symbol limit))
              (at whole (Logic.add start (Logic.Symbol limit)))));
      known
  | View_address -> (
      match find_scalar_bytes element with
      | Some bytes ->
          let length =
            Models.make_sequence_length context element
              (make_buffer_model context View element (read_operand 0))
          in
          Facts.assume context frame
            Logic.(
              less_equal (add known (multiply (int bytes) length)) (Integer (Z.shift_left Z.one 64))
              &&& (greater length (int 0) ==> greater_equal known (int 1)));
          known
      | None -> known)
  | Array_view ->
      let array = read_passed 0 in
      Facts.assume context frame
        (Logic.equal
           (make_buffer_model context View element known)
           (Models.make_array_model context frame array.type_ array.term));
      known
  | Storage_from_array ->
      let array = read_passed 0 in
      let elements = make_buffer_model context Storage element known in
      let count = read_array_count array.type_ in
      Facts.assume context frame
        Logic.(
          equal elements (Models.make_array_model context frame array.type_ array.term)
          &&& equal (length elements) count
          &&& equal (capacity known) count);
      known
  | Array_from_storage ->
      let elements = make_buffer_model context Storage element (read_operand 0) in
      require ~requirement:"have as many elements as the array's count"
        (Logic.equal (length elements) (read_array_count result_type));
      Facts.assume context frame
        (Logic.equal (Models.make_array_model context frame result_type known) elements);
      known

let translate_lend context frame ~(site : Invocation.site) (lend : Intrinsic.lend) types
    (values : State.passed list) =
  match (types, values) with
  | element :: _, [ container; index ] ->
      let sequence =
        match lend with
        | Storage_at -> model_storage context frame element container.term
        | View_at -> model_buffer context frame View element container.term
      in
      require_element context frame site element index.term sequence;
      index_element context element sequence index.term
  | _ ->
      Facts.raise_bug "`%s` without an element type, a container, and an index"
        (Intrinsic.show_operation (Lend lend))

let read_invariant context (frame : State.frame) (values : State.passed list) result_type =
  match values with
  | [ subject; clause ] -> (
      match (clause.term, Validity.find_invariants context subject.type_) with
      | Logic.Integer index, Some (source, written) -> (
          match List.nth_opt written (Z.to_int index) with
          | Some invariant ->
              let inner =
                Validity.make_type_frame context frame source subject.type_
                  ~self:(Some subject.term)
              in
              snd (Validity.read_specification context inner invariant)
          | None -> Facts.arrive context frame "holds" result_type)
      | _ -> Facts.arrive context frame "holds" result_type)
  | _ -> Facts.arrive context frame "holds" result_type

let declare_system context (runtime : Intrinsic.runtime) kind =
  let make_symbol runtime = Logic.Symbol.System runtime in
  List.iter
    (fun other -> Facts.declare context (Logic.Constant (make_symbol other, Logic.Bool)))
    kind;
  Facts.run_once context
    (Exclusive (make_symbol runtime))
    (fun () ->
      List.iteri
        (fun index first ->
          List.iteri
            (fun later second ->
              if later > index then
                Facts.add_fact context
                  Logic.(not_ (Symbol (make_symbol first) &&& Symbol (make_symbol second))))
            kind)
        kind);
  Logic.Symbol (make_symbol runtime)

let translate_runtime context frame ~(site : Invocation.site) (runtime : Intrinsic.runtime)
    (values : State.passed list) ~changed result_type known =
  let operands = List.map (fun (passed : State.passed) -> passed.term) values in
  match runtime with
  | Holds_invariant -> read_invariant context frame values result_type
  | Shared_update ->
      Validity.assume_valid context frame result_type (Lazy.force known);
      Lazy.force known
  | Libc function_ -> call_libc context frame ~site function_ operands ~changed (Lazy.force known)
  | Libc_number number -> declare_libc_number context frame number
  | System_is_os _ ->
      declare_system context runtime (List.map (fun os -> Intrinsic.System_is_os os) Libc.oses)
  | System_is_architecture _ ->
      declare_system context runtime
        (List.map
           (fun architecture -> Intrinsic.System_is_architecture architecture)
           Libc.architectures)
  | Environment_entry ->
      let byte = Types.make_builtin UInt8 in
      let model = make_buffer_model context View byte (Lazy.force known) in
      let length = Models.make_sequence_length context byte model in
      (match
         Models.index_sequence context byte model (Logic.Symbol (Facts.make_variable "entry.index"))
       with
      | Some at ->
          Facts.assume context frame
            (Logic.forall
               ( [ (Facts.make_variable "entry.index", Logic.Int) ],
                 Logic.(
                   less_equal (int 0) (Symbol (Facts.make_variable "entry.index"))
                   &&& less (Symbol (Facts.make_variable "entry.index")) length
                   ==> not_ (equal at (int 0))) ))
      | None -> ());
      Lazy.force known
  | Handle_from -> (
      match operands with
      | [ descriptor ] ->
          Facts.assume context frame
            (Logic.equal (handle_descriptor context (Lazy.force known)) descriptor);
          Lazy.force known
      | _ -> Lazy.force known)
  | Handle_descriptor -> (
      match operands with
      | [ handle ] ->
          let descriptor = handle_descriptor context handle in
          Facts.assume context frame (Facts.make_in_range (Types.make_builtin Int32) descriptor);
          descriptor
      | _ -> Lazy.force known)
  | Crash | Handle_release | Run_test | Report_tests_to | Live_blocks | Coroutine_start
  | Coroutine_resume | Coroutine_suspend | Tasks_spawn | Shared_new | Shared_key ->
      Lazy.force known

let translate_intrinsic context frame ~(site : Invocation.site) (operation : Intrinsic.operation)
    types (values : State.passed list) ~changed result_type =
  let known = lazy (Facts.arrive context frame "result" result_type) in
  match operation with
  | Scalar scalar ->
      Operations.translate_primitive_operation context frame ~site scalar types
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
      translate_buffer_operation context frame ~site buffer element values ~changed result_type
        (Lazy.force known)
  | Lend lend -> translate_lend context frame ~site lend types values
  | Runtime runtime ->
      translate_runtime context frame ~site runtime values ~changed result_type known

let replace_element context frame element ~before ~after index part =
  let length sequence = Models.make_sequence_length context element sequence in
  let at = index_element context element in
  let limit = Facts.make_fresh_name context "index" in
  Facts.assume context frame
    (Logic.conjunction
       [ Logic.equal (length after) (length before); Logic.equal (at after index) part ]);
  Facts.assume context frame
    (Logic.forall
       ( [ (limit, Logic.Int) ],
         Logic.(
           less_equal (int 0) (Symbol limit)
           &&& less (Symbol limit) (length before)
           &&& not_ (equal (Symbol limit) index)
           ==> equal (at after (Symbol limit)) (at before (Symbol limit))) ))

let declare_buffer_slack context (ty : Types.ty) term =
  let symbol = Logic.Symbol.Slack ty in
  Facts.declare context (Logic.Function (symbol, [ Facts.declare_sort context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

let find_sequence_element context frame (sequence : Types.ty) =
  match sequence with
  | Types.Named { arguments = Types.Type element :: _; _ } ->
      Facts.substitute_type context frame element
  | _ -> Facts.raise_bug "an element of `%s`, which is no sequence" (Types.show sequence)

let find_sequence_model context frame (sequence : Types.ty) term =
  match sequence with
  | Types.Named { path; _ } when Well_known.find_builtin_type path = Some Array ->
      Models.make_array_model context frame sequence term
  | _ -> (
      match
        Models.find_model context sequence term
          ~element:(find_sequence_element context frame sequence)
      with
      | Some model -> model
      | None ->
          Facts.raise_unsupported Whole_definition "the elements of `%s`" (Types.show sequence))

let oblige_in_bounds context (frame : State.frame) ~origin condition =
  Facts.oblige context frame Out_of_bounds
    (Facts.locate context frame.source origin)
    [ Text "`"; Facts.quote frame.source origin; Text "` may not be within the collection." ]
    condition

let read_sequence_element context frame (sequence : Types.ty) term index ~node ~origin =
  let element = find_sequence_element context frame sequence in
  let model = find_sequence_model context frame sequence term in
  oblige_in_bounds context frame ~origin
    Logic.(
      less_equal (int 0) index &&& less index (Models.make_sequence_length context element model));
  Validity.note_place context frame ~node ~origin (One index);
  let read = index_element context element model index in
  Facts.assume context frame (Facts.make_in_range element read);
  Validity.assume_valid context frame element read;
  read

let write_sequence context frame (sequence : Types.ty) before ~write_model =
  let element = find_sequence_element context frame sequence in
  let after =
    match (sequence, Facts.find_constructors context sequence) with
    | Types.Named { path; _ }, _ when Well_known.find_builtin_type path = Some Array ->
        let after = Facts.arrive context frame "changed" sequence in
        write_model
          ~before:(Models.make_array_model context frame sequence before)
          ~after:(Models.make_array_model context frame sequence after);
        after
    | _, Some [ (None, [ (field, buffer_type) ]) ] ->
        ignore (Facts.declare_sort context sequence);
        let buffer = Validity.select_field context sequence None field before in
        let written = Facts.arrive context frame "changed" buffer_type in
        let builtin =
          match buffer_type with
          | Types.Named { path; _ } -> (
              match Well_known.find_builtin_type path with
              | Some ((Storage | View) as builtin) -> builtin
              | _ -> Facts.raise_bug "the field of `%s` is no buffer" (Types.show sequence))
          | _ -> Facts.raise_bug "the field of `%s` is no buffer" (Types.show sequence)
        in
        write_model
          ~before:(make_buffer_model context builtin element buffer)
          ~after:(make_buffer_model context builtin element written);
        if builtin = Storage then
          Facts.assume context frame
            (Logic.equal
               (make_buffer_capacity context element written)
               (make_buffer_capacity context element buffer));
        let after = Logic.Apply (Facts.make_constructor_symbol sequence None, [ written ]) in
        write_model
          ~before:(find_sequence_model context frame sequence before)
          ~after:(find_sequence_model context frame sequence after);
        after
    | _, None ->
        let after = Facts.arrive context frame "changed" sequence in
        write_model
          ~before:(find_sequence_model context frame sequence before)
          ~after:(find_sequence_model context frame sequence after);
        Facts.assume context frame
          (Logic.equal
             (declare_buffer_slack context sequence after)
             (declare_buffer_slack context sequence before));
        after
    | _, Some _ -> Facts.raise_bug "a sequence `%s` with more than one field" (Types.show sequence)
  in
  Validity.assume_valid context frame sequence after;
  after

let write_sequence_element context frame (sequence : Types.ty) before index part =
  let element = find_sequence_element context frame sequence in
  write_sequence context frame sequence before ~write_model:(fun ~before ~after ->
      replace_element context frame element ~before ~after index part)

let write_sequence_range context frame (sequence : Types.ty) before ~start ~stop slice =
  let element = find_sequence_element context frame sequence in
  let slice_model =
    find_sequence_model context frame
      (Types.Named { path = Well_known.make_path Slice; arguments = [ Types.Type element ] })
      slice
  in
  write_sequence context frame sequence before ~write_model:(fun ~before ~after ->
      assume_unchanged_outside context frame element ~before ~after ~start ~stop;
      Facts.assume context frame
        (Logic.equal (make_sequence_range context element after ~start ~stop) slice_model);
      let replaced = make_sequence_range context element before ~start ~stop in
      Facts.assume context frame
        (make_each_sum context element (fun sum _ ->
             Logic.equal
               (Logic.add (sum after) (sum replaced))
               (Logic.add (sum before) (sum slice_model)))))

let assume_same_length context frame (sequence : Types.ty) ~before ~after =
  let element = find_sequence_element context frame sequence in
  Facts.assume context frame
    (Logic.equal
       (Models.make_sequence_length context element
          (find_sequence_model context frame sequence after))
       (Models.make_sequence_length context element
          (find_sequence_model context frame sequence before)))
