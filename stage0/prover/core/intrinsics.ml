let apply_slice context (frame : State.frame) (site : Invocation.site) ~(base_type : Types.ty)
    ~collection ~low ~high =
  let location = Facts.locate context frame.source site.origin in
  let element =
    match base_type with
    | Types.Named { arguments = Types.Type element :: _; _ } -> element
    | _ -> Facts.unsupported location "a slice of `%s`" (Types.show base_type)
  in
  let model =
    match Models.model_of context base_type collection ~element with
    | Some model -> model
    | None -> Facts.unsupported location "a slice of `%s`" (Types.show base_type)
  in
  let length = Models.sequence_length context element model in
  let high =
    match high with
    | Some high -> high
    | None ->
        Facts.assume context frame (Operation ("<=", [ Logic.int 0; length ]));
        length
  in
  Facts.oblige context frame Requires location
    [ Text "`"; Facts.quote frame.source site.origin; Text "` may not be within the collection." ]
    Logic.(
      Operation ("<=", [ int 0; low ])
      &&& Operation ("<=", [ low; high ])
      &&& Operation ("<=", [ high; length ]));
  Validity.note_place context frame site.origin (Run (low, high));
  let slice_type = Facts.substituted context frame site.type_ in
  let viewed = Facts.arrive context frame "slice" slice_type in
  (match Models.model_of context slice_type viewed ~element with
  | Some viewed_model -> (
      let count = Costs.minus high low in
      Facts.assume context frame
        (Logic.equal (Models.sequence_length context element viewed_model) count);
      let position = Facts.fresh_name context "index" in
      match
        ( Models.sequence_at context element viewed_model (Logic.Symbol position),
          Models.sequence_at context element model (Costs.plus low (Logic.Symbol position)) )
      with
      | Some inside, Some outside ->
          Facts.assume context frame
            (Logic.forall
               ( [ (position, Logic.Int) ],
                 Logic.(
                   Operation ("<=", [ int 0; Symbol position ])
                   &&& Operation ("<", [ Symbol position; count ])
                   ==> equal inside outside) ))
      | _ -> ())
  | None -> ());
  (frame, viewed, low, high)

let element_at context element term index =
  match Models.sequence_at context element term index with
  | Some term -> term
  | None -> raise (Facts.Foreign_unsupported "the elements of a sequence")

let unchanged_outside context frame element ~before ~after ~start ~stop =
  let length sequence = Models.sequence_length context element sequence in
  let at = element_at context element in
  let limit = Facts.fresh_name context "index" in
  let index = Logic.Symbol limit in
  Facts.assume context frame (Logic.equal (length after) (length before));
  Facts.assume context frame
    (Logic.forall
       ( [ (limit, Logic.Int) ],
         Logic.(
           Operation ("<=", [ int 0; index ])
           &&& Operation ("<", [ index; length before ])
           ==> (Operation ("<=", [ start; index ])
               &&& Operation ("<", [ index; stop ])
               ||| equal (at after index) (at before index))) ))

let sliced_owner_changed context frame ~(owner : State.passed_place) ~owner_type ~start ~stop =
  let element =
    match owner_type with
    | Types.Named { arguments = Types.Type element :: _; _ } -> element
    | _ ->
        raise (Facts.Foreign_unsupported (Printf.sprintf "a slice of `%s`" (Types.show owner_type)))
  in
  let before_value = owner.read frame in
  let changed = Facts.arrive context frame "changed" owner_type in
  match
    ( Models.model_of context owner_type before_value ~element,
      Models.model_of context owner_type changed ~element )
  with
  | Some before, Some after ->
      unchanged_outside context frame element ~before ~after ~start ~stop;
      Validity.assume_valid context frame owner_type changed;
      owner.write frame changed
  | _ ->
      raise (Facts.Foreign_unsupported (Printf.sprintf "a slice of `%s`" (Types.show owner_type)))

let slice_place context (site : Invocation.site) ~(owner : State.passed_place) ~owner_type ~low
    ~high =
  {
    State.read =
      (fun frame ->
        let frame = { frame with makes_obligations = false } in
        let _, viewed, _, _ =
          apply_slice context frame site ~base_type:(owner_type frame)
            ~collection:(owner.read frame) ~low ~high:(Some high)
        in
        viewed);
    write =
      (fun frame _ ->
        try
          sliced_owner_changed context frame ~owner ~owner_type:(owner_type frame) ~start:low
            ~stop:high
        with Facts.Unsupported _ | Facts.Foreign_unsupported _ ->
          owner.write frame (Facts.arrive context frame "changed" (owner_type frame)));
  }

let handle_descriptor context handle =
  let handle_sort = Facts.sort_of context (Types.make_builtin Handle) in
  Facts.declare context
    (Logic.Function (Logic.Symbol.Handle_descriptor, [ handle_sort ], Logic.Int));
  Logic.Apply (Logic.Symbol.Handle_descriptor, [ handle ])

let libc_number context frame (number : Libc.number) =
  let symbol = Logic.Symbol.Libc_number number in
  Facts.declare context (Logic.Constant (symbol, Logic.Int));
  let term = Logic.Symbol symbol in
  Facts.assume context frame
    (Facts.in_range (Types.make_builtin (Intrinsic.libc_builtin (Libc.number_type number))) term);
  term

let buffer_capacity context element term =
  let ty =
    Types.Named { path = Intrinsic.builtin_path Storage; arguments = [ Types.Type element ] }
  in
  let symbol = Logic.Symbol.Capacity ty in
  Facts.declare context (Logic.Function (symbol, [ Facts.sort_of context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

let buffer_model context (builtin : Intrinsic.builtin) element term =
  let ty =
    Types.Named { path = Intrinsic.builtin_path builtin; arguments = [ Types.Type element ] }
  in
  let symbol = Logic.Symbol.Model ty in
  Facts.declare context
    (Logic.Function
       (symbol, [ Facts.sort_of context ty ], Facts.sort_of context (Models.sequence_type element)));
  Logic.Apply (symbol, [ term ])

let libc_call context frame ~(site : Invocation.site) (function_ : Libc.function_) operands ~changed
    known =
  let { Libc.parameters; at_most; _ } = Libc.signature function_ in
  let arguments =
    List.concat_map
      (fun (name, (passes : Libc.passes)) ->
        match passes with
        | Value _ | Elements _ | Room _ | Elements_to_change _ -> [ (name, Some passes) ]
        | Written (_, names) -> List.map (fun name -> (name, None)) names
        | Always _ | Fixed _ -> [])
      parameters
  in
  let value_of name =
    List.find_map
      (fun (position, (named, _)) -> if named = name then List.nth_opt operands position else None)
      (List.mapi (fun position argument -> (position, argument)) arguments)
  in
  let count (extent : Libc.extent) =
    match extent with
    | Counted { by; each } ->
        Option.map
          (fun value ->
            if each = 1 then value else Logic.Operation ("*", [ Logic.int each; value ]))
          (value_of by)
    | Exactly elements -> Some (Logic.int elements)
    | Number number -> Some (libc_number context frame number)
    | Through_zero -> None
  in
  let needs requirement condition =
    Facts.oblige context frame Requires
      (Facts.locate context frame.source site.origin)
      [
        Text "`";
        Facts.quote frame.source site.origin;
        Text (Printf.sprintf "` may not %s." requirement);
      ]
      condition
  in
  let element_of scalar = Types.make_builtin (Intrinsic.libc_builtin scalar) in
  let length element sequence = Models.sequence_length context element sequence in
  List.iteri
    (fun position (_, passes) ->
      match (passes, List.nth_opt operands position, List.nth_opt changed position) with
      | ( Some ((Libc.Room (scalar, extent) | Elements_to_change (scalar, extent)) as passes),
          Some before,
          Some after ) -> (
          let element = element_of scalar in
          let model term = buffer_model context Storage element term in
          let capacity term = buffer_capacity context element term in
          Facts.assume context frame
            Logic.(
              equal (length element (model after)) (length element (model before))
              &&& equal (capacity after) (capacity before));
          match (passes, count extent) with
          | Room _, counted ->
              Facts.assume context frame (Logic.equal (model after) (model before));
              Option.iter
                (fun counted ->
                  needs "have the room it writes into"
                    (Logic.Operation
                       ( "<=",
                         [
                           Logic.Operation ("+", [ length element (model before); counted ]);
                           capacity before;
                         ] )))
                counted
          | _, Some counted ->
              needs "have the elements it mutates"
                (Logic.Operation ("<=", [ counted; length element (model before) ]))
          | _, None -> ())
      | Some (Libc.Elements (scalar, extent)), Some view, _ -> (
          let element = element_of scalar in
          let elements = buffer_model context View element view in
          match count extent with
          | Some counted ->
              needs "have the elements it reads"
                (Logic.Operation ("<=", [ counted; length element elements ]))
          | None ->
              let last = Logic.Operation ("-", [ length element elements; Logic.int 1 ]) in
              needs "end with a zero, which it reads up to"
                Logic.(
                  Operation (">=", [ length element elements; int 1 ])
                  &&&
                  match Models.sequence_at context element elements last with
                  | Some last_element -> equal last_element (int 0)
                  | None -> Boolean false))
      | _ -> ())
    arguments;
  (match Option.bind at_most value_of with
  | Some bound ->
      Facts.assume context frame
        Logic.(Operation (">=", [ known; int 0 ]) ==> Operation ("<=", [ known; bound ]))
  | None -> ());
  known

let measure_type element : Types.function_type =
  {
    inputs = [ (Types.Read, element) ];
    output = Types.Integer;
    uses = Types.no_capabilities;
    costs = [ { amortized = false; resource = Types.Time; bound = Finite_cost } ];
  }

let sequence_sum context element term measure =
  let path = Path.Method { owner = Models.sequence_path; name = "sum"; receiver = Read } in
  let symbol = Logic.Symbol.Function { callee = path; instance = [ Types.Type element ] } in
  Facts.declare context
    (Logic.Function
       ( symbol,
         [
           Facts.sort_of context (Models.sequence_type element);
           Facts.sort_of context (Types.Function (measure_type element));
         ],
         Logic.Int ));
  Logic.Apply (symbol, [ term; measure ])

let appended context frame element parts part =
  let longer =
    Facts.fresh context frame "parts" (Facts.sort_of context (Models.sequence_type element))
  in
  let length = Models.sequence_length context element parts in
  Facts.assume context frame
    Logic.(
      Operation (">=", [ length; int 0 ])
      &&& equal (Models.sequence_length context element longer) (Operation ("+", [ length; int 1 ])));
  (match (Models.sequence_at context element longer length, frame.bound) with
  | Some last, _ -> Facts.assume context frame (Logic.equal last part)
  | None, _ -> ());
  let index = Facts.fresh_name context "index" in
  (match
     ( Models.sequence_at context element longer (Logic.Symbol index),
       Models.sequence_at context element parts (Logic.Symbol index) )
   with
  | Some after, Some before ->
      Facts.assume context frame
        (Logic.forall
           ( [ (index, Logic.Int) ],
             Logic.(
               Operation ("<=", [ int 0; Symbol index ])
               &&& Operation ("<", [ Symbol index; length ])
               ==> equal after before) ))
  | _ -> ());
  let measure = Facts.fresh_name context "measure" in
  Facts.assume context frame
    (Logic.forall
       ( [ (measure, Facts.sort_of context (Types.Function (measure_type element))) ],
         Logic.equal
           (sequence_sum context element longer (Logic.Symbol measure))
           (Logic.Operation
              ( "+",
                [
                  sequence_sum context element parts (Logic.Symbol measure);
                  Lambdas.applied context (measure_type element) (Logic.Symbol measure) [ part ];
                ] )) ));
  longer

let byte_order context left right =
  let sequence = Facts.sort_of context (Models.sequence_type (Types.make_builtin UInt8)) in
  let symbol = Logic.Symbol.Compare_bytes_order in
  let first = not (Tables.Symbol_table.mem context.declared symbol) in
  Facts.declare context (Logic.Function (symbol, [ sequence; sequence ], Logic.Int));
  let order first_term second_term = Logic.Apply (symbol, [ first_term; second_term ]) in
  if first then begin
    let first_term = Logic.Symbol (Facts.variable "bytes.first")
    and second_term = Logic.Symbol (Facts.variable "bytes.second")
    and third_term = Logic.Symbol (Facts.variable "bytes.third") in
    let over names body = Logic.forall (List.map (fun name -> (name, sequence)) names, body) in
    List.iter (Facts.add_fact context)
      (List.rev
         [
           over
             [ Facts.variable "bytes.first"; Facts.variable "bytes.second" ]
             Logic.(
               Operation ("<=", [ int (-1); order first_term second_term ])
               &&& Operation ("<=", [ order first_term second_term; int 1 ])
               &&& (equal (order first_term second_term) (int 0) ==> equal first_term second_term)
               &&& equal (order second_term first_term)
                     (Operation ("-", [ order first_term second_term ])));
           over
             [ Facts.variable "bytes.first" ]
             (Logic.equal (order first_term first_term) (Logic.int 0));
           over
             [
               Facts.variable "bytes.first";
               Facts.variable "bytes.second";
               Facts.variable "bytes.third";
             ]
             Logic.(
               Operation ("<", [ order first_term second_term; int 0 ])
               &&& Operation ("<", [ order second_term third_term; int 0 ])
               ==> Operation ("<", [ order first_term third_term; int 0 ]));
         ])
  end;
  order left right

let buffer_operation context frame ~(site : Invocation.site) (operation : Intrinsic.operation)
    element operands ~changed known =
  let length sequence = Models.sequence_length context element sequence in
  let fits value =
    Logic.(Operation ("<=", [ int 0; value ]) &&& Facts.in_range (Types.make_builtin Int64) value)
  in
  let model builtin term =
    let sequence = buffer_model context builtin element term in
    Facts.assume context frame (fits (length sequence));
    sequence
  in
  let view = model Intrinsic.View in
  let capacity term = buffer_capacity context element term in
  let storage term =
    let sequence = model Intrinsic.Storage term in
    Facts.assume context frame
      Logic.(Operation ("<=", [ length sequence; capacity term ]) &&& fits (capacity term));
    sequence
  in
  let needs ?(requirement = "have the room it writes into") condition =
    Facts.oblige context frame Requires
      (Facts.locate context frame.source site.origin)
      [
        Text "`";
        Facts.quote frame.source site.origin;
        Text (Printf.sprintf "` may not %s." requirement);
      ]
      condition
  in
  let keeps_capacity () =
    Facts.assume context frame
      (Logic.equal (capacity (List.hd changed)) (capacity (List.hd operands)))
  in
  let at = element_at context element in
  let bound () = Facts.fresh_name context "index" in
  let in_interval index low high =
    Logic.(Operation ("<=", [ low; index ]) &&& Operation ("<", [ index; high ]))
  in
  let all name low high body =
    Logic.forall ([ (name, Logic.Int) ], Logic.(in_interval (Symbol name) low high ==> body))
  in
  let in_bounds index sequence = in_interval index (Logic.int 0) (length sequence) in
  let each_sum relation =
    let measure = Facts.fresh_name context "measure" in
    Logic.forall
      ( [ (measure, Facts.sort_of context (Types.Function (measure_type element))) ],
        relation
          (fun sequence -> sequence_sum context element sequence (Logic.Symbol measure))
          (fun value ->
            Lambdas.applied context (measure_type element) (Logic.Symbol measure) [ value ]) )
  in
  let changed_storage () = storage (List.hd changed) in
  match (operation, operands) with
  | Storage_model, [ buffer ] -> storage buffer
  | View_model, [ buffer ] -> view buffer
  | Storage_empty, _ ->
      Facts.assume context frame (Logic.equal (length (storage known)) (Logic.int 0));
      known
  | Storage_with_capacity, [ room ] ->
      Facts.assume context frame
        Logic.(equal (length (storage known)) (int 0) &&& equal (capacity known) room);
      known
  | Storage_length, [ buffer ] -> length (storage buffer)
  | View_length, [ buffer ] -> length (view buffer)
  | Storage_capacity, [ buffer ] ->
      ignore (storage buffer);
      capacity buffer
  | Storage_set_capacity, [ buffer; room ] ->
      needs (Logic.Operation (">=", [ room; length (storage buffer) ]));
      Facts.assume context frame (Logic.equal (changed_storage ()) (storage buffer));
      Facts.assume context frame (Logic.equal (capacity (List.hd changed)) room);
      known
  | Storage_lengthen, [ buffer; by ] ->
      let before = storage buffer and after = changed_storage () in
      needs
        (Logic.Operation ("<=", [ Logic.Operation ("+", [ length before; by ]); capacity buffer ]));
      keeps_capacity ();
      let limit = bound () in
      Facts.assume context frame
        (Logic.equal (length after) (Logic.Operation ("+", [ length before; by ])));
      Facts.assume context frame
        (all limit (Logic.int 0) (length before)
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      known
  | Storage_shorten, [ buffer; shorter ] ->
      let before = storage buffer and after = changed_storage () in
      needs ~requirement:"be given a length at most the storage's"
        (Logic.Operation ("<=", [ shorter; length before ]));
      keeps_capacity ();
      let limit = bound () in
      Facts.assume context frame (Logic.equal (length after) shorter);
      Facts.assume context frame
        (all limit (Logic.int 0) shorter
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      known
  | Storage_push, [ buffer; value ] ->
      needs (Logic.Operation ("<", [ length (storage buffer); capacity buffer ]));
      keeps_capacity ();
      let longer = appended context frame element (storage buffer) value in
      Facts.assume context frame (Logic.equal (changed_storage ()) longer);
      known
  | Storage_pop, [ _ ] ->
      keeps_capacity ();
      let longer = appended context frame element (changed_storage ()) known in
      Facts.assume context frame (Logic.equal (storage (List.hd operands)) longer);
      known
  | Storage_insert, [ buffer; index; value ] ->
      let before = storage buffer and after = changed_storage () in
      needs (Logic.Operation ("<", [ length before; capacity buffer ]));
      keeps_capacity ();
      let limit = bound () in
      Facts.assume context frame
        (Logic.conjunction
           [
             Logic.Operation ("<=", [ Logic.int 0; index ]);
             Logic.Operation ("<=", [ index; length before ]);
             Logic.equal (length after) (Logic.Operation ("+", [ length before; Logic.int 1 ]));
             Logic.equal (at after index) value;
           ]);
      Facts.assume context frame
        (all limit (Logic.int 0) index
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      let limit = bound () in
      Facts.assume context frame
        (all limit index (length before)
           (Logic.equal
              (at after (Logic.Operation ("+", [ Logic.Symbol limit; Logic.int 1 ])))
              (at before (Logic.Symbol limit))));
      let limit = bound () in
      Facts.assume context frame
        (all limit
           (Logic.Operation ("+", [ index; Logic.int 1 ]))
           (length after)
           (Logic.equal (at after (Logic.Symbol limit))
              (at before (Logic.Operation ("-", [ Logic.Symbol limit; Logic.int 1 ])))));
      Facts.assume context frame
        (each_sum (fun sum measure ->
             Logic.equal (sum after) (Logic.Operation ("+", [ sum before; measure value ]))));
      known
  | Storage_remove, [ buffer; index ] ->
      keeps_capacity ();
      let before = storage buffer and after = changed_storage () in
      let limit = bound () in
      Facts.assume context frame
        (Logic.conjunction
           [
             in_bounds index before;
             Logic.equal (length after) (Logic.Operation ("-", [ length before; Logic.int 1 ]));
             Logic.equal known (at before index);
           ]);
      Facts.assume context frame
        (all limit (Logic.int 0) index
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      let limit = bound () in
      Facts.assume context frame
        (all limit index (length after)
           (Logic.equal (at after (Logic.Symbol limit))
              (at before (Logic.Operation ("+", [ Logic.Symbol limit; Logic.int 1 ])))));
      Facts.assume context frame
        (each_sum (fun sum measure ->
             Logic.equal (sum before) (Logic.Operation ("+", [ sum after; measure known ]))));
      known
  | (Storage_swap | View_swap), [ buffer; first; second ] ->
      let before, after =
        if operation = View_swap then (view buffer, view (List.hd changed))
        else begin
          keeps_capacity ();
          (storage buffer, changed_storage ())
        end
      in
      let limit = bound () in
      Facts.assume context frame
        (Logic.conjunction
           [
             in_bounds first before;
             in_bounds second before;
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
  | (Storage_at | Storage_at_mut), [ buffer; index ] ->
      Facts.assume context frame (in_bounds index (storage buffer));
      at (storage buffer) index
  | View_at_mut, [ buffer; index ] ->
      Facts.assume context frame (in_bounds index (view buffer));
      at (view buffer) index
  | View_at, [ buffer; index ] ->
      Facts.assume context frame (in_bounds index (view buffer));
      at (view buffer) index
  | Storage_view, [ buffer ] ->
      Facts.assume context frame (Logic.equal (view known) (storage buffer));
      known
  | Compare_bytes, [ left; right ] -> byte_order context (view left) (view right)
  | View_slice, [ buffer; start; stop ] ->
      let whole = view buffer and part = view known in
      let limit = bound () in
      Facts.assume context frame
        (Logic.conjunction
           [
             Logic.Operation ("<=", [ Logic.int 0; start ]);
             Logic.Operation ("<=", [ start; stop ]);
             Logic.Operation ("<=", [ stop; length whole ]);
             Logic.equal (length part) (Logic.Operation ("-", [ stop; start ]));
           ]);
      Facts.assume context frame
        (all limit (Logic.int 0) (length part)
           (Logic.equal (at part (Logic.Symbol limit))
              (at whole (Logic.Operation ("+", [ start; Logic.Symbol limit ])))));
      known
  | _ -> known

let scalar_bytes element : int option =
  match Types.find_builtin element with
  | Some (Int8 | UInt8 | Bool) -> Some 1
  | Some (Int16 | UInt16) -> Some 2
  | Some (Int32 | UInt32 | Float32 | Character) -> Some 4
  | Some (Int64 | UInt64 | Float64) -> Some 8
  | _ -> None

let intrinsic context frame ~(site : Invocation.site) (operation : Intrinsic.operation) types
    operands ~arguments ~changed result_type =
  let known = lazy (Facts.arrive context frame "result" result_type) in
  match (operation, types) with
  | Shared_update, _ ->
      Validity.assume_valid context frame result_type (Lazy.force known);
      Lazy.force known
  | ( ( Storage_model | View_model | Storage_empty | Storage_with_capacity | Storage_length
      | Storage_capacity | Storage_set_capacity | Storage_lengthen | Storage_shorten | Storage_push
      | Storage_pop | Storage_insert | Storage_remove | Storage_swap | Storage_at | Storage_at_mut
      | Storage_view | View_at_mut | View_swap | View_length | View_at | View_slice ),
      element :: _ ) ->
      buffer_operation context frame ~site operation element operands ~changed (Lazy.force known)
  | Compare_bytes, _ ->
      buffer_operation context frame ~site operation (Types.make_builtin UInt8) operands ~changed
        (Lazy.force known)
  | Libc function_, _ ->
      libc_call context frame ~site function_ operands ~changed (Lazy.force known)
  | Libc_number number, _ -> libc_number context frame number
  | (System_is_os _ | System_is_architecture _), _ ->
      let symbol operation = Logic.Symbol.System operation in
      let kind =
        List.filter
          (fun (other : Intrinsic.operation) ->
            match (operation, other) with
            | System_is_os _, System_is_os _ | System_is_architecture _, System_is_architecture _ ->
                true
            | _ -> false)
          Intrinsic.operations
      in
      List.iter
        (fun other -> Facts.declare context (Logic.Constant (symbol other, Logic.Bool)))
        kind;
      Facts.once context
        (Exclusive (symbol operation))
        (fun () ->
          List.iteri
            (fun index first ->
              List.iteri
                (fun later second ->
                  if later > index then
                    Facts.add_fact context
                      Logic.(not_ (Symbol (symbol first) &&& Symbol (symbol second))))
                kind)
            kind);
      Logic.Symbol (symbol operation)
  | View_address, element :: _ when scalar_bytes element <> None -> (
      match (operands, scalar_bytes element) with
      | [ view ], Some bytes ->
          let length =
            Models.sequence_length context element (buffer_model context View element view)
          in
          Facts.assume context frame
            Logic.(
              Operation
                ( "<=",
                  [
                    Operation ("+", [ Lazy.force known; Operation ("*", [ int bytes; length ]) ]);
                    Integer (Z.shift_left Z.one 64);
                  ] )
              &&& (Operation (">", [ length; int 0 ])
                  ==> Operation (">=", [ Lazy.force known; int 1 ])));
          Lazy.force known
      | _ -> Lazy.force known)
  | Environment_entry, _ ->
      let byte = Types.make_builtin UInt8 in
      let model = buffer_model context View byte (Lazy.force known) in
      let length = Models.sequence_length context byte model in
      (match
         Models.sequence_at context byte model (Logic.Symbol (Facts.variable "entry.index"))
       with
      | Some at ->
          Facts.assume context frame
            (Logic.forall
               ( [ (Facts.variable "entry.index", Logic.Int) ],
                 Logic.(
                   Operation ("<=", [ int 0; Symbol (Facts.variable "entry.index") ])
                   &&& Operation ("<", [ Symbol (Facts.variable "entry.index"); length ])
                   ==> not_ (equal at (int 0))) ))
      | None -> ());
      Lazy.force known
  | Handle_from, _ -> (
      match operands with
      | [ descriptor ] ->
          Facts.assume context frame
            (Logic.equal (handle_descriptor context (Lazy.force known)) descriptor);
          Lazy.force known
      | _ -> Lazy.force known)
  | Handle_descriptor, _ -> (
      match operands with
      | [ handle ] ->
          let descriptor = handle_descriptor context handle in
          Facts.assume context frame (Facts.in_range (Types.make_builtin Int32) descriptor);
          descriptor
      | _ -> Lazy.force known)
  | _ ->
      Operations.primitive_operation context frame ~site operation types operands ~arguments
        ~fallback:(fun () -> Lazy.force known)

let replaced context frame element ~before ~after index part =
  let length sequence = Models.sequence_length context element sequence in
  let at = element_at context element in
  let limit = Facts.fresh_name context "index" in
  Facts.assume context frame
    (Logic.conjunction
       [ Logic.equal (length after) (length before); Logic.equal (at after index) part ]);
  Facts.assume context frame
    (Logic.forall
       ( [ (limit, Logic.Int) ],
         Logic.(
           Operation ("<=", [ int 0; Symbol limit ])
           &&& Operation ("<", [ Symbol limit; length before ])
           &&& not_ (equal (Symbol limit) index)
           ==> equal (at after (Symbol limit)) (at before (Symbol limit))) ))

let storage_updated context frame element storage index part =
  let storage_type =
    Types.Named { path = Intrinsic.builtin_path Storage; arguments = [ Types.Type element ] }
  in
  let updated = Facts.arrive context frame "changed" storage_type in
  replaced context frame element
    ~before:(buffer_model context Storage element storage)
    ~after:(buffer_model context Storage element updated)
    index part;
  Facts.assume context frame
    (Logic.equal
       (buffer_capacity context element updated)
       (buffer_capacity context element storage));
  updated

let array_updated context frame (array_type : Types.ty) array index part =
  match array_type with
  | Types.Named { arguments = Types.Type element :: _; _ } ->
      let updated = Facts.arrive context frame "changed" array_type in
      replaced context frame element
        ~before:(Models.array_model context frame array_type array)
        ~after:(Models.array_model context frame array_type updated)
        index part;
      updated
  | _ ->
      raise
        (Facts.Foreign_unsupported (Printf.sprintf "the elements of `%s`" (Types.show array_type)))

let element_written_back context frame ~(operation : Intrinsic.operation) ~type_arguments
    ~(receiver : State.passed_place) ~receiver_type index final =
  let element () =
    match type_arguments with
    | Types.Type element :: _ -> Facts.substituted context frame element
    | _ -> Facts.bug "an element's lend with no element type"
  in
  match operation with
  | Storage_at_mut ->
      receiver.write frame
        (storage_updated context frame (element ()) (receiver.read frame) index final)
  | Array_at_mut ->
      receiver.write frame
        (array_updated context frame receiver_type (receiver.read frame) index final)
  | View_at_mut ->
      let element = element () in
      let updated = Facts.arrive context frame "changed" receiver_type in
      replaced context frame element
        ~before:(buffer_model context View element (receiver.read frame))
        ~after:(buffer_model context View element updated)
        index final;
      receiver.write frame updated
  | _ -> Facts.bug "a lend of an element by an operation that lends none"
