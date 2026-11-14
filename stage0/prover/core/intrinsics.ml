(* Slices, calls of the C library, buffers, and the intrinsics. *)

open State
open Facts
open Validity
open Operations
open Models
open Lambdas

(* A slice, [items[a..b]]: a view of the elements from [a] to before [b],
   which must be within the collection, whose model is that run of the
   collection's model. *)

(* A slice of [collection], of [base_type], from [low] to before [high], or
   to its end. *)
let apply_slice context frame (site : Invocation.site) ~(base_type : Types.ty) ~collection ~low
    ~high =
  let span = span_of frame.source site.origin in
  let element =
    match base_type with
    | Types.Named { arguments = Types.Type element :: _; _ } -> element
    | _ -> unsupported span "a slice of `%s`" (Types.show base_type)
  in
  let model =
    match model_of context base_type collection ~element with
    | Some model -> model
    | None -> unsupported span "a slice of `%s`" (Types.show base_type)
  in
  let length = sequence_length context element model in
  let high =
    match high with
    | Some high -> high
    | None ->
        assume context frame (Operation ("<=", [ Logic.int 0; length ]));
        length
  in
  oblige context frame Requires span
    (Printf.sprintf "`%s` may not be within the collection." (quote frame.source site.origin))
    Logic.(
      Operation ("<=", [ int 0; low ])
      &&& Operation ("<=", [ low; high ])
      &&& Operation ("<=", [ high; length ]));
  note_place context frame site.origin (Run (low, high));
  let slice_type = substituted context frame site.type_ in
  let viewed = arrive context frame "slice" slice_type in
  (match model_of context slice_type viewed ~element with
  | Some viewed_model -> (
      let count = Costs.minus high low in
      assume context frame (Logic.equal (sequence_length context element viewed_model) count);
      let position = fresh_name context "index" in
      match
        ( sequence_at context element viewed_model (Logic.Symbol position),
          sequence_at context element model (Costs.plus low (Logic.Symbol position)) )
      with
      | Some inside, Some outside ->
          assume context frame
            (Logic.forall
               ( [ (position, Logic.Int) ],
                 Logic.(
                   Operation ("<=", [ int 0; Symbol position ])
                   &&& Operation ("<", [ Symbol position; count ])
                   ==> equal inside outside) ))
      | _ -> ())
  | None -> ());
  (frame, viewed, low, high)

(* [sequence_at], for a sequence whose elements the prover reads. *)
let element_at context element term index =
  match sequence_at context element term index with
  | Some term -> term
  | None -> raise (Foreign_unsupported "the elements of a sequence")

(* That one sequence is another as long, the same outside the run from
   [start] to before [stop], and, where [run] is given, [run]'s elements in
   that run. *)
let run_replaced context frame element ~before ~after ~start ~stop ~run =
  let length sequence = sequence_length context element sequence in
  let at = element_at context element in
  let limit = fresh_name context "index" in
  let index = Logic.Symbol limit in
  let inside =
    match run with
    | Some run -> Logic.equal (at after index) (at run (Logic.Operation ("-", [ index; start ])))
    | None -> Logic.Boolean true
  in
  assume context frame (Logic.equal (length after) (length before));
  assume context frame
    (Logic.forall
       ( [ (limit, Logic.Int) ],
         Logic.(
           Operation ("<=", [ int 0; index ])
           &&& Operation ("<", [ index; length before ])
           ==> ite
                 (Operation ("<=", [ start; index ]) &&& Operation ("<", [ index; stop ]))
                 inside
                 (equal (at after index) (at before index))) ))

(* The owner of a slice lent to mutate, after the change: as long as it
   was, and the same outside the slice's run. *)
let sliced_owner_changed context frame ~(owner : passed_place) ~owner_type ~start ~stop =
  let element =
    match owner_type with
    | Types.Named { arguments = Types.Type element :: _; _ } -> element
    | _ -> raise (Foreign_unsupported (Printf.sprintf "a slice of `%s`" (Types.show owner_type)))
  in
  let before_value = owner.read frame in
  let changed = arrive context frame "changed" owner_type in
  match
    (model_of context owner_type before_value ~element, model_of context owner_type changed ~element)
  with
  | Some before, Some after ->
      run_replaced context frame element ~before ~after ~start ~stop ~run:None;
      assume_valid context frame owner_type changed;
      owner.write frame changed
  | _ -> raise (Foreign_unsupported (Printf.sprintf "a slice of `%s`" (Types.show owner_type)))

let slice_place context (site : Invocation.site) ~(owner : passed_place) ~owner_type ~low ~high =
  {
    read =
      (fun frame ->
        let frame = { frame with checking = false } in
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
        with Unsupported _ | Foreign_unsupported _ ->
          owner.write frame (arrive context frame "changed" (owner_type frame)));
  }

(* The result of an intrinsic operation on integers, as the compiler declares
   it. Arithmetic that stops the program on overflow or a zero divisor gives
   the exact result when it returns; wrapping arithmetic gives the exact
   result brought into range by a remainder; the overflow tests, the
   comparisons, and [fits] are exact; and [convert] keeps a value that
   fits. Anything else is known by its type alone. *)
let handle_descriptor context handle =
  let handle_sort = sort_of context (Types.builtin Handle) in
  declare context (Logic.Function (Symbol.Handle_descriptor, [ handle_sort ], Logic.Int));
  Logic.Apply (Symbol.Handle_descriptor, [ handle ])

(* A number of the system that the C library's headers define, such as
   [PATH_MAX]: one constant, whatever call gives it, so the room a caller
   makes for it and the room a function needs are the same term. *)
let libc_number context frame (number : Libc.number) =
  let symbol = Symbol.Libc_number (Libc.number_name number) in
  declare context (Logic.Constant (symbol, Logic.Int));
  let term = Logic.Symbol symbol in
  assume context frame
    (in_range (Types.builtin (Intrinsic.libc_builtin (Libc.number_type number))) term);
  term

(* How many elements a storage has room for, as a function of it. *)
let buffer_capacity context element term =
  let ty =
    Types.Named { path = Intrinsic.builtin_path Storage; arguments = [ Types.Type element ] }
  in
  let symbol = Symbol.Capacity (type_key ty) in
  declare context (Logic.Function (symbol, [ sort_of context ty ], Logic.Int));
  Logic.Apply (symbol, [ term ])

(* The sequence a storage or a view holds, as a function of it. *)
let buffer_model context (builtin : Intrinsic.builtin) element term =
  let ty =
    Types.Named { path = Intrinsic.builtin_path builtin; arguments = [ Types.Type element ] }
  in
  let symbol = Symbol.Model (type_key ty) in
  declare context
    (Logic.Function (symbol, [ sort_of context ty ], sort_of context (sequence_type element)));
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
    oblige context frame Requires
      (span_of frame.source site.origin)
      (Printf.sprintf "`%s` may not %s." (quote frame.source site.origin) requirement)
      condition
  in
  let element_of scalar = Types.builtin (Intrinsic.libc_builtin scalar) in
  let length element sequence = sequence_length context element sequence in
  List.iteri
    (fun position (_, passes) ->
      match (passes, List.nth_opt operands position, List.nth_opt changed position) with
      | ( Some ((Libc.Room (scalar, extent) | Elements_to_change (scalar, extent)) as passes),
          Some before,
          Some after ) -> (
          let element = element_of scalar in
          let model term = buffer_model context Storage element term in
          let capacity term = buffer_capacity context element term in
          assume context frame
            Logic.(
              equal (length element (model after)) (length element (model before))
              &&& equal (capacity after) (capacity before));
          match (passes, count extent) with
          | Room _, counted ->
              assume context frame (Logic.equal (model after) (model before));
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
                  match sequence_at context element elements last with
                  | Some last_element -> equal last_element (int 0)
                  | None -> Boolean false))
      | _ -> ())
    arguments;
  (match Option.bind at_most value_of with
  | Some bound ->
      assume context frame
        Logic.(Operation (">=", [ known; int 0 ]) ==> Operation ("<=", [ known; bound ]))
  | None -> ());
  known

(* The type of a sum's measure: [fn(Element) -> Integer cost time finite]. *)
let measure_type element : Types.function_type =
  {
    inputs = [ (Types.Read, element) ];
    output = Returns Types.Integer;
    uses = Types.no_capabilities;
    costs = [ { amortized = false; resource = Types.Time; bound = Finite_cost } ];
  }

(* A sequence's sum, by [standard::specification]'s [Sequence.sum], over a
   measure of its elements. *)
let sequence_sum context element term measure =
  let path = Path.Method { owner = sequence_path; name = "sum"; receiver = Read } in
  let symbol = Symbol.Function { callee = path; instance = [ type_key element ] } in
  declare context
    (Logic.Function
       ( symbol,
         [
           sort_of context (sequence_type element);
           sort_of context (Types.Function (measure_type element));
         ],
         Logic.Int ));
  Logic.Apply (symbol, [ term; measure ])

(* The parts, with one more after them. *)
let appended context frame element parts part =
  let longer = fresh context frame "parts" (sort_of context (sequence_type element)) in
  let length = sequence_length context element parts in
  assume context frame
    Logic.(
      Operation (">=", [ length; int 0 ])
      &&& equal (sequence_length context element longer) (Operation ("+", [ length; int 1 ])));
  (match (sequence_at context element longer length, frame.bound) with
  | Some last, _ -> assume context frame (Logic.equal last part)
  | None, _ -> ());
  let index = fresh_name context "index" in
  (match
     ( sequence_at context element longer (Logic.Symbol index),
       sequence_at context element parts (Logic.Symbol index) )
   with
  | Some after, Some before ->
      assume context frame
        (Logic.forall
           ( [ (index, Logic.Int) ],
             Logic.(
               Operation ("<=", [ int 0; Symbol index ])
               &&& Operation ("<", [ Symbol index; length ])
               ==> equal after before) ))
  | _ -> ());
  (* Each sum over the longer sequence adds the new part's measure, as
     [Sequence.append]'s contract says. *)
  let measure = fresh_name context "measure" in
  assume context frame
    (Logic.forall
       ( [ (measure, sort_of context (Types.Function (measure_type element))) ],
         Logic.equal
           (sequence_sum context element longer (Logic.Symbol measure))
           (Logic.Operation
              ( "+",
                [
                  sequence_sum context element parts (Logic.Symbol measure);
                  applied context (measure_type element) (Logic.Symbol measure) [ part ];
                ] )) ));
  longer

(* [compare_bytes] of two byte sequences, as the compiler makes it: their
   lexicographic order, below zero, zero, or above zero, which is zero
   exactly when they are the same bytes, and is a total order. *)
let byte_order context left right =
  let sequence = sort_of context (sequence_type (Types.builtin UInt8)) in
  let symbol = Symbol.Compare_bytes_order in
  let first = not (Hashtbl.mem context.declared symbol) in
  declare context (Logic.Function (symbol, [ sequence; sequence ], Logic.Int));
  let order first_term second_term = Logic.Apply (symbol, [ first_term; second_term ]) in
  if first then begin
    let first_term = Logic.Symbol (variable "bytes.first")
    and second_term = Logic.Symbol (variable "bytes.second")
    and third_term = Logic.Symbol (variable "bytes.third") in
    let over names body = Logic.forall (List.map (fun name -> (name, sequence)) names, body) in
    List.iter (add_fact context)
      (List.rev
         [
           over
             [ variable "bytes.first"; variable "bytes.second" ]
             Logic.(
               Operation ("<=", [ int (-1); order first_term second_term ])
               &&& Operation ("<=", [ order first_term second_term; int 1 ])
               &&& (equal (order first_term second_term) (int 0) ==> equal first_term second_term)
               &&& equal (order second_term first_term)
                     (Operation ("-", [ order first_term second_term ])));
           over [ variable "bytes.first" ] (Logic.equal (order first_term first_term) (Logic.int 0));
           over
             [ variable "bytes.first"; variable "bytes.second"; variable "bytes.third" ]
             Logic.(
               Operation ("<", [ order first_term second_term; int 0 ])
               &&& Operation ("<", [ order second_term third_term; int 0 ])
               ==> Operation ("<", [ order first_term third_term; int 0 ]));
         ])
  end;
  order left right

(* The intrinsic storage and view operations, as the compiler declares
   them: a storage or a view is modeled as the sequence of its elements,
   and each operation reads or mutates that sequence. An operation that
   stops the program on a bad index assumes on return that the index was
   valid. *)
let buffer_operation context frame ~(site : Invocation.site) (operation : Intrinsic.operation)
    element operands ~changed known =
  let length sequence = sequence_length context element sequence in
  (* No buffer is larger than C lets an object be, half the address space,
     so a buffer's length fits an [ISize] as well as a [USize]. *)
  let fits value =
    Logic.(Operation ("<=", [ int 0; value ]) &&& in_range (Types.builtin ISize) value)
  in
  let model builtin term =
    let sequence = buffer_model context builtin element term in
    assume context frame (fits (length sequence));
    sequence
  in
  let view = model Intrinsic.View in
  (* A storage also has room for some elements, at least as many as it
     holds. *)
  let capacity term = buffer_capacity context element term in
  let storage term =
    let sequence = model Intrinsic.Storage term in
    assume context frame
      Logic.(Operation ("<=", [ length sequence; capacity term ]) &&& fits (capacity term));
    sequence
  in
  let needs ?(requirement = "have the room it writes into") condition =
    oblige context frame Requires
      (span_of frame.source site.origin)
      (Printf.sprintf "`%s` may not %s." (quote frame.source site.origin) requirement)
      condition
  in
  let keeps_capacity () =
    assume context frame (Logic.equal (capacity (List.hd changed)) (capacity (List.hd operands)))
  in
  let at = element_at context element in
  let bound () = fresh_name context "index" in
  let in_interval index low high =
    Logic.(Operation ("<=", [ low; index ]) &&& Operation ("<", [ index; high ]))
  in
  let all name low high body =
    Logic.forall ([ (name, Logic.Int) ], Logic.(in_interval (Symbol name) low high ==> body))
  in
  let in_bounds index sequence = in_interval index (Logic.int 0) (length sequence) in
  let each_sum relation =
    let measure = fresh_name context "measure" in
    Logic.forall
      ( [ (measure, sort_of context (Types.Function (measure_type element))) ],
        relation
          (fun sequence -> sequence_sum context element sequence (Logic.Symbol measure))
          (fun value -> applied context (measure_type element) (Logic.Symbol measure) [ value ]) )
  in
  let changed_storage () = storage (List.hd changed) in
  match (operation, operands) with
  | Storage_model, [ buffer ] -> storage buffer
  | View_model, [ buffer ] -> view buffer
  | Storage_empty, _ ->
      assume context frame (Logic.equal (length (storage known)) (Logic.int 0));
      known
  | Storage_with_capacity, [ room ] ->
      assume context frame
        Logic.(equal (length (storage known)) (int 0) &&& equal (capacity known) room);
      known
  | Storage_length, [ buffer ] -> length (storage buffer)
  | View_length, [ buffer ] -> length (view buffer)
  | Storage_capacity, [ buffer ] ->
      ignore (storage buffer);
      capacity buffer
  | Storage_set_capacity, [ buffer; room ] ->
      needs (Logic.Operation (">=", [ room; length (storage buffer) ]));
      assume context frame (Logic.equal (changed_storage ()) (storage buffer));
      assume context frame (Logic.equal (capacity (List.hd changed)) room);
      known
  | Storage_lengthen, [ buffer; by ] ->
      (* The elements the C library wrote into the spare capacity join the storage. *)
      let before = storage buffer and after = changed_storage () in
      needs
        (Logic.Operation ("<=", [ Logic.Operation ("+", [ length before; by ]); capacity buffer ]));
      keeps_capacity ();
      let limit = bound () in
      assume context frame
        (Logic.equal (length after) (Logic.Operation ("+", [ length before; by ])));
      assume context frame
        (all limit (Logic.int 0) (length before)
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      known
  | Storage_shorten, [ buffer; shorter ] ->
      (* The first [shorter] elements, in the same room. *)
      let before = storage buffer and after = changed_storage () in
      needs ~requirement:"be given a length at most the storage's"
        (Logic.Operation ("<=", [ shorter; length before ]));
      keeps_capacity ();
      let limit = bound () in
      assume context frame (Logic.equal (length after) shorter);
      assume context frame
        (all limit (Logic.int 0) shorter
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      known
  | Storage_push, [ buffer; value ] ->
      needs (Logic.Operation ("<", [ length (storage buffer); capacity buffer ]));
      keeps_capacity ();
      let longer = appended context frame element (storage buffer) value in
      assume context frame (Logic.equal (changed_storage ()) longer);
      known
  | Storage_pop, [ _ ] ->
      keeps_capacity ();
      let longer = appended context frame element (changed_storage ()) known in
      assume context frame (Logic.equal (storage (List.hd operands)) longer);
      known
  | Storage_insert, [ buffer; index; value ] ->
      let before = storage buffer and after = changed_storage () in
      needs (Logic.Operation ("<", [ length before; capacity buffer ]));
      keeps_capacity ();
      let limit = bound () in
      assume context frame
        (Logic.conjunction
           [
             Logic.Operation ("<=", [ Logic.int 0; index ]);
             Logic.Operation ("<=", [ index; length before ]);
             Logic.equal (length after) (Logic.Operation ("+", [ length before; Logic.int 1 ]));
             Logic.equal (at after index) value;
           ]);
      assume context frame
        (all limit (Logic.int 0) index
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      let limit = bound () in
      assume context frame
        (all limit index (length before)
           (Logic.equal
              (at after (Logic.Operation ("+", [ Logic.Symbol limit; Logic.int 1 ])))
              (at before (Logic.Symbol limit))));
      let limit = bound () in
      assume context frame
        (all limit
           (Logic.Operation ("+", [ index; Logic.int 1 ]))
           (length after)
           (Logic.equal (at after (Logic.Symbol limit))
              (at before (Logic.Operation ("-", [ Logic.Symbol limit; Logic.int 1 ])))));
      assume context frame
        (each_sum (fun sum measure ->
             Logic.equal (sum after) (Logic.Operation ("+", [ sum before; measure value ]))));
      known
  | Storage_remove, [ buffer; index ] ->
      keeps_capacity ();
      let before = storage buffer and after = changed_storage () in
      let limit = bound () in
      assume context frame
        (Logic.conjunction
           [
             in_bounds index before;
             Logic.equal (length after) (Logic.Operation ("-", [ length before; Logic.int 1 ]));
             Logic.equal known (at before index);
           ]);
      assume context frame
        (all limit (Logic.int 0) index
           (Logic.equal (at after (Logic.Symbol limit)) (at before (Logic.Symbol limit))));
      let limit = bound () in
      assume context frame
        (all limit index (length after)
           (Logic.equal (at after (Logic.Symbol limit))
              (at before (Logic.Operation ("+", [ Logic.Symbol limit; Logic.int 1 ])))));
      assume context frame
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
      assume context frame
        (Logic.conjunction
           [
             in_bounds first before;
             in_bounds second before;
             Logic.equal (length after) (length before);
             Logic.equal (at after first) (at before second);
             Logic.equal (at after second) (at before first);
           ]);
      assume context frame
        (all limit (Logic.int 0) (length before)
           Logic.(
             not_ (equal (Symbol limit) first)
             &&& not_ (equal (Symbol limit) second)
             ==> equal (at after (Symbol limit)) (at before (Symbol limit))));
      assume context frame (each_sum (fun sum _ -> Logic.equal (sum after) (sum before)));
      known
  | (Storage_at | Storage_at_mut), [ buffer; index ] ->
      assume context frame (in_bounds index (storage buffer));
      at (storage buffer) index
  | View_at_mut, [ buffer; index ] ->
      assume context frame (in_bounds index (view buffer));
      at (view buffer) index
  | Storage_view_mut, [ buffer ] ->
      (* A view of the storage's elements, to mutate them through. The
         storage keeps its elements; a static one gets a buffer of its own,
         so its capacity may change. *)
      assume context frame
        Logic.(equal (view known) (storage buffer) &&& equal (changed_storage ()) (storage buffer));
      known
  | (Storage_take_view | View_take_view), [ owner; part; start ] ->
      let before, after =
        if operation = View_take_view then (view owner, view (List.hd changed))
        else (storage owner, changed_storage ())
      in
      let run = view part in
      needs Logic.(Operation ("<=", [ Operation ("+", [ start; length run ]); length before ]));
      if operation = Storage_take_view then keeps_capacity ();
      run_replaced context frame element ~before ~after ~start
        ~stop:(Logic.Operation ("+", [ start; length run ]))
        ~run:(Some run);
      known
  | View_at, [ buffer; index ] ->
      assume context frame (in_bounds index (view buffer));
      at (view buffer) index
  | Storage_view, [ buffer ] ->
      assume context frame (Logic.equal (view known) (storage buffer));
      known
  | Compare_bytes, [ left; right ] -> byte_order context (view left) (view right)
  | View_slice, [ buffer; start; stop ] ->
      let whole = view buffer and part = view known in
      let limit = bound () in
      assume context frame
        (Logic.conjunction
           [
             Logic.Operation ("<=", [ Logic.int 0; start ]);
             Logic.Operation ("<=", [ start; stop ]);
             Logic.Operation ("<=", [ stop; length whole ]);
             Logic.equal (length part) (Logic.Operation ("-", [ stop; start ]));
           ]);
      assume context frame
        (all limit (Logic.int 0) (length part)
           (Logic.equal (at part (Logic.Symbol limit))
              (at whole (Logic.Operation ("+", [ start; Logic.Symbol limit ])))));
      known
  | _ -> known

let intrinsic context frame ~(site : Invocation.site) (operation : Intrinsic.operation) types
    operands ~arguments ~changed result_type =
  (* A value of the result's type, made only where an operation needs one,
     so that an operation the logic models adds no symbol. *)
  let known = lazy (arrive context frame "result" result_type) in
  match (operation, types) with
  | Shared_update, _ ->
      (* [change]'s result, which is a function value's result: valid. *)
      assume_valid context frame result_type (Lazy.force known);
      Lazy.force known
  | ( ( Storage_model | View_model | Storage_empty | Storage_with_capacity | Storage_length
      | Storage_capacity | Storage_set_capacity | Storage_lengthen | Storage_shorten | Storage_push
      | Storage_pop | Storage_insert | Storage_remove | Storage_swap | Storage_at | Storage_at_mut
      | Storage_view | View_at_mut | View_swap | Storage_view_mut | Storage_take_view
      | View_take_view | View_length | View_at | View_slice ),
      element :: _ ) ->
      buffer_operation context frame ~site operation element operands ~changed (Lazy.force known)
  | Compare_bytes, _ ->
      buffer_operation context frame ~site operation (Types.builtin UInt8) operands ~changed
        (Lazy.force known)
  | Libc function_, _ ->
      libc_call context frame ~site function_ operands ~changed (Lazy.force known)
  | Libc_number number, _ -> libc_number context frame number
  | (System_is_os _ | System_is_architecture _), _ ->
      (* The system a program runs on is one for the whole run, and it is at
         most one operating system and one architecture. *)
      let symbol operation = Symbol.System (Intrinsic.operation_name operation) in
      let kind =
        List.filter
          (fun (other : Intrinsic.operation) ->
            match (operation, other) with
            | System_is_os _, System_is_os _ | System_is_architecture _, System_is_architecture _ ->
                true
            | _ -> false)
          Intrinsic.operations
      in
      List.iter (fun other -> declare context (Logic.Constant (symbol other, Logic.Bool))) kind;
      once context
        (Exclusive (symbol operation))
        (fun () ->
          List.iteri
            (fun index first ->
              List.iteri
                (fun later second ->
                  if later > index then
                    add_fact context Logic.(not_ (Symbol (symbol first) &&& Symbol (symbol second))))
                kind)
            kind);
      Logic.Symbol (symbol operation)
  | View_address, element :: _ when scalar_bytes element <> None -> (
      (* A view's elements lie in memory, so they end within the address
         space, and a view with any is not at zero. *)
      match (operands, scalar_bytes element) with
      | [ view ], Some bytes ->
          let length = sequence_length context element (buffer_model context View element view) in
          assume context frame
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
      (* An entry is a C string without its end, so none of its bytes is
         zero. *)
      let byte = Types.builtin UInt8 in
      let model = buffer_model context View byte (Lazy.force known) in
      let length = sequence_length context byte model in
      (match sequence_at context byte model (Logic.Symbol (variable "entry.index")) with
      | Some at ->
          assume context frame
            (Logic.forall
               ( [ (variable "entry.index", Logic.Int) ],
                 Logic.(
                   Operation ("<=", [ int 0; Symbol (variable "entry.index") ])
                   &&& Operation ("<", [ Symbol (variable "entry.index"); length ])
                   ==> not_ (equal at (int 0))) ))
      | None -> ());
      Lazy.force known
  | Handle_from, _ -> (
      match operands with
      | [ descriptor ] ->
          assume context frame
            (Logic.equal (handle_descriptor context (Lazy.force known)) descriptor);
          Lazy.force known
      | _ -> Lazy.force known)
  | Handle_descriptor, _ -> (
      match operands with
      | [ handle ] ->
          let descriptor = handle_descriptor context handle in
          assume context frame (in_range (Types.builtin Int32) descriptor);
          descriptor
      | _ -> Lazy.force known)
  | _ ->
      primitive_operation context frame ~site operation types operands ~arguments
        ~fallback:(fun () -> Lazy.force known)
