let make_held_potential ty term =
  let symbol = Logic.Symbol.Potential ty in
  Logic.Apply (symbol, [ term ])

type buffer = {
  kind : Language.Builtin_type.t;
  element : Types.ty;
  model_of : Logic.term -> Logic.term;
}

type state = {
  holds_potential : bool Tables.Type_table.t;
  buffers : buffer option Tables.Type_table.t;
}

let state =
  Private_state.make_key (fun () ->
      { holds_potential = Tables.Type_table.create 16; buffers = Tables.Type_table.create 16 })

let compute_buffer (environment : State.environment) (query : Query.t) (ty : Types.ty) =
  match ty with
  | Types.Named { path; arguments = [ Types.Type element; Types.Value _ ] }
    when Well_known.find_builtin_type path = Some Array ->
      Option.map
        (fun model_of -> { kind = Array; element; model_of })
        (Models.find_model_function environment query ty
           ~model:(Encoding.make_sequence_type element))
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Well_known.find_builtin_type path = Some Storage ->
      Some
        {
          kind = Storage;
          element;
          model_of = (fun term -> Intrinsics.make_buffer_model Storage element term);
        }
  | Types.Named { path; arguments } when Types.find_builtin ty = None -> (
      match Interface.Definition.find_interface environment.lookups.interface path with
      | Some (Interface.Environment.Type_interface { shape = Record [ field ]; type_generics; _ })
        -> (
          let substitution = Types.make_substitution type_generics arguments in
          match Types.substitute_erased substitution field.field_type with
          | Types.Named { path = field_path; arguments = [ Types.Type element ] } -> (
              match Well_known.find_builtin_type field_path with
              | Some Storage ->
                  Option.map
                    (fun model_of -> { kind = Storage; element; model_of })
                    (Models.find_model_function environment query ty
                       ~model:(Encoding.make_sequence_type element))
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None

let find_buffer (environment : State.environment) (query : Query.t) (ty : Types.ty) =
  let buffers = (Query.read_state query state).buffers in
  match Tables.Type_table.find_opt buffers ty with
  | Some buffer -> buffer
  | None ->
      let buffer = compute_buffer environment query ty in
      Tables.Type_table.replace buffers ty buffer;
      buffer

let make_potential_measure (query : Query.t) element =
  let symbol = Logic.Symbol.Potential_measure element in
  let measure = Intrinsics.measure_type element in
  let term = Logic.Symbol symbol in
  Query.run_once query (Potential_of term) begin fun () ->
      let each = Logic.Symbol.Variable { label = "potential.element"; numbers = [] } in
      Query.add_fact query
        (Logic.forall
           ( [ (each, Encoding.sort_of element) ],
             Logic.equal
               (Callbacks.apply_function measure term [ Logic.Symbol each ])
               (make_held_potential element (Logic.Symbol each)) ))
    end;
  term

let sum_element_potentials (query : Query.t) element sequence =
  Intrinsics.make_sequence_sum element sequence (make_potential_measure query element)

let choose_by_variant ty term shape compute_variant =
  match shape with
  | [ (None, fields) ] -> compute_variant (None, fields)
  | variants -> (
      match List.rev variants with
      | last :: earlier ->
          List.fold_left
            (fun otherwise ((variant, _) as one) ->
              Logic.ite
                (Logic.Is (Encoding.make_constructor_symbol ty variant, term))
                (compute_variant one) otherwise)
            (compute_variant last) earlier
      | [] -> Costs.zero)

let find_declared_element (declared : Types.ty) ~(erased : Types.ty) =
  match declared with
  | Types.Named { arguments = Types.Type element :: _; _ }
    when Types.equal (Types.erase_views element) erased ->
      element
  | _ -> erased

let list_declared_fields (environment : State.environment) (declared : Types.ty) =
  match declared with
  | Types.Named { path; arguments } when Types.find_builtin declared = None -> (
      match Interface.Definition.find_interface environment.lookups.interface path with
      | Some (Interface.Environment.Type_interface interface) ->
          let substitution = Types.make_substitution interface.type_generics arguments in
          let declare variant =
            List.map (fun (field : Types.field) ->
                ((variant, field.field_name), Types.substitute substitution field.field_type))
          in
          Some
            (match interface.shape with
            | Record fields -> declare None fields
            | Sum variants ->
                List.concat_map
                  (fun (variant : Types.variant) ->
                    declare (Some variant.variant_name) (Option.value variant.fields ~default:[]))
                  variants
            | Todo_type | Builtin_type _ -> [])
      | _ -> None)
  | _ -> None

let find_potential_clause (environment : State.environment) (ty : Types.ty) =
  match Validity.find_type_clauses environment ty with
  | Some (source, { potential = Some potential; _ }) -> Some (source, potential)
  | _ -> None

let compute_declared_potential (frame : State.frame) (ty : Types.ty) term =
  match find_potential_clause frame.environment ty with
  | Some (source, written) ->
      snd
        (Validity.read_specification
           (Validity.make_type_frame frame source ty ~self:(Some term))
           written)
  | None -> Costs.zero

let rec has_potential (environment : State.environment) (query : Query.t) ?(seen = [])
    (declared : Types.ty) =
  if seen <> [] then holds_potential_type environment query ~seen declared
  else
    let holds_potential = (Query.read_state query state).holds_potential in
    match Tables.Type_table.find_opt holds_potential declared with
    | Some holds -> holds
    | None ->
        let holds = holds_potential_type environment query ~seen declared in
        Tables.Type_table.replace holds_potential declared holds;
        holds

and holds_potential_type (environment : State.environment) (query : Query.t) ~seen
    (declared : Types.ty) =
  let ty = Types.erase_views declared in
  if Types.is_view declared || List.exists (Types.equal declared) seen then false
  else
    match ty with
    | Parameter _ ->
        not
          (Interface.Impls.is_plain environment.lookups.interface ~list_bounds:environment.bounds ty)
    | Named _ when find_potential_clause environment ty <> None -> true
    | Named _ when Option.is_some (find_buffer environment query ty) -> (
        match find_buffer environment query ty with
        | Some { kind = Storage; _ } -> true
        | Some { element; _ } ->
            has_potential environment query ~seen:(declared :: seen)
              (find_declared_element declared ~erased:element)
        | None -> false)
    | Types.Named _ when Types.find_builtin ty = None -> (
        match list_declared_fields environment declared with
        | Some fields ->
            List.exists
              (fun (_, field_type) ->
                has_potential environment query ~seen:(declared :: seen) field_type)
              fields
        | None -> false)
    | Types.Named { arguments; _ } ->
        if
          List.exists
            (function
              | Types.Type element -> has_potential environment query ~seen:(ty :: seen) element
              | _ -> false)
            arguments
        then Facts.raise_unsupported Whole_definition Potential_of_elements
        else false
    | _ -> false

and compute_potential (frame : State.frame) ?(seen = []) (declared : Types.ty) term =
  if not (has_potential frame.environment frame.query declared) then Costs.zero
  else begin
    let ty = Types.erase_views declared in
    let held = make_held_potential declared term in
    if not (Logic.mentions frame.bound term) then
      Query.run_once frame.query (Potential_of held) begin fun () ->
          Facts.add_axiom frame
            Logic.(Validity.make_validity frame ~assuming:true ty term ==> less_equal (int 0) held);
          match
            ( find_potential_clause frame.environment ty,
              Encoding.find_constructors frame.environment ty )
          with
          | None, None when Option.is_some (find_buffer frame.environment frame.query ty) -> (
              match find_buffer frame.environment frame.query ty with
              | Some { kind; element; model_of } ->
                  let sequence = model_of term in
                  let slack = Intrinsics.make_buffer_slack ty term in
                  let length = Models.make_sequence_length element sequence in
                  Facts.add_axiom frame
                    Logic.(less_equal (int 0) slack &&& less_equal slack (multiply (int 2) length));
                  (match (ty, kind) with
                  | Types.Named { path; _ }, _ when Well_known.find_builtin_type path = Some Storage
                    ->
                      let saved =
                        Logic.subtract
                          (Logic.multiply (Logic.int 2) length)
                          (Intrinsics.make_buffer_capacity element term)
                      in
                      Facts.define frame slack
                        (Logic.ite (Logic.greater_equal saved (Logic.int 0)) saved (Logic.int 0))
                  | _, Array -> Facts.define frame slack (Logic.int 0)
                  | _ -> ());
                  let elements =
                    if
                      has_potential frame.environment frame.query
                        (find_declared_element declared ~erased:element)
                    then sum_element_potentials frame.query element sequence
                    else Costs.zero
                  in
                  Facts.define frame held (Logic.add slack elements)
              | None -> ())
          | _, Some shape -> (
              try
                let declared_potential = compute_declared_potential frame ty term in
                let parts =
                  choose_by_variant ty term shape
                    (compute_parts_potential frame ~seen declared term)
                in
                Facts.define frame held (Logic.add declared_potential parts)
              with Facts.Unsupported _ -> ())
          | _ -> ()
        end;
    match
      (find_potential_clause frame.environment ty, Encoding.find_constructors frame.environment ty)
    with
    | None, Some [ (None, fields) ] -> (
        try compute_parts_potential frame ~seen declared term (None, fields)
        with Facts.Unsupported _ -> held)
    | _ -> held
  end

and compute_parts_potential (frame : State.frame) ~seen declared term (variant, fields) =
  let ty = Types.erase_views declared in
  let declared_fields =
    Option.value ~default:[] (list_declared_fields frame.environment declared)
  in
  List.fold_left
    (fun total (field, erased_field_type) ->
      let field_type =
        Option.value ~default:erased_field_type (List.assoc_opt (variant, field) declared_fields)
      in
      if has_potential frame.environment frame.query field_type then
        let part = Encoding.select_field frame.environment ty variant field term in
        Logic.add total
          (if List.exists (Types.equal field_type) (declared :: seen) then
             make_held_potential field_type part
           else compute_potential frame ~seen:(declared :: seen) field_type part)
      else total)
    Costs.zero fields

let compute_elements_potential (environment : State.environment) (query : Query.t)
    (declared : Types.ty) term =
  let rec sum_elements ~enclosing (declared : Types.ty) term =
    if not (has_potential environment query declared) then Costs.zero
    else
      let ty = Types.erase_views declared in
      match Encoding.find_constructors environment ty with
      | Some shape -> (
          let declared_fields =
            Option.value ~default:[] (list_declared_fields environment declared)
          in
          let sum_fields (variant, fields) =
            List.fold_left
              (fun total (field, erased_field_type) ->
                let field_type =
                  Option.value ~default:erased_field_type
                    (List.assoc_opt (variant, field) declared_fields)
                in
                if List.exists (Types.equal field_type) (declared :: enclosing) then total
                else
                  Logic.add total
                    (sum_elements ~enclosing:(declared :: enclosing) field_type
                       (Encoding.select_field environment ty variant field term)))
              Costs.zero fields
          in
          try choose_by_variant ty term shape sum_fields with Facts.Unsupported _ -> Costs.zero)
      | None -> (
          match (find_potential_clause environment ty, find_buffer environment query ty) with
          | None, Some { element; model_of; _ }
            when has_potential environment query (find_declared_element declared ~erased:element) ->
              sum_element_potentials query element (model_of term)
          | _ -> Costs.zero)
  in
  sum_elements ~enclosing:[] declared term

let has_declared_potential (environment : State.environment) ty =
  Option.is_some (find_potential_clause environment ty)

let compute_arguments_potential_change ~(before : State.frame) ~(after : State.frame)
    (values : State.passed list) ~changed =
  List.fold_left
    (fun total (passed : State.passed) ->
      match passed.mode with
      | Language.Mode.Mut -> (
          match List.assoc_opt passed.position changed with
          | Some later ->
              Logic.add total
                (Logic.subtract
                   (compute_potential after passed.declared_type later)
                   (compute_potential before passed.declared_type passed.term))
          | None -> total)
      | Own -> Logic.subtract total (compute_potential before passed.declared_type passed.term)
      | Read -> total)
    Costs.zero values

let compute_call_potential_change ~before ~after values ~changed ~result_type ~result =
  Logic.add
    (compute_arguments_potential_change ~before ~after values ~changed)
    (compute_potential after result_type result)

let assume_element_potential_change (frame : State.frame) (sequence : Types.ty) ~before ~after
    ~replaced ~written =
  match find_buffer frame.environment frame.query sequence with
  | Some { element; model_of; _ } -> (
      try
        if has_potential frame.environment frame.query element then
          let sum term = sum_element_potentials frame.query element (model_of term) in
          Facts.assume frame
            (Logic.equal (sum after)
               (Logic.add
                  (Logic.subtract (sum before) (compute_potential frame element replaced))
                  (compute_potential frame element written)))
      with Facts.Unsupported _ -> ())
  | None -> ()

let spend_declared_potential (frame : State.frame) ty term =
  Counters.spend frame (fun (counter : Costs.counter) ->
      if counter.amortized then
        Counters.count_declared_potential frame.environment frame.query ~of_:ty
          (compute_declared_potential frame ty term)
      else Costs.zero)

let compute_enclosing_change ~(before : State.frame) ~(after : State.frame) (place : Mir.place)
    ~place_type ~read =
  let measure_declared (at : State.frame) prefix =
    let ty = place_type at prefix in
    if has_declared_potential before.environment ty then
      compute_declared_potential at ty (read { at with makes_obligations = false } prefix)
    else Costs.zero
  in
  snd
    (List.fold_left
       (fun (prefix, total) (projection : Mir.projection) ->
         let base = { place with Mir.projections = prefix } in
         ( prefix @ [ projection ],
           match projection with
           | Field _ | Variant_field _ ->
               Logic.add total
                 (Counters.count_declared_potential before.environment before.query
                    ~of_:(place_type after base)
                    (Logic.subtract (measure_declared after base) (measure_declared before base)))
           | Element _ | Range _ -> total ))
       ([], Costs.zero) place.Mir.projections)

let spend_enclosing_change (query : Query.t) ~before ~after alternatives ~place_type ~read =
  let parts =
    List.filter
      (fun (_, (place : Mir.place)) ->
        place.projections <> [] && match place.root with Local _ -> true | _ -> false)
      alternatives
  in
  if
    parts = []
    || not
         (List.exists
            (fun (counter : Costs.counter) -> counter.amortized)
            (Counters.list_counters query))
  then after
  else
    let change =
      lazy
        (List.fold_left
           (fun total (condition, place) ->
             Logic.add total
               (Costs.make_conditional_amount condition
                  (compute_enclosing_change ~before ~after place ~place_type ~read)))
           Costs.zero parts)
    in
    Counters.spend after (fun (counter : Costs.counter) ->
        if counter.amortized then Lazy.force change else Costs.zero)

let spend_forgotten roots ~(before : State.frame) ~(after : State.frame) =
  let measure (at : State.frame) =
    List.fold_left
      (fun total (root, ty) ->
        match
          match root with
          | Locals.Core_local Self -> at.self
          | root -> Locals.find_opt root at.locals
        with
        | Some term -> Logic.add total (compute_potential at ty term)
        | None -> total)
      Costs.zero roots
  in
  Counters.spend after (fun (counter : Costs.counter) ->
      if counter.amortized then
        Counters.count_whole_potential before.environment before.query
          (Logic.subtract (Logic.at_least_zero (measure after)) (measure before))
      else Costs.zero)

let spend_provided (frame : State.frame) potential =
  Counters.spend frame (fun (counter : Costs.counter) ->
      if counter.amortized || counter.counting <> Units then Costs.zero else Lazy.force potential)
