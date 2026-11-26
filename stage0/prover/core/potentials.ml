let make_held_potential ty term =
  let symbol = Logic.Symbol.Potential ty in
  Logic.Apply (symbol, [ term ])

let compute_buffer (context : State.context) (ty : Types.ty) : State.buffer option =
  match ty with
  | Types.Named { path; arguments = [ Types.Type element; Types.Value _ ] }
    when Well_known.find_builtin_type path = Some Array ->
      Option.map
        (fun model_of -> { State.kind = Array; element; model_of })
        (Models.find_model_function context ty ~model:(Encoding.make_sequence_type element))
  | Types.Named { path; arguments = [ Types.Type element ] }
    when Well_known.find_builtin_type path = Some Storage ->
      Some
        {
          kind = Storage;
          element;
          model_of = (fun term -> Intrinsics.make_buffer_model Storage element term);
        }
  | Types.Named { path; arguments } when Types.find_builtin ty = None -> (
      match Interface.Definition.find_interface context.environment.lookups.interface path with
      | Some (Interface.Environment.Type_interface { shape = Record [ field ]; type_generics; _ })
        -> (
          let substitution = Types.make_substitution type_generics arguments in
          match Types.substitute_erased substitution field.field_type with
          | Types.Named { path = field_path; arguments = [ Types.Type element ] } -> (
              match Well_known.find_builtin_type field_path with
              | Some Storage ->
                  Option.map
                    (fun model_of -> { State.kind = Storage; element; model_of })
                    (Models.find_model_function context ty
                       ~model:(Encoding.make_sequence_type element))
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None

let find_buffer (context : State.context) (ty : Types.ty) =
  let key = ty in
  match Tables.Type_table.find_opt context.cost.buffers key with
  | Some buffer -> buffer
  | None ->
      let buffer = compute_buffer context ty in
      Tables.Type_table.replace context.cost.buffers key buffer;
      buffer

let declare_potential_measure (context : State.context) element =
  let symbol = Logic.Symbol.Potential_measure element in
  let measure = Intrinsics.measure_type element in
  let term = Logic.Symbol symbol in
  if not (List.mem term context.cost.potentials) then begin
    context.cost.potentials <- term :: context.cost.potentials;
    let each = Logic.Symbol.Variable { label = "potential.element"; numbers = [] } in
    Query.add_fact context.query
      (Logic.forall
         ( [ (each, Encoding.sort_of element) ],
           Logic.equal
             (Callbacks.apply_function measure term [ Logic.Symbol each ])
             (make_held_potential element (Logic.Symbol each)) ))
  end;
  term

let sum_element_potentials (context : State.context) element sequence =
  Intrinsics.make_sequence_sum context.query element sequence
    (declare_potential_measure context element)

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

let find_potential_clause (context : State.context) (ty : Types.ty) =
  match Validity.find_type_clauses context ty with
  | Some (source, { potential = Some potential; _ }) -> Some (source, potential)
  | _ -> None

let compute_declared_potential (context : State.context) frame (ty : Types.ty) term =
  match find_potential_clause context ty with
  | Some (source, written) ->
      snd
        (Validity.read_specification context
           (Validity.make_type_frame frame source ty ~self:(Some term))
           written)
  | None -> Costs.zero

let rec has_potential (context : State.context) ?(seen = []) (declared : Types.ty) =
  if seen <> [] then holds_potential_type context ~seen declared
  else
    match Tables.Type_table.find_opt context.cost.holds_potential declared with
    | Some holds -> holds
    | None ->
        let holds = holds_potential_type context ~seen declared in
        Tables.Type_table.replace context.cost.holds_potential declared holds;
        holds

and holds_potential_type (context : State.context) ~seen (declared : Types.ty) =
  let ty = Types.erase_views declared in
  if Types.is_view declared || List.exists (Types.equal declared) seen then false
  else
    match ty with
    | Parameter _ ->
        not
          (Interface.Impls.is_plain context.environment.lookups.interface
             ~list_bounds:context.environment.bounds ty)
    | Named _ when find_potential_clause context ty <> None -> true
    | Named _ when Option.is_some (find_buffer context ty) -> (
        match find_buffer context ty with
        | Some { kind = Storage; _ } -> true
        | Some { element; _ } ->
            has_potential context ~seen:(declared :: seen)
              (find_declared_element declared ~erased:element)
        | None -> false)
    | Types.Named _ when Types.find_builtin ty = None -> (
        match list_declared_fields context.environment declared with
        | Some fields ->
            List.exists
              (fun (_, field_type) -> has_potential context ~seen:(declared :: seen) field_type)
              fields
        | None -> false)
    | Types.Named { arguments; _ } ->
        if
          List.exists
            (function
              | Types.Type element -> has_potential context ~seen:(ty :: seen) element | _ -> false)
            arguments
        then Facts.raise_unsupported Whole_definition Potential_of_elements
        else false
    | _ -> false

and compute_potential (context : State.context) (frame : State.frame) ?(seen = [])
    (declared : Types.ty) term =
  if not (has_potential context declared) then Costs.zero
  else begin
    let ty = Types.erase_views declared in
    let held = make_held_potential declared term in
    if (not (List.mem held context.cost.potentials)) && not (Logic.mentions frame.bound term) then begin
      context.cost.potentials <- held :: context.cost.potentials;
      Facts.add_frame_fact frame
        Logic.(
          Validity.make_validity context frame ~assuming:true ty term ==> less_equal (int 0) held);
      match
        (find_potential_clause context ty, Encoding.find_constructors context.environment ty)
      with
      | None, None when Option.is_some (find_buffer context ty) -> (
          match find_buffer context ty with
          | Some { kind; element; model_of } ->
              let sequence = model_of term in
              let slack = Intrinsics.make_buffer_slack ty term in
              let length = Models.make_sequence_length context.query element sequence in
              Facts.add_frame_fact frame
                Logic.(less_equal (int 0) slack &&& less_equal slack (multiply (int 2) length));
              (match (ty, kind) with
              | Types.Named { path; _ }, _ when Well_known.find_builtin_type path = Some Storage ->
                  let saved =
                    Logic.subtract
                      (Logic.multiply (Logic.int 2) length)
                      (Intrinsics.make_buffer_capacity element term)
                  in
                  Facts.add_frame_fact frame
                    (Logic.equal slack
                       (Logic.ite (Logic.greater_equal saved (Logic.int 0)) saved (Logic.int 0)))
              | _, Array -> Facts.add_frame_fact frame (Logic.equal slack (Logic.int 0))
              | _ -> ());
              let elements =
                if has_potential context (find_declared_element declared ~erased:element) then
                  sum_element_potentials context element sequence
                else Costs.zero
              in
              Facts.add_frame_fact frame (Logic.equal held (Logic.add slack elements))
          | None -> ())
      | _, Some shape -> (
          try
            let declared_potential = compute_declared_potential context frame ty term in
            let parts =
              choose_by_variant ty term shape
                (compute_parts_potential context frame ~seen declared term)
            in
            Facts.add_frame_fact frame (Logic.equal held (Logic.add declared_potential parts))
          with Facts.Unsupported _ -> ())
      | _ -> ()
    end;
    match (find_potential_clause context ty, Encoding.find_constructors context.environment ty) with
    | None, Some [ (None, fields) ] -> (
        try compute_parts_potential context frame ~seen declared term (None, fields)
        with Facts.Unsupported _ -> held)
    | _ -> held
  end

and compute_parts_potential (context : State.context) frame ~seen declared term (variant, fields) =
  let ty = Types.erase_views declared in
  let declared_fields =
    Option.value ~default:[] (list_declared_fields context.environment declared)
  in
  List.fold_left
    (fun total (field, erased_field_type) ->
      let field_type =
        Option.value ~default:erased_field_type (List.assoc_opt (variant, field) declared_fields)
      in
      if has_potential context field_type then
        let part = Encoding.select_field context.environment ty variant field term in
        Logic.add total
          (if List.exists (Types.equal field_type) (declared :: seen) then
             make_held_potential field_type part
           else compute_potential context frame ~seen:(declared :: seen) field_type part)
      else total)
    Costs.zero fields

let compute_elements_potential (context : State.context) (declared : Types.ty) term =
  let rec sum_elements ~enclosing (declared : Types.ty) term =
    if not (has_potential context declared) then Costs.zero
    else
      let ty = Types.erase_views declared in
      match Encoding.find_constructors context.environment ty with
      | Some shape -> (
          let declared_fields =
            Option.value ~default:[] (list_declared_fields context.environment declared)
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
                       (Encoding.select_field context.environment ty variant field term)))
              Costs.zero fields
          in
          try choose_by_variant ty term shape sum_fields with Facts.Unsupported _ -> Costs.zero)
      | None -> (
          match (find_potential_clause context ty, find_buffer context ty) with
          | None, Some { element; model_of; _ }
            when has_potential context (find_declared_element declared ~erased:element) ->
              sum_element_potentials context element (model_of term)
          | _ -> Costs.zero)
  in
  sum_elements ~enclosing:[] declared term

let has_declared_potential (context : State.context) ty =
  Option.is_some (find_potential_clause context ty)

let compute_arguments_potential_change (context : State.context) ~(before : State.frame)
    ~(after : State.frame) (values : State.passed list) ~changed =
  List.fold_left
    (fun total (passed : State.passed) ->
      match passed.mode with
      | Language.Mode.Mut -> (
          match List.assoc_opt passed.position changed with
          | Some later ->
              Logic.add total
                (Logic.subtract
                   (compute_potential context after passed.declared_type later)
                   (compute_potential context before passed.declared_type passed.term))
          | None -> total)
      | Own ->
          Logic.subtract total (compute_potential context before passed.declared_type passed.term)
      | Read -> total)
    Costs.zero values

let compute_call_potential_change (context : State.context) ~before ~after values ~changed
    ~result_type ~result =
  Logic.add
    (compute_arguments_potential_change context ~before ~after values ~changed)
    (compute_potential context after result_type result)

let assume_element_potential_change (context : State.context) frame (sequence : Types.ty) ~before
    ~after ~replaced ~written =
  match find_buffer context sequence with
  | Some { element; model_of; _ } -> (
      try
        if has_potential context element then
          let sum term = sum_element_potentials context element (model_of term) in
          Facts.assume frame
            (Logic.equal (sum after)
               (Logic.add
                  (Logic.subtract (sum before) (compute_potential context frame element replaced))
                  (compute_potential context frame element written)))
      with Facts.Unsupported _ -> ())
  | None -> ()

let spend_declared_potential (context : State.context) frame ty term =
  Counters.spend context frame (fun (counter : Costs.counter) ->
      if counter.amortized then
        Counters.count_declared_potential context ~of_:ty
          (compute_declared_potential context frame ty term)
      else Costs.zero)

let compute_enclosing_change (context : State.context) ~(before : State.frame)
    ~(after : State.frame) (place : Mir.place) ~place_type ~read =
  let measure_declared (at : State.frame) prefix =
    let ty = place_type at prefix in
    if has_declared_potential context ty then
      compute_declared_potential context at ty (read { at with makes_obligations = false } prefix)
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
                 (Counters.count_declared_potential context ~of_:(place_type after base)
                    (Logic.subtract (measure_declared after base) (measure_declared before base)))
           | Element _ | Range _ -> total ))
       ([], Costs.zero) place.Mir.projections)

let spend_enclosing_change (context : State.context) ~before ~after alternatives ~place_type ~read =
  let parts =
    List.filter
      (fun (_, (place : Mir.place)) ->
        place.projections <> [] && match place.root with Local _ -> true | _ -> false)
      alternatives
  in
  if
    parts = []
    || not (List.exists (fun (counter : Costs.counter) -> counter.amortized) context.cost.counters)
  then after
  else
    let change =
      lazy
        (List.fold_left
           (fun total (condition, place) ->
             Logic.add total
               (Costs.make_conditional_amount condition
                  (compute_enclosing_change context ~before ~after place ~place_type ~read)))
           Costs.zero parts)
    in
    Counters.spend context after (fun (counter : Costs.counter) ->
        if counter.amortized then Lazy.force change else Costs.zero)

let spend_forgotten (context : State.context) roots ~(before : State.frame) ~(after : State.frame) =
  let measure (at : State.frame) =
    List.fold_left
      (fun total (root, ty) ->
        match
          match root with
          | Locals.Core_local Self -> at.self
          | root -> Locals.find_opt root at.locals
        with
        | Some term -> Logic.add total (compute_potential context at ty term)
        | None -> total)
      Costs.zero roots
  in
  Counters.spend context after (fun (counter : Costs.counter) ->
      if counter.amortized then
        Counters.count_whole_potential context
          (Logic.subtract (Logic.at_least_zero (measure after)) (measure before))
      else Costs.zero)

let spend_provided (context : State.context) frame potential =
  Counters.spend context frame (fun (counter : Costs.counter) ->
      if counter.amortized || counter.counting <> Units then Costs.zero else Lazy.force potential)
