let ( let* ) = Option.bind

type loop_exits = {
  loop : Core.id;
  mutable breaks : State.frame list;
  mutable ends : State.frame list;
}

type branch_exit = { exited : State.frame; exit_locals : Locals.local list }

type run = {
  infos : Mir.local_info array;
  changed_in_place : (Mir.local, unit) Hashtbl.t;
  lambdas : Mir.body array;
  mutable loops : loop_exits list;
  mutable cancelled : (Mir.task * branch_exit list ref) list;
  mutable returns : State.function_exit list;
  mutable lends : State.lent_part list;
}

let resolve_callee (frame : State.frame) (callee : Mir.callee) ~lends =
  Callee.resolve frame callee.target ~lends ~uses:callee.uses

let find_declared_fields (environment : State.environment) ty variant =
  match Encoding.find_visible_type environment ty with
  | Some (interface, substitution) -> (
      let list_fields (list : Types.field list) =
        List.map
          (fun (field : Types.field) ->
            (field.field_name, Types.substitute_erased substitution field.field_type))
          list
      in
      match (interface.shape, variant) with
      | Record list, None -> Some (list_fields list)
      | Sum variants, Some name -> (
          match
            List.find_opt (fun (variant : Types.variant) -> variant.variant_name = name) variants
          with
          | Some { fields = Some list; _ } -> Some (list_fields list)
          | Some { fields = None; _ } -> Some []
          | None -> None)
      | _ -> None)
  | None -> None

let rec compute_place_type (frame : State.frame) run (place : Mir.place) =
  match place.Mir.projections with
  | [] -> (
      match place.Mir.root with
      | Local local -> Encoding.substitute_type frame run.infos.(local).type_
      | Constant path ->
          Interface.Definition.read_constant_type frame.environment.lookups.interface path
      | Literal { type_; _ } -> Encoding.substitute_type frame type_)
  | _ -> (
      let base =
        { place with Mir.projections = List.rev (List.tl (List.rev place.Mir.projections)) }
      in
      let base_type = compute_place_type frame run base in
      let find_field_type variant field =
        match
          Option.bind
            (find_declared_fields frame.environment base_type variant)
            (List.assoc_opt field)
        with
        | Some field_type -> Encoding.substitute_type frame field_type
        | None -> Facts.raise_unsupported Whole_definition (Field field)
      in
      match List.nth place.Mir.projections (List.length place.Mir.projections - 1) with
      | Field field -> find_field_type None field
      | Variant_field { variant; field } -> find_field_type (Some variant) field
      | Element _ -> Intrinsics.find_sequence_element frame base_type
      | Range _ ->
          if Types.is_well_known String base_type then base_type
          else
            Types.make_named (Well_known.make_path List)
              [ Intrinsics.find_sequence_element frame base_type ])

let rec resolve_aliases (frame : State.frame) run (place : Mir.place) :
    (Logic.term * Mir.place) list =
  match place.Mir.root with
  | Local local -> (
      match Locals.find_opt (Locals.make_key run.infos local) frame.aliases with
      | Some bound ->
          List.concat_map
            (fun (bound_on, bound_place) ->
              List.map
                (fun (condition, (resolved : Mir.place)) ->
                  ( Logic.( &&& ) bound_on condition,
                    {
                      resolved with
                      Mir.projections = resolved.Mir.projections @ place.Mir.projections;
                    } ))
                (resolve_aliases frame run bound_place))
            bound
      | None -> [ (Logic.Boolean true, place) ])
  | Constant _ | Literal _ -> [ (Logic.Boolean true, place) ]

let expand_place frame run (place : Mir.place) =
  match resolve_aliases frame run place with
  | [ (_, place) ] -> place
  | _ -> Facts.raise_unsupported Whole_definition Alternatives_binding_mut

let describe_local : Mir.local_kind -> string = function
  | Source { local; _ } -> (
      match Mir.find_local_name local with
      | Some name -> Printf.sprintf "`%s`" name
      | None -> "a local that the compiler introduces")
  | Temporary -> "a temporary"
  | Lent _ -> "a lent part"

let read_root (frame : State.frame) run (root : Mir.root) =
  match root with
  | Constant path -> Values.evaluate_constant frame path
  | Literal { value; type_ } ->
      Values.make_literal_value frame (Encoding.substitute_type frame type_) value
  | Local local -> (
      match Locals.make_key run.infos local with
      | Core_local Self -> (
          match frame.self with
          | Some self -> self
          | None ->
              Facts.raise_bug "`%s` reads `self` outside a method"
                (Resolve.Names.show_key frame.source.key))
      | key -> (
          match Locals.find_opt key frame.locals with
          | Some term ->
              Callbacks.check_read frame term;
              term
          | None ->
              Facts.raise_bug "`%s` reads %s before the prover binds it"
                (Resolve.Names.show_key frame.source.key)
                (describe_local run.infos.(local).kind)))

let rec read_resolved (frame : State.frame) run (place : Mir.place) =
  let _, term =
    List.fold_left
      (fun (prefix, term) (projection : Mir.projection) ->
        let base = { place with Mir.projections = prefix } in
        let base_type = compute_place_type frame run base in
        let projected = { place with Mir.projections = prefix @ [ projection ] } in
        let project_field variant field =
          if Encoding.find_constructors frame.environment base_type = None then
            Facts.raise_unsupported Whole_definition (Hidden_field_of base_type);
          Values.project_field frame base_type variant field
            (compute_place_type frame run projected)
            term
        in
        ( prefix @ [ projection ],
          match projection with
          | Field field -> project_field None field
          | Variant_field { variant; field } -> project_field (Some variant) field
          | Element { node; index; origin; _ } ->
              Intrinsics.read_sequence_element frame base_type term (read_index frame run index)
                ~node ~origin
          | Range { node; start; stop; origin; _ } ->
              let _, viewed, _, _ =
                Intrinsics.apply_range frame ~node
                  { origin; type_ = compute_place_type frame run projected }
                  ~base_type ~collection:term ~low:(read_index frame run start)
                  ~high:(Option.map (read_index frame run) stop)
              in
              viewed ))
      ([], read_root frame run place.Mir.root)
      place.Mir.projections
  in
  term

and read_index (frame : State.frame) run (index : Mir.operand) =
  match index with
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> (
      match (read_resolved frame run place, frame.bound) with
      | ((Logic.Symbol _ | Logic.Integer _) as term), _ | term, _ :: _ -> term
      | computed, [] ->
          let named = Facts.declare_fresh frame "index" Logic.Int in
          Facts.assume frame (Logic.equal named computed);
          named)
  | Immediate { value = Integer number; _ } -> Logic.Integer number
  | Immediate { value = Unit | Float _ | Boolean _; _ } ->
      Facts.raise_bug "an index that is not an integer"

let read_place (frame : State.frame) run (place : Mir.place) =
  match resolve_aliases frame run place with
  | [ (_, place) ] -> read_resolved frame run place
  | alternatives -> (
      match List.rev alternatives with
      | (_, first) :: later ->
          List.fold_left
            (fun otherwise (condition, place) ->
              Logic.ite condition (read_resolved frame run place) otherwise)
            (read_resolved frame run first) later
      | [] -> Facts.raise_bug "a place that is no place")

let write_resolved (frame : State.frame) run (place : Mir.place) ~check_element ~is_valid new_value
    =
  let rec rebuild prefix whole = function
    | [] -> new_value
    | (projection : Mir.projection) :: rest -> (
        let base_type = compute_place_type frame run { place with Mir.projections = prefix } in
        let projected = { place with Mir.projections = prefix @ [ projection ] } in
        let part_type = compute_place_type frame run projected in
        let rebuilt part = rebuild (prefix @ [ projection ]) part rest in
        let replace_part variant field =
          let part = Values.project_field frame base_type variant field part_type whole in
          Encoding.replace_field frame.environment base_type variant field whole (rebuilt part)
        in
        match projection with
        | Field field -> replace_part None field
        | Variant_field { variant; field } -> replace_part (Some variant) field
        | Element { node; index; origin; _ } ->
            let index = read_index frame run index in
            let replaced =
              Intrinsics.read_sequence_element frame base_type whole index ~node ~origin
            in
            let element = rebuilt replaced in
            if rest <> [] || not is_valid then check_element ~origin part_type element;
            let after = Intrinsics.write_sequence_element frame base_type whole index element in
            Potentials.assume_element_potential_change frame base_type ~before:whole ~after
              ~replaced ~written:element;
            after
        | Range { node; start; stop; origin; _ } ->
            let _, viewed, start, stop =
              Intrinsics.apply_range frame ~node { origin; type_ = part_type } ~base_type
                ~collection:whole ~low:(read_index frame run start)
                ~high:(Option.map (read_index frame run) stop)
            in
            Intrinsics.write_sequence_range frame base_type whole ~start ~stop ~range_type:part_type
              (rebuilt viewed))
  in
  match place.Mir.root with
  | Constant _ | Literal _ -> Facts.raise_unsupported Whole_definition Constant_assignment
  | Local local -> (
      if place.Mir.projections <> [] || not is_valid then
        Hashtbl.replace run.changed_in_place local ();
      let whole =
        if place.Mir.projections = [] then new_value
        else rebuild [] (read_root frame run place.Mir.root) place.Mir.projections
      in
      match Locals.make_key run.infos local with
      | Core_local Self -> { frame with self = Some whole }
      | key -> Facts.bind frame key (Encoding.substitute_type frame run.infos.(local).type_) whole)

let write_alternatives (frame : State.frame) run alternatives ~check_element ~is_valid new_value =
  let write_resolved frame place =
    write_resolved frame run place ~check_element ~is_valid new_value
  in
  match alternatives with
  | [ (_, place) ] -> write_resolved frame place
  | alternatives ->
      List.fold_left
        (fun frame (condition, (place : Mir.place)) ->
          let written = write_resolved frame place in
          match place.Mir.root with
          | Constant _ | Literal _ -> written
          | Local local -> (
              match Locals.make_key run.infos local with
              | Core_local Self -> (
                  match (written.self, frame.self) with
                  | Some after, Some before ->
                      { frame with self = Some (Logic.ite condition after before) }
                  | _ -> written)
              | key -> (
                  match (Locals.find_opt key written.locals, Locals.find_opt key frame.locals) with
                  | Some after, Some before ->
                      Facts.bind frame key
                        (Encoding.substitute_type frame run.infos.(local).type_)
                        (Logic.ite condition after before)
                  | _ -> written)))
        frame alternatives

let write_through (frame : State.frame) run (place : Mir.place) ~check_element ~is_valid new_value =
  let alternatives = resolve_aliases frame run place in
  Potentials.spend_enclosing_change frame.query ~before:frame
    ~after:(write_alternatives frame run alternatives ~check_element ~is_valid new_value)
    alternatives
    ~place_type:(fun at place -> compute_place_type at run place)
    ~read:(fun at place -> read_resolved at run place)

let check_changed_element (frame : State.frame) ~origin element_type element =
  Validity.check_valid frame (Facts.locate frame origin) element_type element ~deep:true
    ~moment:Element_changed

let write_place (frame : State.frame) run place new_value =
  write_through frame run place ~check_element:(check_changed_element frame) ~is_valid:true
    new_value

let write_place_until_its_write_ends (frame : State.frame) run place ~is_valid new_value =
  let changed_elements = ref [] in
  let written =
    write_through frame run place ~is_valid new_value
      ~check_element:(fun ~origin element_type element ->
        changed_elements := (origin, element_type, element) :: !changed_elements)
  in
  ( written,
    fun (after : State.frame) ->
      List.iter
        (fun (origin, element_type, element) ->
          check_changed_element after ~origin element_type element)
        (List.rev !changed_elements) )

let describe_root (frame : State.frame) (info : Mir.local_info) : Catalog.Prover.value =
  match info.kind with
  | Source { local = Self; _ } -> Self_value
  | Source { local = Declared { name; _ } | Trait_parameter { name; _ }; _ } -> Named name
  | Source { local = Synthetic _; _ } -> Quoted (Facts.quote frame.source info.origin)
  | Temporary | Lent _ -> Temporary

let compute_changes ?(also = []) (environment : State.environment) run (frame : State.frame)
    (blocks : Mir.block list) =
  let is_bound : Locals.local -> bool = function
    | Core_local Self -> Option.is_some frame.self
    | key -> Locals.mem key frame.locals
  in
  let list_parts (place : Mir.place) =
    List.filter_map
      (fun (_, (place : Mir.place)) ->
        match place.Mir.root with
        | Local local ->
            let root = Locals.make_key run.infos local in
            if is_bound root then
              Some
                {
                  State.root;
                  root_description = describe_root frame run.infos.(local);
                  declared_root_type =
                    Encoding.substitute_declared_type frame run.infos.(local).type_;
                  fields = Mir.list_leading_fields place.Mir.projections;
                }
            else None
        | Constant _ | Literal _ -> None)
      (resolve_aliases frame run place)
  in
  let parts =
    List.sort_uniq compare
      (List.concat_map
         (fun (changed : Mir.changed) -> list_parts changed.place)
         (Mir.list_changed_places
            ~list_modified:
              (Mir.list_callee_modified_parts
                 ~read_signature:(Contracts.read_signature environment)
                 environment.lookups.interface frame.substitution)
            blocks)
      @ List.concat_map list_parts also)
  in
  List.filter
    (fun (part : State.changed_part) ->
      not
        (List.exists
           (fun (other : State.changed_part) ->
             other <> part && other.root = part.root
             && Types.is_field_path_prefix other.fields part.fields)
           parts))
    parts

let forget_changes (frame : State.frame) (changed : State.changed_part list) =
  let roots =
    List.sort_uniq compare
      (List.map (fun (part : State.changed_part) -> (part.root, part.declared_root_type)) changed)
  in
  Potentials.spend_forgotten roots ~before:frame ~after:(Loops.havoc frame changed)

let read_operand (frame : State.frame) run (operand : Mir.operand) =
  match operand with
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> read_place frame run place
  | Immediate { value; type_ } -> (
      let ty = Encoding.substitute_type frame type_ in
      match value with
      | Unit -> Logic.Apply (Logic.Symbol.Unit, [])
      | Integer number -> Logic.Integer number
      | Float number -> (
          match Encoding.find_float_format ty with
          | Some format -> Operations.make_float_literal format number
          | None -> Facts.raise_unsupported Whole_definition Float_literal_without_type)
      | Boolean truth -> Logic.Boolean truth)

let compute_operand_type (frame : State.frame) operand =
  Encoding.substitute_type frame (Mir.extract_operand_type operand)

let find_operand_origin : Mir.operand -> Core.origin option = function
  | Use { origin; _ } | Borrow { origin; _ } | Take { origin; _ } -> Some origin
  | Immediate _ -> None

let make_passed_place run place =
  {
    State.read = (fun frame -> read_place { frame with makes_obligations = false } run place);
    write = (fun frame -> write_place_until_its_write_ends frame run place);
  }

let find_argument_place run (mode : Language.Mode.t) (value : Mir.operand) =
  match (mode, value) with
  | Mut, Borrow { place; _ } -> Some (make_passed_place run place)
  | Mut, (Use _ | Take _ | Immediate _) | (Read | Own), _ -> None

let evaluate_call_values (frame : State.frame) run ~at (callee : Callee.t)
    (arguments : Mir.argument list) =
  Lambdas.make_passed_values frame ~at callee
    (List.mapi
       (fun position ({ mode; value; function_ } : Mir.argument) ->
         match function_ with
         | Some (Lambda_expression { body; origin; type_ }) ->
             State.Lambda_argument
               {
                 position;
                 mode;
                 site = { origin; type_ };
                 lambda = { code = run.lambdas.(body); lambdas = run.lambdas };
               }
         | Some (Function_reference _) | None ->
             Value_argument
               {
                 position;
                 mode;
                 origin = find_operand_origin value;
                 passed_place = find_argument_place run mode value;
                 is_step_self = position = 0 && Callee.is_update_step frame.environment callee;
                 type_ = compute_operand_type frame value;
                 declared_type =
                   Encoding.substitute_declared_type frame (Mir.extract_operand_type value);
                 term = read_operand { frame with is_reading_callback = true } run value;
               })
       arguments)

let read_call (frame : State.frame) run (call : Mir.call) ~result_type =
  match (call.callee.target, call.arguments) with
  | ( Trait_method { trait; name; receiver; _ },
      [
        { value = tested; _ };
        {
          value =
            Borrow { place = { root = Literal { value = Text text; _ }; projections = [] }; _ };
          _;
        };
      ] )
    when Well_known.is_method Equal_equal (Method { owner = trait.trait; name; receiver }) ->
      let ty = compute_operand_type frame tested in
      Some
        ( frame,
          Values.make_text_match frame.environment frame.query (Facts.locate frame call.origin) ty
            (read_operand frame run tested) text )
  | _ ->
      let through =
        match call.callee.target with
        | Indirect callee ->
            Some
              ( compute_operand_type frame callee,
                read_operand { frame with is_reading_callback = true } run callee )
        | _ -> None
      in
      let callee = resolve_callee frame call.callee ~lends:None in
      let values = evaluate_call_values frame run ~at:call.origin callee call.arguments in
      Calls.apply_call frame { origin = call.origin; type_ = result_type } callee ~through values

let read_lend (frame : State.frame) run part (call : Mir.call) =
  let mode = match run.infos.(part).kind with Lent mode -> mode | _ -> Language.Mode.Read in
  let callee = resolve_callee frame call.callee ~lends:(Some mode) in
  let site : Invocation.site = { origin = call.origin; type_ = run.infos.(part).type_ } in
  let values = evaluate_call_values frame run ~at:call.origin callee call.arguments in
  Option.map
    (fun ({ frame = after; result; end_lend } : Calls.applied) ->
      let lent = write_place after run { root = Local part; projections = [] } result in
      match (end_lend, mode) with
      | Some end_lend, _ ->
          {
            lent with
            lends =
              Locals.add (Locals.make_key run.infos part)
                [ (Logic.Boolean true, end_lend) ]
                lent.lends;
          }
      | None, Language.Mode.Mut -> Facts.raise_bug "a `mut` lend that no call ends"
      | None, (Read | Own) -> lent)
    (Calls.apply_lend frame site callee ~through:None values)

let compute_target_type (frame : State.frame) run (target : Mir.place) =
  match target with
  | { root = Local local; projections = [] } -> run.infos.(local).type_
  | _ -> compute_place_type frame run target

let lends_places (part : Mir.yielded) =
  match part with Built _ | Part (Borrow _) -> true | Part (Use _ | Take _ | Immediate _) -> false

let rec read_yielded_value (frame : State.frame) run ~origin (part : Mir.yielded) =
  match part with
  | Part operand -> (frame, read_operand frame run operand)
  | Built { variant; fields; type_ } ->
      let frame, values =
        List.fold_left
          (fun (frame, values) (name, field) ->
            match field with
            | Some field ->
                let frame, term = read_yielded_value frame run ~origin field in
                (frame, values @ [ (name, Some term) ])
            | None -> (frame, values @ [ (name, None) ]))
          (frame, []) fields
      in
      Values.apply_construct frame { origin; type_ } variant values

let rec write_back_part (environment : State.environment) run ty (part : Mir.yielded) frame after =
  match part with
  | Part (Borrow { place; _ }) -> write_place frame run place after
  | Built { variant; fields; _ } -> (
      match Encoding.find_constructors environment ty with
      | Some shape ->
          let shaped = Option.value (List.assoc_opt variant shape) ~default:[] in
          List.fold_left
            (fun frame (name, field) ->
              match (field, List.assoc_opt name shaped) with
              | Some field, Some field_type when lends_places field ->
                  let field_type = Encoding.substitute_type frame field_type in
                  let selected = Values.project_field frame ty variant name field_type after in
                  let value =
                    match variant with
                    | None -> selected
                    | Some _ ->
                        Logic.ite
                          (Logic.Is (Encoding.make_constructor_symbol ty variant, after))
                          selected
                          (Encoding.arrive frame "lent" field_type)
                  in
                  write_back_part environment run field_type field frame value
              | _ -> frame)
            frame fields
      | None -> Facts.raise_unsupported Whole_definition (Fields_of ty))
  | Part (Use _ | Take _ | Immediate _) -> frame

let bind_parts (frame : State.frame) run =
  Locals.fold
    (fun key parts (frame : State.frame) ->
      match (key, Locals.find_opt key frame.types, List.rev parts) with
      | Locals.Mir_local _, _, _ -> frame
      | _, Some ty, (_, first) :: later -> (
          let read = read_place { frame with makes_obligations = false } run in
          try
            Facts.bind frame key ty
              (List.fold_left
                 (fun otherwise (condition, part) -> Logic.ite condition (read part) otherwise)
                 (read first) later)
          with Facts.Unsupported _ -> frame)
      | _ -> frame)
    frame.aliases frame

let refresh_place (frame : State.frame) ty (place : State.passed_place) =
  let fresh_value = Encoding.arrive frame "changed" ty in
  let frame, end_write = place.write frame ~is_valid:true fresh_value in
  end_write frame;
  Validity.assume_valid frame ty fresh_value;
  frame

let record_todo (frame : State.frame) origin =
  Query.add_hole frame.query (frame.source.key, Obligation.Node origin);
  if frame.is_ghost then Values.note_unfinished frame

let oblige_unreachable frame location =
  Obligations.oblige frame location Unreachable_reached (Logic.Boolean false)

let rec read_rvalue (frame : State.frame) run (value : Mir.rvalue) ~(site : Invocation.site) =
  let location = Facts.locate frame site.origin in
  let ty = Encoding.substitute_type frame site.type_ in
  let translate_operand = read_operand frame run in
  match value with
  | Operand value -> (frame, translate_operand value)
  | Compare { comparison = compared; left; right } ->
      ( frame,
        Operations.compare_terms (compute_operand_type frame left) compared (translate_operand left)
          (translate_operand right) )
  | Not inner -> (frame, Logic.not_ (translate_operand inner))
  | Is_variant { place; variant } ->
      let ty = compute_place_type frame run place in
      if Encoding.find_constructors frame.environment ty = None then
        Facts.raise_unsupported location (Hidden_variant_of ty);
      ( frame,
        Logic.Is (Encoding.make_constructor_symbol ty (Some variant), read_place frame run place) )
  | Copy copied_operand ->
      let declared =
        Encoding.substitute_declared_type frame (Mir.extract_operand_type copied_operand)
      in
      let term = translate_operand copied_operand in
      let literal =
        match copied_operand with
        | Borrow { place = { root = Literal { value; _ }; projections = [] }; _ } -> Some value
        | _ -> None
      in
      (Amounts.spend_copy ?literal frame ~declared term, term)
  | Convert { conversion = Widen; value; converts_function_expression } ->
      Operations.check_widened location ~is_written:converts_function_expression
        (compute_operand_type frame value)
        ty;
      (frame, translate_operand value)
  | Value_parameter parameter -> (frame, Models.make_value_term frame (Value_parameter parameter))
  | Parameter_default { definition; position; substitution } ->
      let default =
        Mir.read_parameter_default frame.environment.lookups.mir ~definition ~position
      in
      let declared, term =
        Lambdas.run_code
          {
            frame with
            source = Contracts.read_source_at_key frame.environment.lookups default.source;
            locals = Locals.empty;
            types = Locals.empty;
            makes_obligations = false;
            substitution = Types.substitute_substitution frame.substitution substitution;
          }
          default.form ~type_:ty
      in
      ({ frame with spent = declared.spent }, term)
  | Convert { conversion = To_integer | To_view; value; _ } -> (frame, translate_operand value)
  | Convert { conversion = From_integer; value; _ } ->
      (frame, Operations.convert_from_integer frame site (translate_operand value))
  | Function_value { path; instantiation; is_argument } ->
      (frame, Callbacks.read_named_function frame site path instantiation ~is_argument)
  | Operation { operation; operands; type_arguments } ->
      let types =
        List.filter_map
          (function Types.Type ty -> Some (Encoding.substitute_type frame ty) | _ -> None)
          type_arguments
      in
      let types = match types with [] -> [ ty ] | types -> types in
      let terms = List.map translate_operand operands in
      ( frame,
        Operations.translate_primitive_operation frame ~site operation types terms
          ~arguments:(List.map find_operand_origin operands) ~fallback:(fun () ->
            Encoding.arrive frame "result" ty) )
  | Construct { variant; fields; type_ } ->
      Values.apply_construct frame { site with type_ } variant
        (List.map (fun (name, field) -> (name, Option.map translate_operand field)) fields)
  | Array elements -> Values.apply_list_literal frame site (List.map translate_operand elements)
  | Lambda { body; _ } ->
      Lambdas.translate_lambda frame ~site
        { code = run.lambdas.(body); lambdas = run.lambdas }
        ~stated:None
  | Specification Result -> (
      match frame.result with
      | Some result -> (frame, result)
      | None ->
          Facts.raise_bug "`%s` reads `result` outside an `ensures`"
            (Resolve.Names.show_key frame.source.key))
  | Specification (Entry local) -> (
      match Locals.make_key run.infos local with
      | Core_local Self -> (
          match frame.old_self with
          | Some self -> (frame, self)
          | None ->
              Facts.raise_bug "`%s` reads `old(self)` outside a method"
                (Resolve.Names.show_key frame.source.key))
      | key -> (
          match Locals.find_opt key frame.old_locals with
          | Some term -> (frame, term)
          | None ->
              Facts.raise_bug "`%s` reads the entry value of %s, which the prover did not bind"
                (Resolve.Names.show_key frame.source.key)
                (describe_local run.infos.(local).kind)))
  | Specification Visited -> (
      match frame.visited with
      | Some visited -> (frame, visited)
      | None ->
          Facts.raise_bug "`%s` reads `visited` outside a loop's clause"
            (Resolve.Names.show_key frame.source.key))
  | Specification Final_result -> (frame, Lending.read_final_result frame)
  | Specification (Identical (first, second)) ->
      let first_value = translate_operand first and second_value = translate_operand second in
      Values.assume_extensional frame (compute_operand_type frame first) first_value second_value;
      (frame, Logic.equal first_value second_value)
  | Specification (Applied { function_; arguments; unconverted }) ->
      let values =
        List.map (read_operand { frame with is_reading_callback = true } run) arguments
      in
      Values.apply_specification_function frame ~location function_ values
        ~unconverted:(List.map (Encoding.substitute_type frame) unconverted)
        ~types:(List.map (compute_operand_type frame) arguments)
  | Specification (Method_cost { metric; method_ }) ->
      ( frame,
        Amounts.compute_method_cost frame metric
          (Callee.resolve frame method_ ~lends:None ~uses:Types.no_capabilities) )
  | Specification (Map entries) ->
      Values.apply_map_literal frame ~ty ~location
        (List.map
           (fun (key, entry) ->
             (find_operand_origin key, translate_operand key, translate_operand entry))
           entries)
  | Specification (Quantified { quantifier; range; parameter; matches; body }) ->
      let range =
        match range with
        | Over_type ty -> Models.Range_of_type (Encoding.substitute_type frame ty)
        | Over_range { start; stop; inclusive } ->
            Range_of_integers
              {
                low = translate_operand start;
                high = translate_operand stop;
                inclusive;
                type_ = compute_operand_type frame start;
              }
      in
      translate_quantifier_value frame run quantifier range ~parameter ~matches ~body

and translate_quantifier_value (frame : State.frame) run quantifier range ~parameter
    ~(matches : Mir.block) ~(body : Mir.block) =
  Models.quantify_over frame quantifier range
    ~bind:(fun inner value ty -> Facts.bind inner (Locals.make_key run.infos parameter) ty value)
    ~read:(fun body_frame _ ->
      let after_matches, matched = read_value body_frame run matches in
      let after, holds = read_value (Facts.restrict after_matches matched) run body in
      ( { body_frame with spent = after.spent },
        match quantifier with
        | Forall -> Logic.( ==> ) matched holds
        | Exists -> Logic.( &&& ) matched holds ))

and read_statements (frame : State.frame) run (statements : Mir.statement list) =
  List.fold_left
    (fun frame statement ->
      Option.bind frame (fun frame ->
          Option.map (fun frame -> bind_parts frame run) (read_statement frame run statement)))
    (Some frame) statements

and read_block (frame : State.frame) run (block : Mir.block) =
  Option.map
    (fun after ->
      match block.value with
      | Some value -> (after, read_operand after run value)
      | None -> Facts.raise_bug "a block with no value, whose end control reaches")
    (read_statements frame run block.statements)

and read_value (frame : State.frame) run (block : Mir.block) =
  match read_block frame run block with
  | Some read -> read
  | None -> Facts.raise_unsupported Whole_definition Nonreturning_specification_call

and join_after_either ~(outer : State.frame) ~condition
    ((entered : State.frame), (after : State.frame))
    ((entered_otherwise : State.frame), (after_otherwise : State.frame)) =
  fst
    (Joins.merge
       ~condition:
         (if
            after.condition == entered.condition
            && after_otherwise.condition == entered_otherwise.condition
          then outer.condition
          else
            Joins.name_path_condition outer
              (Logic.( ||| ) after.condition after_otherwise.condition))
       [ (condition, after, None); (Logic.not_ condition, after_otherwise, None) ])

and merge_alternatives ~outer ~condition (entered, read) (entered_otherwise, otherwise) =
  match (read, otherwise) with
  | None, None -> None
  | Some after, None | None, Some after -> Some after
  | Some (after, value), Some (after_otherwise, value_otherwise) ->
      Some
        ( join_after_either ~outer ~condition (entered, after) (entered_otherwise, after_otherwise),
          Logic.ite condition value value_otherwise )

and read_choice (frame : State.frame) run (choice : Mir.choice) =
  match choice with
  | Conditional { condition; then_; else_ } -> (
      match read_block frame run condition with
      | None -> None
      | Some (frame, test) ->
          let entered_then = Facts.restrict frame test
          and entered_else = Facts.restrict frame (Logic.not_ test) in
          merge_alternatives ~outer:frame ~condition:test
            (entered_then, read_block entered_then run then_)
            (entered_else, read_block entered_else run else_))
  | Cases cases ->
      let rec find_first_taken (current : State.frame) = function
        | [] -> Facts.raise_bug "a `match` with no case"
        | (case : Mir.case) :: later ->
            let bound, matches = read_value current run case.tests in
            let entered, is_taken, after_tests =
              match case.guard with
              | Some guard ->
                  let guarded = Facts.restrict bound matches
                  and unmatched = Facts.restrict bound (Logic.not_ matches) in
                  let after, holds = read_value guarded run guard in
                  ( Facts.restrict after holds,
                    Logic.( &&& ) matches holds,
                    join_after_either ~outer:current ~condition:matches (guarded, after)
                      (unmatched, unmatched) )
              | None ->
                  ( Facts.restrict bound matches,
                    matches,
                    { bound with condition = current.condition } )
            in
            let read = read_block entered run case.value in
            if later = [] then
              Option.map
                (fun ((after : State.frame), value) ->
                  ( (if after.condition == entered.condition then
                       { after with condition = current.condition }
                     else after),
                    value ))
                read
            else
              let not_taken = Facts.restrict after_tests (Logic.not_ is_taken) in
              merge_alternatives ~outer:current ~condition:is_taken (entered, read)
                (not_taken, find_first_taken not_taken later)
      in
      find_first_taken frame cases
  | Connective { connective; left; right } -> (
      match read_block frame run left with
      | None -> None
      | Some (frame, left) -> (
          let reads_right = match connective with And | Implies -> left | Or -> Logic.not_ left in
          let entered = Facts.restrict frame reads_right in
          match read_block entered run right with
          | Some (after, right) ->
              let skipped = Facts.restrict frame (Logic.not_ reads_right) in
              Some
                ( join_after_either ~outer:frame ~condition:reads_right (entered, after)
                    (skipped, skipped),
                  match connective with
                  | And -> Logic.( &&& ) left right
                  | Or -> Logic.( ||| ) left right
                  | Implies -> Logic.( ==> ) left right )
          | None ->
              Some (Facts.restrict frame (Logic.not_ reads_right), Logic.Boolean (connective <> And))
          ))

and read_providing run ~refresh read =
  let returns = run.returns in
  let loops = List.map (fun (exits : loop_exits) -> (exits, exits.breaks, exits.ends)) run.loops in
  let cancelled = List.map (fun (_, frames) -> (frames, !frames)) run.cancelled in
  let read = read () in
  let rec refresh_since ~before refresh_exit = function
    | exits when exits == before -> exits
    | exit :: rest -> refresh_exit exit :: refresh_since ~before refresh_exit rest
    | [] -> Facts.raise_bug "the exits before a `provide` block are gone after it"
  in
  run.returns <-
    refresh_since ~before:returns
      (fun (exit_ : State.function_exit) -> { exit_ with frame = refresh exit_.frame })
      run.returns;
  List.iter
    (fun ((exits : loop_exits), breaks, ends) ->
      exits.breaks <- refresh_since ~before:breaks refresh exits.breaks;
      exits.ends <- refresh_since ~before:ends refresh exits.ends)
    loops;
  List.iter
    (fun (exits, before) ->
      exits := refresh_since ~before (fun exit -> { exit with exited = refresh exit.exited }) !exits)
    cancelled;
  read

and read_statement (frame : State.frame) run (statement : Mir.statement) =
  let location = Facts.locate frame statement.origin in
  Termination.reject_recursion_through_supplied_code frame location statement;
  match statement.kind with
  | Basic basic -> read_basic frame run statement basic
  | Assert_by_bit_vector { names; code; _ } ->
      let named =
        List.map
          (fun local ->
            match run.infos.(local) with
            | { kind = Source { local; _ }; type_; _ } -> (local, type_)
            | { kind = Temporary | Lent _; _ } ->
                Facts.raise_bug "an assertion that names a temporary")
          names
      in
      let frame, term = read_value frame run code in
      Assertions.check_assertion frame ~origin:statement.origin
        ~bit_vector:(Some (named, fun isolated -> snd (read_value isolated run code)))
        term;
      Some frame
  | Provide { target; provided; body; _ } ->
      let provider_potential =
        lazy
          (List.fold_left
             (fun total (implementation : Mir.provided) ->
               Logic.add total
                 (Potentials.compute_potential frame
                    (Encoding.substitute_type frame implementation.type_)
                    (read_operand { frame with makes_obligations = false } run implementation.value)))
             Costs.zero provided)
      in
      let refresh (inside : State.frame) =
        {
          (Potentials.spend_provided
             (List.fold_left
                (fun frame place ->
                  let root = { (expand_place frame run place) with Mir.projections = [] } in
                  refresh_place frame
                    (compute_place_type frame run root)
                    (make_passed_place run root))
                inside
                (Mir.list_mut_provided_places provided))
             provider_potential)
          with
          provided = frame.provided;
        }
      in
      let read =
        read_providing run ~refresh (fun () ->
            read_block { frame with provided = provided :: frame.provided } run body)
      in
      write_assignment run target (Option.map (fun (after, term) -> (refresh after, term)) read)
  | Choose { target; choice } -> write_assignment run target (read_choice frame run choice)
  | Yield { mode; part } ->
      let origin = statement.origin in
      let frame, handed = read_yielded_value frame run ~origin part in
      let part_type =
        match part with
        | Part operand -> compute_operand_type frame operand
        | Built { type_; _ } -> Encoding.substitute_type frame type_
      in
      let lent, after =
        Lending.lend_part frame origin mode ~handed ~lends_places:(lends_places part)
          ~write_back:(fun frame final ->
            write_back_part frame.environment run part_type part frame final)
      in
      run.lends <- lent :: run.lends;
      Some after
  | Jump jump ->
      (match jump with
      | Return returned ->
          run.returns <-
            {
              frame;
              returned = Option.map (read_operand frame run) returned;
              return_origin = statement.origin;
            }
            :: run.returns
      | Break -> (
          match run.loops with
          | exits :: _ -> exits.breaks <- frame :: exits.breaks
          | [] -> Facts.raise_bug "a `break` outside a loop")
      | Continue -> (
          match run.loops with
          | exits :: _ -> exits.ends <- frame :: exits.ends
          | [] -> Facts.raise_bug "a `continue` outside a loop")
      | Cancel { task; winner; number; returned } -> (
          let frame =
            Facts.bind frame
              (Locals.make_key run.infos winner)
              (Types.make_builtin UInt32)
              (Logic.Integer (Z.of_int number))
          in
          let frame =
            match returned with
            | Some (value, local) ->
                Facts.bind frame (Locals.make_key run.infos local)
                  (compute_operand_type frame value)
                  (read_operand frame run value)
            | None -> frame
          in
          match task with
          | Branch _ -> (
              let exit_locals =
                Locals.make_key run.infos winner
                :: Option.to_list
                     (Option.map (fun (_, local) -> Locals.make_key run.infos local) returned)
              in
              match List.assoc_opt task run.cancelled with
              | Some exits -> exits := { exited = frame; exit_locals } :: !exits
              | None -> Facts.raise_bug "an early exit of a branch that is not around it")
          | Iteration { loop } -> (
              match List.find_opt (fun (exits : loop_exits) -> exits.loop = loop) run.loops with
              | Some exits -> exits.breaks <- frame :: exits.breaks
              | None -> Facts.raise_bug "an early exit of an iteration that is not around it"))
      | Unreachable -> ()
      | Written_unreachable -> oblige_unreachable frame location
      | Todo -> record_todo frame statement.origin);
      None
  | Fork { fork; concurrent; branches } ->
      let run_branch (start : State.frame) index (branch : Mir.block) =
        let cancelled = ref [] in
        run.cancelled <- (Mir.Branch { fork; index }, cancelled) :: run.cancelled;
        let ended = read_statements start run branch.statements in
        run.cancelled <- List.tl run.cancelled;
        (ended, List.rev !cancelled)
      in
      let alone =
        List.mapi
          (fun index branch -> run_branch (snd (Facts.suppose frame "branch")) index branch)
          branches
      in
      let ended =
        if List.exists (fun (ended, _) -> Option.is_none ended) alone then None
        else
          Option.map
            (fun (ended : State.frame) ->
              { ended with makes_obligations = frame.makes_obligations })
            (List.fold_left
               (fun after_earlier (index, branch) ->
                 Option.bind after_earlier (fun after_earlier ->
                     fst (run_branch after_earlier index branch)))
               (Some (snd (Facts.suppose { frame with makes_obligations = false } "ended")))
               (List.mapi (fun index branch -> (index, branch)) branches))
      in
      let leave_other_branches index exit =
        let others =
          List.filteri
            (fun other _ -> other <> index)
            (List.map2
               (fun branch (ended, exits) ->
                 ( List.filter
                     (fun (part : State.changed_part) -> not (List.mem part.root exit.exit_locals))
                     (compute_changes frame.environment run exit.exited [ branch ]),
                   Option.to_list ended @ List.map (fun exit -> exit.exited) exits ))
               branches alone)
        in
        let is_changed_by_one_branch (part : State.changed_part) =
          List.length
            (List.filter
               (fun (parts, _) ->
                 List.exists (fun (other : State.changed_part) -> other.root = part.root) parts)
               others)
          = 1
        in
        List.fold_left
          (fun (left : State.frame) (parts, outcomes) ->
            let amounts =
              List.map
                (fun (counter, _) -> (counter, Facts.declare_fresh left "spent" Logic.Int))
                left.spent
            in
            let describe (at : State.frame) =
              Logic.conjunction
                (List.filter_map
                   (fun part ->
                     match
                       (Encoding.find_changed_part left part, Encoding.find_changed_part at part)
                     with
                     | Some (_, value), Some (_, value_at) -> Some (Logic.equal value value_at)
                     | _ -> None)
                   (List.filter is_changed_by_one_branch parts)
                @ List.map
                    (fun (counter, amount) ->
                      Logic.equal amount
                        (Costs.since
                           ~start:(Counters.lookup_spent frame counter)
                           (Counters.lookup_spent at counter)))
                    amounts)
            in
            Facts.assume left
              (Logic.disjunction
                 (describe frame
                 :: List.map
                      (fun (at : State.frame) -> Logic.( &&& ) at.condition (describe at))
                      outcomes));
            Counters.spend left (fun counter ->
                Option.value (List.assoc_opt counter amounts) ~default:Costs.zero))
          (forget_changes exit.exited (List.concat_map fst others))
          others
      in
      let joined =
        Joins.join_frames
          (Option.to_list ended
          @ List.concat
              (List.mapi
                 (fun index (_, exits) -> List.map (leave_other_branches index) exits)
                 alone))
      in
      if concurrent then Option.map Amounts.spend_wait_for_tasks joined else joined
  | Resume { winner; exits } ->
      let won =
        read_operand frame run
          (Use
             {
               place = { root = Local winner; projections = [] };
               type_ = Types.make_builtin UInt32;
               origin = statement.origin;
             })
      in
      let others, resumed =
        List.fold_left
          (fun (frame, resumed) (number, (exit : Mir.early_exit)) ->
            let has_won = Logic.equal won (Logic.Integer (Z.of_int number)) in
            ( Facts.restrict frame (Logic.not_ has_won),
              resumed
              @ Option.to_list
                  (read_statements (Facts.restrict frame has_won) run exit.resumed.statements) ))
          (frame, [])
          (List.mapi (fun index exit -> (index + 1, exit)) exits)
      in
      Joins.join_frames (others :: resumed)
  | While { loop; condition; body; failed; compared } ->
      Loops.run_while_loop frame
        {
          while_at = loop.origin;
          while_clauses = Loops.keep_holding_clauses frame.environment frame.query loop.clauses;
          changed = compute_changes frame.environment run frame (Mir.list_nested_blocks statement);
          bind_parts = (fun frame -> bind_parts frame run);
          test = (fun head -> read_block head run condition);
          run_body =
            (fun entered ->
              let exits = { loop = loop.node; breaks = []; ends = [] } in
              run.loops <- exits :: run.loops;
              let ended = read_statements entered run body.statements in
              run.loops <- List.tl run.loops;
              (List.rev exits.ends @ Option.to_list ended, List.rev exits.breaks));
          on_failure = (fun frame -> read_statements frame run failed);
          measure_operands =
            Option.map
              (fun ({ statements; comparison; left; right } : Mir.compared) ->
                ( comparison,
                  fun at ->
                    let after =
                      List.fold_left
                        (fun frame statement ->
                          Option.value (read_statement frame run statement) ~default:frame)
                        at statements
                    in
                    (read_operand after run left, read_operand after run right) ))
              compared;
        }
  | For
      {
        loop = { quantified = Some { quantifier; decides }; _ };
        iteration;
        part;
        elements;
        bindings;
        body;
      } ->
      let frame =
        match elements with
        | Some elements -> fst (read_value frame run elements.count)
        | None -> frame
      in
      let range : Models.quantified_range =
        match iteration with
        | Range { start; stop; inclusive } ->
            Range_of_integers
              {
                low = read_operand frame run start;
                high = read_operand frame run stop;
                inclusive;
                type_ = compute_operand_type frame start;
              }
        | Pull _ -> Facts.raise_bug "a quantifier loop that pulls from a cursor"
      in
      let decision : Mir.operand =
        Use
          {
            place = { root = Local decides; projections = [] };
            type_ = Types.bool;
            origin = statement.origin;
          }
      in
      let after, term =
        translate_quantifier_value frame run quantifier range ~parameter:part
          ~matches:
            {
              statements = [];
              value = Some (Immediate { value = Boolean true; type_ = Types.bool });
            }
          ~body:{ statements = bindings.statements @ body.statements; value = Some decision }
      in
      Some (write_place after run { root = Local decides; projections = [] } term)
  | For { loop; iteration; part; elements; bindings = loop_bindings; body } ->
      let frame =
        match elements with
        | Some elements -> fst (read_value frame run elements.count)
        | None -> frame
      in
      let find_lent_mode (elements : Mir.elements) =
        match elements.element with
        | Sequence_element { mode; _ } -> mode
        | Lent_by_call part -> (
            match run.infos.(part).kind with
            | Lent mode -> mode
            | Source _ | Temporary -> Facts.raise_bug "a loop's element that no call lends")
      in
      let count_kept_by_iterations =
        Option.bind elements (fun (elements : Mir.elements) ->
            match find_lent_mode elements with
            | Mut ->
                Some
                  (fun at ->
                    Counters.run_without_counters frame.query (fun () ->
                        snd (read_value at run elements.count)))
            | Read | Own -> None)
      in
      let run_body inside element =
        let inside =
          Facts.bind inside (Locals.make_key run.infos part)
            (Encoding.substitute_type inside run.infos.(part).type_)
            element
        in
        let exits = { loop = loop.node; breaks = []; ends = [] } in
        run.loops <- exits :: run.loops;
        let ended = read_statements inside run (loop_bindings.statements @ body.statements) in
        run.loops <- List.tl run.loops;
        let breaks =
          match loop.schedule with
          | Concurrent ->
              let changed = compute_changes frame.environment run inside [ loop_bindings; body ] in
              List.map
                (fun exited ->
                  let forgotten = Loops.havoc exited changed in
                  Option.iter
                    (fun count_of ->
                      Facts.assume forgotten (Logic.equal (count_of forgotten) (count_of exited)))
                    count_kept_by_iterations;
                  forgotten)
                exits.breaks
          | Sequential | Parallel -> exits.breaks
        in
        (List.rev exits.ends @ Option.to_list ended, List.rev breaks)
      in
      let bindings = loop_bindings.statements and after_bindings = body.statements in
      let bind_element frame element =
        let frame =
          Facts.bind frame (Locals.make_key run.infos part)
            (Encoding.substitute_type frame run.infos.(part).type_)
            element
        in
        List.fold_left
          (fun frame statement -> Option.value (read_statement frame run statement) ~default:frame)
          frame bindings
      in
      let translate_operand = read_operand frame run in
      let iterated = match iteration with Pull { cursor; _ } -> [ cursor ] | Range _ -> [] in
      let iterable =
        match iteration with
        | Range { start; stop; inclusive } ->
            Loops.Over_range
              { low = translate_operand start; high = translate_operand stop; inclusive }
        | Pull { cursor; next; next_origin } ->
            Over_cursor
              {
                cursor = make_passed_place run cursor;
                cursor_type = compute_place_type frame run cursor;
                next = resolve_callee frame next ~lends:None;
                next_origin;
              }
      in
      let for_loop =
        {
          Loops.for_at = loop.origin;
          for_clauses = Loops.keep_holding_clauses frame.environment frame.query loop.clauses;
          iterable;
          element_type = run.infos.(part).type_;
          lent_element =
            Option.map
              (fun (elements : Mir.elements) ->
                match elements.element with
                | Lent_by_call part -> run.infos.(part).type_
                | Sequence_element { place; _ } -> compute_place_type frame run place)
              elements;
          invariant_count = count_kept_by_iterations;
          collection =
            Option.map
              (fun (elements : Mir.elements) frame ->
                ( compute_place_type frame run elements.collection,
                  read_place { frame with makes_obligations = false } run elements.collection ))
              elements;
          element_call =
            Option.bind elements (fun (elements : Mir.elements) ->
                match (find_lent_mode elements, elements.element) with
                | Mut, _ -> None
                | (Read | Own), Sequence_element { place; _ } ->
                    Some
                      (fun at ->
                        Counters.run_without_counters frame.query (fun () ->
                            read_place { at with makes_obligations = false } run place))
                | (Read | Own), Lent_by_call lent ->
                    Some
                      (fun at ->
                        let rec lend frame = function
                          | [] -> Facts.raise_bug "a loop over elements that no statement lends"
                          | (statement : Mir.statement) :: rest -> (
                              let frame =
                                Option.value (read_statement frame run statement) ~default:frame
                              in
                              match statement.kind with
                              | Basic (Lend { part; _ }) when part = lent -> frame
                              | _ -> lend frame rest)
                        in
                        Counters.run_without_counters frame.query (fun () ->
                            read_place (lend at after_bindings) run
                              { root = Local lent; projections = [] })));
          bind_element;
          compute_changed_in =
            (fun frame ->
              compute_changes ~also:iterated frame.environment run frame [ loop_bindings; body ]);
          compute_changed_by_body =
            (fun frame -> compute_changes frame.environment run frame [ loop_bindings; body ]);
          run_body;
          bind_parts = (fun frame -> bind_parts frame run);
        }
      in
      let ended = Loops.run_for_loop frame for_loop in
      if loop.schedule = Concurrent then Option.map Amounts.spend_wait_for_tasks ended else ended

and read_basic (frame : State.frame) run (statement : Mir.statement) (basic : Mir.basic) =
  match basic with
  | Assign
      {
        target = { root = Local local; projections = [] };
        value = Operand (Borrow { place; mode = Mut; _ });
        _;
      } ->
      let key = Locals.make_key run.infos local in
      Some
        {
          frame with
          aliases = Locals.add key [ (Logic.Boolean true, place) ] frame.aliases;
          types =
            Locals.add key (Encoding.substitute_type frame run.infos.(local).type_) frame.types;
        }
  | Assign { target; value = Lambda { is_argument = true; _ }; _ } ->
      Some
        (write_place frame run target
           (Encoding.arrive frame "lambda" (compute_place_type frame run target)))
  | Assign { target; value } -> (
      let read (reading : State.frame) =
        let after, term =
          read_rvalue reading run value
            ~site:{ origin = statement.origin; type_ = compute_target_type frame run target }
        in
        ({ after with is_reading_callback = frame.is_reading_callback }, term)
      in
      match (target, value) with
      | { root = Local held; projections = [] }, (Operand _ | Convert { conversion = Widen; _ })
        when match run.infos.(held).kind with Temporary | Lent _ -> true | Source _ -> false ->
          write_assignment run target (Some (read { frame with is_reading_callback = true }))
      | _ -> write_assignment run target (Some (read frame)))
  | Call { destination; call } -> read_call_statement frame run ~destination call
  | Live _ | Loan_start _ | Loan_end _ | Echo _ -> Some frame
  | Dead locals ->
      if frame.makes_obligations then
        List.iter
          (fun local ->
            let info = run.infos.(local) in
            let moment : Catalog.Prover.invariant_moment option =
              match info.kind with
              | Temporary -> Some Built_here
              | Source { is_var = true; local; _ } ->
                  Some
                    (At_scope_end
                       (match Mir.find_local_name local with
                       | Some name -> Named name
                       | None -> Compiler_local))
              | Source { is_var = false; _ } | Lent _ -> None
            in
            match (moment, Locals.find_opt (Locals.make_key run.infos local) frame.locals) with
            | Some moment, Some term when Hashtbl.mem run.changed_in_place local ->
                Validity.check_valid frame (Facts.locate frame info.origin)
                  (Encoding.substitute_type frame info.type_)
                  term ~deep:true ~moment
            | _ -> ())
          locals;
      let frame =
        List.fold_left
          (fun (frame : State.frame) local ->
            match Locals.find_opt (Locals.make_key run.infos local) frame.lends with
            | Some lent ->
                let final =
                  read_place
                    { frame with makes_obligations = false }
                    run
                    { root = Local local; projections = [] }
                in
                List.fold_left
                  (fun frame (lent_on, write_back) ->
                    match lent_on with
                    | Logic.Boolean true -> write_back frame final
                    | _ ->
                        let lent = Facts.restrict frame lent_on
                        and not_lent = Facts.restrict frame (Logic.not_ lent_on) in
                        fst
                          (Joins.merge ~condition:frame.condition
                             [
                               (lent_on, write_back lent final, None);
                               (Logic.not_ lent_on, not_lent, None);
                             ]))
                  frame lent
            | None -> frame)
          frame (List.rev locals)
      in
      let remove_locals map =
        List.fold_left
          (fun map local -> Locals.remove (Locals.make_key run.infos local) map)
          map locals
      in
      Some
        {
          frame with
          locals = remove_locals frame.locals;
          aliases = remove_locals frame.aliases;
          lends = remove_locals frame.lends;
        }
  | Lend { part; call } -> read_lend frame run part call
  | Assert condition ->
      Assertions.check_assertion frame ~origin:statement.origin ~bit_vector:None
        (read_operand frame run condition);
      Some frame
  | Ghost_assert { condition; by_bit_vector } ->
      let frame, term = Validity.read_specification frame condition in
      let list_named () =
        List.map
          (fun parameter ->
            match condition.locals.(parameter) with
            | { kind = Source { local; _ }; type_; _ } -> (local, type_)
            | { kind = Temporary | Lent _; _ } ->
                Facts.raise_bug "an assertion's formula that takes no local")
          condition.parameters
      in
      Assertions.check_assertion frame ~origin:condition.origin
        ~bit_vector:
          (if by_bit_vector then
             Some
               ( list_named (),
                 fun isolated ->
                   snd (frame.environment.read_formula isolated condition ~arguments:[]) )
           else None)
        term;
      Some frame
  | Proof code -> Some (Facts.restrict frame (Logic.not_ (Values.run_ghost_code frame code)))
  | Evaluated_assert code ->
      let symbol =
        Logic.Symbol.Evaluated
          (Assertion
             {
               definition = frame.source.key.path;
               condition = Core_walk.locate_origin statement.origin;
             })
      in
      Query.declare frame.query (Logic.Constant (symbol, Logic.Bool));
      let _, holds =
        Validity.run_as_specification { frame with is_ghost = true } (fun specification ->
            Lambdas.run_code specification code ~type_:Types.bool)
      in
      Facts.assume frame (Logic.equal (Logic.Symbol symbol) holds);
      let location = Facts.locate frame statement.origin in
      Obligations.oblige ~is_proven_by_evaluation:true frame location
        (match statement.origin with
        | Written _ -> Assertion_may_fail { clause = Facts.quote frame.source statement.origin }
        | Desugared _ ->
            Desugared_assertion_may_fail
              {
                call =
                  {
                    at = location;
                    callee =
                      List.find_map
                        (fun (asserted : Mir.statement) ->
                          match asserted.kind with
                          | Basic (Call { call; _ }) ->
                              (Mir.Call_edges.resolve_callee frame.environment.lookups.interface
                                 frame.substitution call.callee.target)
                                .target
                          | _ -> None)
                        (List.rev code.body.code.statements);
                  };
              })
        holds;
      Some frame

and read_call_statement (frame : State.frame) run ~destination (call : Mir.call) =
  let result_type =
    match destination with
    | Some destination -> compute_target_type frame run destination
    | None -> Types.unit
  in
  match read_call frame run call ~result_type with
  | Some (after, term) -> (
      match destination with
      | Some destination -> Some (write_place after run destination term)
      | None -> Some after)
  | None -> None

and write_assignment run (target : Mir.place) read =
  let* frame, term = read in
  Some (write_place frame run target term)

let make_run ~locals ~lambdas =
  {
    infos = locals;
    changed_in_place = Hashtbl.create 4;
    lambdas;
    loops = [];
    cancelled = [];
    returns = [];
    lends = [];
  }

let read_formula (frame : State.frame) (formula : Mir.formula) ~arguments =
  let run = make_run ~locals:formula.locals ~lambdas:formula.lambdas in
  let inside =
    {
      frame with
      State.locals = Lambdas.remove_temporaries frame.locals;
      aliases = Locals.empty;
      lends = Locals.empty;
      is_ghost = true;
    }
  in
  let inside =
    if arguments = [] then inside
    else
      List.fold_left2
        (fun inside parameter argument ->
          Facts.bind inside
            (Locals.make_key run.infos parameter)
            (Encoding.substitute_type inside formula.locals.(parameter).type_)
            argument)
        inside formula.parameters arguments
  in
  Facts.run_in_source frame (fun () ->
      match read_block inside run formula.value with
      | Some (after, term) -> ({ frame with spent = after.spent }, term)
      | None when Types.equal formula.type_ Types.bool -> (frame, Logic.Boolean true)
      | None -> (frame, Encoding.arrive frame "unfinished" formula.type_))

let read_body (start : State.frame) ~(lambdas : Mir.body array) (body : Mir.body) =
  let run = make_run ~locals:body.locals ~lambdas in
  let start = { start with State.aliases = Locals.empty; lends = Locals.empty } in
  let rec list_returned_locals (block : Mir.block) =
    List.concat_map
      (fun (statement : Mir.statement) ->
        (match statement.kind with
          | Resume { exits; _ } ->
              List.filter_map (fun (exit : Mir.early_exit) -> exit.returned) exits
          | _ -> [])
        @ List.concat_map list_returned_locals (Mir.list_nested_blocks statement))
      block.statements
  in
  let start =
    List.fold_left
      (fun frame local ->
        let ty = Encoding.substitute_type frame body.locals.(local).type_ in
        Facts.bind frame (Locals.make_key run.infos local) ty (Encoding.arrive frame "returned" ty))
      start (list_returned_locals body.code)
  in
  match read_statements start run body.code.statements with
  | None -> { State.returns = run.returns; lends = run.lends }
  | Some _ -> Facts.raise_bug "a body whose end control reaches"
