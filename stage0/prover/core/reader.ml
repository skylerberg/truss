let ( let* ) = Option.bind

type loop_exits = {
  loop : Core.id;
  mutable breaks : State.frame list;
  mutable ends : State.frame list;
}

type run = {
  infos : Mir.local_info array;
  changed_in_place : (Mir.local, unit) Hashtbl.t;
  held_callbacks : (Mir.local, Core.local) Hashtbl.t;
  lambdas : Mir.body array;
  mutable loops : loop_exits list;
  mutable cancelled : (Mir.task * State.frame list ref) list;
}

let make_unit_callee : _ Core.target -> Invocation.callee = function
  | Function { path; instantiation } -> Function { path; instantiation }
  | Trait_method { trait; name; receiver; self_type; instantiation; evidence } ->
      Trait_method { trait; name; receiver; self_type; instantiation; evidence }
  | Capability_method { capability; name } -> Capability_method { capability; name }
  | Intrinsic { operation; type_arguments } -> Intrinsic { operation; type_arguments }
  | Indirect _ -> Indirect ()

let make_invocation (callee : Mir.callee) ~lends : Invocation.t =
  { callee = make_unit_callee callee.target; lends; uses = callee.uses }

let find_declared_fields context ty variant =
  match Facts.find_visible_type context ty with
  | Some (interface, substitution) -> (
      let list_fields (list : Types.field list) =
        List.map
          (fun (field : Types.field) ->
            (field.field_name, Types.substitute substitution field.field_type))
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

let rec compute_place_type context frame run (place : Mir.place) =
  match place.Mir.projections with
  | [] -> (
      match place.Mir.root with
      | Local local -> Facts.substitute_type context frame run.infos.(local).type_
      | Constant path -> Interface.Definition.read_constant_type context.lookups.interface path
      | Literal { type_; _ } -> Facts.substitute_type context frame type_)
  | _ -> (
      let base =
        { place with Mir.projections = List.rev (List.tl (List.rev place.Mir.projections)) }
      in
      let base_type = compute_place_type context frame run base in
      let find_field_type variant field =
        match
          Option.bind (find_declared_fields context base_type variant) (List.assoc_opt field)
        with
        | Some field_type -> Facts.substitute_type context frame field_type
        | None -> Facts.raise_unsupported Whole_definition "the field `%s`" field
      in
      match List.nth place.Mir.projections (List.length place.Mir.projections - 1) with
      | Field field -> find_field_type None field
      | Variant_field { variant; field } -> find_field_type (Some variant) field
      | Element _ -> Intrinsics.find_sequence_element context frame base_type
      | Range _ ->
          Types.Named
            {
              path = Well_known.make_path Slice;
              arguments = [ Types.Type (Intrinsics.find_sequence_element context frame base_type) ];
            })

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
  | _ ->
      Facts.raise_unsupported Whole_definition
        "a name that the alternatives of a pattern bind `mut`, here"

let describe_local : Mir.local_kind -> string = function
  | Source { local; _ } -> (
      match Mir.find_local_name local with
      | Some name -> Printf.sprintf "`%s`" name
      | None -> "a local that the compiler introduces")
  | Temporary -> "a temporary"
  | Lent _ -> "a lent part"

let read_root context frame run (root : Mir.root) =
  match root with
  | Constant path -> Values.evaluate_constant context frame path
  | Literal { value; type_ } ->
      Values.make_literal_value context frame (Facts.substitute_type context frame type_) value
  | Local local -> (
      match Locals.make_key run.infos local with
      | Core_local Self -> (
          match frame.self with
          | Some self -> self
          | None -> Facts.raise_bug "`%s` reads `self` outside a method" frame.source.name)
      | key -> (
          (if frame.makes_obligations && not context.reading_callback then
             match key with
             | Core_local core -> Validity.check_escaping_callback context frame core
             | Mir_local _ -> (
                 match Hashtbl.find_opt run.held_callbacks local with
                 | Some core -> Validity.check_escaping_callback context frame core
                 | None -> ()));
          match Locals.find_opt key frame.locals with
          | Some term -> term
          | None ->
              Facts.raise_bug "`%s` reads %s before the prover binds it" frame.source.name
                (describe_local run.infos.(local).kind)))

let rec read_resolved context frame run (place : Mir.place) =
  let _, term =
    List.fold_left
      (fun (prefix, term) (projection : Mir.projection) ->
        let base = { place with Mir.projections = prefix } in
        let base_type = compute_place_type context frame run base in
        let projected = { place with Mir.projections = prefix @ [ projection ] } in
        let project_field variant field =
          if Facts.find_constructors context base_type = None then
            Facts.raise_unsupported Whole_definition
              "a field of `%s`, whose fields the prover does not see" (Types.show base_type);
          ignore (Facts.declare_sort context base_type);
          Values.project_field context frame base_type variant field
            (compute_place_type context frame run projected)
            term
        in
        ( prefix @ [ projection ],
          match projection with
          | Field field -> project_field None field
          | Variant_field { variant; field } -> project_field (Some variant) field
          | Element { node; index; origin; _ } ->
              Intrinsics.read_sequence_element context frame base_type term
                (read_index context frame run index)
                ~node ~origin
          | Range { node; start; stop; origin; _ } ->
              let _, viewed, _, _ =
                Intrinsics.apply_slice context frame ~node
                  { origin; type_ = compute_place_type context frame run projected }
                  ~base_type ~collection:term
                  ~low:(read_index context frame run start)
                  ~high:(Option.map (read_index context frame run) stop)
              in
              viewed ))
      ([], read_root context frame run place.Mir.root)
      place.Mir.projections
  in
  term

and read_index context frame run (index : Mir.operand) =
  match index with
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> (
      match (read_resolved context frame run place, frame.bound) with
      | ((Logic.Symbol _ | Logic.Integer _) as term), _ | term, _ :: _ -> term
      | computed, [] ->
          let named = Facts.declare_fresh context frame "index" Logic.Int in
          Facts.assume context frame (Logic.equal named computed);
          named)
  | Immediate { value = Integer number; _ } -> Logic.Integer number
  | Immediate { value = Unit | Float _ | Boolean _; _ } ->
      Facts.raise_bug "an index that is not an integer"

let read_place context frame run (place : Mir.place) =
  match resolve_aliases frame run place with
  | [ (_, place) ] -> read_resolved context frame run place
  | alternatives -> (
      match List.rev alternatives with
      | (_, first) :: later ->
          List.fold_left
            (fun otherwise (condition, place) ->
              Logic.ite condition (read_resolved context frame run place) otherwise)
            (read_resolved context frame run first)
            later
      | [] -> Facts.raise_bug "a place that is no place")

let replace_field context ty variant field whole new_value =
  match Option.bind (Facts.find_constructors context ty) (List.assoc_opt variant) with
  | Some fields ->
      Logic.Apply
        ( Facts.make_constructor_symbol ty variant,
          List.map
            (fun (name, _) ->
              if name = field then new_value
              else Validity.select_field context ty variant name whole)
            fields )
  | None -> Facts.raise_unsupported Whole_definition "the fields of `%s`" (Types.show ty)

let write_resolved context frame run (place : Mir.place) new_value =
  let rec rebuild prefix whole = function
    | [] -> new_value
    | (projection : Mir.projection) :: rest -> (
        let base_type =
          compute_place_type context frame run { place with Mir.projections = prefix }
        in
        let projected = { place with Mir.projections = prefix @ [ projection ] } in
        let part_type = compute_place_type context frame run projected in
        let rebuilt part = rebuild (prefix @ [ projection ]) part rest in
        let replace_part variant field =
          let part = Values.project_field context frame base_type variant field part_type whole in
          replace_field context base_type variant field whole (rebuilt part)
        in
        match projection with
        | Field field -> replace_part None field
        | Variant_field { variant; field } -> replace_part (Some variant) field
        | Element { node; index; origin; _ } ->
            let index = read_index context frame run index in
            let replaced =
              Intrinsics.read_sequence_element context frame base_type whole index ~node ~origin
            in
            let element = rebuilt replaced in
            (match rest with
            | [] -> ()
            | _ :: _ ->
                Lambdas.check_valid context frame
                  (Facts.locate context frame.source origin)
                  part_type element ~deep:true ~when_:"for the element changed here");
            let after =
              Intrinsics.write_sequence_element context frame base_type whole index element
            in
            Amounts.assume_element_potential_change context frame base_type ~before:whole ~after
              ~replaced ~written:element;
            after
        | Range { node; start; stop; origin; _ } ->
            let _, viewed, start, stop =
              Intrinsics.apply_slice context frame ~node { origin; type_ = part_type } ~base_type
                ~collection:whole
                ~low:(read_index context frame run start)
                ~high:(Option.map (read_index context frame run) stop)
            in
            Intrinsics.write_sequence_range context frame base_type whole ~start ~stop
              (rebuilt viewed))
  in
  match place.Mir.root with
  | Constant _ | Literal _ -> Facts.raise_unsupported Whole_definition "assigning to a constant"
  | Local local -> (
      let whole =
        if place.Mir.projections = [] then new_value
        else begin
          Hashtbl.replace run.changed_in_place local ();
          rebuild [] (read_root context frame run place.Mir.root) place.Mir.projections
        end
      in
      match Locals.make_key run.infos local with
      | Core_local Self -> { frame with self = Some whole }
      | key ->
          Facts.bind frame key (Facts.substitute_type context frame run.infos.(local).type_) whole)

let write_place context frame run (place : Mir.place) new_value =
  match resolve_aliases frame run place with
  | [ (_, place) ] -> write_resolved context frame run place new_value
  | alternatives ->
      List.fold_left
        (fun frame (condition, (place : Mir.place)) ->
          let written = write_resolved context frame run place new_value in
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
                        (Facts.substitute_type context frame run.infos.(local).type_)
                        (Logic.ite condition after before)
                  | _ -> written)))
        frame alternatives

let list_mut_provided_places (provided : Mir.provided list) =
  List.filter_map
    (fun (implementation : Mir.provided) ->
      match (implementation.mode, implementation.value) with
      | Language.Mode.Mut, Borrow { place; _ } -> Some place
      | Mut, (Use _ | Take _ | Immediate _) | (Read | Own), _ -> None)
    provided

let compute_changes ?(also = []) run (frame : State.frame) (blocks : Mir.block list) : State.changed
    =
  let locals = ref [] and self = ref false and reassigned = ref [] in
  let note (place : Mir.place) =
    List.iter
      (fun (_, (place : Mir.place)) ->
        match place.Mir.root with
        | Local local -> (
            match Locals.make_key run.infos local with
            | Core_local Self -> self := true
            | key -> if Locals.mem key frame.locals then locals := key :: !locals)
        | Constant _ | Literal _ -> ())
      (resolve_aliases frame run place)
  in
  let note_assigned (place : Mir.place) =
    (match place with
    | { root = Local local; projections = [] } -> (
        match Locals.make_key run.infos local with
        | Core_local Self -> ()
        | key -> if Locals.mem key frame.locals then reassigned := key :: !reassigned)
    | _ -> ());
    note place
  in
  let note_passed (call : Mir.call) =
    List.iter
      (function
        | Mir.Passed { mode = Language.Mode.Mut; value = Borrow { place; _ } | Use { place; _ }; _ }
          ->
            note place
        | Passed _ | Default -> ())
      call.arguments
  in
  let rec note_lent : Mir.yielded -> unit = function
    | Part (Borrow { place; _ }) -> note place
    | Part _ -> ()
    | Built { fields; _ } -> List.iter (fun (_, field) -> Option.iter note_lent field) fields
  in
  let rec visit (block : Mir.block) =
    List.iter
      (fun (statement : Mir.statement) ->
        (match statement.kind with
        | Basic
            (Assign { target; value = Operand (Borrow { place; mode = Language.Mode.Mut; _ }); _ })
          ->
            note target;
            note place
        | Basic (Assign { target; _ }) | Choose { target; _ } -> note_assigned target
        | Basic (Call { destination; call }) ->
            Option.iter note_assigned destination;
            note_passed call
        | Basic (Lend { call; _ }) -> note_passed call
        | Provide { target; provided; _ } ->
            note_assigned target;
            List.iter note (list_mut_provided_places provided)
        | For { iteration = Pull { cursor; _ }; _ } -> note cursor
        | Yield { mode = Language.Mode.Mut; part } -> note_lent part
        | Jump (Cancel { winner; returned; _ }) ->
            note { root = Local winner; projections = [] };
            Option.iter (fun (_, local) -> note { root = Local local; projections = [] }) returned
        | Basic
            ( Live _ | Dead _ | Assert _ | Echo _ | Loan_start _ | Loan_end _ | Ghost_assert _
            | Path_note _ | Proof _ | Evaluated_assert _ )
        | Assert_by_bit_vector _ | While _ | Fork _ | Resume _
        | For { iteration = Range _; _ }
        | Yield { mode = Read | Own; _ }
        | Jump (Return _ | Break | Continue | Unreachable | Written_unreachable | Todo) ->
            ());
        List.iter visit (Mir.list_nested_blocks statement))
      block.statements
  in
  List.iter visit blocks;
  List.iter note also;
  {
    changed_locals = List.sort_uniq compare !locals;
    changes_self = !self && frame.self <> None;
    reassigned = List.sort_uniq compare !reassigned;
  }

let read_operand context frame run (operand : Mir.operand) =
  match operand with
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> read_place context frame run place
  | Immediate { value; type_ } -> (
      let ty = Facts.substitute_type context frame type_ in
      match value with
      | Unit ->
          ignore (Facts.declare_sort context Types.unit);
          Logic.Apply (Logic.Symbol.Unit, [])
      | Integer number -> Logic.Integer number
      | Float number -> (
          match Facts.find_float_format ty with
          | Some format -> Operations.make_float_literal format number
          | None -> Facts.raise_unsupported Whole_definition "a float literal without a float type")
      | Boolean truth -> Logic.Boolean truth)

let compute_operand_type context frame operand =
  Facts.substitute_type context frame (Mir.extract_operand_type operand)

let find_operand_origin : Mir.operand -> Core.origin option = function
  | Use { origin; _ } | Borrow { origin; _ } | Take { origin; _ } -> Some origin
  | Immediate _ -> None

let find_whole_local : Mir.operand -> Mir.local option = function
  | Use { place = { root = Local local; projections = [] }; _ }
  | Borrow { place = { root = Local local; projections = [] }; _ } ->
      Some local
  | Use _ | Borrow _ | Take _ | Immediate _ -> None

let make_passed_place context run place =
  {
    State.read =
      (fun frame -> read_place context { frame with makes_obligations = false } run place);
    write = (fun frame term -> write_place context frame run place term);
    note_changed_in_place =
      (fun () ->
        match place.root with
        | Local local -> Hashtbl.replace run.changed_in_place local ()
        | Constant _ | Literal _ -> ());
  }

let find_held_callback context run held (value : Mir.rvalue) =
  let read_whole (operand : Mir.operand) =
    match operand with
    | Use { place = { root = Local local; projections = [] }; _ }
    | Borrow { place = { root = Local local; projections = [] }; _ } -> (
        match run.infos.(local).kind with
        | Source { local = core; _ } when Option.is_some (Validity.find_own_callback context core)
          ->
            Some core
        | Source _ | Temporary | Lent _ -> Hashtbl.find_opt run.held_callbacks local)
    | Use _ | Borrow _ | Take _ | Immediate _ -> None
  in
  match (run.infos.(held).kind, value) with
  | (Temporary | Lent _), (Operand operand | Convert { conversion = Widen; value = operand; _ }) ->
      read_whole operand
  | _ -> None

let classify_shape run ?function_ (value : Mir.operand) : Invocation.shape =
  match (function_, find_whole_local value) with
  | Some (Mir.Function_reference { path; origin }), _ -> Named_function { origin; path }
  | (Some (Lambda_expression _) | None), Some local -> (
      match (run.infos.(local).kind, Hashtbl.find_opt run.held_callbacks local) with
      | Source { local = core; _ }, _ | (Temporary | Lent _), Some core -> Forwarded core
      | (Temporary | Lent _), None -> Other)
  | (Some (Lambda_expression _) | None), None -> Other

let find_argument_place context run (mode : Language.Mode.t) (value : Mir.operand) =
  match (mode, value) with
  | Mut, Borrow { place; _ } -> Some (make_passed_place context run place)
  | Mut, (Use _ | Take _ | Immediate _) | (Read | Own), _ -> None

let evaluate_call_values context frame run (invocation : Invocation.t)
    (arguments : Mir.argument list) =
  Lambdas.make_passed_values context frame invocation
    (List.concat
       (List.mapi
          (fun position (argument : Mir.argument) ->
            match argument with
            | Passed { mode; value; function_; _ } -> (
                match function_ with
                | Some (Lambda_expression { body; origin; type_ }) ->
                    [
                      State.Lambda_argument
                        {
                          position;
                          mode;
                          site = { origin; type_ };
                          lambda = { code = run.lambdas.(body); lambdas = run.lambdas };
                        };
                    ]
                | Some (Function_reference _) | None ->
                    [
                      Value_argument
                        {
                          position;
                          mode;
                          shape = classify_shape run ?function_ value;
                          origin = find_operand_origin value;
                          passed_place = find_argument_place context run mode value;
                          type_ = compute_operand_type context frame value;
                          term =
                            Validity.run_reading_callback context (fun () ->
                                read_operand context frame run value);
                        };
                    ])
            | Default -> [])
          arguments))

let read_call context frame run (call : Mir.call) ~result_type =
  let invocation = make_invocation call.callee ~lends:None in
  match (invocation.callee, call.arguments) with
  | ( Trait_method { trait; name; receiver; _ },
      [
        Passed { value = tested; _ };
        Passed
          {
            value =
              Borrow { place = { root = Literal { value = Text text; _ }; projections = [] }; _ };
            _;
          };
      ] )
    when Well_known.is_method Equal_equal (Method { owner = trait.trait; name; receiver }) ->
      let ty = compute_operand_type context frame tested in
      Some
        ( frame,
          Values.make_text_match context
            (Facts.locate context frame.source call.origin)
            ty
            (read_operand context frame run tested)
            text )
  | _ ->
      let through =
        match call.callee.target with
        | Indirect callee ->
            Some
              ( compute_operand_type context frame callee,
                Validity.run_reading_callback context (fun () ->
                    read_operand context frame run callee),
                classify_shape run callee )
        | _ -> None
      in
      let values = evaluate_call_values context frame run invocation call.arguments in
      Calls.apply_call context frame
        { origin = call.origin; type_ = result_type }
        invocation ~through values

let read_lend context (frame : State.frame) run part (call : Mir.call) =
  let mode = match run.infos.(part).kind with Lent mode -> mode | _ -> Language.Mode.Read in
  let invocation = make_invocation call.callee ~lends:(Some mode) in
  let site : Invocation.site = { origin = call.origin; type_ = run.infos.(part).type_ } in
  let values = evaluate_call_values context frame run invocation call.arguments in
  let lend ?leave_lent frame =
    Calls.apply_call ?leave_lent context frame site invocation ~through:None values
  in
  let lent, write_back =
    match (invocation.lends, invocation.callee) with
    | Some Language.Mode.Mut, Intrinsic _ -> Facts.raise_bug "an intrinsic that lends `mut`"
    | Some Language.Mode.Mut, _ ->
        ( Validity.run_without_costs context (fun () -> lend frame),
          Some
            (fun frame final ->
              match lend ~leave_lent:(fun _ -> final) frame with
              | Some (after, _) -> after
              | None -> frame) )
    | _ -> (lend frame, None)
  in
  Option.map
    (fun (after, term) ->
      let lent = write_place context after run { root = Local part; projections = [] } term in
      match write_back with
      | Some write_back ->
          {
            lent with
            lends =
              Locals.add (Locals.make_key run.infos part)
                [ (Logic.Boolean true, write_back) ]
                lent.lends;
          }
      | None -> lent)
    lent

let compute_target_type context frame run (target : Mir.place) =
  match target with
  | { root = Local local; projections = [] } -> run.infos.(local).type_
  | _ -> compute_place_type context frame run target

let lends_places (part : Mir.yielded) =
  match part with Built _ | Part (Borrow _) -> true | Part (Use _ | Take _ | Immediate _) -> false

let rec read_yielded_value context frame run ~origin (part : Mir.yielded) =
  match part with
  | Part operand -> (frame, read_operand context frame run operand)
  | Built { variant; fields; type_ } ->
      let frame, values =
        List.fold_left
          (fun (frame, values) (name, field) ->
            match field with
            | Some field ->
                let frame, term = read_yielded_value context frame run ~origin field in
                (frame, values @ [ (name, Some term) ])
            | None -> (frame, values @ [ (name, None) ]))
          (frame, []) fields
      in
      Values.apply_construct context frame { origin; type_ } variant values

let rec write_back_part context run ty (part : Mir.yielded) frame after =
  match part with
  | Part (Borrow { place; _ }) -> write_place context frame run place after
  | Built { variant; fields; _ } -> (
      match Facts.find_constructors context ty with
      | Some shape ->
          let shaped = Option.value (List.assoc_opt variant shape) ~default:[] in
          List.fold_left
            (fun frame (name, field) ->
              match (field, List.assoc_opt name shaped) with
              | Some field, Some field_type when lends_places field ->
                  let field_type = Facts.substitute_type context frame field_type in
                  let selected =
                    Values.project_field context frame ty variant name field_type after
                  in
                  let value =
                    match variant with
                    | None -> selected
                    | Some _ ->
                        Logic.ite
                          (Logic.Is (Facts.make_constructor_symbol ty variant, after))
                          selected
                          (Facts.arrive context frame "lent" field_type)
                  in
                  write_back_part context run field_type field frame value
              | _ -> frame)
            frame fields
      | None -> Facts.raise_unsupported Whole_definition "the fields of `%s`" (Types.show ty))
  | Part (Use _ | Take _ | Immediate _) -> frame

let bind_parts context (frame : State.frame) run =
  Locals.fold
    (fun key parts (frame : State.frame) ->
      match (key, Locals.find_opt key frame.types, List.rev parts) with
      | Locals.Mir_local _, _, _ -> frame
      | _, Some ty, (_, first) :: later -> (
          let read = read_place context { frame with makes_obligations = false } run in
          try
            Facts.bind frame key ty
              (List.fold_left
                 (fun otherwise (condition, part) -> Logic.ite condition (read part) otherwise)
                 (read first) later)
          with Facts.Unsupported _ -> frame)
      | _ -> frame)
    frame.aliases frame

let note_path (context : State.context) (frame : State.frame) (note : Mir.path_note) =
  if frame.makes_obligations && Facts.is_home context frame.source then begin
    let quote = Facts.quote_origin context frame in
    let text =
      match note with
      | Arm_taken patterns ->
          Printf.sprintf "the arm `%s` is taken" (String.concat ", " (List.map quote patterns))
      | Condition_holds { condition; holds } -> Printf.sprintf "`%s` is %b" (quote condition) holds
      | Else_runs pattern ->
          Printf.sprintf "`%s` does not match, so the `else` runs" (quote pattern)
      | Returns_early tried -> Printf.sprintf "`%s` returns early" (quote tried)
    in
    context.path_notes <- (text, frame.condition) :: context.path_notes
  end

let refresh_place context frame ty (place : State.passed_place) =
  let fresh_value = Facts.arrive context frame "changed" ty in
  let frame = place.write frame fresh_value in
  Validity.assume_valid context frame ty fresh_value;
  frame

let record_todo (context : State.context) (frame : State.frame) origin =
  Facts.add_hole context (frame.source.key, Obligation.Node origin);
  if frame.is_ghost then context.unfinished <- frame.condition :: context.unfinished

let oblige_unreachable context frame location =
  Facts.oblige context frame Unreachable location
    [ Text "This `unreachable` may be reached." ]
    (Logic.Boolean false)

let lend_part context (frame : State.frame) origin (mode : Language.Mode.t) ~handed ~lends
    ~write_back =
  let location = Facts.locate context frame.source origin in
  match (context.yielded_part, context.yield_ensures, frame.yielded_so_far) with
  | Some part_type, Some (each, _), Some before ->
      List.iter
        (fun (clause : Mir.formula) ->
          let _, term =
            Validity.read_specification context
              { frame with result = Some handed; yielded = Some before }
              clause
          in
          Facts.oblige context frame Ensures
            (Facts.locate context frame.source clause.origin)
            [
              Text "`";
              Facts.quote frame.source clause.origin;
              Text "` may not hold for the part lent here.";
            ]
            term)
        each;
      Lambdas.check_valid context frame location part_type handed ~deep:true
        ~when_:"for the part lent here";
      let frame, part_after =
        if mode = Language.Mode.Mut && lends then (
          let part_after = Facts.arrive context frame "lent" part_type in
          context.lent_back <- (part_type, handed, part_after) :: context.lent_back;
          (write_back frame part_after, part_after))
        else (frame, handed)
      in
      Some
        {
          frame with
          yielded_so_far = Some (Intrinsics.append_part context frame part_type before part_after);
        }
  | _ -> Facts.raise_unsupported location "a lent part outside a lending method's body"

let rec read_rvalue context (frame : State.frame) run (value : Mir.rvalue) ~(site : Invocation.site)
    =
  let location = Facts.locate context frame.source site.origin in
  let ty = Facts.substitute_type context frame site.type_ in
  let translate_operand = read_operand context frame run in
  match value with
  | Operand value -> (frame, translate_operand value)
  | Compare { comparison = compared; left; right } ->
      ( frame,
        Operations.compare_terms
          (compute_operand_type context frame left)
          compared (translate_operand left) (translate_operand right) )
  | Not inner -> (frame, Logic.not_ (translate_operand inner))
  | Is_variant { place; variant } ->
      let ty = compute_place_type context frame run place in
      ignore (Facts.declare_sort context ty);
      if Facts.find_constructors context ty = None then
        Facts.raise_unsupported location "a variant of `%s`, which the prover does not see"
          (Types.show ty);
      ( frame,
        Logic.Is
          (Facts.make_constructor_symbol ty (Some variant), read_place context frame run place) )
  | Copy copied_operand ->
      let ty = compute_operand_type context frame copied_operand in
      let term = translate_operand copied_operand in
      let literal =
        match copied_operand with
        | Borrow { place = { root = Literal { value; _ }; projections = [] }; _ } -> Some value
        | _ -> None
      in
      (Values.copy_value ?literal context frame ty term, term)
  | Convert { conversion = Widen; value; converts_function_expression } ->
      Operations.check_widened location ~is_written:converts_function_expression
        (compute_operand_type context frame value)
        ty;
      (frame, translate_operand value)
  | Value_parameter parameter ->
      (frame, Models.make_value_term context frame (Value_parameter parameter))
  | Convert { conversion = To_integer; value; _ } -> (frame, translate_operand value)
  | Convert { conversion = View_to_owned; value; _ } ->
      ( frame,
        Values.make_owner_of_view context frame
          ~view:(compute_operand_type context frame value)
          ~owner:ty (translate_operand value) )
  | Convert { conversion = From_integer; value; _ } ->
      (frame, Operations.convert_from_integer context frame site (translate_operand value))
  | Function_value { path; instantiation; is_argument } ->
      ( frame,
        Values.translate_global_value context frame site path instantiation.type_arguments
          ~is_argument )
  | To_any _ -> Operations.convert_to_any context frame site
  | Operation { operation; operands; type_arguments } ->
      let types =
        List.filter_map
          (function Types.Type ty -> Some (Facts.substitute_type context frame ty) | _ -> None)
          type_arguments
      in
      let types = match types with [] -> [ ty ] | types -> types in
      let terms = List.map translate_operand operands in
      ( frame,
        Operations.translate_primitive_operation context frame ~site operation types terms
          ~arguments:(List.map find_operand_origin operands) ~fallback:(fun () ->
            Facts.arrive context frame "result" ty) )
  | Construct { variant; fields; type_ } ->
      Values.apply_construct context frame { site with type_ } variant
        (List.map (fun (name, field) -> (name, Option.map translate_operand field)) fields)
  | Array elements ->
      Values.apply_list_literal context frame site (List.map translate_operand elements)
  | Lambda { body; _ } ->
      Lambdas.translate_lambda context frame ~site
        { code = run.lambdas.(body); lambdas = run.lambdas }
        ~list_facts:(fun _ -> [])
        ~list_promises:(fun ~entries:_ ~exits:_ ~result:_ -> [])
  | Specification Result -> (
      match frame.result with
      | Some result -> (frame, result)
      | None -> Facts.raise_bug "`%s` reads `result` outside an `ensures`" frame.source.name)
  | Specification (Entry local) -> (
      match Locals.make_key run.infos local with
      | Core_local Self -> (
          match frame.old_self with
          | Some self -> (frame, self)
          | None -> Facts.raise_bug "`%s` reads `old(self)` outside a method" frame.source.name)
      | key -> (
          match Locals.find_opt key frame.old_locals with
          | Some term -> (frame, term)
          | None ->
              Facts.raise_bug "`%s` reads the entry value of %s, which the prover did not bind"
                frame.source.name
                (describe_local run.infos.(local).kind)))
  | Specification Yielded -> (
      match (frame.yielded, frame.yielded_so_far) with
      | Some yielded, _ -> (frame, yielded)
      | None, Some yielded_so_far when Facts.is_home context frame.source -> (frame, yielded_so_far)
      | _ -> Facts.raise_bug "`%s` reads `yielded` outside a lending method" frame.source.name)
  | Specification (Identical (first, second)) ->
      let first_value = translate_operand first and second_value = translate_operand second in
      Values.assume_extensional context frame
        (compute_operand_type context frame first)
        first_value second_value;
      (frame, Logic.equal first_value second_value)
  | Specification (Applied { function_; arguments; unconverted }) ->
      let values =
        Validity.run_reading_callback context (fun () -> List.map translate_operand arguments)
      in
      Values.apply_specification_function context frame ~location function_ values
        ~unconverted:(List.map (Facts.substitute_type context frame) unconverted)
        ~types:(List.map (compute_operand_type context frame) arguments)
  | Specification (Method_cost { metric; method_ }) ->
      (frame, Amounts.compute_method_cost context frame metric (make_unit_callee method_))
  | Specification (Map entries) ->
      Values.apply_map_literal context frame ~ty ~location
        (List.map
           (fun (key, entry) ->
             (find_operand_origin key, translate_operand key, translate_operand entry))
           entries)
  | Specification (Quantified { quantifier; range; parameter; matches; body }) ->
      let range =
        match range with
        | Over_type ty -> Models.Range_of_type (Facts.substitute_type context frame ty)
        | Over_range { start; stop; inclusive } ->
            Range_of_integers
              {
                low = translate_operand start;
                high = translate_operand stop;
                inclusive;
                type_ = compute_operand_type context frame start;
              }
      in
      translate_quantifier_value context frame run quantifier range ~parameter ~matches ~body

and translate_quantifier_value context frame run quantifier range ~parameter ~(matches : Mir.block)
    ~(body : Mir.block) =
  Models.quantify_over context frame quantifier range
    ~bind:(fun inner value ty -> Facts.bind inner (Locals.make_key run.infos parameter) ty value)
    ~read:(fun body_frame _ ->
      let after_matches, matched = read_value context body_frame run matches in
      let after, holds = read_value context (Facts.restrict after_matches matched) run body in
      ( { body_frame with spent = after.spent },
        match quantifier with
        | Forall -> Logic.( ==> ) matched holds
        | Exists -> Logic.( &&& ) matched holds ))

and read_statements context frame run (statements : Mir.statement list) =
  List.fold_left
    (fun frame statement ->
      Option.bind frame (fun frame ->
          Option.map
            (fun frame -> bind_parts context frame run)
            (read_statement context frame run statement)))
    (Some frame) statements

and read_block context frame run (block : Mir.block) =
  Option.map
    (fun after ->
      match block.value with
      | Some value -> (after, read_operand context after run value)
      | None -> Facts.raise_bug "a block with no value, whose end control reaches")
    (read_statements context frame run block.statements)

and read_value context frame run (block : Mir.block) =
  match read_block context frame run block with
  | Some read -> read
  | None -> Facts.raise_unsupported Whole_definition "a call in a specification that never returns"

and join_after_either context ~(outer : State.frame) ~condition
    ((entered : State.frame), (after : State.frame))
    ((entered_otherwise : State.frame), (after_otherwise : State.frame)) =
  fst
    (Facts.merge context
       ~condition:
         (if
            after.condition == entered.condition
            && after_otherwise.condition == entered_otherwise.condition
          then outer.condition
          else
            Facts.name_path_condition context outer
              (Logic.( ||| ) after.condition after_otherwise.condition))
       [ (condition, after, None); (Logic.not_ condition, after_otherwise, None) ])

and merge_alternatives context ~outer ~condition (entered, read) (entered_otherwise, otherwise) =
  match (read, otherwise) with
  | None, None -> None
  | Some after, None | None, Some after -> Some after
  | Some (after, value), Some (after_otherwise, value_otherwise) ->
      Some
        ( join_after_either context ~outer ~condition (entered, after)
            (entered_otherwise, after_otherwise),
          Logic.ite condition value value_otherwise )

and read_choice context frame run (choice : Mir.choice) =
  match choice with
  | Conditional { condition; then_; else_ } -> (
      match read_block context frame run condition with
      | None -> None
      | Some (frame, test) ->
          let entered_then = Facts.restrict frame test
          and entered_else = Facts.restrict frame (Logic.not_ test) in
          merge_alternatives context ~outer:frame ~condition:test
            (entered_then, read_block context entered_then run then_)
            (entered_else, read_block context entered_else run else_))
  | Cases cases ->
      let rec find_first_taken (current : State.frame) = function
        | [] -> Facts.raise_bug "a `match` with no case"
        | (case : Mir.case) :: later ->
            let bound, matches = read_value context current run case.tests in
            let entered, is_taken, after_tests =
              match case.guard with
              | Some guard ->
                  let guarded = Facts.restrict bound matches
                  and unmatched = Facts.restrict bound (Logic.not_ matches) in
                  let after, holds = read_value context guarded run guard in
                  ( Facts.restrict after holds,
                    Logic.( &&& ) matches holds,
                    join_after_either context ~outer:current ~condition:matches (guarded, after)
                      (unmatched, unmatched) )
              | None ->
                  ( Facts.restrict bound matches,
                    matches,
                    { bound with condition = current.condition } )
            in
            let read = read_block context entered run case.value in
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
              merge_alternatives context ~outer:current ~condition:is_taken (entered, read)
                (not_taken, find_first_taken not_taken later)
      in
      find_first_taken frame cases
  | Connective { connective; left; right } -> (
      match read_block context frame run left with
      | None -> None
      | Some (frame, left) -> (
          let reads_right = match connective with And | Implies -> left | Or -> Logic.not_ left in
          let entered = Facts.restrict frame reads_right in
          match read_block context entered run right with
          | Some (after, right) ->
              let skipped = Facts.restrict frame (Logic.not_ reads_right) in
              Some
                ( join_after_either context ~outer:frame ~condition:reads_right (entered, after)
                    (skipped, skipped),
                  match connective with
                  | And -> Logic.( &&& ) left right
                  | Or -> Logic.( ||| ) left right
                  | Implies -> Logic.( ==> ) left right )
          | None ->
              Some (Facts.restrict frame (Logic.not_ reads_right), Logic.Boolean (connective <> And))
          ))

and read_providing (context : State.context) run provided ~refresh read =
  let returns = context.returns in
  let loops = List.map (fun (exits : loop_exits) -> (exits, exits.breaks, exits.ends)) run.loops in
  let cancelled = List.map (fun (_, frames) -> (frames, !frames)) run.cancelled in
  let enclosing = context.enclosing_provides in
  context.enclosing_provides <- provided :: enclosing;
  let read = Fun.protect ~finally:(fun () -> context.enclosing_provides <- enclosing) read in
  let rec refresh_since ~before refresh_exit = function
    | exits when exits == before -> exits
    | exit :: rest -> refresh_exit exit :: refresh_since ~before refresh_exit rest
    | [] -> Facts.raise_bug "the exits before a `provide` block are gone after it"
  in
  context.returns <-
    refresh_since ~before:returns (fun (frame, value) -> (refresh frame, value)) context.returns;
  List.iter
    (fun ((exits : loop_exits), breaks, ends) ->
      exits.breaks <- refresh_since ~before:breaks refresh exits.breaks;
      exits.ends <- refresh_since ~before:ends refresh exits.ends)
    loops;
  List.iter (fun (frames, before) -> frames := refresh_since ~before refresh !frames) cancelled;
  read

and read_statement context frame run (statement : Mir.statement) =
  let location = Facts.locate context frame.source statement.origin in
  Facts.reject_recursion_through_supplied_code context frame location statement;
  match statement.kind with
  | Basic basic -> read_basic context frame run statement basic
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
      let frame, term = read_value context frame run code in
      Assertions.check_assertion context frame ~origin:statement.origin
        ~bit_vector:(Some (named, fun isolated -> snd (read_value context isolated run code)))
        term;
      Some frame
  | Provide { target; provided; body; _ } ->
      let refresh frame =
        List.fold_left
          (fun frame place ->
            let root = { (expand_place frame run place) with Mir.projections = [] } in
            refresh_place context frame
              (compute_place_type context frame run root)
              (make_passed_place context run root))
          frame
          (list_mut_provided_places provided)
      in
      let read =
        read_providing context run provided ~refresh (fun () -> read_block context frame run body)
      in
      write_assignment context run target ~copied:(Option.to_list body.value)
        (Option.map (fun (after, term) -> (refresh after, term)) read)
  | Choose { target; choice } ->
      let copied =
        match choice with
        | Conditional { then_; else_; _ } -> List.filter_map Fun.id [ then_.value; else_.value ]
        | Cases cases -> List.filter_map (fun (case : Mir.case) -> case.value.value) cases
        | Connective _ -> []
      in
      write_assignment context run target ~copied (read_choice context frame run choice)
  | Yield { mode; part } ->
      let origin = statement.origin in
      let frame, handed = read_yielded_value context frame run ~origin part in
      let part_type =
        match part with
        | Part operand -> compute_operand_type context frame operand
        | Built { type_; _ } -> Facts.substitute_type context frame type_
      in
      lend_part context frame origin mode ~handed ~lends:(lends_places part)
        ~write_back:(fun frame after -> write_back_part context run part_type part frame after)
  | Jump jump ->
      (match jump with
      | Return returned ->
          context.returns <-
            (frame, Option.map (read_operand context frame run) returned) :: context.returns
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
                  (compute_operand_type context frame value)
                  (read_operand context frame run value)
            | None -> frame
          in
          match task with
          | Branch _ -> (
              match List.assoc_opt task run.cancelled with
              | Some frames -> frames := frame :: !frames
              | None -> Facts.raise_bug "an early exit of a branch that is not around it")
          | Iteration { loop } -> (
              match List.find_opt (fun (exits : loop_exits) -> exits.loop = loop) run.loops with
              | Some exits -> exits.breaks <- frame :: exits.breaks
              | None -> Facts.raise_bug "an early exit of an iteration that is not around it"))
      | Unreachable -> ()
      | Written_unreachable -> oblige_unreachable context frame location
      | Todo -> record_todo context frame statement.origin);
      None
  | Fork { fork; concurrent; branches } ->
      let ended, exits =
        List.fold_left
          (fun (frame, exits) (index, (branch : Mir.block)) ->
            match frame with
            | None -> (None, exits)
            | Some frame ->
                let cancelled = ref [] in
                run.cancelled <- (Mir.Branch { fork; index }, cancelled) :: run.cancelled;
                let ended = read_statements context frame run branch.statements in
                run.cancelled <- List.tl run.cancelled;
                (ended, exits @ List.map (fun exited -> (index, exited)) (List.rev !cancelled)))
          (Some frame, [])
          (List.mapi (fun index branch -> (index, branch)) branches)
      in
      let forget_other_branches (index, (exited : State.frame)) =
        Loops.havoc context exited
          (compute_changes run exited (List.filteri (fun other _ -> other <> index) branches))
      in
      let joined =
        Facts.join_frames context (Option.to_list ended @ List.map forget_other_branches exits)
      in
      if concurrent then Option.map (wait_for_tasks context) joined else joined
  | Resume { winner; exits } ->
      let won =
        read_operand context frame run
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
                  (read_statements context (Facts.restrict frame has_won) run
                     exit.resumed.statements) ))
          (frame, [])
          (List.mapi (fun index exit -> (index + 1, exit)) exits)
      in
      Facts.join_frames context (others :: resumed)
  | While { loop; condition; body; failed; compared } ->
      Loops.run_while_loop context frame
        {
          while_at = loop.origin;
          while_clauses = Loops.keep_holding_clauses context loop.clauses;
          changed = compute_changes run frame (Mir.list_nested_blocks statement);
          bind_parts = (fun frame -> bind_parts context frame run);
          test = (fun head -> read_block context head run condition);
          run_body =
            (fun entered ->
              let exits = { loop = loop.node; breaks = []; ends = [] } in
              run.loops <- exits :: run.loops;
              let ended = read_statements context entered run body.statements in
              run.loops <- List.tl run.loops;
              (List.rev exits.ends @ Option.to_list ended, List.rev exits.breaks));
          on_failure = (fun frame -> read_statements context frame run failed);
          measure_operands =
            Option.map
              (fun ({ statements; comparison; left; right } : Mir.compared) ->
                ( comparison,
                  fun at ->
                    let after =
                      List.fold_left
                        (fun frame statement ->
                          Option.value (read_statement context frame run statement) ~default:frame)
                        at statements
                    in
                    (read_operand context after run left, read_operand context after run right) ))
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
        | Some elements -> fst (read_value context frame run elements.count)
        | None -> frame
      in
      let range : Models.quantified_range =
        match iteration with
        | Range { start; stop; inclusive } ->
            Range_of_integers
              {
                low = read_operand context frame run start;
                high = read_operand context frame run stop;
                inclusive;
                type_ = compute_operand_type context frame start;
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
        translate_quantifier_value context frame run quantifier range ~parameter:part
          ~matches:
            {
              statements = [];
              value = Some (Immediate { value = Boolean true; type_ = Types.bool });
            }
          ~body:{ statements = bindings.statements @ body.statements; value = Some decision }
      in
      Some (write_place context after run { root = Local decides; projections = [] } term)
  | For { loop; iteration; part; elements; bindings = loop_bindings; body } ->
      let frame =
        match elements with
        | Some elements -> fst (read_value context frame run elements.count)
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
                    Validity.run_without_costs context (fun () ->
                        snd (read_value context at run elements.count)))
            | Read | Own -> None)
      in
      let run_body inside element =
        let inside =
          Facts.bind inside (Locals.make_key run.infos part)
            (Facts.substitute_type context inside run.infos.(part).type_)
            element
        in
        let exits = { loop = loop.node; breaks = []; ends = [] } in
        run.loops <- exits :: run.loops;
        let ended =
          read_statements context inside run (loop_bindings.statements @ body.statements)
        in
        run.loops <- List.tl run.loops;
        let breaks =
          match loop.schedule with
          | Concurrent ->
              let changed = compute_changes run inside [ loop_bindings; body ] in
              List.map
                (fun exited ->
                  let forgotten = Loops.havoc context exited changed in
                  Option.iter
                    (fun count_of ->
                      Facts.assume context forgotten
                        (Logic.equal (count_of forgotten) (count_of exited)))
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
            (Facts.substitute_type context frame run.infos.(part).type_)
            element
        in
        List.fold_left
          (fun frame statement ->
            Option.value (read_statement context frame run statement) ~default:frame)
          frame bindings
      in
      let translate_operand = read_operand context frame run in
      let iterated = match iteration with Pull { cursor; _ } -> [ cursor ] | Range _ -> [] in
      let iterable =
        match iteration with
        | Range { start; stop; inclusive } ->
            Loops.Over_range
              { low = translate_operand start; high = translate_operand stop; inclusive }
        | Pull { cursor; next; next_origin } ->
            Over_cursor
              {
                cursor = make_passed_place context run cursor;
                cursor_type = compute_place_type context frame run cursor;
                next = make_invocation next ~lends:None;
                next_origin;
              }
      in
      let for_loop =
        {
          Loops.for_at = loop.origin;
          for_clauses = Loops.keep_holding_clauses context loop.clauses;
          iterable;
          element_type = run.infos.(part).type_;
          lent_element =
            Option.map
              (fun (elements : Mir.elements) ->
                match elements.element with
                | Lent_by_call part -> run.infos.(part).type_
                | Sequence_element { place; _ } -> compute_place_type context frame run place)
              elements;
          invariant_count = count_kept_by_iterations;
          collection =
            Option.map
              (fun (elements : Mir.elements) frame ->
                ( compute_place_type context frame run elements.collection,
                  read_place context
                    { frame with makes_obligations = false }
                    run elements.collection ))
              elements;
          element_call =
            Option.bind elements (fun (elements : Mir.elements) ->
                match (find_lent_mode elements, elements.element) with
                | Mut, _ -> None
                | (Read | Own), Sequence_element { place; _ } ->
                    Some
                      (fun at ->
                        Validity.run_without_costs context (fun () ->
                            read_place context { at with makes_obligations = false } run place))
                | (Read | Own), Lent_by_call lent ->
                    Some
                      (fun at ->
                        let rec lend frame = function
                          | [] -> Facts.raise_bug "a loop over elements that no statement lends"
                          | (statement : Mir.statement) :: rest -> (
                              let frame =
                                Option.value
                                  (read_statement context frame run statement)
                                  ~default:frame
                              in
                              match statement.kind with
                              | Basic (Lend { part; _ }) when part = lent -> frame
                              | _ -> lend frame rest)
                        in
                        Validity.run_without_costs context (fun () ->
                            read_place context (lend at after_bindings) run
                              { root = Local lent; projections = [] })));
          bind_element;
          compute_changed_in =
            (fun frame -> compute_changes ~also:iterated run frame [ loop_bindings; body ]);
          compute_changed_by_body = (fun frame -> compute_changes run frame [ loop_bindings; body ]);
          run_body;
          bind_parts = (fun frame -> bind_parts context frame run);
        }
      in
      let ended = Loops.run_for_loop context frame for_loop in
      if loop.schedule = Concurrent then Option.map (wait_for_tasks context) ended else ended

and wait_for_tasks context frame =
  Operations.spend context frame (fun (counter : Costs.counter) ->
      match counter.resource with
      | Metric Time -> Operations.declare_unknown_amount context frame counter
      | Metric (Allocations | Allocated_bytes) | Calls _ -> Costs.zero)

and read_basic context frame run (statement : Mir.statement) (basic : Mir.basic) =
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
            Locals.add key (Facts.substitute_type context frame run.infos.(local).type_) frame.types;
        }
  | Assign { target; value = Lambda { is_argument = true; _ }; _ } ->
      Some
        (write_place context frame run target
           (Facts.arrive context frame "lambda" (compute_place_type context frame run target)))
  | Assign { target; value } -> (
      let read () =
        read_rvalue context frame run value
          ~site:{ origin = statement.origin; type_ = compute_target_type context frame run target }
      in
      let copied = match value with Operand copied -> [ copied ] | _ -> [] in
      match target with
      | { root = Local held; projections = [] } -> (
          match find_held_callback context run held value with
          | Some core ->
              Hashtbl.replace run.held_callbacks held core;
              write_assignment context run target ~copied
                (Some (Validity.run_reading_callback context read))
          | None -> write_assignment context run target ~copied (Some (read ())))
      | _ -> write_assignment context run target ~copied (Some (read ())))
  | Call { destination; call } -> read_call_statement context frame run ~destination call
  | Live _ | Loan_start _ | Loan_end _ | Echo _ -> Some frame
  | Dead locals ->
      if frame.makes_obligations then
        List.iter
          (fun local ->
            match
              (run.infos.(local), Locals.find_opt (Locals.make_key run.infos local) frame.locals)
            with
            | ( { kind = (Source { is_var = true; _ } | Temporary) as kind; type_; origin; _ },
                Some term )
              when Hashtbl.mem run.changed_in_place local ->
                Lambdas.check_valid context frame
                  (Facts.locate context frame.source origin)
                  (Facts.substitute_type context frame type_)
                  term ~deep:true
                  ~when_:
                    (match kind with
                    | Temporary -> "for the value built here"
                    | _ -> Printf.sprintf "for %s when its scope ends" (describe_local kind))
            | _ -> ())
          locals;
      let frame =
        List.fold_left
          (fun (frame : State.frame) local ->
            match Locals.find_opt (Locals.make_key run.infos local) frame.lends with
            | Some lent ->
                let final =
                  read_place context
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
                          (Facts.merge context ~condition:frame.condition
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
  | Lend { part; call } -> read_lend context frame run part call
  | Assert condition ->
      Assertions.check_assertion context frame ~origin:statement.origin ~bit_vector:None
        (read_operand context frame run condition);
      Some frame
  | Ghost_assert { condition; by_bit_vector } ->
      let frame, term = Validity.read_specification context frame condition in
      let list_named () =
        List.map
          (fun parameter ->
            match condition.locals.(parameter) with
            | { kind = Source { local; _ }; type_; _ } -> (local, type_)
            | { kind = Temporary | Lent _; _ } ->
                Facts.raise_bug "an assertion's formula that takes no local")
          condition.parameters
      in
      Assertions.check_assertion context frame ~origin:condition.origin
        ~bit_vector:
          (if by_bit_vector then
             Some
               ( list_named (),
                 fun isolated -> snd (context.read_formula isolated condition ~arguments:[]) )
           else None)
        term;
      Some frame
  | Proof code ->
      Some (Facts.restrict frame (Logic.not_ (Values.run_ghost_code context frame code)))
  | Evaluated_assert code ->
      let symbol =
        Logic.Symbol.Evaluated
          (Assertion
             {
               definition = frame.source.key.path;
               condition = Core_walk.locate_origin statement.origin;
             })
      in
      Facts.declare context (Logic.Constant (symbol, Logic.Bool));
      let _, holds =
        Validity.run_as_specification context (fun () ->
            Amounts.run_code context frame code ~type_:Types.bool)
      in
      Facts.assume context frame (Logic.equal (Logic.Symbol symbol) holds);
      let location = Facts.locate context frame.source statement.origin in
      Facts.oblige context frame Assertion location
        (match statement.origin with
        | Written _ ->
            [ Text "`"; Facts.quote frame.source statement.origin; Text "` may not hold." ]
        | Desugared _ ->
            let callee =
              List.find_map
                (fun (asserted : Mir.statement) ->
                  match asserted.kind with
                  | Basic (Call { call; _ }) ->
                      (Mir.Call_edges.resolve_callee context.lookups.interface frame.substitution
                         call.callee.target)
                        .target
                  | _ -> None)
                (List.rev code.body.code.statements)
            in
            [
              Text
                (String.capitalize_ascii
                   (Facts.describe_call context location
                      ?callee:(Option.map Facts.show_callee callee)
                      ()));
              Text " may not give `true`.";
            ])
        holds;
      Some frame
  | Path_note note ->
      note_path context frame note;
      Some frame

and read_call_statement context frame run ~destination (call : Mir.call) =
  let result_type =
    match destination with
    | Some destination -> compute_target_type context frame run destination
    | None -> Types.unit
  in
  match read_call context frame run call ~result_type with
  | Some (after, term) -> (
      match destination with
      | Some destination -> Some (write_place context after run destination term)
      | None -> Some after)
  | None -> None

and write_assignment context run (target : Mir.place) ~(copied : Mir.operand list) read =
  let copied =
    match List.sort_uniq compare (List.map find_whole_local copied) with
    | [ Some source ] -> Some source
    | _ -> None
  in
  let* frame, term = read in
  (match target.root with
  | Local local -> (
      match run.infos.(local).kind with
      | Source { local = (Declared { name; _ } | Trait_parameter { name; _ }) as core; _ }
        when Facts.is_home context frame.source ->
          Tables.Local_table.replace context.local_names (Core_local core) name
      | Source { local = Synthetic _ as core; _ } when Facts.is_home context frame.source ->
          Tables.Local_table.replace context.local_origins (Core_local core)
            run.infos.(local).origin
      | Source _ | Temporary | Lent _ -> ())
  | Constant _ | Literal _ -> ());
  ignore copied;
  Some (write_place context frame run target term)

let make_run ~locals ~lambdas =
  {
    infos = locals;
    changed_in_place = Hashtbl.create 4;
    held_callbacks = Hashtbl.create 4;
    lambdas;
    loops = [];
    cancelled = [];
  }

let read_formula context (frame : State.frame) (formula : Mir.formula) ~arguments =
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
            (Facts.substitute_type context inside formula.locals.(parameter).type_)
            argument)
        inside formula.parameters arguments
  in
  Facts.run_in_source context frame.source (fun () ->
      match read_block context inside run formula.value with
      | Some (after, term) -> ({ frame with spent = after.spent }, term)
      | None when Types.equal formula.type_ Types.bool -> (frame, Logic.Boolean true)
      | None -> (frame, Facts.arrive context frame "unfinished" formula.type_))

let read_body context start ~(lambdas : Mir.body array) (body : Mir.body) =
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
        let ty = Facts.substitute_type context frame body.locals.(local).type_ in
        Facts.bind frame (Locals.make_key run.infos local) ty
          (Facts.arrive context frame "returned" ty))
      start (list_returned_locals body.code)
  in
  match read_statements context start run body.code.statements with
  | None -> ()
  | Some _ -> Facts.raise_bug "a body whose end control reaches"
