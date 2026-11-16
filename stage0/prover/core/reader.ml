open Core
open State
open Facts
open Validity
open Operations
open Models
open Lambdas
open Intrinsics
open Amounts
open Calls
open Values
open Loops
open Assertions

let ( let* ) = Option.bind

type loop_exits = { loop : Core.origin; mutable breaks : frame list; mutable ends : frame list }

type run = {
  infos : Mir.local_info array;
  lambdas : Mir.body array;
  in_formula : bool;
  provides : (Core.origin, Mir.provided list) Hashtbl.t;
  mutable loops : loop_exits list;
  mutable cancelled : (Mir.task * frame list ref) list;
}

let unit_callee : _ Core.target -> Invocation.callee = function
  | Function { path; type_arguments } -> Function { path; type_arguments }
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } ->
      Trait_method { trait; name; receiver; self_type; type_arguments; evidence }
  | Capability_method { capability; name } -> Capability_method { capability; name }
  | Intrinsic { operation; type_arguments } -> Intrinsic { operation; type_arguments }
  | Indirect _ -> Indirect ()

let invocation_of (call : Mir.call) ~lends : Invocation.t =
  { callee = unit_callee call.callee; lends; uses = call.uses }

let local_key run local =
  match run.infos.(local).kind with
  | Source { local = core; _ } -> core
  | Temporary | Lent _ -> Core.Synthetic (-1 - local)

let declared_fields context ty variant =
  match visible_type context ty with
  | Some (interface, substitution) -> (
      let fields (list : Types.field list) =
        List.map
          (fun (field : Types.field) ->
            (field.field_name, Types.substitute substitution field.field_type))
          list
      in
      match (interface.shape, variant) with
      | Record list, None -> Some (fields list)
      | Sum variants, Some name -> (
          match
            List.find_opt (fun (variant : Types.variant) -> variant.variant_name = name) variants
          with
          | Some { fields = Some list; _ } -> Some (fields list)
          | Some { fields = None; _ } -> Some []
          | None -> None)
      | _ -> None)
  | None -> None

let rec place_type context frame run (place : Mir.place) =
  match place.Mir.projections with
  | [] -> (
      match place.Mir.root with
      | Local local -> substituted context frame run.infos.(local).type_
      | Constant path -> constant_type context path
      | Literal { type_; _ } -> substituted context frame type_)
  | _ -> (
      let base =
        { place with Mir.projections = List.rev (List.tl (List.rev place.Mir.projections)) }
      in
      let base_type = place_type context frame run base in
      let variant, field =
        match List.nth place.Mir.projections (List.length place.Mir.projections - 1) with
        | Field field -> (None, field)
        | Variant_field { variant; field } -> (Some variant, field)
      in
      match Option.bind (declared_fields context base_type variant) (List.assoc_opt field) with
      | Some field_type -> substituted context frame field_type
      | None -> raise (Foreign_unsupported (Printf.sprintf "the field `%s`" field)))

let rec aliased (frame : frame) run (place : Mir.place) : (Logic.term * Mir.place) list =
  match place.Mir.root with
  | Local local -> (
      match Locals.find_opt (local_key run local) frame.aliases with
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
                (aliased frame run bound_place))
            bound
      | None -> [ (Logic.Boolean true, place) ])
  | Constant _ | Literal _ -> [ (Logic.Boolean true, place) ]

let expanded frame run (place : Mir.place) =
  match aliased frame run place with
  | [ (_, place) ] -> place
  | _ -> raise (Foreign_unsupported "a name that the alternatives of a pattern bind `mut`, here")

let read_root context frame run (root : Mir.root) =
  match root with
  | Constant path -> constant_value context frame path
  | Literal { text; type_ } -> text_value context frame (substituted context frame type_) text
  | Local local -> (
      match local_key run local with
      | Self -> (
          match frame.self with
          | Some self -> self
          | None -> raise (Foreign_unsupported "`self` outside a method"))
      | key -> (
          if frame.makes_obligations && not context.reading_callback then
            escaping_callback context frame key;
          match Locals.find_opt key frame.locals with
          | Some term -> term
          | None
            when run.in_formula
                 &&
                 match run.infos.(local).kind with
                 | Source _ -> false
                 | Temporary | Lent _ -> true ->
              bug "a temporary of a formula of `%s` is read before it is assigned" frame.source.name
          | None -> raise (Foreign_unsupported "a local the prover did not bind")))

let read_resolved context frame run (place : Mir.place) =
  let _, term =
    List.fold_left
      (fun (prefix, term) (projection : Mir.projection) ->
        let base = { place with Mir.projections = prefix } in
        let base_type = place_type context frame run base in
        let variant, field =
          match projection with
          | Field field -> (None, field)
          | Variant_field { variant; field } -> (Some variant, field)
        in
        let projected = { place with Mir.projections = prefix @ [ projection ] } in
        if constructors context base_type = None then
          raise
            (Foreign_unsupported
               (Printf.sprintf "a field of `%s`, whose fields the prover does not see"
                  (Types.show base_type)));
        ignore (sort_of context base_type);
        ( prefix @ [ projection ],
          field_of context frame base_type variant field
            (place_type context frame run projected)
            term ))
      ([], read_root context frame run place.Mir.root)
      place.Mir.projections
  in
  term

let read_place context frame run (place : Mir.place) =
  match aliased frame run place with
  | [ (_, place) ] -> read_resolved context frame run place
  | alternatives -> (
      match List.rev alternatives with
      | (_, first) :: later ->
          List.fold_left
            (fun otherwise (condition, place) ->
              Logic.ite condition (read_resolved context frame run place) otherwise)
            (read_resolved context frame run first)
            later
      | [] -> bug "a place that is no place")

let field_replaced context ty variant field whole new_value =
  match Option.bind (constructors context ty) (List.assoc_opt variant) with
  | Some fields ->
      Logic.Apply
        ( constructor_name ty variant,
          List.map
            (fun (name, _) ->
              if name = field then new_value else selected context ty variant name whole)
            fields )
  | None -> raise (Foreign_unsupported (Printf.sprintf "the fields of `%s`" (Types.show ty)))

let write_resolved context frame run (place : Mir.place) new_value =
  let rec rebuilt prefix whole = function
    | [] -> new_value
    | (projection : Mir.projection) :: rest ->
        let base_type = place_type context frame run { place with Mir.projections = prefix } in
        let variant, field =
          match projection with
          | Field field -> (None, field)
          | Variant_field { variant; field } -> (Some variant, field)
        in
        let field_type =
          place_type context frame run { place with Mir.projections = prefix @ [ projection ] }
        in
        let part = field_of context frame base_type variant field field_type whole in
        field_replaced context base_type variant field whole
          (rebuilt (prefix @ [ projection ]) part rest)
  in
  match place.Mir.root with
  | Constant _ | Literal _ -> raise (Foreign_unsupported "assigning to a constant")
  | Local local -> (
      let whole =
        if place.Mir.projections = [] then new_value
        else rebuilt [] (read_root context frame run place.Mir.root) place.Mir.projections
      in
      match local_key run local with
      | Self -> { frame with self = Some whole }
      | key -> bind frame key (substituted context frame run.infos.(local).type_) whole)

let write_place context frame run (place : Mir.place) new_value =
  match aliased frame run place with
  | [ (_, place) ] -> write_resolved context frame run place new_value
  | alternatives ->
      List.fold_left
        (fun frame (condition, (place : Mir.place)) ->
          let written = write_resolved context frame run place new_value in
          match place.Mir.root with
          | Constant _ | Literal _ -> written
          | Local local -> (
              match local_key run local with
              | Self -> (
                  match (written.self, frame.self) with
                  | Some after, Some before ->
                      { frame with self = Some (Logic.ite condition after before) }
                  | _ -> written)
              | key -> (
                  match (Locals.find_opt key written.locals, Locals.find_opt key frame.locals) with
                  | Some after, Some before ->
                      bind frame key
                        (substituted context frame run.infos.(local).type_)
                        (Logic.ite condition after before)
                  | _ -> written)))
        frame alternatives

let changes ?(also = []) run frame (blocks : Mir.block list) : changed =
  let locals = ref [] and self = ref false and reassigned = ref [] in
  let note (place : Mir.place) =
    List.iter
      (fun (_, (place : Mir.place)) ->
        match place.Mir.root with
        | Local local -> (
            match local_key run local with
            | Self -> self := true
            | key -> if Locals.mem key frame.locals then locals := key :: !locals)
        | Constant _ | Literal _ -> ())
      (aliased frame run place)
  in
  let assigned (place : Mir.place) =
    (match place with
    | { root = Local local; projections = [] } -> (
        match local_key run local with
        | Self -> ()
        | key -> if Locals.mem key frame.locals then reassigned := key :: !reassigned)
    | _ -> ());
    note place
  in
  let passed (call : Mir.call) =
    List.iter
      (function
        | Mir.Passed { mode = Types.Mut; value = Borrow { place; _ } | Use { place; _ }; _ } ->
            note place
        | Passed _ | Default -> ())
      call.arguments
  in
  let rec lent : Mir.yielded -> unit = function
    | Part (Borrow { place; _ }) -> note place
    | Part _ -> ()
    | Built { fields; _ } -> List.iter (fun (_, field) -> Option.iter lent field) fields
  in
  let rec visit (block : Mir.block) =
    List.iter
      (fun (statement : Mir.statement) ->
        (match statement.kind with
        | Basic (Assign { target; value = Operand (Borrow { place; mode = Types.Mut; _ }); _ }) ->
            note target;
            note place
        | Basic (Assign { target; _ }) | Choose { target; _ } -> assigned target
        | Basic (Call { destination; call }) ->
            Option.iter assigned destination;
            passed call
        | Basic (Lend { call; _ }) -> passed call
        | Basic (Slice { destination; call; _ } | Template { destination; call; _ }) ->
            assigned destination;
            passed call
        | For { iteration = Pull { cursor; _ }; _ } -> note cursor
        | Yield { mode = Types.Mut; part } -> lent part
        | Jump (Cancel { winner; returned; _ }) ->
            note { root = Local winner; projections = [] };
            Option.iter (fun (_, local) -> note { root = Local local; projections = [] }) returned
        | _ -> ());
        List.iter visit (Mir.nested_blocks statement))
      block.statements
  in
  List.iter visit blocks;
  List.iter note also;
  {
    changed_locals = List.sort_uniq compare !locals;
    changes_self = !self && frame.self <> None;
    reassigned = List.sort_uniq compare !reassigned;
  }

let float_literal (exponent, significand) value =
  let bits =
    if exponent = 8 then Z.extract (Z.of_int32 (Int32.bits_of_float value)) 0 32
    else Z.extract (Z.of_int64 (Int64.bits_of_float value)) 0 64
  in
  let fraction = significand - 1 in
  Logic.Operation
    ( "fp",
      [
        Logic.Bits (1, Z.extract bits (exponent + fraction) 1);
        Logic.Bits (exponent, Z.extract bits fraction exponent);
        Logic.Bits (fraction, Z.extract bits 0 fraction);
      ] )

let read_operand context frame run (operand : Mir.operand) =
  match operand with
  | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> read_place context frame run place
  | Constant { value; type_ } -> (
      let ty = substituted context frame type_ in
      match value with
      | Unit ->
          ignore (sort_of context Types.unit);
          Logic.Apply (Symbol.Unit, [])
      | Integer number -> Logic.Integer number
      | Float number -> (
          match float_format ty with
          | Some format -> float_literal format number
          | None -> raise (Foreign_unsupported "a float literal without a float type"))
      | Boolean truth -> Logic.Boolean truth)

let operand_type context frame operand = substituted context frame (Mir.operand_type operand)

let operand_origin : Mir.operand -> Core.origin option = function
  | Use { origin; _ } | Borrow { origin; _ } | Take { origin; _ } -> Some origin
  | Constant _ -> None

let whole_local : Mir.operand -> Mir.local option = function
  | Use { place = { root = Local local; projections = [] }; _ }
  | Borrow { place = { root = Local local; projections = [] }; _ } ->
      Some local
  | Use _ | Borrow _ | Take _ | Constant _ -> None

let passed_place_of context run place =
  {
    read = (fun frame -> read_place context { frame with makes_obligations = false } run place);
    write = (fun frame term -> write_place context frame run place term);
  }

let shape_of run ?function_ (value : Mir.operand) : Invocation.shape =
  match (function_, whole_local value) with
  | Some (Mir.Function_reference { path; node; origin }), _ ->
      Named_function { id = node; origin; path }
  | (Some (Lambda_expression _) | None), Some local -> (
      match run.infos.(local).kind with
      | Source { local = core; _ } -> Forwarded core
      | Temporary | Lent _ -> Other)
  | (Some (Lambda_expression _) | None), None -> Other

let one_place context (places : (Logic.term * passed_place) list) : passed_place =
  match List.rev places with
  | [] -> bug "a place that is none"
  | [ (_, place) ] -> place
  | (_, last) :: before ->
      {
        read =
          (fun frame ->
            List.fold_left
              (fun otherwise ((condition, place) : Logic.term * passed_place) ->
                Logic.ite condition (place.read frame) otherwise)
              (last.read frame) before);
        write =
          (fun frame term ->
            Option.value ~default:frame
              (join_frames context
                 (List.map
                    (fun ((condition, place) : Logic.term * passed_place) ->
                      place.write (restrict frame condition) term)
                    places)));
      }

let argument_place context (frame : frame) run (mode : Types.mode) (value : Mir.operand) =
  let held =
    Option.bind (whole_local value) (fun local ->
        Locals.find_opt (local_key run local) frame.slices)
  in
  match (mode, held) with
  | Types.Mut, Some (Slices slices) ->
      Some
        (one_place context
           (List.map
              (fun (condition, (slice : slice)) ->
                ( condition,
                  slice_place context slice.made_at
                    ~owner:(passed_place_of context run slice.collection)
                    ~owner_type:(fun frame -> place_type context frame run slice.collection)
                    ~low:slice.start ~high:slice.stop ))
              slices))
  | Types.Mut, Some Unknown_slice when Types.is_well_known Slice (Mir.operand_type value) ->
      unsupported
        (span_of frame.source (Option.value (operand_origin value) ~default:0))
        "a slice passed `mut` whose collection the prover does not know: a loop assigns the slice, \
         a call returns it, or it is a copy of a parameter"
  | Types.Mut, (Some Unknown_slice | None) -> (
      match value with Borrow { place; _ } -> Some (passed_place_of context run place) | _ -> None)
  | _ -> None

let call_values context frame run (invocation : Invocation.t) (arguments : Mir.argument list) =
  passed_values context frame invocation
    (List.concat
       (List.mapi
          (fun position (argument : Mir.argument) ->
            match argument with
            | Passed { mode; value; function_; _ } -> (
                match function_ with
                | Some (Lambda_expression { body; node; origin; type_ }) ->
                    [
                      Lambda_argument
                        {
                          position;
                          mode;
                          site = { id = node; origin; type_ };
                          lambda = { code = run.lambdas.(body); lambdas = run.lambdas };
                        };
                    ]
                | Some (Function_reference _) | None ->
                    [
                      Value_argument
                        {
                          position;
                          mode;
                          shape = shape_of run ?function_ value;
                          origin = operand_origin value;
                          passed_place = argument_place context frame run mode value;
                          type_ = operand_type context frame value;
                          term =
                            reading_callback context (fun () ->
                                read_operand context frame run value);
                        };
                    ])
            | Default -> [])
          arguments))

let read_call context frame run (call : Mir.call) ~result_type =
  let invocation = invocation_of call ~lends:None in
  match (invocation.callee, call.arguments) with
  | ( Trait_method { trait; name = "equal"; _ },
      [
        Passed { value = tested; _ };
        Passed { value = Borrow { place = { root = Literal { text; _ }; projections = [] }; _ }; _ };
      ] )
    when Path.equal trait.trait equal_trait ->
      let ty = operand_type context frame tested in
      Some
        ( frame,
          text_matches context
            (span_of frame.source call.origin)
            ty
            (read_operand context frame run tested)
            text )
  | _ ->
      let through =
        match call.callee with
        | Indirect callee ->
            Some
              ( operand_type context frame callee,
                reading_callback context (fun () -> read_operand context frame run callee),
                shape_of run callee )
        | _ -> None
      in
      let values = call_values context frame run invocation call.arguments in
      apply_call context frame
        { id = call.node; origin = call.origin; type_ = result_type }
        invocation ~through values

let read_lend context frame run part (call : Mir.call) =
  let mode = match run.infos.(part).kind with Lent mode -> mode | _ -> Types.Read in
  let invocation = invocation_of call ~lends:(Some mode) in
  let site : Invocation.site =
    { id = call.node; origin = call.origin; type_ = run.infos.(part).type_ }
  in
  let span = span_of frame.source call.origin in
  let values = call_values context frame run invocation call.arguments in
  let lend ?lent_final frame =
    apply_call ?lent_final context frame site invocation ~through:None values
  in
  let receiver =
    match call.arguments with
    | Passed { value = Borrow { place; _ }; _ } :: _ -> Some place
    | _ -> None
  in
  let index_term () =
    match List.find_opt (fun (passed : passed) -> passed.position = 1) values with
    | Some passed -> passed.term
    | None -> bug "a lend at an index with no index"
  in
  let lent, write_back =
    match (invocation.lends, invocation.callee, receiver) with
    | ( Some Types.Mut,
        Intrinsic
          { operation = (Storage_at_mut | Array_at_mut | View_at_mut) as operation; type_arguments },
        Some receiver ) ->
        let index = index_term () in
        ( lend frame,
          Some
            (fun frame final ->
              element_written_back context frame ~operation ~type_arguments
                ~receiver:(passed_place_of context run receiver)
                ~receiver_type:(place_type context frame run receiver)
                index final) )
    | Some Types.Mut, Intrinsic _, _ -> unsupported span "this lend"
    | Some Types.Mut, _, _ ->
        ( without_costs context (fun () -> lend frame),
          Some
            (fun frame final ->
              match lend ~lent_final:(fun _ -> final) frame with
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
            lends = Locals.add (local_key run part) [ (Logic.Boolean true, write_back) ] lent.lends;
          }
      | None -> lent)
    lent

let target_type context frame run (target : Mir.place) =
  match target with
  | { root = Local local; projections = [] } -> run.infos.(local).type_
  | _ -> place_type context frame run target

let lends_places (part : Mir.yielded) =
  match part with Built _ | Part (Borrow _) -> true | Part (Use _ | Take _ | Constant _) -> false

let rec yielded_value context frame run ~origin (part : Mir.yielded) =
  match part with
  | Part operand -> (frame, read_operand context frame run operand)
  | Built { variant; fields; node; type_ } ->
      let frame, values =
        List.fold_left
          (fun (frame, values) (name, field) ->
            match field with
            | Some field ->
                let frame, term = yielded_value context frame run ~origin field in
                (frame, values @ [ (name, Some term) ])
            | None -> (frame, values @ [ (name, None) ]))
          (frame, []) fields
      in
      apply_construct context frame { id = node; origin; type_ } variant values

let rec written_back context run ty (part : Mir.yielded) frame after =
  match part with
  | Part (Borrow { place; _ }) -> write_place context frame run place after
  | Built { variant; fields; _ } -> (
      match constructors context ty with
      | Some shape ->
          let shaped = Option.value (List.assoc_opt variant shape) ~default:[] in
          List.fold_left
            (fun frame (name, field) ->
              match (field, List.assoc_opt name shaped) with
              | Some field, Some field_type when lends_places field ->
                  let field_type = substituted context frame field_type in
                  let selected = field_of context frame ty variant name field_type after in
                  let value =
                    match variant with
                    | None -> selected
                    | Some _ ->
                        Logic.ite
                          (Logic.Is (constructor_name ty variant, after))
                          selected
                          (arrive context frame "lent" field_type)
                  in
                  written_back context run field_type field frame value
              | _ -> frame)
            frame fields
      | None -> raise (Foreign_unsupported (Printf.sprintf "the fields of `%s`" (Types.show ty))))
  | Part (Use _ | Take _ | Constant _) -> frame

let bind_parts context (frame : frame) run =
  Locals.fold
    (fun key parts frame ->
      match (key, Locals.find_opt key frame.types, List.rev parts) with
      | Core.Synthetic number, _, _ when number < 0 -> frame
      | _, Some ty, (_, first) :: later -> (
          let read = read_place context { frame with makes_obligations = false } run in
          try
            bind frame key ty
              (List.fold_left
                 (fun otherwise (condition, part) -> Logic.ite condition (read part) otherwise)
                 (read first) later)
          with Unsupported _ | Foreign_unsupported _ -> frame)
      | _ -> frame)
    frame.aliases frame

let note_decision context frame origin test =
  if frame.makes_obligations && frame.source.key = Some context.home then begin
    let text = text_of frame.source origin in
    context.decisions <-
      ( Printf.sprintf "`%s` is true" text,
        Some (Printf.sprintf "`%s` is false" text),
        frame.condition,
        test )
      :: context.decisions
  end

let refreshed context frame ty (place : passed_place) =
  let fresh_value = arrive context frame "changed" ty in
  let frame = place.write frame fresh_value in
  assume_valid context frame ty fresh_value;
  frame

let todo_reached context frame span =
  if context.proving then begin
    context.holes <- (context.home, span) :: context.holes;
    context.unfinished <- frame.condition :: context.unfinished
  end

let unreachable_reached context frame span =
  oblige context frame Unreachable span
    [ Text "This `unreachable` may be reached." ]
    (Logic.Boolean false)

let lend_part context frame origin (mode : Types.mode) ~handed ~lends ~write_back =
  let span = span_of frame.source origin in
  match (context.yielded_part, context.yield_ensures, frame.yielded_so_far) with
  | Some part_type, Some (each, _), Some before ->
      List.iter
        (fun (clause : Mir.formula) ->
          let _, term =
            specification_value context
              { frame with result = Some handed; yielded = Some before }
              clause
          in
          oblige context frame Ensures
            (span_of frame.source clause.origin)
            [
              Text "`";
              quote frame.source clause.origin;
              Text "` may not hold for the part lent here.";
            ]
            term)
        each;
      check_valid context frame span part_type handed ~deep:true ~when_:"for the part lent here";
      let frame, part_after =
        if mode = Types.Mut && lends then (
          let part_after = arrive context frame "lent" part_type in
          context.lent_back <- (part_type, handed, part_after) :: context.lent_back;
          (write_back frame part_after, part_after))
        else (frame, handed)
      in
      Some { frame with yielded_so_far = Some (appended context frame part_type before part_after) }
  | _ -> unsupported span "a lent part outside a lending method's body"

let rec read_rvalue context frame run (value : Mir.rvalue) ~(site : Invocation.site) =
  let span = span_of frame.source site.origin in
  let ty = substituted context frame site.type_ in
  let operand = read_operand context frame run in
  match value with
  | Operand value -> (frame, operand value)
  | Compare { comparison = compared; left; right } ->
      ( frame,
        compared_terms (operand_type context frame left) compared (operand left) (operand right) )
  | Not inner -> (frame, Logic.not_ (operand inner))
  | Is_variant { place; variant } ->
      let ty = place_type context frame run place in
      ignore (sort_of context ty);
      if constructors context ty = None then
        unsupported span "a variant of `%s`, which the prover does not see" (Types.show ty);
      (frame, Logic.Is (constructor_name ty (Some variant), read_place context frame run place))
  | Copy copied_operand ->
      let ty = operand_type context frame copied_operand in
      let term = operand copied_operand in
      let literal =
        match copied_operand with
        | Borrow { place = { root = Literal { text; _ }; projections = [] }; _ } -> Some text
        | _ -> None
      in
      (copied ?literal context frame ty term, term)
  | Convert { conversion = Widen; value; converts_function_expression } ->
      check_widened span ~is_written:converts_function_expression
        (operand_type context frame value)
        ty;
      (frame, operand value)
  | Value_parameter parameter -> (frame, value_term context frame (Value_parameter parameter))
  | Convert { conversion = To_integer; value; _ } -> (frame, operand value)
  | Convert { conversion = From_integer; value; _ } ->
      (frame, from_integer context frame site (operand value))
  | Function_value { path; type_arguments; is_argument } ->
      (frame, global_value context frame site path type_arguments ~is_argument)
  | To_any _ -> to_any context frame site
  | Operation { operation; operands; type_arguments } ->
      let types =
        List.filter_map
          (function Types.Type ty -> Some (substituted context frame ty) | _ -> None)
          type_arguments
      in
      let types = match types with [] -> [ ty ] | types -> types in
      let terms = List.map operand operands in
      ( frame,
        intrinsic context frame ~site operation types terms
          ~arguments:(List.map operand_origin operands)
          ~changed:terms ty )
  | Construct { variant; fields } ->
      apply_construct context frame site variant
        (List.map (fun (name, field) -> (name, Option.map operand field)) fields)
  | Array elements -> apply_list_literal context frame site (List.map operand elements)
  | Lambda { body; _ } ->
      lambda context frame ~site
        { code = run.lambdas.(body); lambdas = run.lambdas }
        ~facts:(fun _ -> [])
  | Specification Result -> (
      match frame.result with
      | Some result -> (frame, result)
      | None -> unsupported span "`result` here")
  | Specification (Entry local) -> (
      match local_key run local with
      | Self -> (
          match frame.old_self with
          | Some self -> (frame, self)
          | None -> raise (Foreign_unsupported "`self` outside a method"))
      | key -> (
          match Locals.find_opt key frame.old_locals with
          | Some term -> (frame, term)
          | None -> raise (Foreign_unsupported "a local the prover did not bind")))
  | Specification Yielded -> (
      match (frame.yielded, frame.yielded_so_far) with
      | Some yielded, _ -> (frame, yielded)
      | None, Some yielded_so_far when frame.source.key = Some context.home ->
          (frame, yielded_so_far)
      | _ -> unsupported span "`yielded` here")
  | Specification (Identical (first, second)) ->
      let first_value = operand first and second_value = operand second in
      extensional context frame (operand_type context frame first) first_value second_value;
      (frame, Logic.equal first_value second_value)
  | Specification (Applied { function_; arguments; unconverted }) ->
      let values = reading_callback context (fun () -> List.map operand arguments) in
      apply_specification_function context frame ~span function_ values
        ~unconverted:(List.map (substituted context frame) unconverted)
        ~types:(List.map (operand_type context frame) arguments)
  | Specification (Method_time callee) -> (frame, method_time context frame (unit_callee callee))
  | Specification (Map entries) ->
      apply_map_literal context frame ~ty ~span
        (List.map (fun (key, entry) -> (operand_origin key, operand key, operand entry)) entries)
  | Specification (Quantified { quantifier; range; parameter; matches; body }) ->
      let range =
        match range with
        | Over_type ty -> Range_of_type (substituted context frame ty)
        | Over_range { start; stop; inclusive } ->
            Range_of_integers
              {
                low = operand start;
                high = operand stop;
                inclusive;
                type_ = operand_type context frame start;
              }
        | Over_collection collection ->
            Range_of_collection
              {
                collection_type = operand_type context frame collection;
                collected = operand collection;
                element = substituted context frame run.infos.(parameter).type_;
                span;
              }
      in
      quantifier_value context frame run ~span quantifier range ~parameter ~matches ~body

and quantifier_value context frame run ~span quantifier range ~parameter ~(matches : Mir.block)
    ~(body : Mir.block) =
  match
    quantified_over context frame quantifier range
      ~bind:(fun inner value ty ->
        let after, matched =
          read_value context (bind inner (local_key run parameter) ty value) run matches
        in
        (matched, after))
      ~read:(fun body_frame _ ->
        let after, term = read_value context body_frame run body in
        ({ body_frame with spent = after.spent }, term))
  with
  | Some quantified -> quantified
  | None -> unsupported span "a quantifier that gives no value"

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
      | None -> bug "a block with no value, whose end control reaches")
    (read_statements context frame run block.statements)

and read_value context frame run (block : Mir.block) =
  match read_block context frame run block with
  | Some read -> read
  | None -> raise (Foreign_unsupported "a call in a specification that never returns")

and after_either context ~(outer : frame) ~condition ((entered : frame), (after : frame))
    ((entered_otherwise : frame), (after_otherwise : frame)) =
  fst
    (merge context
       ~condition:
         (if
            after.condition == entered.condition
            && after_otherwise.condition == entered_otherwise.condition
          then outer.condition
          else
            path_condition context outer (Logic.( ||| ) after.condition after_otherwise.condition))
       [ (condition, after, None); (Logic.not_ condition, after_otherwise, None) ])

and either context ~outer ~condition (entered, read) (entered_otherwise, otherwise) =
  match (read, otherwise) with
  | None, None -> None
  | Some after, None | None, Some after -> Some after
  | Some (after, value), Some (after_otherwise, value_otherwise) ->
      Some
        ( after_either context ~outer ~condition (entered, after)
            (entered_otherwise, after_otherwise),
          Logic.ite condition value value_otherwise )

and chosen_value context frame run (choice : Mir.choice) =
  match choice with
  | Conditional { condition; then_; else_; if_condition } ->
      let test = read_operand context frame run condition in
      (match if_condition with
      | Some origin -> note_decision context frame origin test
      | None -> ());
      let entered_then = restrict frame test and entered_else = restrict frame (Logic.not_ test) in
      either context ~outer:frame ~condition:test
        (entered_then, read_block context entered_then run then_)
        (entered_else, read_block context entered_else run else_)
  | Cases cases ->
      let rec first_taken (current : frame) = function
        | [] -> bug "a `match` with no case"
        | (case : Mir.case) :: later ->
            let bound, matches = read_value context current run case.tests in
            let entered, is_taken, after_tests =
              match case.guard with
              | Some guard ->
                  let guarded = restrict bound matches
                  and unmatched = restrict bound (Logic.not_ matches) in
                  let after, holds = read_value context guarded run guard in
                  ( restrict after holds,
                    Logic.( &&& ) matches holds,
                    after_either context ~outer:current ~condition:matches (guarded, after)
                      (unmatched, unmatched) )
              | None ->
                  (restrict bound matches, matches, { bound with condition = current.condition })
            in
            let read = read_block context entered run case.value in
            if later = [] then
              Option.map
                (fun ((after : frame), value) ->
                  ( (if after.condition == entered.condition then
                       { after with condition = current.condition }
                     else after),
                    value ))
                read
            else
              let not_taken = restrict after_tests (Logic.not_ is_taken) in
              either context ~outer:current ~condition:is_taken (entered, read)
                (not_taken, first_taken not_taken later)
      in
      first_taken frame cases
  | Connective { connective; left; right } -> (
      let left = read_operand context frame run left in
      let reads_right = match connective with And | Implies -> left | Or -> Logic.not_ left in
      let entered = restrict frame reads_right in
      match read_block context entered run right with
      | Some (after, right) ->
          let skipped = restrict frame (Logic.not_ reads_right) in
          Some
            ( after_either context ~outer:frame ~condition:reads_right (entered, after)
                (skipped, skipped),
              match connective with
              | And -> Logic.( &&& ) left right
              | Or -> Logic.( ||| ) left right
              | Implies -> Logic.( ==> ) left right )
      | None -> Some (restrict frame (Logic.not_ reads_right), Logic.Boolean (connective <> And)))

and read_statement context frame run (statement : Mir.statement) =
  let span = span_of frame.source statement.origin in
  match statement.kind with
  | Basic basic -> read_basic context frame run statement ~span basic
  | Assert_by_bit_vector { condition; names; code } ->
      let named =
        List.map
          (fun local ->
            match run.infos.(local) with
            | { kind = Source { local; _ }; type_; _ } -> (local, type_)
            | { kind = Temporary | Lent _; _ } -> bug "an assertion that names a temporary")
          names
      in
      let frame, term = read_value context frame run code in
      assertion context frame
        ~origin:(Option.value (operand_origin condition) ~default:statement.origin)
        ~bit_vector:(Some (named, fun isolated -> snd (read_value context isolated run code)))
        term;
      Some frame
  | Choose { target; choice } ->
      let copied =
        match choice with
        | Conditional { then_; else_; _ } -> List.filter_map Fun.id [ then_.value; else_.value ]
        | Cases cases -> List.filter_map (fun (case : Mir.case) -> case.value.value) cases
        | Connective _ -> []
      in
      write_assignment context run target ~copied (chosen_value context frame run choice)
  | Yield { mode; part } ->
      let origin = statement.origin in
      let frame, handed = yielded_value context frame run ~origin part in
      let part_type =
        match part with
        | Part operand -> operand_type context frame operand
        | Built { type_; _ } -> substituted context frame type_
      in
      lend_part context frame origin mode ~handed ~lends:(lends_places part)
        ~write_back:(fun frame after -> written_back context run part_type part frame after)
  | Jump jump ->
      (match jump with
      | Return returned ->
          context.returns <-
            (frame, Option.map (read_operand context frame run) returned) :: context.returns
      | Break -> (
          match run.loops with
          | exits :: _ -> exits.breaks <- frame :: exits.breaks
          | [] -> bug "a `break` outside a loop")
      | Continue -> (
          match run.loops with
          | exits :: _ -> exits.ends <- frame :: exits.ends
          | [] -> bug "a `continue` outside a loop")
      | Cancel { task; winner; number; returned } -> (
          let frame =
            bind frame (local_key run winner) (Types.make_builtin UInt32)
              (Logic.Integer (Z.of_int number))
          in
          let frame =
            match returned with
            | Some (value, local) ->
                bind frame (local_key run local)
                  (operand_type context frame value)
                  (read_operand context frame run value)
            | None -> frame
          in
          match task with
          | Branch _ -> (
              match List.assoc_opt task run.cancelled with
              | Some frames -> frames := frame :: !frames
              | None -> bug "an early exit of a branch that is not around it")
          | Iteration { loop } -> (
              match List.find_opt (fun (exits : loop_exits) -> exits.loop = loop) run.loops with
              | Some exits -> exits.ends <- frame :: exits.ends
              | None -> bug "an early exit of an iteration that is not around it"))
      | Unreachable -> ()
      | Written_unreachable -> unreachable_reached context frame span
      | Todo -> todo_reached context frame span);
      None
  | Fork { fork; branches; _ } ->
      List.fold_left
        (fun frame (index, (branch : Mir.block)) ->
          let* frame = frame in
          let cancelled = ref [] in
          run.cancelled <- (Mir.Branch { block = fork; index }, cancelled) :: run.cancelled;
          let ended = read_statements context frame run branch.statements in
          run.cancelled <- List.tl run.cancelled;
          join_frames context (Option.to_list ended @ List.rev !cancelled))
        (Some frame)
        (List.mapi (fun index branch -> (index, branch)) branches)
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
            ( restrict frame (Logic.not_ has_won),
              resumed
              @ Option.to_list
                  (read_statements context (restrict frame has_won) run exit.resumed.statements) ))
          (frame, [])
          (List.mapi (fun index exit -> (index + 1, exit)) exits)
      in
      join_frames context (others :: resumed)
  | While { loop; condition; body; failed; compared } ->
      while_ context frame
        {
          while_at = loop.origin;
          while_clauses = loop.clauses;
          changed = changes run frame (Mir.nested_blocks statement);
          bind_parts = (fun frame -> bind_parts context frame run);
          test = (fun head -> read_block context head run condition);
          run_body =
            (fun entered ->
              let exits = { loop = loop.origin; breaks = []; ends = [] } in
              run.loops <- exits :: run.loops;
              let ended = read_statements context entered run body.statements in
              run.loops <- List.tl run.loops;
              (List.rev exits.ends @ Option.to_list ended, List.rev exits.breaks));
          on_failure = (fun frame -> read_statements context frame run failed);
          measure_operands =
            Option.map
              (fun ({ comparison; left; right } : Mir.compared) ->
                ( comparison,
                  fun at ->
                    let after =
                      List.fold_left
                        (fun frame statement ->
                          Option.value (read_statement context frame run statement) ~default:frame)
                        at condition.statements
                    in
                    (read_operand context after run left, read_operand context after run right) ))
              compared;
        }
  | For
      {
        loop =
          { quantified = Some { quantifier; binding_count = bound; decision; holds; decides }; _ };
        iteration;
        part;
        lent;
        binding_count = positioned;
        body;
      } ->
      let from start stop =
        List.filteri (fun index _ -> index >= start && index < stop) body.statements
      in
      let range, parameter, binding =
        match (lent, iteration) with
        | Some { element; collection; _ }, _ ->
            ( Range_of_collection
                {
                  collection_type = place_type context frame run collection;
                  collected = read_place context frame run collection;
                  element = substituted context frame run.infos.(element).type_;
                  span;
                },
              element,
              List.filter
                (fun (statement : Mir.statement) ->
                  match statement.kind with Basic (Lend _) -> false | _ -> true)
                (from positioned bound) )
        | None, Range { start; stop; inclusive } ->
            ( Range_of_integers
                {
                  low = read_operand context frame run start;
                  high = read_operand context frame run stop;
                  inclusive;
                  type_ = operand_type context frame start;
                },
              part,
              from 0 bound )
        | None, Pull _ -> unsupported span "a quantifier over the values of a cursor"
      in
      let after, term =
        quantifier_value context frame run ~span quantifier range ~parameter
          ~matches:
            {
              statements = binding;
              value = Some (Constant { value = Boolean true; type_ = Types.bool });
            }
          ~body:{ statements = from bound decision; value = Some holds }
      in
      Some (write_place context after run { root = Local decides; projections = [] } term)
  | For { loop; iteration; part; lent; binding_count; body } ->
      let frame =
        match lent with Some lent -> fst (read_value context frame run lent.count) | None -> frame
      in
      let run_body inside element =
        let inside =
          bind inside (local_key run part)
            (substituted context inside run.infos.(part).type_)
            element
        in
        let exits = { loop = loop.origin; breaks = []; ends = [] } in
        run.loops <- exits :: run.loops;
        let ended = read_statements context inside run body.statements in
        run.loops <- List.tl run.loops;
        (List.rev exits.ends @ Option.to_list ended, List.rev exits.breaks)
      in
      let bindings = List.filteri (fun index _ -> index < binding_count) body.statements
      and after_bindings = List.filteri (fun index _ -> index >= binding_count) body.statements in
      let bind_element frame element =
        let frame =
          bind frame (local_key run part) (substituted context frame run.infos.(part).type_) element
        in
        List.fold_left
          (fun frame statement ->
            Option.value (read_statement context frame run statement) ~default:frame)
          frame bindings
      in
      let operand = read_operand context frame run in
      let iterated = match iteration with Pull { cursor; _ } -> [ cursor ] | Range _ -> [] in
      let iterable =
        match iteration with
        | Range { start; stop; inclusive } ->
            Over_range { low = operand start; high = operand stop; inclusive }
        | Pull { cursor; next } ->
            Over_cursor
              {
                cursor = passed_place_of context run cursor;
                cursor_type = place_type context frame run cursor;
                next = unit_callee next;
              }
      in
      let for_loop =
        {
          for_at = loop.origin;
          for_clauses = loop.clauses;
          iterable;
          element_type = run.infos.(part).type_;
          lent_element =
            Option.map (fun (lent : Mir.lent_element) -> run.infos.(lent.element).type_) lent;
          invariant_count =
            Option.bind lent (fun (lent : Mir.lent_element) ->
                match run.infos.(lent.element).kind with
                | Lent Mut ->
                    Some
                      (fun at ->
                        without_costs context (fun () -> snd (read_value context at run lent.count)))
                | _ -> None);
          collection =
            Option.map
              (fun (lent : Mir.lent_element) frame ->
                ( place_type context frame run lent.collection,
                  read_place context { frame with makes_obligations = false } run lent.collection ))
              lent;
          element_call =
            Option.bind lent (fun (lent : Mir.lent_element) ->
                match run.infos.(lent.element).kind with
                | Lent Mut -> None
                | _ ->
                    Some
                      (fun at ->
                        let rec lend frame = function
                          | [] -> bug "a loop over elements that no statement lends"
                          | (statement : Mir.statement) :: rest -> (
                              let frame =
                                Option.value
                                  (read_statement context frame run statement)
                                  ~default:frame
                              in
                              match statement.kind with
                              | Basic (Lend { part; _ }) when part = lent.element -> frame
                              | _ -> lend frame rest)
                        in
                        without_costs context (fun () ->
                            read_place context (lend at after_bindings) run
                              { root = Local lent.element; projections = [] })));
          bind_element;
          changed_in = (fun frame -> changes ~also:iterated run frame [ body ]);
          changed_by_body = (fun frame -> changes run frame [ body ]);
          run_body;
          bind_parts = (fun frame -> bind_parts context frame run);
        }
      in
      for_ context frame for_loop

and read_basic context frame run (statement : Mir.statement) ~span (basic : Mir.basic) =
  match basic with
  | Assign
      {
        target = { root = Local local; projections = [] };
        value = Operand (Borrow { place; mode = Mut; _ });
        _;
      } ->
      let key = local_key run local in
      Some
        {
          frame with
          aliases = Locals.add key [ (Logic.Boolean true, place) ] frame.aliases;
          types = Locals.add key (substituted context frame run.infos.(local).type_) frame.types;
        }
  | Assign { target; value = Lambda { is_argument = true; _ }; _ } ->
      Some
        (write_place context frame run target
           (arrive context frame "lambda" (place_type context frame run target)))
  | Assign { target; value; node } ->
      write_assignment context run target
        ~copied:(match value with Operand copied -> [ copied ] | _ -> [])
        (Some
           (read_rvalue context frame run value
              ~site:
                {
                  id = Option.value node ~default:(-1);
                  origin = statement.origin;
                  type_ = target_type context frame run target;
                }))
  | Call { destination; call } -> (
      let result_type =
        match destination with
        | Some destination -> target_type context frame run destination
        | None -> Types.unit
      in
      match read_call context frame run call ~result_type with
      | Some (after, term) -> (
          match destination with
          | Some ({ root = Local local; projections = [] } as destination)
            when Types.is_well_known Slice run.infos.(local).type_ ->
              let written = write_place context after run destination term in
              Some
                {
                  written with
                  slices = Locals.add (local_key run local) Unknown_slice written.slices;
                }
          | Some destination -> Some (write_place context after run destination term)
          | None -> Some after)
      | None -> None)
  | Live _ | Loan_start _ | Loan_end _ | Echo _ -> Some frame
  | Dead locals ->
      let frame =
        List.fold_left
          (fun (frame : frame) local ->
            match Locals.find_opt (local_key run local) frame.lends with
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
                        let lent = restrict frame lent_on
                        and not_lent = restrict frame (Logic.not_ lent_on) in
                        fst
                          (merge context ~condition:frame.condition
                             [
                               (lent_on, write_back lent final, None);
                               (Logic.not_ lent_on, not_lent, None);
                             ]))
                  frame lent
            | None -> frame)
          frame (List.rev locals)
      in
      let without map =
        List.fold_left (fun map local -> Locals.remove (local_key run local) map) map locals
      in
      Some
        {
          frame with
          locals = without frame.locals;
          aliases = without frame.aliases;
          slices = without frame.slices;
          lends = without frame.lends;
        }
  | Lend { part; call } -> read_lend context frame run part call
  | Assert condition ->
      assertion context frame
        ~origin:(Option.value (operand_origin condition) ~default:statement.origin)
        ~bit_vector:None
        (read_operand context frame run condition);
      Some frame
  | Ghost_assert { condition; by_bit_vector } ->
      let frame, term = specification_value context frame condition in
      let named () =
        List.map
          (fun parameter ->
            match condition.locals.(parameter) with
            | { kind = Source { local; _ }; type_; _ } -> (local, type_)
            | { kind = Temporary | Lent _; _ } -> bug "an assertion's formula that takes no local")
          condition.parameters
      in
      assertion context frame ~origin:condition.origin
        ~bit_vector:
          (if by_bit_vector then
             Some
               ( named (),
                 fun isolated -> snd (context.formula_term isolated condition ~arguments:[]) )
           else None)
        term;
      Some frame
  | Proof code -> Some (restrict frame (Logic.not_ (ghost_code context frame code)))
  | Matched { patterns } ->
      if frame.makes_obligations then
        context.decisions <-
          ( Printf.sprintf "the arm `%s` is taken"
              (String.concat ", " (List.map (text_of frame.source) patterns)),
            None,
            frame.condition,
            Logic.Boolean true )
          :: context.decisions;
      Some frame
  | Slice { destination; base; call } ->
      let values = call_values context frame run (invocation_of call ~lends:None) call.arguments in
      let argument position =
        Option.map
          (fun (passed : passed) -> passed.term)
          (List.find_opt (fun (passed : passed) -> passed.position = position) values)
      in
      let low = Option.value (argument 1) ~default:(Logic.int 0) in
      let site : Invocation.site =
        { id = call.node; origin = call.origin; type_ = target_type context frame run destination }
      in
      let base_type = place_type context frame run base in
      let collection = read_place context frame run base in
      let frame, viewed, low, high =
        apply_slice context frame site ~base_type ~collection ~low ~high:(argument 2)
      in
      let collection = expanded frame run base in
      let written = write_place context frame run destination viewed in
      Some
        (match destination with
        | { root = Local local; projections = [] } ->
            {
              written with
              slices =
                Locals.add (local_key run local)
                  (Slices
                     [
                       (Logic.Boolean true, { made_at = site; collection; start = low; stop = high });
                     ])
                  written.slices;
            }
        | _ -> written)
  | Template { destination; literals; call } -> (
      match (call.callee, call.arguments) with
      | Trait_method { trait; name; receiver; evidence; _ }, [ Passed { value = template; _ } ] ->
          let frame, tagged =
            apply_template context frame
              {
                id = call.node;
                origin = call.origin;
                type_ = target_type context frame run destination;
              }
              ~trait ~name ~receiver ~evidence ~literals
              (read_operand context frame run template)
          in
          Some (write_place context frame run destination tagged)
      | _ -> unsupported span "a tagged template whose tag the prover cannot read")
  | Provide { provided; _ } ->
      Hashtbl.replace run.provides statement.origin provided;
      Some frame
  | Provide_end -> (
      match Hashtbl.find_opt run.provides statement.origin with
      | Some provided ->
          Some
            (List.fold_left
               (fun frame (implementation : Mir.provided) ->
                 match (implementation.mode, implementation.value) with
                 | Types.Mut, Borrow { place; _ } ->
                     let root = { (expanded frame run place) with Mir.projections = [] } in
                     refreshed context frame
                       (place_type context frame run root)
                       (passed_place_of context run root)
                 | _ -> frame)
               frame provided)
      | None -> Some frame)

and write_assignment context run (target : Mir.place) ~(copied : Mir.operand list) read =
  let copied =
    match List.sort_uniq compare (List.map whole_local copied) with
    | [ Some source ] -> Some source
    | _ -> None
  in
  let* frame, term = read in
  (match target.root with
  | Local local -> (
      match run.infos.(local).kind with
      | Source { local = (Named _ | Synthetic _) as core; name = Some name; _ }
        when frame.source.key = Some context.home ->
          Hashtbl.replace context.local_names core name
      | Source _ | Temporary | Lent _ -> ())
  | Constant _ | Literal _ -> ());
  let copied_slice =
    Option.bind copied (fun source -> Locals.find_opt (local_key run source) frame.slices)
  in
  let written = write_place context frame run target term in
  Some
    (match target with
    | { root = Local local; projections = [] } ->
        let key = local_key run local in
        {
          written with
          slices =
            (match copied_slice with
            | Some held -> Locals.add key held written.slices
            | None when Types.is_well_known Slice run.infos.(local).type_ ->
                Locals.add key Unknown_slice written.slices
            | None -> Locals.remove key written.slices);
        }
    | _ -> written)

let new_run ~in_formula ~locals ~lambdas =
  { infos = locals; lambdas; in_formula; provides = Hashtbl.create 2; loops = []; cancelled = [] }

let formula_term context frame (formula : Mir.formula) ~arguments =
  let run = new_run ~in_formula:true ~locals:formula.locals ~lambdas:formula.lambdas in
  let inside =
    {
      frame with
      locals = without_temporaries frame.locals;
      aliases = Locals.empty;
      slices = Locals.empty;
      lends = Locals.empty;
    }
  in
  let inside =
    if arguments = [] then inside
    else
      List.fold_left2
        (fun inside parameter argument ->
          bind inside (local_key run parameter)
            (substituted context inside formula.locals.(parameter).type_)
            argument)
        inside formula.parameters arguments
  in
  try
    let after, term = read_value context inside run formula.value in
    ({ frame with spent = after.spent }, term)
  with Unsupported (_, message) when frame.source.key <> Some context.home ->
    raise (Foreign_unsupported (Printf.sprintf "%s, in `%s`" message frame.source.name))

let read_body context start ~(lambdas : Mir.body array) (body : Mir.body) =
  let run = new_run ~in_formula:false ~locals:body.locals ~lambdas in
  let start = { start with aliases = Locals.empty; slices = Locals.empty; lends = Locals.empty } in
  let rec returned_locals (block : Mir.block) =
    List.concat_map
      (fun (statement : Mir.statement) ->
        (match statement.kind with
          | Resume { exits; _ } ->
              List.filter_map (fun (exit : Mir.early_exit) -> exit.returned) exits
          | _ -> [])
        @ List.concat_map returned_locals (Mir.nested_blocks statement))
      block.statements
  in
  let start =
    List.fold_left
      (fun frame local ->
        let ty = substituted context frame body.locals.(local).type_ in
        bind frame (local_key run local) ty (arrive context frame "returned" ty))
      start (returned_locals body.code)
  in
  match read_statements context start run body.code.statements with
  | None -> ()
  | Some _ -> bug "a body whose end control reaches"
