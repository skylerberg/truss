(* The reader of the MIR: runs a body's blocks forward from a frame, and
   maps a formula to a term, by the rules. *)

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

type run = {
  infos : Mir.local_info array;  (** Each local of the body or the formula being read. *)
  lambdas : Mir.body array;  (** The bodies that its lambdas name. *)
  in_formula : bool;  (** Whether the code read is a formula's. *)
  functions : (Mir.local, Core.id * Core.origin * Path.t) Hashtbl.t;
      (** Each local that the statements read so far assigned a named function: the node and the
          origin of the function's name, and its path *)
  function_values : (Mir.local, unit) Hashtbl.t;
      (** Each local that the statements read so far assigned a function or a lambda written there
      *)
  lambda_arguments : (Mir.local, Invocation.site * lambda_code) Hashtbl.t;
      (** Each temporary that holds a lambda written as a call's argument, which the call reads with
          what its parameter promises *)
  held : (Mir.local, Mir.place) Hashtbl.t;
      (** Each temporary that holds a borrow of a place until its operation runs, with the place *)
  places : (Mir.local, Mir.place) Hashtbl.t;
  lends : (Mir.local, frame -> Logic.term -> frame) Hashtbl.t;
      (** For each part lent to mutate, how its final value goes back where it was lent from, as the
          lend ends *)
  slices : (Mir.local, Invocation.site * Mir.place * Logic.term * Logic.term) Hashtbl.t;
      (** Each temporary that holds a slice: where it is made, the collection it views, and its
          run's start and stop, for a callee that mutates the slice *)
  provides : (Core.origin, Mir.provided list) Hashtbl.t;
}

(* The key of a local of the MIR in a frame's locals: a parameter's or a
   binding's own core local, which specifications name, and for a
   temporary, a synthetic local numbered below zero, which no core form
   has. *)
let mir_key run local =
  match run.infos.(local).kind with
  | Source { local = core; _ } -> core
  | Temporary | Lent _ -> Core.Synthetic (-1 - local)

let rec mir_place_type context frame run (place : Mir.place) =
  match place.Mir.projections with
  | [] -> (
      match place.Mir.root with
      | Local local -> substituted context frame run.infos.(local).type_
      | Constant path -> constant_type context path)
  | _ -> (
      let base =
        { place with Mir.projections = List.rev (List.tl (List.rev place.Mir.projections)) }
      in
      let base_type = mir_place_type context frame run base in
      let variant, field =
        match List.nth place.Mir.projections (List.length place.Mir.projections - 1) with
        | Field field -> (None, field)
        | Variant_field { variant; field } -> (Some variant, field)
      in
      match Option.bind (declared_fields context base_type variant) (List.assoc_opt field) with
      | Some field_type -> substituted context frame field_type
      | None -> raise (Foreign_unsupported (Printf.sprintf "the field `%s`" field)))

(* A place with each local that is a place it was bound to replaced by that
   place. *)
let rec expanded run (place : Mir.place) =
  match place.Mir.root with
  | Local local -> (
      match Hashtbl.find_opt run.places local with
      | Some bound ->
          let bound = expanded run bound in
          { bound with Mir.projections = bound.Mir.projections @ place.Mir.projections }
      | None -> place)
  | Constant _ -> place

let read_root context frame run (root : Mir.root) =
  match root with
  | Constant path -> constant_value context frame path
  | Local local -> (
      match mir_key run local with
      | Self -> (
          match frame.self with
          | Some self -> self
          | None -> raise (Foreign_unsupported "`self` outside a method"))
      | key -> (
          (* A function-typed parameter read other than to be called or passed
             on keeps its [requires]. *)
          if frame.checking && not context.reading_callback then escaping_callback context frame key;
          match Locals.find_opt key frame.locals with
          | Some term -> term
          | None
            when run.in_formula
                 &&
                 match run.infos.(local).kind with
                 | Source _ -> false
                 | Temporary | Lent _ -> true ->
              (* A clause that reads it would otherwise be left out, and say nothing. *)
              bug "a temporary of a formula of `%s` is read before it is assigned" frame.source.name
          | None -> raise (Foreign_unsupported "a local the prover did not bind")))

(* The value at a place of the MIR. *)
let read_place context frame run (place : Mir.place) =
  let place = expanded run place in
  let _, term =
    List.fold_left
      (fun (prefix, term) (projection : Mir.projection) ->
        let base = { place with Mir.projections = prefix } in
        let base_type = mir_place_type context frame run base in
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
            (mir_place_type context frame run projected)
            term ))
      ([], read_root context frame run place.Mir.root)
      place.Mir.projections
  in
  term

(* The frame after a place of the MIR takes a new value: a local, [self],
   or a field, which rebuilds each value it is in. *)
let write_place context frame run (place : Mir.place) new_value =
  let place = expanded run place in
  let rec rebuilt prefix whole = function
    | [] -> new_value
    | (projection : Mir.projection) :: rest ->
        let base_type = mir_place_type context frame run { place with Mir.projections = prefix } in
        let variant, field =
          match projection with
          | Field field -> (None, field)
          | Variant_field { variant; field } -> (Some variant, field)
        in
        let field_type =
          mir_place_type context frame run { place with Mir.projections = prefix @ [ projection ] }
        in
        let part = field_of context frame base_type variant field field_type whole in
        field_replaced context base_type variant field whole
          (rebuilt (prefix @ [ projection ]) part rest)
  in
  match place.Mir.root with
  | Constant _ -> raise (Foreign_unsupported "assigning to a constant")
  | Local local -> (
      let whole =
        if place.Mir.projections = [] then new_value
        else rebuilt [] (read_root context frame run place.Mir.root) place.Mir.projections
      in
      match mir_key run local with
      | Self -> { frame with self = Some whole }
      | key -> bind frame key (substituted context frame run.infos.(local).type_) whole)

let mir_changes ?(also = []) run (body : Mir.body) frame (blocks : Mir.block list) : changed =
  let locals = ref [] and self = ref false in
  let note (place : Mir.place) =
    match (expanded run place).root with
    | Local local -> (
        match mir_key run local with
        | Self -> self := true
        | key -> if Locals.mem key frame.locals then locals := key :: !locals)
    | Constant _ -> ()
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
  List.iter
    (fun block ->
      let basic = body.blocks.(block) in
      List.iter
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Assign { target; value = Operand (Borrow { place; mode = Types.Mut; _ }); _ } ->
              note target;
              note place
          | Assign { target; _ } -> note target
          | Call { destination; call } ->
              Option.iter note destination;
              passed call
          | Lend { call; _ } -> passed call
          | Slice { destination; call; _ } | Template { destination; call; _ } ->
              note destination;
              passed call
          | _ -> ())
        basic.statements;
      match basic.terminator with
      | For { iteration = Pull { cursor; _ }; _ } -> note cursor
      | Yield { mode = Types.Mut; part; _ } -> lent part
      | Cancel { winner; returned; _ } ->
          note { root = Local winner; projections = [] };
          Option.iter (fun (_, local) -> note { root = Local local; projections = [] }) returned
      | _ -> ())
    blocks;
  List.iter note also;
  { changed_locals = List.sort_uniq compare !locals; changes_self = !self && frame.self <> None }

let mir_operand context frame run (operand : Mir.operand) =
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
      | Boolean truth -> Logic.Boolean truth
      | String text -> text_value context frame ty text)

let mir_operand_type context frame operand = substituted context frame (Mir.operand_type operand)

(* Where an operand's value is written, if it has a place. *)
let operand_origin : Mir.operand -> Core.origin option = function
  | Use { origin; _ } | Borrow { origin; _ } | Take { origin; _ } -> Some origin
  | Constant _ -> None

(* The local an operand reads whole. *)
let whole_local : Mir.operand -> Mir.local option = function
  | Use { place = { root = Local local; projections = [] }; _ }
  | Borrow { place = { root = Local local; projections = [] }; _ } ->
      Some local
  | Use _ | Borrow _ | Take _ | Constant _ -> None

(* A place of the MIR as the place of a [mut] argument. *)
let mir_passed_place context run place =
  {
    read = (fun frame -> read_place context { frame with checking = false } run place);
    write = (fun frame term -> write_place context frame run place term);
  }

let mir_shape run (value : Mir.operand) : Invocation.shape =
  match whole_local value with
  | Some local -> (
      match (Hashtbl.find_opt run.functions local, run.infos.(local).kind) with
      | Some (id, origin, path), _ -> Named_function { id; origin; path }
      | None, Source { local = core; _ } -> Forwarded core
      | None, (Temporary | Lent _) -> Other)
  | None -> Other

(* The place an argument passed [mut] is in. A slice gives its run back to
   the collection it views: read again after the call, it is a view of the
   collection's new run. *)
let mir_argument_place context run (mode : Types.mode) (value : Mir.operand) =
  let slice = Option.bind (whole_local value) (Hashtbl.find_opt run.slices) in
  match (mode, slice) with
  | Types.Mut, Some (site, base, low, high) ->
      Some
        (slice_place context site
           ~owner:(mir_passed_place context run base)
           ~owner_type:(fun frame -> mir_place_type context frame run base)
           ~low ~high)
  | Types.Mut, None -> (
      match value with
      | Borrow { place; _ } -> Some (mir_passed_place context run place)
      | _ -> None)
  | _ -> None

(* The lambda a temporary passed as an argument holds, as written. *)
let passed_lambda run (value : Mir.operand) =
  match value with
  | Use { place = { root = Local local; projections = [] }; _ } ->
      Hashtbl.find_opt run.lambda_arguments local
  | _ -> None

(* A call's arguments as the callee is given them, from the values the MIR
   has evaluated. *)
let mir_values context frame run (invocation : Invocation.t) (arguments : Mir.argument list) =
  passed_values context frame invocation
    (List.concat
       (List.mapi
          (fun position (argument : Mir.argument) ->
            match argument with
            | Passed { mode; value; _ } -> (
                match passed_lambda run value with
                | Some (site, lambda) -> [ Given_lambda { position; mode; site; lambda } ]
                | None ->
                    [
                      Given_value
                        {
                          position;
                          mode;
                          shape = mir_shape run value;
                          origin = operand_origin value;
                          passed_place = mir_argument_place context run mode value;
                          type_ = mir_operand_type context frame value;
                          term =
                            reading_callback context (fun () -> mir_operand context frame run value);
                        };
                    ])
            | Default -> [])
          arguments))

(* A call, through the callee's contract, with the arguments the MIR has
   evaluated, giving a value of [result_type]. An equality with a string
   literal, as a string pattern tests, compares the text's bytes. *)
let mir_call context frame run (call : Mir.call) ~result_type =
  let invocation = Invocation.of_mir call ~lends:None in
  match (invocation.callee, call.arguments) with
  | ( Trait_method { trait; name = "equal"; _ },
      [ Passed { value = tested; _ }; Passed { value = Constant { value = String text; _ }; _ } ] )
    when Path.equal trait.trait equal_trait ->
      let ty = mir_operand_type context frame tested in
      Some
        ( frame,
          text_matches context
            (span_of frame.source call.origin)
            ty
            (mir_operand context frame run tested)
            text )
  | _ ->
      let through =
        match call.callee with
        | Indirect callee ->
            Some
              ( mir_operand_type context frame callee,
                reading_callback context (fun () -> mir_operand context frame run callee),
                mir_shape run callee )
        | _ -> None
      in
      let values = mir_values context frame run invocation call.arguments in
      apply_call context frame
        { id = call.node; origin = call.origin; type_ = result_type }
        invocation ~through values

let mir_lend context frame run part (call : Mir.call) =
  let mode = match run.infos.(part).kind with Lent mode -> mode | _ -> Types.Read in
  let invocation = Invocation.of_mir call ~lends:(Some mode) in
  let site : Invocation.site =
    { id = call.node; origin = call.origin; type_ = run.infos.(part).type_ }
  in
  let span = span_of frame.source call.origin in
  let values = mir_values context frame run invocation call.arguments in
  let lend ?lent_final frame =
    apply_call ?lent_final context frame site invocation ~through:None values
  in
  begin
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
    let lent =
      match (invocation.lends, invocation.callee, receiver) with
      | ( Some Types.Mut,
          Intrinsic
            {
              operation = (Storage_at_mut | Array_at_mut | View_at_mut) as operation;
              type_arguments;
            },
          Some receiver ) ->
          let index = index_term () in
          Hashtbl.replace run.lends part (fun frame final ->
              element_written_back context frame ~operation ~type_arguments
                ~receiver:(mir_passed_place context run receiver)
                ~receiver_type:(mir_place_type context frame run receiver)
                index final);
          lend frame
      | Some Types.Mut, Intrinsic _, _ -> unsupported span "this lend"
      | Some Types.Mut, _, _ ->
          Hashtbl.replace run.lends part (fun frame final ->
              match lend ~lent_final:(fun _ -> final) frame with
              | Some (after, _) -> after
              | None -> frame);
          without_costs context (fun () -> lend frame)
      | _ -> lend frame
    in
    match lent with
    | Some (after, term) ->
        Some (write_place context after run { root = Local part; projections = [] } term)
    | None -> None
  end

(* The place a place stands for: through each binding of a part to mutate,
   and each temporary that holds a borrow of a place. *)
let rec borrowed run (place : Mir.place) =
  let place = expanded run place in
  match place.root with
  | Local local -> (
      match Hashtbl.find_opt run.held local with
      | Some held ->
          let held = borrowed run held in
          { held with Mir.projections = held.Mir.projections @ place.Mir.projections }
      | None -> place)
  | Constant _ -> place

(* The type of a place a value is written to, as the MIR declares it. *)
let mir_target_type context frame run (target : Mir.place) =
  match target with
  | { root = Local local; projections = [] } -> run.infos.(local).type_
  | _ -> mir_place_type context frame run target

(* Whether a yielded value lends places: it is a place, or a constructor
   built where it is yielded. *)
let mir_lends_places (part : Mir.yielded) =
  match part with Built _ | Part (Borrow _) -> true | Part (Use _ | Take _ | Constant _) -> false

(* The part a lending method lends, and the frame after it is built: a
   constructor built where it is lent is built here, from its fields. *)
let rec mir_yielded context frame run ~origin (part : Mir.yielded) =
  match part with
  | Part operand -> (frame, mir_operand context frame run operand)
  | Built { variant; fields; node; type_ } ->
      let frame, values =
        List.fold_left
          (fun (frame, values) (name, field) ->
            match field with
            | Some field ->
                let frame, term = mir_yielded context frame run ~origin field in
                (frame, values @ [ (name, Some term) ])
            | None -> (frame, values @ [ (name, None) ]))
          (frame, []) fields
      in
      apply_construct context frame { id = node; origin; type_ } variant values

let rec mir_written_back context run ty (part : Mir.yielded) frame after =
  match part with
  | Part (Borrow { place; _ }) -> write_place context frame run place after
  | Built { variant; fields; _ } -> (
      match constructors context ty with
      | Some shape ->
          let shaped = Option.value (List.assoc_opt variant shape) ~default:[] in
          List.fold_left
            (fun frame (name, field) ->
              match (field, List.assoc_opt name shaped) with
              | Some field, Some field_type when mir_lends_places field ->
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
                  mir_written_back context run field_type field frame value
              | _ -> frame)
            frame fields
      | None -> raise (Foreign_unsupported (Printf.sprintf "the fields of `%s`" (Types.show ty))))
  | Part (Use _ | Take _ | Constant _) -> frame

(* The frame with each binding of a part to mutate holding the part's
   value, for the core form's expressions that name the binding: a loop's
   clauses and measure, and the specifications read here. A change through
   the binding goes to the part. *)
let mir_bindings context frame run =
  Hashtbl.fold
    (fun local place frame ->
      match run.infos.(local).kind with
      | Source { local = core; _ } -> (
          try
            bind frame core
              (substituted context frame run.infos.(local).type_)
              (read_place context { frame with checking = false } run place)
          with Unsupported _ | Foreign_unsupported _ -> frame)
      | Temporary | Lent _ -> frame)
    run.places frame

(* What reading a value of a formula spent, where one of two blocks is read:
   each counter's cost in the block that [condition] reads. *)
let spent_in_one ~condition ~(read : frame) ~(otherwise : frame) =
  List.map
    (fun (counter, spent) ->
      match List.assoc_opt counter otherwise.spent with
      | Some other when other <> spent -> (counter, Logic.ite condition spent other)
      | _ -> (counter, spent))
    read.spent

(* Records the case that the condition of an [if] takes, for the path a
   counterexample shows. *)
let note_decision context frame origin test =
  if frame.checking && frame.source.key = Some context.home then begin
    let text = quote frame.source origin in
    context.decisions <-
      ( Printf.sprintf "`%s` is true" text,
        Some (Printf.sprintf "`%s` is false" text),
        frame.condition,
        test )
      :: context.decisions
  end

(* The value an rvalue computes, and the frame after it. *)
let rec mir_rvalue context frame run (value : Mir.rvalue) ~(site : Invocation.site) =
  let span = span_of frame.source site.origin in
  let ty = substituted context frame site.type_ in
  let operand = mir_operand context frame run in
  match value with
  | Operand value -> (frame, operand value)
  | Compare { comparison = compared; left; right } ->
      ( frame,
        compared_terms (mir_operand_type context frame left) compared (operand left) (operand right)
      )
  | Not inner -> (frame, Logic.not_ (operand inner))
  | Is_variant { place; variant } ->
      let ty = mir_place_type context frame run place in
      ignore (sort_of context ty);
      if constructors context ty = None then
        unsupported span "a variant of `%s`, which the prover does not see" (Types.show ty);
      (frame, Logic.Is (constructor_name ty (Some variant), read_place context frame run place))
  | Copy copied_operand ->
      let ty = mir_operand_type context frame copied_operand in
      let term = operand copied_operand in
      (copied context frame ty term, term)
  | Convert { conversion = Widen; value } ->
      check_widened span
        ~is_written:
          (Option.fold ~none:false ~some:(Hashtbl.mem run.function_values) (whole_local value))
        (mir_operand_type context frame value)
        ty;
      (frame, operand value)
  | Value_parameter parameter -> (frame, value_term context frame (Value_parameter parameter))
  | Convert { conversion = To_integer; value } -> (frame, operand value)
  | Convert { conversion = From_integer; value } ->
      (frame, from_integer context frame site (operand value))
  | Function_value { path; type_arguments; is_argument } ->
      (frame, global_value context frame site path type_arguments ~is_argument)
  | To_any _ -> to_any context frame site
  | Operation { operation; operands; type_arguments } ->
      (* An operator and a call of the intrinsic are one operation, read as
         the intrinsic: a primitive operation takes constant time and
         allocates nothing, so its call costs nothing more. *)
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
  | Lambda { body; captures; definition; value_type; _ } ->
      lambda context frame ~site
        { code = run.lambdas.(body); lambdas = run.lambdas; captures; definition; value_type }
        ~facts:(fun _ -> [])
  | Specification Result -> (
      match frame.result with
      | Some result -> (frame, result)
      | None -> unsupported span "`result` here")
  | Specification (Entry local) -> (
      match mir_key run local with
      | Self -> (
          match frame.old_self with
          | Some self -> (frame, self)
          | None -> raise (Foreign_unsupported "`self` outside a method"))
      | key -> (
          match Locals.find_opt key frame.old_locals with
          | Some term -> (frame, term)
          | None -> raise (Foreign_unsupported "a local the prover did not bind")))
  | Specification Yielded -> (
      (* The values the innermost loop has received, or else, in a lending
         method's body, the part the method has lent. *)
      match (frame.yielded, frame.yielded_so_far) with
      | Some yielded, _ -> (frame, yielded)
      | None, Some yielded_so_far when frame.source.key = Some context.home ->
          (frame, yielded_so_far)
      | _ -> unsupported span "`yielded` here")
  | Specification (Identical (first, second)) ->
      (* Identity, for every type: the solver's equality. *)
      let first_value = operand first and second_value = operand second in
      extensional context frame (mir_operand_type context frame first) first_value second_value;
      (frame, Logic.equal first_value second_value)
  | Specification (Applied { function_; arguments; unconverted }) ->
      (* A specification function never runs, so a callback read for it is
         not used as a value. *)
      let values = reading_callback context (fun () -> List.map operand arguments) in
      apply_specification_function context frame ~span function_ values
        ~unconverted:(List.map (substituted context frame) unconverted)
        ~types:(List.map (mir_operand_type context frame) arguments)
  | Specification (Method_time callee) ->
      (frame, method_time context frame (Invocation.unit_callee callee))
  | Specification (Map entries) ->
      apply_map_literal context frame ~ty ~span
        (List.map (fun (key, entry) -> (operand_origin key, operand key, operand entry)) entries)
  | Specification (Quantified { quantifier; range; parameter; matches; body }) -> (
      let range =
        match range with
        | Over_type ty -> Range_of_type (substituted context frame ty)
        | Over_range { start; stop; inclusive } ->
            Range_of_integers
              {
                low = operand start;
                high = operand stop;
                inclusive;
                type_ = mir_operand_type context frame start;
              }
        | Over_collection collection ->
            Range_of_collection
              {
                collection_type = mir_operand_type context frame collection;
                collected = operand collection;
                element = substituted context frame run.infos.(parameter).type_;
                span;
              }
      in
      (* The quantifier ranges over the values that its pattern matches: [matches] binds the
         pattern's names to the value in [parameter], and gives whether it matches. *)
      match
        quantified_over context frame quantifier range
          ~bind:(fun inner value ty ->
            let after, matched =
              value_block_value context (bind inner (mir_key run parameter) ty value) run matches
            in
            (matched, after))
          ~read:(fun body_frame _ ->
            let after, term = value_block_value context body_frame run body in
            ({ body_frame with spent = after.spent }, term))
      with
      | Some quantified -> quantified
      | None -> unsupported span "a quantifier that gives no value")
  | Specification (Conditional { condition; then_; else_; if_condition }) -> (
      let test = operand condition in
      (match if_condition with
      | Some origin -> note_decision context frame origin test
      | None -> ());
      (* The value of the case that is read, and the frame after either: the locals that a
         case's block assigns end with it. *)
      let case condition block =
        let after, value = value_block_value context (restrict frame condition) run block in
        (end_scope ~outer:frame after, Some value)
      in
      match join context ~value_type:ty [ case test then_; case (Logic.not_ test) else_ ] with
      | Some (joined, Some value) -> (joined, value)
      | Some (_, None) | None -> bug "a conditional of a formula with no value")
  | Specification (Cases cases) -> (
      (* Each case is tried where no case before it is taken: where its tests do not hold,
         or they do and its guard does not. *)
      let scoped = end_scope ~outer:frame in
      let untaken = ref (Some frame) in
      let reached =
        List.filter_map
          (fun (case : Mir.case) ->
            Option.map
              (fun current ->
                let bound, matches = value_block_value context current run case.tests in
                let entered = restrict bound matches in
                let entered, guarded_out =
                  match case.guard with
                  | Some guard ->
                      let after, holds = value_block_value context entered run guard in
                      (restrict after holds, [ scoped (restrict after (Logic.not_ holds)) ])
                  | None -> (entered, [])
                in
                untaken := join_frames context (restrict current (Logic.not_ matches) :: guarded_out);
                let after, value = value_block_value context entered run case.value in
                (scoped after, Some value))
              !untaken)
          cases
      in
      match join context ~value_type:ty reached with
      | Some (joined, Some value) -> (joined, value)
      | Some (_, None) | None -> bug "a `match` of a formula with no value")
  | Specification (Connective { connective; left; right }) -> (
      let left = operand left in
      (* The right operand is read only where the left leaves the value open. *)
      let reads_right = match connective with And | Implies -> left | Or -> Logic.not_ left in
      let after, right = value_block_value context (restrict frame reads_right) run right in
      let spent = spent_in_one ~condition:reads_right ~read:after ~otherwise:frame in
      (* A name that an [is] in the right operand of [&&] binds is read after the [&&],
         where the [&&] holds, as [x] is in [a && b is Some(x) && x > 0]. *)
      ( (match connective with
        | And -> { after with condition = frame.condition; spent }
        | Or | Implies -> { frame with spent }),
        match connective with
        | And -> Logic.( &&& ) left right
        | Or -> Logic.( ||| ) left right
        | Implies -> Logic.( ==> ) left right ))

(* The value of a block of a formula read from [frame]: the frame after its
   statements, and the term. *)
and value_block_value context frame run (block : Mir.value_block) =
  let after =
    List.fold_left
      (fun frame statement ->
        match mir_statement context frame run statement with
        | Some frame -> frame
        | None -> raise (Foreign_unsupported "a call in a specification that never returns"))
      frame block.statements
  in
  (after, mir_operand context after run block.value)

and mir_statement context frame run (statement : Mir.statement) =
  let span = span_of frame.source statement.origin in
  match statement.kind with
  | Assign
      {
        target = { root = Local local; projections = [] };
        value = Operand (Borrow { place; mode = Mut; _ });
        _;
      } ->
      (* A binding of a part to mutate is the part itself. *)
      Hashtbl.replace run.places local place;
      Some frame
  | Assign
      {
        target = { root = Local local; projections = [] } as target;
        value = Lambda { body; captures; definition; value_type; is_argument = true };
        node;
      } ->
      (* A lambda written as an argument is read by the call, with what the parameter
         promises of its arguments. *)
      Hashtbl.replace run.function_values local ();
      Hashtbl.replace run.lambda_arguments local
        ( {
            id = Option.value node ~default:(-1);
            origin = statement.origin;
            type_ = run.infos.(local).type_;
          },
          { code = run.lambdas.(body); lambdas = run.lambdas; captures; definition; value_type } );
      Some
        (write_place context frame run target
           (arrive context frame "lambda" (mir_place_type context frame run target)))
  | Assign { target; value; node } ->
      (* What the local holds, for the statements after this one. *)
      (match (target, value) with
      | { root = Local local; projections = [] }, Function_value { path; _ } ->
          Hashtbl.replace run.function_values local ();
          Option.iter
            (fun id -> Hashtbl.replace run.functions local (id, statement.origin, path))
            node
      | { root = Local local; projections = [] }, Lambda _ ->
          Hashtbl.replace run.function_values local ()
      | { root = Local local; projections = [] }, Convert { conversion = Widen; value = converted }
        ->
          Option.iter
            (fun named -> Hashtbl.replace run.functions local named)
            (Option.bind (whole_local converted) (Hashtbl.find_opt run.functions))
      | { root = Local local; projections = [] }, Operand copied -> (
          Option.iter
            (fun slice -> Hashtbl.replace run.slices local slice)
            (Option.bind (whole_local copied) (Hashtbl.find_opt run.slices));
          match (copied, run.infos.(local).kind) with
          | Borrow { place; _ }, (Temporary | Lent _) -> Hashtbl.replace run.held local place
          | _ -> ())
      | _ -> ());
      let frame, term =
        mir_rvalue context frame run value
          ~site:
            {
              id = Option.value node ~default:(-1);
              origin = statement.origin;
              type_ = mir_target_type context frame run target;
            }
      in
      (match target.root with
      | Local local -> (
          match run.infos.(local).kind with
          | Source { local = (Named _ | Synthetic _) as core; name = Some name; _ }
            when frame.source.key = Some context.home ->
              Hashtbl.replace context.local_names core name
          | Source _ | Temporary | Lent _ -> ())
      | Constant _ -> ());
      Some (write_place context frame run target term)
  | Call { destination; call } -> (
      let result_type =
        match destination with
        | Some destination -> mir_target_type context frame run destination
        | None -> Types.unit
      in
      match mir_call context frame run call ~result_type with
      | Some (after, term) -> (
          match destination with
          | Some destination -> Some (write_place context after run destination term)
          | None -> Some after)
      | None -> None)
  | Live _ | Loan_start _ | Loan_end _ | Echo _ -> Some frame
  | Dead locals ->
      let frame =
        List.fold_left
          (fun frame local ->
            match Hashtbl.find_opt run.lends local with
            | Some finish ->
                Hashtbl.remove run.lends local;
                finish frame
                  (read_place context { frame with checking = false } run
                     { root = Local local; projections = [] })
            | None -> frame)
          frame (List.rev locals)
      in
      List.iter (Hashtbl.remove run.places) locals;
      Some
        {
          frame with
          locals =
            List.fold_left
              (fun locals local -> Locals.remove (mir_key run local) locals)
              frame.locals locals;
        }
  | Lend { part; call } -> mir_lend context frame run part call
  | Assert { condition; bit_vector } ->
      assertion context frame
        ~origin:(Option.value (operand_origin condition) ~default:statement.origin)
        ~bit_vector
        (mir_operand context frame run condition);
      Some frame
  | Ghost_assert { condition; by_bit_vector } ->
      let frame, term = specification_value context frame condition in
      assertion context frame ~origin:condition.origin
        ~bit_vector:(if by_bit_vector then Some condition else None)
        term;
      Some frame
  | Proof code -> Some (restrict frame (Logic.not_ (ghost_code context frame code)))
  | Matched { patterns } ->
      if frame.checking then
        context.decisions <-
          ( Printf.sprintf "the arm `%s` is taken"
              (String.concat ", " (List.map (quote frame.source) patterns)),
            None,
            frame.condition,
            Logic.Boolean true )
          :: context.decisions;
      Some frame
  | Slice { destination; base; call } ->
      let values =
        mir_values context frame run (Invocation.of_mir call ~lends:None) call.arguments
      in
      let argument position =
        Option.map
          (fun (passed : passed) -> passed.term)
          (List.find_opt (fun (passed : passed) -> passed.position = position) values)
      in
      let low = Option.value (argument 1) ~default:(Logic.int 0) in
      let site : Invocation.site =
        {
          id = call.node;
          origin = call.origin;
          type_ = mir_target_type context frame run destination;
        }
      in
      let base_type = mir_place_type context frame run base in
      let collection = read_place context frame run base in
      let frame, viewed, low, high =
        apply_slice context frame site ~base_type ~collection ~low ~high:(argument 2)
      in
      (* The collection is recorded as the place it is, since a temporary
         that names it may end before the slice is passed. *)
      (match destination with
      | { root = Local local; projections = [] } ->
          Hashtbl.replace run.slices local (site, borrowed run base, low, high)
      | _ -> ());
      Some (write_place context frame run destination viewed)
  | Template { destination; literals; call } -> (
      match (call.callee, call.arguments) with
      | Trait_method { trait; name; receiver; evidence; _ }, [ Passed { value = template; _ } ] ->
          let frame, tagged =
            apply_template context frame
              {
                id = call.node;
                origin = call.origin;
                type_ = mir_target_type context frame run destination;
              }
              ~trait ~name ~receiver ~evidence ~texts:literals
              (mir_operand context frame run template)
          in
          Some (write_place context frame run destination tagged)
      | _ -> unsupported span "a tagged template whose tag the prover cannot read")
  | Provide { provided; _ } ->
      (* The body runs with the implementations, which the prover never
         models, so a capability call in it gives a fresh value by its
         contract. *)
      Hashtbl.replace run.provides statement.origin provided;
      Some frame
  | Provide_end -> (
      (* Where the body ends, each implementation handed over [mut] holds a
         fresh value of its type, which meets its type's invariants. *)
      match Hashtbl.find_opt run.provides statement.origin with
      | Some provided ->
          Some
            (List.fold_left
               (fun frame (implementation : Mir.provided) ->
                 match (implementation.mode, implementation.value) with
                 | Types.Mut, Borrow { place; _ } ->
                     let root = { (expanded run place) with Mir.projections = [] } in
                     refreshed context frame
                       (mir_place_type context frame run root)
                       (mir_passed_place context run root)
                 | _ -> frame)
               frame provided)
      | None -> Some frame)

(* A run of code before it starts: the locals it reads and the bodies of
   its lambdas. *)
let new_run ~in_formula ~locals ~lambdas =
  {
    infos = locals;
    lambdas;
    in_formula;
    functions = Hashtbl.create 4;
    function_values = Hashtbl.create 4;
    lambda_arguments = Hashtbl.create 2;
    held = Hashtbl.create 8;
    places = Hashtbl.create 4;
    lends = Hashtbl.create 4;
    slices = Hashtbl.create 2;
    provides = Hashtbl.create 2;
  }

(* The value of a formula read from [frame], with [arguments] for its
   parameters, or none where it reads them from the frame: the term, and
   the frame as it was but for what reading the formula spent. A formula is
   one block, so nothing is joined: an [if] in it is one value. *)
let formula_term context frame (formula : Mir.formula) ~arguments =
  let run = new_run ~in_formula:true ~locals:formula.locals ~lambdas:formula.lambdas in
  let inside = { frame with locals = without_temporaries frame.locals } in
  let inside =
    if arguments = [] then inside
    else
      List.fold_left2
        (fun inside parameter argument ->
          bind inside (mir_key run parameter)
            (substituted context inside formula.locals.(parameter).type_)
            argument)
        inside formula.parameters arguments
  in
  try
    let after, term = value_block_value context inside run formula.value in
    ({ frame with spent = after.spent }, term)
  with Unsupported (_, message) when frame.source.key <> Some context.home ->
    raise (Foreign_unsupported (Printf.sprintf "%s, in `%s`" message frame.source.name))

(* Runs a body of the MIR forward from [start]. Each [return] joins
   [context.returns]. Its blocks are in reverse postorder, so each block
   runs once every block that jumps to it has, but for a loop's back edges:
   a [while] loop runs as the core form's does, with its changes havocked
   at its head and its invariants checked at the end of each iteration. *)
let mir_run context start ~(lambdas : Mir.body array) (body : Mir.body) =
  let run = new_run ~in_formula:false ~locals:body.locals ~lambdas in
  let count = Array.length body.blocks in
  let incoming = Array.make count [] in
  (* The local each early exit leaves its returned value in holds one on
     every path, so that paths that meet agree on it. *)
  let start =
    Array.fold_left
      (fun frame (block : Mir.basic_block) ->
        match block.terminator with
        | Resume { exits; _ } ->
            List.fold_left
              (fun frame (exit : Mir.early_exit) ->
                match exit.returned with
                | Some local ->
                    let ty = substituted context frame body.locals.(local).type_ in
                    bind frame (mir_key run local) ty (arrive context frame "returned" ty)
                | None -> frame)
              frame exits
        | _ -> frame)
      start body.blocks
  in
  let ran = Array.make count false in
  let rec terminator frame (block : Mir.basic_block) ~jump ~iteration_end =
    let span = span_of frame.source block.terminator_origin in
    match block.terminator with
    | Goto target -> jump target frame
    (* The branches of a [parallel] or [concurrent] block are disjoint, so
       they can run in order. *)
    | Fork { branches = first :: _; _ } -> jump first.entry frame
    | Fork { branches = []; _ } -> ()
    | Join { next; _ } -> jump next frame
    | Branch { condition; yes; no; is_if_condition } ->
        let test = mir_operand context frame run condition in
        if is_if_condition then note_decision context frame block.terminator_origin test;
        jump yes (restrict frame test);
        jump no (restrict frame (Logic.not_ test))
    | Switch_variant { place; cases } ->
        let ty = mir_place_type context frame run place in
        let term = read_place context frame run place in
        List.iter
          (fun (variant, target) ->
            jump target (restrict frame (Logic.Is (constructor_name ty (Some variant), term))))
          cases
    | Return returned ->
        context.returns <-
          (frame, Option.map (mir_operand context frame run) returned) :: context.returns
    | Unreachable -> ()
    | Written_unreachable -> unreachable_reached context frame span
    | Todo -> todo_reached context frame span
    | Iteration_end _ -> iteration_end frame
    | For { loop = { quantified = Some { quantifier; decides }; _ }; after; _ } ->
        (* A quantifier in code, which the MIR runs as a loop and the logic reads as the
           quantifier: its value goes to the local the loop decides, and the loop's body is
           not run. *)
        let after_frame, term = context.formula_term frame quantifier ~arguments:[] in
        jump after
          (write_place context after_frame run { root = Local decides; projections = [] } term)
    | For { iteration; part; lent; body = first; binding_count; blocks; after; loop } ->
        let in_body = Hashtbl.create 16 in
        List.iter (fun block -> Hashtbl.replace in_body block ()) blocks;
        (* An iteration: the part takes the element, and the body's blocks
           run, each once, to the end of the iteration or a [break]. *)
        let run_body inside element =
          let inside =
            bind inside (mir_key run part)
              (substituted context inside body.locals.(part).type_)
              element
          in
          let ends = ref [] and breaks = ref [] in
          incoming.(first) <- [ inside ];
          run_region ~inside:(Hashtbl.mem in_body)
            ~jump:(fun target frame ->
              if target = after then breaks := frame :: !breaks else jump target frame)
            ~iteration_end:(fun frame -> ends := frame :: !ends);
          (List.rev !ends, List.rev !breaks)
        in
        (* In the loop's clauses, the pattern's names are the element's parts, as the
           statements that the body starts with bind them. *)
        let bind_element frame element =
          let frame =
            bind frame (mir_key run part)
              (substituted context frame body.locals.(part).type_)
              element
          in
          List.fold_left
            (fun frame statement ->
              Option.value (mir_statement context frame run statement) ~default:frame)
            frame
            (List.filteri (fun index _ -> index < binding_count) body.blocks.(first).statements)
        in
        let operand = mir_operand context frame run in
        let iterated = match iteration with Pull { cursor; _ } -> [ cursor ] | Range _ -> [] in
        let looped =
          match iteration with
          | Range { start; stop; inclusive } ->
              Over_range { low = operand start; high = operand stop; inclusive }
          | Pull { cursor; next } ->
              Over_cursor
                {
                  cursor = mir_passed_place context run cursor;
                  cursor_type = mir_place_type context frame run cursor;
                  next = Invocation.unit_callee next;
                }
        in
        let driven =
          {
            loop_at = loop.origin;
            loop_clauses = loop.clauses;
            looped;
            element_type = body.locals.(part).type_;
            lent_element =
              Option.map (fun (lent : Mir.lent_element) -> body.locals.(lent.element).type_) lent;
            kept_count =
              Option.bind lent (fun (lent : Mir.lent_element) ->
                  match body.locals.(lent.element).kind with
                  | Lent Mut -> Some lent.count
                  | _ -> None);
            collection =
              Option.map
                (fun (lent : Mir.lent_element) frame ->
                  ( mir_place_type context frame run lent.collection,
                    read_place context { frame with checking = false } run lent.collection ))
                lent;
            element_call =
              Option.bind lent (fun (lent : Mir.lent_element) ->
                  match body.locals.(lent.element).kind with
                  | Lent Mut -> None
                  | _ -> Some lent.call);
            bind_element;
            changed_in = (fun frame -> mir_changes ~also:iterated run body frame blocks);
            changed_by_body = (fun frame -> mir_changes run body frame blocks);
            run_body;
            bindings = (fun frame -> mir_bindings context frame run);
          }
        in
        Option.iter (jump after) (for_ ~driven context frame)
    | Yield { mode; part; resume } ->
        let origin = block.terminator_origin in
        begin
          let frame, handed = mir_yielded context frame run ~origin part in
          let part_type =
            match part with
            | Part operand -> mir_operand_type context frame operand
            | Built { type_; _ } -> substituted context frame type_
          in
          match
            lend_part context frame origin mode ~handed ~lends:(mir_lends_places part)
              ~write_back:(fun frame after ->
                mir_written_back context run part_type part frame after)
          with
          | Some after -> jump resume after
          | None -> ()
        end
    | Cancel { task; task_end; winner; number; returned } -> (
        (* The branches of a group run in order, so the last exit that cancels
           is the one that won. *)
        let frame =
          bind frame (mir_key run winner) (Types.builtin UInt32) (Logic.Integer (Z.of_int number))
        in
        let frame =
          match returned with
          | Some (value, local) ->
              bind frame (mir_key run local)
                (mir_operand_type context frame value)
                (mir_operand context frame run value)
          | None -> frame
        in
        match (task, task_end) with
        | Branch _, Some target -> jump target frame
        | Branch _, None -> bug "a branch's early exit with no end"
        | Iteration _, _ -> iteration_end frame)
    | Resume { winner; exits; next } ->
        let won =
          mir_operand context frame run
            (Use
               {
                 place = { root = Local winner; projections = [] };
                 type_ = Types.builtin UInt32;
                 node = block.terminator_origin;
                 origin = block.terminator_origin;
               })
        in
        let others =
          List.fold_left
            (fun frame (number, (exit : Mir.early_exit)) ->
              let taken = Logic.equal won (Logic.Integer (Z.of_int number)) in
              jump exit.resume (restrict frame taken);
              restrict frame (Logic.not_ taken))
            frame
            (List.mapi (fun index exit -> (index + 1, exit)) exits)
        in
        jump next others
  and run_block position frame ~jump ~iteration_end =
    let block = body.blocks.(position) in
    let ended =
      List.fold_left
        (fun frame (statement : Mir.statement) ->
          Option.bind frame (fun frame ->
              Option.map
                (fun frame -> mir_bindings context frame run)
                (mir_statement context frame run statement)))
        (Some frame) block.statements
    in
    Option.iter (fun frame -> terminator frame block ~jump ~iteration_end) ended
  (* Runs the blocks of a region, each once, in order, from the frames that
     reach them. A jump to a block outside the region leaves by [jump], and
     the end of an iteration of the innermost [for] by [iteration_end]. *)
  and run_region ~inside ~jump ~iteration_end =
    for position = 0 to count - 1 do
      if inside position && not ran.(position) then begin
        ran.(position) <- true;
        let frames = List.rev incoming.(position) in
        incoming.(position) <- [];
        match join_frames context frames with
        | None -> ()
        | Some entry -> (
            let local_jump target frame =
              if inside target && not ran.(target) then
                incoming.(target) <- frame :: incoming.(target)
              else jump target frame
            in
            match body.blocks.(position).header with
            | Some natural -> run_loop position natural entry ~jump:local_jump ~iteration_end
            | None -> run_block position entry ~jump:local_jump ~iteration_end)
      end
    done
  (* A [while] loop, from the frame on entry to its header. *)
  and run_loop header (natural : Mir.natural_loop) frame ~jump ~iteration_end =
    let clauses = natural.loop.clauses in
    let span = span_of frame.source natural.loop.origin in
    let member (blocks : Mir.block list) =
      let members = Array.make count false in
      List.iter (fun block -> members.(block) <- true) blocks;
      fun block -> members.(block)
    in
    let in_loop = member natural.blocks
    and tests = member natural.condition
    and exits = member natural.exits in
    check_invariants context frame clauses ~when_:"on entry to the loop";
    let { loop_costs = costs; fresh_mark = mark; facts_mark; preserved; havocked = head } =
      enter_loop context frame ~entry:frame clauses
        ~changed:(mir_changes run body frame natural.blocks)
    in
    let head = mir_bindings context head run in
    let iterations = iterations_so_far context head costs in
    let head = loop_head context head costs ~iterations in
    assume_invariants context head clauses;
    let top = head in
    let ends = ref [] and failed = ref [] and breaks = ref [] and inside = ref [] in
    let leaving_from = ref header in
    let loop_jump target frame =
      if target = header then ends := frame :: !ends
      else if target = natural.body then incoming.(target) <- frame :: incoming.(target)
      else if in_loop target then incoming.(target) <- frame :: incoming.(target)
      else if exits target then
        if tests !leaving_from then failed := (target, frame) :: !failed
        else breaks := (target, frame) :: !breaks
      else jump target frame
    in
    (* The body's entry takes one step, as each iteration does. *)
    let enter_body () =
      let frames = List.rev incoming.(natural.body) in
      incoming.(natural.body) <-
        (match join_frames context frames with
        | Some entry ->
            let entry = spend context entry one_step in
            inside := [ entry ];
            [ entry ]
        | None -> [])
    in
    ran.(header) <- true;
    leaving_from := header;
    run_block header head ~jump:loop_jump ~iteration_end;
    for position = 0 to count - 1 do
      if in_loop position && not ran.(position) then begin
        if position = natural.body then enter_body ();
        ran.(position) <- true;
        leaving_from := position;
        let frames = List.rev incoming.(position) in
        incoming.(position) <- [];
        match join_frames context frames with
        | None -> ()
        | Some entry -> (
            match body.blocks.(position).header with
            | Some inner ->
                run_loop position inner entry ~iteration_end ~jump:(fun target frame ->
                    leaving_from := position;
                    loop_jump target frame)
            | None -> run_block position entry ~jump:loop_jump ~iteration_end)
      end
    done;
    let inside =
      match !inside with [ entry ] -> entry | _ -> restrict head (Logic.Boolean false)
    in
    (* The measures the loop writes, or else one guessed from its condition, where that is
       a comparison: the distance between its operands. *)
    let measure_terms (at : frame) =
      let read measure = snd (specification_value context { at with checking = false } measure) in
      match (measures_of clauses, natural.compared) with
      | Some measures, _ -> Some (List.map read measures)
      | None, Some { comparison; left; right } -> (
          let left = read left and right = read right in
          let distance from into = Logic.Operation ("-", [ into; from ]) in
          let through distance = Logic.Operation ("+", [ distance; Logic.int 1 ]) in
          match comparison with
          | Less -> Some [ distance left right ]
          | Less_equal -> Some [ through (distance left right) ]
          | Greater -> Some [ distance right left ]
          | Greater_equal -> Some [ through (distance right left) ]
          | Equal | Not_equal -> None)
      | None, None -> None
    in
    let start_measures = if context.terminates then measure_terms inside else None in
    if context.terminates && start_measures = None then
      oblige context inside Termination span "This loop may not end: give it a `decreases` clause."
        (Logic.Boolean false);
    let most =
      match (start_measures, measure_terms frame, iterations) with
      | Some [ at_head ], Some [ on_entry ], Some iterations ->
          let last = fresh context head "last" Logic.Int in
          assume context head
            Logic.(
              equal iterations (int 0)
              ==> Operation ("<=", [ at_head; on_entry ])
              &&& (Operation (">=", [ iterations; int 1 ])
                  ==> (Operation ("<=", [ int 0; last ])
                      &&& Operation
                            ( "<=",
                              [
                                Operation ("+", [ Operation ("-", [ iterations; int 1 ]); last ]);
                                on_entry;
                              ] )
                      &&& Operation ("<", [ at_head; last ]))));
          [ Costs.at_least_zero (Costs.plus on_entry (Logic.int 1)) ]
      | _ -> []
    in
    let ends = List.rev !ends in
    let breaks = List.rev !breaks in
    loop_iterations context natural.loop.origin top costs ~mark
      ~facts:(facts_since context facts_mark @ [ inside.condition ])
      ~ends ~breaks:(List.map snd breaks);
    List.iter
      (fun (end_ : frame) ->
        check_invariants context end_ clauses ~when_:"after an iteration";
        check_preserved_validity context end_ span preserved;
        match (start_measures, measure_terms end_) with
        | Some before, Some after ->
            oblige context end_ Termination span "This loop's measure may not decrease."
              (lexicographically_less before after)
        | _ -> ())
      ends;
    List.iter
      (fun (target, (failing : frame)) ->
        jump target (loop_exit context failing costs ~iterations ~most))
      (List.rev !failed);
    List.iter
      (fun (target, (leaving : frame)) ->
        jump target
          (loop_exit context leaving costs
             ~iterations:(Option.map (fun count -> Costs.plus count (Logic.int 1)) iterations)
             ~most))
      breaks
  in
  incoming.(0) <- [ start ];
  run_region
    ~inside:(fun _ -> true)
    ~jump:(fun target frame -> incoming.(target) <- frame :: incoming.(target))
    ~iteration_end:(fun _ -> bug "the end of an iteration outside a loop")
