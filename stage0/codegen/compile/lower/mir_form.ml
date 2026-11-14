(* Lowers a body from its MIR to C. The MIR has made every
   decision about the order of evaluation, the scope of temporaries and
   bindings, and the flow of patterns and loops, so this lowering decides
   only what is C's: pointers, layout, the calling convention, drops,
   and the outlining of [parallel] and [concurrent] code.

   A body is lowered as regions. A region is the code of one body that is
   lowered in one state of the scopes: a whole body, the body of a [for]
   loop, or a branch of a [concurrent] block. Each region lowers each of its
   blocks of the MIR once, the first time a jump reaches it. A jump to a
   block of an enclosing region of the same body leaves the scopes between,
   as a [break] does. *)

open Definitions
open Lowering
open Targets
open Emit_c.Builder

let mir st =
  match st.frame.mir with Some mir -> mir | None -> bug "MIR lowering outside a MIR frame"

let mir_of context path : Mir.t =
  match demand context Mir.of_path path with
  | Some (mir, _) -> mir
  | None -> bug "%s has no MIR" (Path.show path)

(* A parameter's mode, name, and type, from its local. *)
let parameter_of (body : Mir.body) local =
  match body.locals.(local) with
  | { kind = Source { mode; name; _ }; type_; _ } -> (mode, Option.value name ~default:"_", type_)
  | _ -> bug "a parameter that is no source local"

let spans st =
  match demand st.context Names.spans st.frame.code.definition_key with
  | Some spans -> spans
  | None -> bug "no spans for %s" (Path.show st.frame.code.anchor)

let site_of st (origin : Core.origin) =
  let spans = spans st in
  if origin >= 0 && origin < Array.length spans then site st spans.(origin)
  else site st (Syntax.Span.make 0 0)

(* The call site that a check that fails in the code being lowered reports
   instead of its own position: in a lending method of the standard
   library, the one that the caller passed. An index out of bounds is the
   caller's error. *)
let reported_site st : Lowered.operand option =
  match st.frame.mir with
  | Some { lending = Some { site; _ }; _ }
    when Path.package st.frame.code.anchor = Path.standard_package ->
      Some site
  | _ -> None

let info st local = (mir st).body.locals.(local)

let core_local st local =
  match (info st local).kind with Source { local; _ } -> Some local | Temporary | Lent _ -> None

(* Binds a local of the MIR to its place. The place of [self] is also the
   code's own, which the evidence of a capability it implements names. *)
let bind_local st local place =
  Hashtbl.replace (mir st).places local place;
  if core_local st local = Some Self then st.frame.self_place <- Some place

(* Where the value a [return] returns is written: the slot of the
   function's result, or of the value of an expression lowered on its own. *)
let result_slot st =
  match (mir st).returns_into with Some destination -> Some destination | None -> result_place st

(* A new C local for a local of the MIR. A temporary that a [return]
   returns is the result's slot. *)
let rec fresh_place st local : Lowered.place =
  match result_slot st with
  | Some slot when List.mem local (mir st).returned ->
      bind_local st local slot;
      slot
  | _ -> new_place st local

and new_place st local : Lowered.place =
  let ty = ground st (info st local).type_ in
  let name = match core_local st local with Some _ -> Some "binding" | None -> None in
  let place = held st ?name (Value ty) in
  bind_local st local place;
  place

(* The place of a local of the MIR: made when it first holds a value. A
   parameter and a capture are bound before the code runs. *)
let local_place st local : Lowered.place =
  match Hashtbl.find_opt (mir st).places local with
  | Some place -> place
  | None -> fresh_place st local

let binary : Core.comparison -> Lowered.binary = function
  | Equal -> Equal
  | Not_equal -> Not_equal
  | Less -> Less
  | Less_equal -> Less_equal
  | Greater -> Greater
  | Greater_equal -> Greater_equal

let ground_argument st argument =
  Monomorphic.ground_argument st.context.monomorphic st.frame.code.substitution argument

(* The types of an intrinsic's type arguments, and its values. *)
let split_arguments st type_arguments =
  let ground_arguments = List.map (ground_argument st) type_arguments in
  ( List.filter_map (function Ground.Type ty -> Some ty | _ -> None) ground_arguments,
    List.filter_map (function Ground.Value value -> Some value | _ -> None) ground_arguments )

(* Places *)

let place st (written : Mir.place) : Lowered.place =
  let root =
    match written.root with
    | Local local -> local_place st local
    | Constant path -> static_constant st path
  in
  List.fold_left
    (fun place (projection : Mir.projection) ->
      match projection with
      | Field field -> place / Field field
      | Variant_field { variant; field } -> place / Variant_field { variant; field })
    root written.projections

let variants_of st (ty : Ground.ty) : (string option * (string * Ground.ty) list) list =
  let typed fields =
    List.map
      (fun (name, (member : Memory_layout.member)) ->
        match member with
        | Typed field_ty -> (name, field_ty)
        | Raw _ -> bug "a field %s of %s that no Truss type names" name (Ground.to_string ty))
      fields
  in
  match Memory_layout.shape st.context.env ty with
  | Record fields -> [ (None, typed fields) ]
  | Sum variants ->
      List.map
        (fun (variant_shape : Memory_layout.variant_shape) ->
          (Some variant_shape.name, typed variant_shape.fields))
        variants
  | Scalar _ | Array _ -> bug "the fields of %s, which has none" (Ground.to_string ty)

let frame_of_body st ?owner ?returns_into ?lending ?(passed : Ground.mode list option) ~lambdas
    (body : Mir.body) : mir_frame =
  (* How each parameter is passed, where it is not as its binding says: a
     lambda's parameters are patterns, and its function type says how each
     is passed. *)
  let passed local : Types.mode option =
    Option.bind passed (fun modes ->
        Option.map
          (fun position : Types.mode ->
            match List.nth modes position with Ground.Read -> Read | Mut -> Mut | Own -> Own)
          (List.find_index (Int.equal local) body.parameters))
  in
  let needs_drop (path : Moves.path) =
    let rec path_type ty = function
      | [] -> Some ty
      | step :: rest -> (
          let member =
            match (Memory_layout.shape st.context.env ty, (step : Moves.step)) with
            | Record fields, Field name -> List.assoc_opt name fields
            | Sum variants, Variant { variant; field } ->
                Option.bind
                  (List.find_opt
                     (fun (shape : Memory_layout.variant_shape) -> shape.name = variant)
                     variants)
                  (fun (shape : Memory_layout.variant_shape) -> List.assoc_opt field shape.fields)
            | _ -> None
          in
          match member with Some (Typed field_ty) -> path_type field_ty rest | _ -> None)
    in
    match path_type (ground st body.locals.(path.local).type_) path.steps with
    | Some ty -> not (trivial st ty)
    | None -> false
  in
  let moves = Moves.analyse ~passed ~tracks:needs_drop body in
  (* The blocks that run after a lending method has lent its part: they end
     its scopes, and it returns. *)
  let after_lend = Array.make (Array.length body.blocks) false in
  let rec reach block =
    if not after_lend.(block) then begin
      after_lend.(block) <- true;
      List.iter reach (Mir.block_successors body block)
    end
  in
  Array.iter
    (fun (basic : Mir.basic_block) ->
      match basic.terminator with Yield { resume; _ } -> reach resume | _ -> ())
    body.blocks;
  let statements_where in_block select =
    List.concat
      (List.mapi
         (fun block (basic : Mir.basic_block) ->
           if in_block block then List.concat_map select basic.statements else [])
         (Array.to_list body.blocks))
  in
  {
    body;
    lambdas;
    places = Hashtbl.create 32;
    owner;
    returns_into;
    provides = [];
    returned =
      Array.fold_left
        (fun returned (block : Mir.basic_block) ->
          match block.terminator with
          | Return (Some (Use { place = { root = Local local; projections = [] }; _ }))
            when body.locals.(local).kind = Temporary ->
              local :: returned
          | _ -> returned)
        [] body.blocks;
    taken = [];
    moves;
    flags =
      List.map
        (fun (path : Moves.path) -> (path, held st ~name:"owned" (Raw Bool)))
        (Moves.flagged moves);
    state = Moves.entry moves 0;
    lending;
    called_parts =
      statements_where
        (fun _ -> true)
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Lend { call = { callee = Intrinsic _; _ }; _ } -> []
          | Lend { part; _ } -> [ part ]
          | _ -> []);
    lent_calls = Hashtbl.create 4;
    ended_after_lend = statements_where (fun block -> after_lend.(block)) Moves.ended_by;
    after_lend;
    block = 0;
  }

(* Whether the storage of a place of a lending method's body outlives the
   method's call: a part of a parameter that the method borrows, or of a
   constant, or a part that a lending call lent the method from such
   storage. The storage of a value that the method owns does not: the
   method frees it where it returns. A part of a view is stored in the
   view's referent, so a view that the method made is not the part's
   storage. [owns] says whether a local owns its value, and [is_view]
   whether a type holds a view. *)
let outlives_call ~(owns : Mir.local -> bool) ~(is_view : Types.ty -> bool) (body : Mir.body)
    (place : Mir.place) : bool =
  (* A place that an operand reads, and whether its value holds a view. *)
  let operand_place (operand : Mir.operand) =
    match operand with
    | Borrow { place; type_; _ } | Use { place; type_; _ } | Take { place; type_; _ } ->
        Some (place, is_view type_)
    | Constant _ -> None
  in
  (* The places that the result of a call may view: each argument that the
     call borrows, and each view that it is passed. *)
  let viewed_by (call : Mir.call) =
    List.filter_map
      (function
        | Mir.Passed { mode; value; _ } -> (
            match operand_place value with
            | Some (place, holds_view) when holds_view || mode <> Own -> Some (place, holds_view)
            | _ -> None)
        | Default -> None)
      call.arguments
  in
  (* The part of a lending call is a part of the call's receiver, its
     first argument, or it is in the caller's lend record, which outlives
     the call. *)
  let receiver (call : Mir.call) =
    match call.arguments with
    | Passed { mode = Read | Mut; value; _ } :: _ -> Option.to_list (operand_place value)
    | _ -> []
  in
  (* The places that the value of a local is stored in, or that it views
     where [holds_view], from each statement that gives the local a value.
     [None] where one gives it a value that the method made, which the
     method then stores itself. *)
  let sources ~holds_view local : (Mir.place * bool) list option =
    let exception Made in
    let is_local (target : Mir.place) = target = { root = Local local; projections = [] } in
    let given (statement : Mir.statement) =
      match statement.kind with
      | Assign { target; value; _ } when is_local target -> (
          match value with
          | Operand (Borrow { place; _ }) -> [ (place, holds_view) ]
          | Operand ((Use _ | Take _) as operand) when holds_view ->
              Option.to_list (operand_place operand)
          | Construct { fields; _ } when holds_view ->
              List.filter_map
                (fun (_, field) ->
                  match (field : Mir.operand option) with
                  | Some (Borrow { place; _ }) -> Some (place, false)
                  | Some operand ->
                      Option.bind (operand_place operand) (fun (place, holds_view) ->
                          if holds_view then Some (place, true) else None)
                  | None -> None)
                fields
          | _ -> raise Made)
      | Lend { part; call } when part = local ->
          if holds_view then receiver call @ viewed_by call else receiver call
      | Slice { destination; base; call } when is_local destination ->
          [ (base, match receiver call with (_, holds_view) :: _ -> holds_view | [] -> false) ]
      | (Call { destination = Some target; call } | Template { destination = target; call; _ })
        when is_local target ->
          if holds_view then viewed_by call else raise Made
      | _ -> []
    in
    try
      Some
        (Array.fold_left
           (fun places (block : Mir.basic_block) ->
             let places =
               List.fold_left
                 (fun places statement -> given statement @ places)
                 places block.statements
             in
             match block.terminator with
             | For { iteration = Pull { cursor; _ }; part; _ } when part = local && holds_view ->
                 (cursor, true) :: places
             | For { part; _ } when part = local -> raise Made
             | _ -> places)
           [] body.blocks)
    with Made -> None
  in
  let rec outlives seen ~holds_view (place : Mir.place) =
    match place.root with
    | Constant _ -> true
    | Local local when List.mem (local, holds_view) seen -> true
    | Local local -> (
        match body.locals.(local).kind with
        | Source { mode = Read | Mut; _ } when List.mem local body.parameters -> true
        (* A view that the method is passed whole views the caller's
           storage. *)
        | _ when List.mem local body.parameters -> holds_view
        | _ when owns local && not holds_view -> false
        | _ -> (
            match sources ~holds_view local with
            | Some places ->
                List.for_all
                  (fun (place, holds_view) ->
                    outlives ((local, holds_view) :: seen) ~holds_view place)
                  places
            | None -> false))
  in
  outlives [] ~holds_view:false place

let field_of variant field : Lowered.projection =
  match variant with Some variant -> Variant_field { variant; field } | None -> Field field

(* Operands *)

(* The place of a compound assignment's target, whose old value an operator
   takes. The target holds nothing until the statement assigns it again, so
   that assignment drops nothing: an element is not a place the move
   analysis tracks, and a drop would free its old value a second time. *)
let taken st (written : Mir.place) =
  let frame = mir st in
  frame.taken <- written :: frame.taken;
  place st written

let operand_types_ty (operand : Mir.operand) =
  match operand with
  | Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } | Constant { type_; _ } -> type_

(* The type an operand's value has in this instance. *)
let operand_type st operand = ground st (operand_types_ty operand)

let constant st ty (value : Mir.constant) : Lowered.operand =
  match value with
  | Unit -> bug "a unit constant as a value"
  | Integer number -> constant_of st ty (Integer_value number)
  | Float number -> constant_of st ty (Float_value number)
  | Boolean truth -> Constant (Bool truth)
  | String _ -> bug "a string literal as an operand"

(* An operand as a value: copied, moved, or a constant. A string literal is
   written into a temporary first. *)
let value st (operand : Mir.operand) : Lowered.operand =
  let ty = operand_type st operand in
  match operand with
  | Constant { value = String text; _ } ->
      let held = temporary st ty in
      string_literal st ty text ~destination:held;
      owned st held ty
  | Constant { value; _ } -> constant st ty value
  | Use { place = written; _ } -> owned st (place st written) ty
  | Take { place = written; _ } -> owned st (taken st written) ty
  | Borrow { place = written; _ } -> Copy (place st written)

let operand_place st (operand : Mir.operand) : Lowered.place =
  let ty = operand_type st operand in
  match operand with
  | Borrow { place = written; _ } -> place st written
  | Use { place = { root = Local local; projections = [] } as written; _ }
    when (info st local).kind = Temporary ->
      place st written
  | Use { place = written; _ } ->
      let held = temporary st ty in
      take st (place st written) ty ~destination:held;
      held
  | Take { place = written; _ } ->
      let held = temporary st ty in
      take st (taken st written) ty ~destination:held;
      held
  | Constant { value = String text; _ } ->
      let held = temporary st ty in
      string_literal st ty text ~destination:held;
      held
  | Constant { value = Unit; _ } -> temporary st ty
  | Constant { value; _ } ->
      let held = temporary st ty in
      emit st.builder (Assign (held, Use (constant st ty value)));
      held

(* Writes an operand's value to [destination], which holds nothing. *)
let write_operand st (operand : Mir.operand) (destination : Lowered.place) =
  let ty = operand_type st operand in
  match operand with
  | Constant { value = Unit; _ } -> ()
  | Constant { value = String text; _ } -> string_literal st ty text ~destination
  | Constant { value; _ } -> emit st.builder (Assign (destination, Use (constant st ty value)))
  | Use { place = written; _ } -> take st (place st written) ty ~destination
  | Take { place = written; _ } -> take st (taken st written) ty ~destination
  | Borrow { place = written; _ } ->
      emit st.builder (Assign (destination, Use (Copy (place st written))))

let discarded st = temporary st (Monomorphic.builtin Unit)

(* Regions *)

(* The state a block of the MIR starts in, which every jump to it shares:
   the evidence in force and the [provide]s around it. *)
type entry = {
  evidence : (Path.t * Lowered.operand) list;
  provides : (Path.t * Lowered.operand) list list;
}

type region = {
  region_frame : frame;
  region_body : mir_frame;
  lowered : (Mir.block, Lowered.block) Hashtbl.t;
  mutable pending : (Mir.block * Lowered.block * entry) list;
      (** The blocks reached and not yet lowered. The region lowers the first of them in the MIR's
          order, which is reverse postorder, so that every block is lowered after the blocks that
          jump to it, other than by a loop's back edge. A block's code can then read what an earlier
          block's lowering recorded, such as the rest of a lending call that a local's end runs. *)
  depth : int;  (** The number of scopes the region's blocks are lowered in *)
  start : entry;  (** The state the region's code starts in *)
  enclosing : region option;
  ending : (int * Lowered.block) option;
      (** For a branch of a [concurrent] block: the block's fork, and the block its {!Mir.Join} goes
          to *)
}

let save (st : state) = { evidence = st.evidence; provides = (mir st).provides }

let new_region ?ending ?enclosing (st : state) =
  {
    region_frame = st.frame;
    region_body = mir st;
    lowered = Hashtbl.create 16;
    pending = [];
    depth = List.length st.scopes;
    start = save st;
    enclosing;
    ending;
  }

let restore (st : state) (entry : entry) =
  st.evidence <- entry.evidence;
  (mir st).provides <- entry.provides

let rec owner_of region body block =
  if region.region_body == body && Hashtbl.mem region.lowered block then Some region
  else Option.bind region.enclosing (fun enclosing -> owner_of enclosing body block)

(* The C block a jump from [region] to a block of the MIR goes to. A jump
   to a block of an enclosing region leaves the scopes between. *)
let jump ?entry st region target : Lowered.block =
  match owner_of region region.region_body target with
  | Some owner when owner == region -> Hashtbl.find region.lowered target
  | Some owner ->
      let pad = block st.builder in
      let lowered = Hashtbl.find owner.lowered target in
      in_block st.builder pad (fun () ->
          leave_to st owner.depth;
          finish st.builder (Goto lowered));
      pad
  | None ->
      let lowered = block st.builder in
      Hashtbl.replace region.lowered target lowered;
      region.pending <- (target, lowered, Option.value entry ~default:(save st)) :: region.pending;
      lowered

(* Claims a block for a region before code that may jump to it from an
   inner region is lowered. *)
let claim st region target = ignore (jump st region target)

let goto st region target =
  finish st.builder (Goto (jump st region target));
  start st.builder (block st.builder)

let continue_loop st =
  match st.loops with
  | loop :: _ ->
      leave_to st loop.continue_depth;
      finish st.builder (Goto loop.continue_);
      start st.builder (block st.builder)
  | [] -> bug "the end of an iteration outside a loop"

let break_loop st =
  match st.loops with
  | loop :: _ ->
      leave_to st loop.break_depth;
      finish st.builder (Goto loop.break_);
      start st.builder (block st.builder)
  | [] -> bug "a break outside a loop"

(* Drops *)

(* The place of a path of the MIR. *)
let path_place st (path : Moves.path) =
  place st
    {
      root = Local path.local;
      projections =
        List.map
          (function
            | Moves.Field field -> Mir.Field field
            | Variant { variant; field } -> Mir.Variant_field { variant; field })
          path.steps;
    }

let rec drop_path st (path : Moves.path) =
  let frame = mir st in
  match Moves.status frame.moves frame.state path with
  | None -> (
      let place = path_place st path in
      match place_type st place with
      | Some (Value ty) when not (trivial st ty) -> emit st.builder (Drop place)
      | _ -> ())
  | Some Empty -> ()
  | Some Holds -> drop_held st path
  | Some Maybe ->
      let flag =
        match List.assoc_opt path frame.flags with
        | Some flag -> flag
        | None ->
            bug "local %d%s, which may hold nothing, has no flag" path.local
              (String.concat ""
                 (List.map
                    (function
                      | Moves.Field field -> "." ^ field
                      | Variant { variant; field } -> Printf.sprintf ".(%s).%s" variant field)
                    path.steps))
      in
      when_ st.builder (Copy flag) (fun () -> drop_held st path)

(* Drops a path that holds a value. *)
and drop_held st (path : Moves.path) =
  let frame = mir st in
  if
    List.for_all
      (fun inner -> Moves.status frame.moves frame.state inner = Some Holds)
      (Moves.inside frame.moves path)
  then emit st.builder (Drop (path_place st path))
  else drop_parts st path

(* Drops the parts of a path that holds a value, some part of which was moved
   out. *)
and drop_parts st (path : Moves.path) =
  let frame = mir st in
  let place = path_place st path in
  let ty =
    match place_type st place with
    | Some (Value ty) -> ty
    | _ -> bug "a path to drop that holds no value"
  in
  let child step =
    let inner = { path with steps = path.steps @ [ step ] } in
    match place_type st (path_place st inner) with
    | Some (Value inner_ty) when not (trivial st inner_ty) -> drop_path st inner
    | _ -> ()
  in
  match (Memory_layout.of_type st.context.env ty).form with
  | Struct fields ->
      List.iter (fun (field : Memory_layout.field) -> child (Field field.name)) fields
  | Tagged _ | Niche_encoded _ -> (
      let depth = List.length path.steps in
      let inside = Moves.inside frame.moves path in
      let variants =
        List.sort_uniq compare
          (List.filter_map
             (fun (inner : Moves.path) ->
               match List.nth_opt inner.steps depth with
               | Some (Variant { variant; _ }) -> Some variant
               | _ -> None)
             inside)
      in
      let open_variant variant =
        List.iter
          (fun (name, _) -> child (Variant { variant; field = name }))
          (List.assoc (Some variant) (variants_of st ty));
        if
          List.exists
            (fun (shape : Memory_layout.variant_shape) -> shape.name = variant && shape.indirect)
            (match Memory_layout.shape st.context.env ty with Sum shapes -> shapes | _ -> [])
        then emit st.builder (Free_block { place; variant })
      in
      let certain variant =
        List.exists
          (fun (inner : Moves.path) ->
            match List.nth_opt inner.steps depth with
            | Some (Variant { variant = inner_variant; _ }) ->
                inner_variant = variant && Moves.status frame.moves frame.state inner = Some Empty
            | _ -> false)
          inside
      in
      match variants with
      | [] -> emit st.builder (Drop place)
      | [ only ] when certain only -> open_variant only
      | variants ->
          let after = block st.builder in
          let cases =
            List.map
              (fun variant ->
                let case = block st.builder in
                in_block st.builder case (fun () ->
                    open_variant variant;
                    finish st.builder (Goto after));
                (variant, case))
              variants
          in
          let other = block st.builder in
          in_block st.builder other (fun () ->
              emit st.builder (Drop place);
              finish st.builder (Goto after));
          finish st.builder (Switch_variant { place; cases; default = Some other });
          start st.builder after)
  | _ -> emit st.builder (Drop place)

let drop_local st local =
  let path : Moves.path = { local; steps = [] } in
  if Moves.owns (mir st).moves local && Moves.status (mir st).moves (mir st).state path <> None then
    drop_path st path

let update_flags st ~before =
  let frame = mir st in
  List.iter
    (fun ((path : Moves.path), holds) ->
      emit st.builder (Assign (List.assoc path frame.flags, Use (Constant (Bool holds)))))
    (Moves.changed frame.moves ~before ~after:frame.state)

(* Drops the values the function's own parameters still hold, where it
   returns. *)
let drop_parameters st = List.iter (drop_local st) (mir st).body.parameters

let overwritten st (target : Mir.place) (destination : Lowered.place) ty =
  match Moves.path_of_place target with
  | Some path when Moves.status (mir st).moves (mir st).state { path with steps = [] } <> None ->
      drop_path st path
  | _ -> if not (trivial st ty) then emit st.builder (Drop destination)

(* Returns from the function, whose result is already written. In an
   expression lowered on its own, jumps to its end instead. *)
let return_from_frame st =
  (match st.frame.exit with
  | Some (exit, depth) ->
      leave_to st depth;
      finish st.builder (Goto exit)
  | None ->
      drop_parameters st;
      leave_to st 0;
      finish st.builder (return_result st));
  start st.builder (block st.builder)

(* Calls *)

(* The function or method that a callee resolves to in this instance, with
   its type arguments. [None] for a callee that is neither. *)
let resolve_callee st (callee : Mir.callee) : (Path.t * Ground.argument list) option =
  match callee with
  | Function { path; type_arguments } -> Some (path, List.map (ground_argument st) type_arguments)
  | Trait_method { evidence = Dynamic; _ } -> None
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } -> (
      match trait_method_key st ~trait ~name ~receiver ~self_type ~type_arguments ~evidence with
      | Code { path; type_arguments } -> Some (path, type_arguments)
      | _ -> bug "a trait method's key")
  | Capability_method _ | Intrinsic _ | Indirect _ -> None

let resolved st (callee : Mir.callee) =
  match resolve_callee st callee with
  | Some (path, type_arguments) ->
      let signature = signature_of st.context path in
      (path, type_arguments, signature, bind signature.generics type_arguments)
  | None -> bug "a callee that is not a function or a method"

let result_type st (callee : Mir.callee) =
  let path, _, signature, substitution = resolved st callee in
  match signature.output with
  | Returns ty -> Monomorphic.ground st.context.monomorphic substitution ty
  | Lends _ -> bug "%s does not return a value" (Path.show path)

(* Calls a function or a method with arguments that are already in places,
   one for each parameter in order. *)
let call_with_places st (callee : Mir.callee) (places : Lowered.place list) ~destination =
  let path, type_arguments, signature, substitution = resolved st callee in
  let arguments =
    List.map2
      (fun (mode, ty) place ->
        (mode, Monomorphic.ground st.context.monomorphic substitution ty, place))
      (interface_parameters signature) places
  in
  call_instance st
    (Code { path; type_arguments })
    ~signature ~substitution ~arguments ~destination ()

(* Evaluates a call's arguments, one for each of the callee's parameters, in
   order. An omitted argument gets a local that holds nothing, and which
   nothing drops: the callee makes the default its own. The returned mask has one bit for each
   parameter with a default, set where the call passes an argument. *)
let evaluate_arguments st (signature : Types.signature) substitution (arguments : Mir.argument list)
    =
  let parameters = interface_parameters signature in
  if List.length parameters <> List.length arguments then
    bug "a call with %d arguments for %d parameters" (List.length arguments)
      (List.length parameters);
  let receivers = List.length parameters - List.length signature.parameters in
  let mask = ref 0 and defaulted = ref 0 in
  let evaluated =
    List.mapi
      (fun index ((mode, ty), (argument : Mir.argument)) ->
        let ty = Monomorphic.ground st.context.monomorphic substitution ty in
        let bit =
          if index >= receivers && (List.nth signature.parameters (index - receivers)).has_default
          then begin
            incr defaulted;
            Some (!defaulted - 1)
          end
          else None
        in
        match argument with
        | Default -> (mode, ty, at (local st.builder (Value ty)))
        | Passed { value; _ } ->
            Option.iter (fun bit -> mask := !mask lor (1 lsl bit)) bit;
            (mode, ty, operand_place st value))
      (List.combine parameters arguments)
  in
  if !defaulted > 62 then unsupported "a function with more than 62 parameters that have defaults";
  (evaluated, !mask)

(* An argument's mode, type, and place, for a call whose callee has no
   signature to read the parameter's type from. *)
let argument_place st (argument : Mir.argument) =
  match argument with
  | Passed { mode; value; _ } -> (mode, operand_type st value, operand_place st value)
  | Default -> bug "an omitted argument in a call that has no defaults"

let shared_update st ~shared ~input ~change ~destination =
  let _, _, shared = argument_place st shared in
  let _, _, input = argument_place st input in
  let _, change_ty, change = argument_place st change in
  let function_type =
    match change_ty with
    | Function function_type -> function_type
    | ty -> bug "shared_update with a %s, which is not a function" (Ground.to_string ty)
  in
  let value_ty, result_ty =
    match (function_type.parameters, function_type.result) with
    | (_, value_ty) :: _, Returns result_ty -> (value_ty, result_ty)
    | _ -> bug "shared_update with a function that takes no value or returns none"
  in
  let pointer = Lowered.Copy (shared / Field "value") in
  emit st.builder
    (Call { target = Intrinsic Shared_lock; arguments = [ pointer ]; result = Discarded });
  let typed = local st.builder (Pointer { target = Value value_ty; writable = true }) in
  emit st.builder (Assign (at typed, Use pointer));
  let result =
    match destination with Some destination -> destination | None -> temporary st result_ty
  in
  call_indirect st ~function_type ~value:change
    [ { root = Local typed; projections = [ Deref ] }; input ]
    result;
  emit st.builder
    (Call { target = Intrinsic Shared_unlock; arguments = [ pointer ]; result = Discarded })

(* Lowers a call of an intrinsic. Returns the place it lends, for one that
   lends. An intrinsic takes storage and views by place. *)
let intrinsic st ?reported (operation : Intrinsic.operation) ~type_arguments
    (arguments : Mir.argument list) ~destination ~site =
  match (operation, arguments) with
  | Shared_update, [ shared; input; change ] ->
      shared_update st ~shared ~input ~change ~destination;
      None
  | _ ->
      let type_arguments, value_arguments = split_arguments st type_arguments in
      let arguments =
        List.map
          (fun (argument : Mir.argument) ->
            match argument with
            | Passed { value = Borrow _ as borrowed; _ } ->
                Intrinsics.Place (operand_place st borrowed)
            | Passed { value = passed; _ } ->
                let ty = operand_type st passed in
                if Storage.elements_of ty <> None || Storage.viewed ty <> None then
                  Intrinsics.Place (operand_place st passed)
                else Intrinsics.Value (value st passed)
            | Default -> bug "an intrinsic called with an omitted argument")
          arguments
      in
      List.iter
        (fun position ->
          match List.nth arguments position with
          | Intrinsics.Place place -> ignore (moved st place)
          | Value _ -> ())
        (Intrinsics.consumed_places operation);
      Intrinsics.lower ~checks:st.context.checks ~value_arguments ?reported st.context.env
        st.builder st.context.types operation ~type_arguments arguments ~destination ~site

(* The default of a field, from the core form of the type's definition. *)
let field_default st (ty : Ground.ty) ~variant ~field : Core.expression =
  let path =
    match ty with Named { path; _ } -> path | _ -> bug "defaults of %s" (Ground.to_string ty)
  in
  match demand st.context Infer.core_of_path path with
  | Some ({ definition = Type { defaults; _ }; _ }, _) -> (
      match
        List.find_opt (fun (of_variant, name, _) -> of_variant = variant && name = field) defaults
      with
      | Some (_, _, default) -> default
      | None -> bug "%s has no default for %s" (Path.show path) field)
  | _ -> bug "%s has no core form" (Path.show path)

(* Tasks *)

(* A call of the [Tasks] method [name]. [places] holds one argument for
   each parameter, and the call writes its return value to [result]. *)
let tasks_call st name ?result (places : Lowered.place list) : Lowered.statement =
  let capability = Well_known.path Tasks in
  let slot, signature = capability_method st.context capability name in
  let c_signature, convention = entry_signature st.context signature in
  Call
    {
      target =
        Evidence_call
          { evidence = evidence_of st capability; capability; slot; signature = c_signature };
      arguments =
        List.filter_map Fun.id
          (List.map2
             (fun (mode, ty) place ->
               pass st mode (Monomorphic.ground st.context.monomorphic [] ty) place)
             (interface_parameters { signature with receiver = None })
             places);
      result =
        (match result with
        | Some place -> Convention.destination convention place
        | None -> Discarded);
    }

(* Calls a [Tasks] method that returns a [Bool], and gives the result. *)
let tasks_bool st name places : Lowered.operand =
  let result = at (local st.builder (Value st.context.bool)) in
  emit st.builder (tasks_call st name ~result places);
  Copy result

(* Opens a task group, runs [f] with it, and joins it. A scope owns the
   join, so an early exit from [f] joins the group too. The scope's other
   temporaries are dropped after the join, because a task may still read
   them until then. *)
let with_group st (f : Lowered.place -> unit) =
  let scope = open_scope st Statement in
  let group = at (local st.builder ~name:"group" (Value (Monomorphic.builtin UInt64))) in
  emit st.builder (tasks_call st "open" ~result:group []);
  let join = tasks_call st "join" [ group ] in
  let cleanup = Join_group join in
  scope.owned <- [ cleanup ];
  f group;
  emit st.builder join;
  scope.owned <- List.filter (fun owned -> owned != cleanup) scope.owned;
  close_scope st scope

(* The type of the function value that [Tasks.spawn] takes. *)
let task_function_type st : Lowered.ty =
  let _, signature = capability_method st.context (Well_known.path Tasks) "spawn" in
  match signature.parameters with
  | [ _; work; _ ] -> Value (Monomorphic.ground st.context.monomorphic [] work.type_)
  | _ -> bug "Tasks.spawn does not take a group, a function, and an item"

(* Writes the body of a task with [f], as an outlined function given
   [parts]. Every
   exit from the task jumps to [end_block], where the task returns. Gives
   the task's function value, for [Tasks.spawn]. *)
let task_body st ~(id : Core.task) ~group ~parts (f : task -> unit) : Lowered.rvalue =
  let nested, environment =
    outlined st ~parts (fun () ->
        let task =
          { id; group; end_block = block st.builder; scope_depth = List.length st.scopes }
        in
        st.tasks <- task :: st.tasks;
        f task;
        st.tasks <- List.tl st.tasks;
        finish st.builder (Goto task.end_block);
        start st.builder task.end_block;
        finish st.builder (Return None))
  in
  Function_value { code = Nested nested; environment = Some environment }

(* Evidence for the capabilities of one [mut] implementation whose calls
   are mutually exclusive. The implementation's capabilities share one
   mutex, a word in this frame. The evidence for each capability has the
   capability's locking table, the mutex's address as its implementation
   pointer, and the implementation's own evidence and the evidence for
   [Tasks] as its outer evidence. *)
let locked_evidence st ~(tasks : Lowered.operand) (evidence : (Path.t * Lowered.operand) list) =
  let mutex = at (local st.builder ~name:"mutex" (Value (Monomorphic.builtin UInt64))) in
  emit st.builder (Assign (mutex, Use (constant_int UInt64 Z.zero)));
  List.map
    (fun (capability, implementation) ->
      let slot = local st.builder (Evidence 2) in
      emit st.builder
        (Call
           {
             target = Intrinsic Evidence_fill;
             arguments =
               [
                 Address { place = at slot; writable = true };
                 Address { place = mutex; writable = true };
                 Constant (Symbol_address (Locked_table capability));
                 implementation;
                 tasks;
               ];
             result = Discarded;
           });
      (capability, Lowered.Address { place = at slot; writable = false }))
    evidence

(* Lowers an early exit from [task], the innermost task around it. The task
   cancels its group. If it is the first to cancel, it records the exit's
   [number] in [winner] and moves the value it returns, if any, into the
   exit's local, for the code after the group; otherwise it drops the
   value. The task then ends, whether or not it was first. *)
let cancel st ~(task : Core.task) ~winner ~number ~value =
  match st.tasks with
  | current :: _ when current.id = task ->
      let won = block st.builder and lost = block st.builder and after = block st.builder in
      Emit_c.Builder.branch st.builder (tasks_bool st "cancel" [ current.group ]) ~yes:won ~no:lost;
      start st.builder won;
      emit st.builder (Assign (local_place st winner, Use (constant_int UInt32 (Z.of_int number))));
      Option.iter
        (fun (value, ty, slot) ->
          emit st.builder (Assign (local_place st slot, Use (owned st value ty))))
        value;
      finish st.builder (Goto after);
      start st.builder lost;
      Option.iter
        (fun (value, ty, _) -> if not (trivial st ty) then emit st.builder (Drop value))
        value;
      finish st.builder (Goto after);
      start st.builder after;
      leave_to st current.scope_depth;
      finish st.builder (Goto current.end_block);
      start st.builder (block st.builder)
  | _ -> bug "an early exit leaves a task that is not the innermost enclosing task"

(* Spawns one iteration of a [concurrent for] loop as a task. [f] lowers
   the iteration's body, and the task's argument is the current value of
   [loop.item]. If the group is already cancelled, [spawn] returns false:
   [not_spawned] then drops the item, and the enclosing code breaks out of
   the loop that produces the items. *)
let spawn_iteration st (loop : spawn_loop) ~(not_spawned : unit -> unit) (f : unit -> unit) =
  let function_value = local st.builder ~name:"task" (task_function_type st) in
  emit st.builder
    (Assign
       ( at function_value,
         task_body st
           ~id:(Iteration { loop = loop.origin })
           ~group:loop.group ~parts:[ loop.item ]
           (fun task ->
             (* A [continue] of the loop ends the task. A [break] of the loop
                never jumps: it is an early exit that ends the task. *)
             looping st ~continue_:task.end_block ~break_:task.end_block ~depth:task.scope_depth f)
       ));
  let spawned = tasks_bool st "spawn" [ loop.group; at function_value; at loop.item ] in
  let next = block st.builder and cancelled = block st.builder in
  Emit_c.Builder.branch st.builder spawned ~yes:next ~no:cancelled;
  start st.builder cancelled;
  not_spawned ();
  break_loop st;
  start st.builder next

(* Spawns one iteration of a [concurrent for] loop with the value at
   [value]. The value's bytes go into a heap block, the block's address is
   the task's argument, and the task takes the bytes out and frees the
   block. A zero-sized value needs no block.

   If the loop owns the value ([owned]), it is moved, and the task owns
   and drops it. Otherwise the bytes are a bitwise copy of a borrowed
   place, and the task never drops them: the place still owns the memory
   they point to, and it outlives the task. *)
let spawn_with_item st (loop : spawn_loop) (value : Lowered.place) ~owned:is_owned
    ~(each : Lowered.place -> unit) =
  let ty = loop.element in
  let item = at loop.item in
  let boxed = not (is_zero_size st ty) in
  let move_or_copy place : Lowered.operand = if is_owned then owned st place ty else Copy place in
  (* The block's address, read back from the item, and the value's place
     in the block. *)
  let block_of () : Lowered.local * Lowered.place =
    let pointer = local st.builder (Raw (Pointer Opaque)) in
    emit st.builder (Assign (at pointer, Convert (Copy item, Pointer Opaque)));
    let typed = local st.builder (Pointer { target = Value ty; writable = true }) in
    emit st.builder (Assign (at typed, Use (Copy (at pointer))));
    (pointer, { root = Local typed; projections = [ Deref ] })
  in
  let unbox ~dropped_here : Lowered.place =
    if boxed then begin
      let unboxed =
        if is_owned && dropped_here then binding st ty else at (local st.builder (Value ty))
      in
      let pointer, inside = block_of () in
      emit st.builder (Assign (unboxed, Use (move_or_copy inside)));
      emit st.builder
        (Call { target = Intrinsic Free; arguments = [ Copy (at pointer) ]; result = Discarded });
      unboxed
    end
    else at (local st.builder (Value ty))
  in
  if boxed then begin
    let pointer = local st.builder (Raw (Pointer Opaque)) in
    emit st.builder
      (Call
         {
           target = Intrinsic Allocate;
           arguments = [ Constant (Size_of ty); Constant (Alignment_of ty) ];
           result = Returned (at pointer);
         });
    emit st.builder (Assign (item, Convert (Copy (at pointer), Integer UInt64)));
    emit st.builder (Assign (snd (block_of ()), Use (move_or_copy value)))
  end
  else emit st.builder (Assign (item, Use (constant_int UInt64 Z.zero)));
  spawn_iteration st loop
    ~not_spawned:(fun () -> in_scope st (fun () -> ignore (unbox ~dropped_here:true)))
    (fun () -> in_scope st (fun () -> each (unbox ~dropped_here:false)))

(* Lending *)

(* A pointer to the lend record of the C function being written, which the
   lending methods that the function calls add to. A lending method adds
   to its caller's record instead, since it may forward the part of a
   lending call. *)
let lend_record st : Lowered.operand =
  match st.lend_record with
  | Some record -> record
  | None ->
      let record : Lowered.operand =
        Address { place = held st ~name:"lend" Lend; writable = true }
      in
      st.lend_record <- Some record;
      record

(* The lending call that lends [part]. *)
let lent_call st part : lent_call =
  let frame = mir st in
  match Hashtbl.find_opt frame.lent_calls part with
  | Some call -> call
  | None ->
      let call = { mark = held st ~name:"lent" Lend_mark; record = lend_record st } in
      Hashtbl.replace frame.lent_calls part call;
      call

(* Emits an operation on a lending call's mark. *)
let emit_mark st (intrinsic : Lowered.intrinsic) (call : lent_call) =
  emit st.builder
    (Call
       {
         target = Intrinsic intrinsic;
         arguments = [ call.record; Address { place = call.mark; writable = true } ];
         result = Discarded;
       })

(* Whether the block being lowered ends where the method lends [part]
   whole: the method forwards the part of a lending call as its own. *)
let is_forwarded_whole (frame : mir_frame) part =
  match frame.body.blocks.(frame.block).terminator with
  | Yield { part = Part (Borrow { place = { root = Local lent; projections = [] }; _ }); _ } ->
      lent = part
  | _ -> false

(* The cleanup of a part that a lending method built, which runs when the
   lend ends. *)
type deferred =
  | Deferred_drop of Ground.ty  (** Of a value that the method made, which the part owns *)
  | Deferred_write_back of { source : Lowered.place; ty : Ground.ty }
      (** To a place lent [mut], whose bits the part holds until the lend ends *)
  | Deferred_free of string  (** Of the block of an indirect variant that the method built *)

(* Lowering *)

let make_owned_locals st =
  let frame = mir st in
  let parts =
    Array.fold_left
      (fun parts (block : Mir.basic_block) ->
        match block.terminator with For { part; _ } -> part :: parts | _ -> parts)
      [] frame.body.blocks
  in
  Array.iteri
    (fun local _ ->
      if
        Moves.owns frame.moves local
        && (not (List.mem local frame.body.parameters))
        && not (List.mem local parts)
      then ignore (local_place st local))
    frame.body.locals

let rec lower_body ?enclosing st (frame : mir_frame) =
  st.frame <- { st.frame with mir = Some frame };
  List.iter
    (fun path -> emit st.builder (Assign (List.assoc path frame.flags, Use (Constant (Bool true)))))
    (Moves.held_at_entry frame.moves);
  run_region st (new_region ?enclosing st) ~entry:(0, 0)

and run_region st region ~entry:(block, index) =
  let caller = st.frame in
  st.frame <- region.region_frame;
  lower_from st region block index;
  let rec drain () =
    match
      List.fold_left
        (fun first ((block, _, _) as next) ->
          match first with Some (earliest, _, _) when earliest <= block -> first | _ -> Some next)
        None region.pending
    with
    | None -> ()
    | Some (next, lowered, entry) ->
        region.pending <- List.filter (fun (block, _, _) -> block <> next) region.pending;
        restore st entry;
        in_block st.builder lowered (fun () ->
            lower_from st region next 0;
            finish st.builder Unreachable);
        drain ()
  in
  drain ();
  st.frame <- caller

and lower_from st region block index =
  let basic = (mir st).body.blocks.(block) in
  st.frame <- region.region_frame;
  let frame = mir st in
  frame.block <- block;
  frame.state <- Moves.entry frame.moves block;
  if index = 0 then
    List.iter
      (fun path ->
        emit st.builder (Assign (List.assoc path frame.flags, Use (Constant (Bool true)))))
      (Moves.given_on_entry frame.moves block);
  List.iteri
    (fun position (statement : Mir.statement) ->
      if position >= index then begin
        let before = Moves.copy frame.state in
        (* A statement's moves happen before it gives its destination a
           value, which drops what the destination held. *)
        Moves.apply_moves frame.moves frame.state statement;
        in_statement st (fun () -> lower_statement st statement);
        Moves.apply frame.moves frame.state statement;
        update_flags st ~before
      end
      else Moves.apply frame.moves frame.state statement)
    basic.statements;
  let before = Moves.copy frame.state in
  Moves.apply_terminator_moves frame.moves frame.state basic;
  update_flags st ~before;
  terminator st region basic.terminator ~origin:basic.terminator_origin

(* A [concurrent] block. Each branch is a task, an outlined function, and
   the code after them spawns each as a task of one group. The block's end
   follows, if a branch reaches it. *)
and concurrent_block st region ~fork ~(branches : Mir.branch list) ~join =
  let function_type = task_function_type st in
  let item = local st.builder (Value (Monomorphic.builtin UInt64)) in
  emit st.builder (Assign (at item, Use (constant_int UInt64 Z.zero)));
  with_group st (fun group ->
      let functions =
        List.mapi
          (fun index (branch : Mir.branch) ->
            task_body st
              ~id:(Branch { block = fork; index })
              ~group ~parts:[ item ]
              (fun task ->
                let inner = new_region st ~enclosing:region ~ending:(fork, task.end_block) in
                run_region st inner ~entry:(branch.entry, 0)))
          branches
      in
      (* [spawn] returns false once the group is cancelled, and the branch
         then never runs. *)
      List.iter
        (fun code ->
          let function_value = at (local st.builder ~name:"task" function_type) in
          emit st.builder (Assign (function_value, code));
          ignore (tasks_bool st "spawn" [ group; function_value; at item ]))
        functions);
  match join with Some join -> goto st region join | None -> unreachable_block st

and lower_statement st (statement : Mir.statement) =
  let origin = statement.origin in
  match statement.kind with
  | Assign { target; value; _ } -> assign st target value ~origin
  | Call { destination; call } ->
      let destination =
        match destination with
        | Some written ->
            let destination = place st written in
            (match place_type st destination with
            | Some (Value ty) -> overwritten st written destination ty
            | _ -> ());
            destination
        | None -> discarded st
      in
      call_into st call destination ~origin
  | Lend { part; call } -> lend st part call ~origin
  | Slice { destination; call; _ } | Template { destination; call; _ } ->
      call_into st call (place st destination) ~origin
  | Live _ | Loan_start _ | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ -> ()
  | Dead locals -> List.iter (dead st) locals
  | Assert { condition; _ } ->
      let holds = value st condition in
      let failed = block st.builder and after = block st.builder in
      Emit_c.Builder.branch st.builder holds ~yes:after ~no:failed;
      start st.builder failed;
      let text =
        match condition with
        | Constant { value = Boolean truth; _ } -> string_of_bool truth
        | Use { origin; _ } | Borrow { origin; _ } | Take { origin; _ } ->
            source st (spans st).(origin)
        | Constant _ -> source st (spans st).(origin)
      in
      let message = "assert " ^ text in
      finish st.builder
        (Fail
           {
             failure = Assertion;
             message = Constant (Bytes message);
             length = usize (String.length message);
             site = site_of st origin;
             reported = None;
           });
      start st.builder after
  | Echo echoed ->
      echo st (operand_place st echoed) (operand_type st echoed) ~site:(site_of st origin)
  | Provide { provided; can_use_tasks } -> provide st provided ~can_use_tasks
  | Provide_end -> (
      let frame = mir st in
      match frame.provides with
      | enclosing :: rest ->
          st.evidence <- enclosing;
          frame.provides <- rest
      | [] -> bug "the end of a provide that did not start")

(* The end of a local. The part of a lending call ends its lend: the
   cleanup that the call deferred runs. Where the method has lent its own
   part, it may have forwarded the call's part, so that cleanup stays in
   the caller's record and runs when the method's lend ends. *)
and dead st local =
  let frame = mir st in
  if List.mem local frame.called_parts then
    emit_mark st
      (if frame.after_lend.(frame.block) then Lend_transfer else Lend_release)
      (lent_call st local)
  else drop_local st local

and provide st (provided : Mir.provided list) ~can_use_tasks =
  (* The body runs with the evidence of each implementation added. *)
  let enclosing = st.evidence in
  let implementations =
    List.map
      (fun (implementation : Mir.provided) ->
        let place =
          match implementation.value with
          | Use { place = written; _ } | Borrow { place = written; _ } -> place st written
          | value -> operand_place st value
        in
        let pointer =
          if is_zero_size st (ground st implementation.type_) then Lowered.Constant Null
          else Address { place; writable = true }
        in
        ( implementation.mode,
          provided_evidence st ~implementation:pointer
            (List.map
               (fun (provided : Core.provided) ->
                 (provided.capability, provided.impl, provided.arguments))
               implementation.provides) ))
      provided
  in
  (* Several tasks may call a [mut] implementation at the same time when the
     body can use [Tasks], which would be a data race on the
     implementation. Its evidence is then replaced by evidence whose table
     locks a mutex around each call. The locks go through the [Tasks] that
     this [provide] lists, or else the enclosing one, so that a scheduler
     sees them. An implementation of [Tasks] is never locked: it guards its
     own state. *)
  let is_tasks (capability, _) = Path.equal capability (Well_known.path Tasks) in
  let tasks =
    if can_use_tasks then
      Option.map snd (List.find_opt is_tasks (List.concat_map snd implementations @ enclosing))
    else None
  in
  let added =
    List.concat_map
      (fun ((mode : Types.mode), evidence) ->
        match tasks with
        | Some tasks when mode = Mut && not (List.exists is_tasks evidence) ->
            locked_evidence st ~tasks evidence
        | _ -> evidence)
      implementations
  in
  let frame = mir st in
  frame.provides <- enclosing :: frame.provides;
  st.evidence <- added @ enclosing

(* The type of the value an assignment writes to its target. *)
and target_type st (target : Mir.place) (value : Mir.rvalue) =
  match (target, value) with
  | _, Operand operand -> operand_type st operand
  | _ -> mir_place_type st target

and mir_place_type st (written : Mir.place) =
  match written with
  | { root = Local local; projections = [] } -> ground st (info st local).type_
  | _ -> (
      match place_type st (place st written) with
      | Some (Value ty) -> ty
      | _ -> bug "a place of no known type")

and assign st (target : Mir.place) (value : Mir.rvalue) ~origin =
  let frame = mir st in
  match (target, value) with
  | { root = Local local; projections = [] }, Operand (Borrow { place = source; mode; _ })
    when Moves.places_given frame.moves local > 0 ->
      alias st local (place st source) ~writable:(mode = Mut)
  | _ -> (
      let ty = target_type st target value in
      let types_ty =
        match target with
        | { root = Local local; projections = [] } -> Some (info st local).type_
        | _ -> None
      in
      let reads_target =
        match target.root with Local local -> reads value local | Constant _ -> false
      in
      let evaluated =
        if reads_target then begin
          let fresh = temporary st ty in
          into ?types_ty st value fresh ty ~origin;
          Some fresh
        end
        else None
      in
      let destination = place st target in
      let frame = mir st in
      if List.mem target frame.taken then
        frame.taken <- List.filter (fun taken -> taken <> target) frame.taken
      else overwritten st target destination ty;
      match evaluated with
      | Some fresh -> emit st.builder (Assign (destination, Use (owned st fresh ty)))
      | None -> into ?types_ty st value destination ty ~origin)

(* Whether an rvalue reads a local. *)
and reads (value : Mir.rvalue) local =
  let in_place (written : Mir.place) = written.root = Local local in
  let in_operand (operand : Mir.operand) =
    match operand with
    | Use { place; _ } | Borrow { place; _ } | Take { place; _ } -> in_place place
    | Constant _ -> false
  in
  match value with
  | Operand operand | Not operand | Copy operand -> in_operand operand
  | Convert { value; _ } | To_any { value; _ } -> in_operand value
  | Operation { operands; _ } | Array operands -> List.exists in_operand operands
  | Compare { left; right; _ } -> in_operand left || in_operand right
  | Construct { fields; _ } ->
      List.exists (fun (_, field) -> Option.fold ~none:false ~some:in_operand field) fields
  | Is_variant { place; _ } -> in_place place
  | Function_value _ | Lambda _ | Value_parameter _ -> false

and alias st local (source : Lowered.place) ~writable =
  let ty = ground st (info st local).type_ in
  if Moves.places_given (mir st).moves local > 1 then begin
    let frame = mir st in
    let pointer =
      match Hashtbl.find_opt frame.places local with
      | Some { root = Local pointer; projections = [ Deref ] } -> at pointer
      | Some { root = Local pointer; projections = [ Deref; Field field; Deref ] } ->
          { root = Local pointer; projections = [ Deref; Field field ] }
      | _ ->
          let pointer = held st ~name:"binding" (Pointer { target = Value ty; writable }) in
          bind_local st local (pointer / Deref);
          pointer
    in
    emit st.builder (Assign (pointer, Use (Address { place = source; writable })))
  end
  else if
    (not writable)
    && (match (Memory_layout.of_type st.context.env ty).form with Scalar _ -> true | _ -> false)
    && match (info st local).kind with Source _ -> true | Temporary | Lent _ -> false
  then begin
    let copy = held st ~name:"binding" (Value ty) in
    emit st.builder (Assign (copy, Use (Copy source)));
    bind_local st local copy
  end
  else bind_local st local (snapshot st source)

and into ?types_ty st (rvalue : Mir.rvalue) (destination : Lowered.place) ty ~origin =
  let assign built = emit st.builder (Assign (destination, built)) in
  match rvalue with
  | Operand operand -> write_operand st operand destination
  | Operation { operation; type_arguments; operands } ->
      let type_arguments, value_arguments = split_arguments st type_arguments in
      ignore
        (Intrinsics.lower ~checks:st.context.checks ~value_arguments ?reported:(reported_site st)
           st.context.env st.builder st.context.types operation ~type_arguments
           (List.map
              (fun operand ->
                let operand_ty = operand_type st operand in
                if Storage.elements_of operand_ty <> None || Storage.viewed operand_ty <> None then
                  Intrinsics.Place (operand_place st operand)
                else Intrinsics.Value (value st operand))
              operands)
           ~destination:(Some destination) ~site:(site_of st origin))
  | Compare { comparison; left; right } ->
      assign (Binary (binary comparison, value st left, value st right))
  | Not inner -> assign (Unary (Not, value st inner))
  | Construct { variant; fields } ->
      let fields =
        List.map
          (fun (name, (field : Mir.operand option)) ->
            match field with
            | Some field -> (name, value st field)
            | None ->
                let default, default_ty = field_default_place st ty ~variant ~field:name in
                (name, owned st default default_ty))
          fields
      in
      assign (Build { ty; variant; fields })
  | Array elements ->
      List.iteri
        (fun index element ->
          emit st.builder (Assign (destination / Index (usize index), Use (value st element))))
        elements
  | Is_variant { place = tested; variant } -> assign (Is_variant (place st tested, variant))
  | Convert { conversion = Widen; value = inner } ->
      (* A function value has the same representation at a wider type. *)
      write_operand st inner destination
  | Convert { conversion = To_integer | From_integer; _ } ->
      bug "a conversion that exists only in specifications"
  | To_any { value = inner; trait; evidence } ->
      let impl, type_arguments =
        resolve_impl st ~trait ~self_type:(operand_types_ty inner) ~evidence
      in
      any_into st ~any_ty:ty ~inner_ty:(operand_type st inner) ~impl ~type_arguments
        ~value:(operand_place st inner) destination
  | Copy source ->
      Glue.copy_into st.context.glue st.builder ~destination ~source:(operand_place st source) ty
  | Function_value { path; type_arguments } -> (
      (* A named function as a value: an adapter that takes an environment
         and ignores it. *)
      match ty with
      | Function function_type ->
          let function_ =
            Instance.Code { path; type_arguments = List.map (ground_argument st) type_arguments }
          in
          assign
            (Function_value
               { code = Instance (Adapter { function_; ty = function_type }); environment = None })
      | _ -> bug "a function value of type %s" (Ground.to_string ty))
  | Value_parameter parameter -> (
      match ground_argument st (Value (Value_parameter parameter)) with
      | Value number -> assign (Use (constant_of st ty (Integer_value number)))
      | _ -> bug "the value parameter %s is not a number" parameter.name)
  | Lambda { body = index; captures; _ } ->
      let function_type =
        match ty with
        | Function function_type -> function_type
        | _ -> bug "a lambda of %s" (Ground.to_string ty)
      in
      let lambdas = (mir st).lambdas in
      let lambda = lambdas.(index) in
      nested_function st ~function_type
        ~output:
          (match types_ty with
          | Some (Types.Function function_type) -> Some function_type.output
          | _ -> None)
        ~captures:
          (List.map
             (fun (capture : Mir.capture) -> (place st capture.place, ground st capture.type_))
             captures)
        ~body:(fun inner ~captures:capture_places parameter_places ->
          inner.frame <-
            {
              inner.frame with
              mir =
                Some
                  (frame_of_body inner ~owner:(innermost_scope inner)
                     ~passed:(List.map (fun (_, mode, _) -> mode) parameter_places)
                     ~lambdas lambda);
            };
          List.iter2 (bind_local inner) lambda.captures capture_places;
          make_owned_locals inner;
          List.iter2
            (fun local (place, _, _) -> bind_local inner local place)
            lambda.parameters parameter_places;
          lower_body inner (Option.get inner.frame.mir))
        destination

(* A field's default value and its type, evaluated in the type's
   definition, where the default is written. *)
and field_default_place st ty ~variant ~field =
  let default = field_default st ty ~variant ~field in
  in_type_definition st ty (fun () ->
      let default_ty = ground st default.type_ in
      let place = temporary st default_ty in
      expression_into st default place;
      (place, default_ty))

(* Evaluates a core expression that runs on its own, such as a default, and
   writes its value to [destination], from the expression's MIR. [arguments]
   are the parameters it reads, with their places. *)
and expression_into ?(arguments = []) st (expression : Core.expression)
    (destination : Lowered.place) =
  mir_into st
    (Mir.of_expression ~parameters:(List.map fst arguments) expression)
    ~arguments:(List.map snd arguments) destination

(* Lowers the MIR of one expression, with its parameters bound to
   [arguments], into [destination]. *)
and mir_into ?(arguments = []) st (expression_mir : Mir.t) (destination : Lowered.place) =
  let expression_mir = Loop_parts.ended expression_mir in
  let caller = st.frame in
  let exit = block st.builder in
  let frame =
    frame_of_body st ~returns_into:destination ~lambdas:expression_mir.lambdas expression_mir.body
  in
  st.frame <- { caller with exit = Some (exit, List.length st.scopes); mir = Some frame };
  List.iter2 (bind_local st) expression_mir.body.parameters arguments;
  lower_body st frame;
  finish st.builder Unreachable;
  start st.builder exit;
  st.frame <- caller

and call_into st (call : Mir.call) destination ~origin =
  match (resolve_callee st call.callee, call.callee) with
  | Some (path, type_arguments), _ -> (
      let signature = signature_of st.context path in
      let substitution = bind signature.generics type_arguments in
      let arguments, mask = evaluate_arguments st signature substitution call.arguments in
      match signature.output with
      | Returns _ ->
          call_instance st
            (Code { path; type_arguments })
            ~signature ~substitution ~arguments ~mask ~destination ()
      | Lends _ -> bug "a lending call that lends no part")
  | None, Intrinsic { operation; type_arguments } -> (
      match
        intrinsic st operation ~type_arguments call.arguments ~destination:(Some destination)
          ~site:(site_of st origin)
      with
      | Some _ -> bug "a lending intrinsic that lends no part"
      | None -> ())
  | None, Capability_method { capability; name } ->
      let slot, signature = capability_method st.context capability name in
      let arguments, _ =
        evaluate_arguments st { signature with receiver = None } [] call.arguments
      in
      capability_defaults st ~capability ~name call.arguments arguments;
      if Path.equal capability panic_path then
        (* [Panic.crash] has no evidence: it ends the process at once. *)
        match arguments with
        | [ (_, _, message) ] ->
            ignore
              (Intrinsics.lower ~checks:st.context.checks st.context.env st.builder st.context.types
                 Crash ~type_arguments:[] [ Intrinsics.Place message ] ~destination:None
                 ~site:(site_of st origin))
        | _ -> bug "Panic.crash takes one message"
      else begin
        let c_signature, result = entry_signature st.context signature in
        let target =
          Lowered.Evidence_call
            { evidence = evidence_of st capability; capability; slot; signature = c_signature }
        in
        emit st.builder
          (Call
             {
               target;
               arguments =
                 List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments;
               result = Convention.destination result destination;
             });
        if not c_signature.returns then unreachable_block st
      end
  | None, Trait_method { trait; name; self_type; _ } -> (
      (* Through an [any] value, which is the receiver. *)
      let any_type =
        match Types.substitute st.frame.code.substitution self_type with
        | Types.Any reference -> reference
        | receiver -> bug "a call through any on %s" (Types.show receiver)
      in
      match List.map (argument_place st) call.arguments with
      | (_, _, any) :: arguments ->
          call_through_any st ~any_type ~trait:trait.trait ~name ~any ~arguments destination
      | [] -> bug "a call through any with no receiver")
  | None, Indirect function_value ->
      let function_type =
        match operand_type st function_value with
        | Function function_type -> function_type
        | callee_ty -> bug "a call of %s" (Ground.to_string callee_ty)
      in
      let value = operand_place st function_value in
      call_indirect st ~function_type ~value
        (List.map
           (fun argument ->
             let _, _, place = argument_place st argument in
             place)
           call.arguments)
        destination
  | None, Function _ -> bug "a function that does not resolve"

(* Evaluates the default of each argument that a call of a capability method
   omits, into the temporary [evaluate_arguments] gave it. The caller
   evaluates these defaults: an entry of a capability's table takes every
   argument, and there is no one implementation to evaluate them. A default
   is written in the capability's definition, so it is lowered in that
   definition's frame. *)
and capability_defaults st ~capability ~name (arguments : Mir.argument list) evaluated =
  if List.mem Mir.Default arguments then begin
    let receiver =
      match demand st.context Environment.trait_interface capability with
      | Some interface -> (
          match
            List.find_opt
              (fun (trait_method : Types.trait_method) -> trait_method.method_name = name)
              interface.methods
          with
          | Some declared -> declared.method_receiver
          | None -> bug "%s has no method %s" (Path.show capability) name)
      | None -> bug "no interface for %s" (Path.show capability)
    in
    let path : Path.t = Method { owner = capability; name; receiver } in
    let parameters =
      match demand st.context Infer.core_of_path path with
      | Some ({ definition = Function { parameters; _ }; _ }, _) -> parameters
      | _ -> bug "%s has no core form" (Path.show path)
    in
    let key = key_of st.context capability in
    let caller = st.frame in
    st.frame <-
      {
        caller with
        code =
          {
            caller.code with
            definition_key = key;
            anchor = capability;
            enclosing_impl = None;
            text = text_of st.context key;
            substitution = [];
          };
        self_place = None;
      };
    List.iter2
      (fun (parameter : Core.parameter) ((argument : Mir.argument), (_, ty, place)) ->
        match (argument, parameter.default) with
        | Default, Some default ->
            expression_into st default place;
            if not (trivial st ty) then
              (innermost_scope st).owned <- Drop_value place :: (innermost_scope st).owned
        | Default, None -> bug "%s is omitted and has no default" parameter.name
        | Passed _, _ -> ())
      parameters
      (List.combine arguments evaluated);
    st.frame <- caller
  end

and lend st part (call : Mir.call) ~origin =
  match call.callee with
  | Intrinsic { operation; type_arguments } ->
      in_statement st (fun () ->
          match
            intrinsic st operation ~type_arguments call.arguments ~destination:None
              ?reported:(reported_site st) ~site:(site_of st origin)
          with
          | Some place -> bind_local st part place
          | None -> bug "a lent place from an intrinsic that does not lend")
  | callee ->
      let frame = mir st in
      let lent = lent_call st part in
      (* The callee's trailing arguments, for a part of the type [part_ty].
         A method that forwards the part whole passes its caller's slot. A
         part that may still be lent when the method lends its own has no
         slot of this function's, which would be freed by then: the callee
         allocates from the record. *)
      let lending part_ty : Lowered.operand list =
        (if is_zero_size st part_ty then []
         else
           [
             (match frame.lending with
             | Some { slot = Some slot; part = own; _ }
               when is_forwarded_whole frame part && Ground.compare own part_ty = 0 ->
                 Lowered.Copy slot
             | Some _ when List.mem part frame.ended_after_lend -> Constant Null
             | _ -> Address { place = held st ~name:"lent" (Value part_ty); writable = true });
           ])
        @ [
            lent.record;
            (* The call site that the callee reports a failed check at. A
               lending method of the standard library forwards its own. *)
            Option.value (reported_site st) ~default:(Constant (Site (site_of st origin)));
          ]
      in
      (* Calls the callee, whose result is the lent place. *)
      let lent_place (output : Types.result) substitution called =
        let mode, part_ty =
          match output with
          | Lends (mode, ty) -> (mode, Monomorphic.ground st.context.monomorphic substitution ty)
          | Returns _ -> bug "a lending call of a method that does not lend"
        in
        emit_mark st Lend_begin lent;
        if is_zero_size st part_ty then begin
          called ~lending:(lending part_ty) (discarded st);
          held st (Value part_ty)
        end
        else begin
          let pointer =
            held st ~name:"part" (Pointer { target = Value part_ty; writable = mode = Mut })
          in
          called ~lending:(lending part_ty) pointer;
          pointer / Deref
        end
      in
      let place =
        match (resolve_callee st callee, callee) with
        | Some (path, type_arguments), _ ->
            let signature = signature_of st.context path in
            let substitution = bind signature.generics type_arguments in
            let arguments, mask = evaluate_arguments st signature substitution call.arguments in
            lent_place signature.output substitution (fun ~lending destination ->
                call_instance st
                  (Code { path; type_arguments })
                  ~signature ~substitution ~arguments ~mask ~lending ~destination ())
        | None, Trait_method { trait; name; self_type; _ } -> (
            (* Through an [any] value, which is the receiver. *)
            let any_type =
              match Types.substitute st.frame.code.substitution self_type with
              | Types.Any reference -> reference
              | receiver -> bug "a call through any on %s" (Types.show receiver)
            in
            let _, signature = dynamic_slot st.context trait.trait name in
            match List.map (argument_place st) call.arguments with
            | (_, _, any) :: arguments ->
                lent_place signature.output (any_substitution st.context ~any:any_type trait.trait)
                  (fun ~lending destination ->
                    call_through_any st ~any_type ~trait:trait.trait ~name ~any ~arguments ~lending
                      destination)
            | [] -> bug "a call through any with no receiver")
        | None, (Capability_method _ | Indirect _) ->
            unsupported ~at:(site_of st origin)
              "a lending call of a capability's method or of a function value"
        | None, (Function _ | Intrinsic _) -> bug "a lending call that does not resolve"
      in
      emit_mark st Lend_called lent;
      bind_local st part place

(* Where a lending method lends its part: writes the pointer to the part as
   the function's result. A place that outlives the call is lent by its
   address. Any other part is built in the caller's slot: a constructor, a
   value that the method made, or a copy of a [Plain] value. The cleanup of
   a built part is deferred to the end of the lend, in the caller's
   record: a value that the method made is dropped, and a place lent [mut]
   is written back from the part, which holds its bits until then. *)
and lend_part st ~(mode : Types.mode) (part : Mir.yielded) =
  let frame = mir st in
  let lending =
    match frame.lending with
    | Some lending -> lending
    | None -> bug "a part lent outside a lending method"
  in
  let owns = Moves.owns frame.moves in
  let outlives =
    outlives_call ~owns
      ~is_view:(fun ty ->
        Interface.Impls.is_view st.context.database
          ~bounds:(fun _ -> [])
          (Types.substitute st.frame.code.substitution ty))
      frame.body
  in
  (* The place to lend by its address: one that outlives the call and that
     this function reaches through a pointer. A parameter passed by value
     is a copy in a local of this function, whose lifetime ends at return. *)
  let lent_in_place (written : Mir.place) : Lowered.place option =
    let lowered = place st written in
    let is_reached_through_pointer =
      match lowered.root with
      | Static _ -> true
      | Local _ -> List.exists (function Lowered.Deref -> true | _ -> false) lowered.projections
    in
    if outlives written && is_reached_through_pointer then Some lowered else None
  in
  (* Writes a part to [destination], which holds nothing. Gives the part's
     deferred cleanup, each with its place in the part. *)
  let rec write (yielded : Mir.yielded) (destination : Lowered.place) :
      (Lowered.projection list * deferred) list =
    match yielded with
    | Part operand -> (
        let ty = operand_type st operand in
        let made () = if trivial st ty then [] else [ ([], Deferred_drop ty) ] in
        match operand with
        | Borrow { place = { root = Local local; projections = [] } as written; _ } when owns local
          ->
            take st (place st written) ty ~destination;
            made ()
        | Borrow { place = written; _ } -> (
            emit st.builder (Assign (destination, Use (Copy (place st written))));
            match (lent_in_place written, mode) with
            | Some source, Mut -> [ ([], Deferred_write_back { source; ty }) ]
            | Some _, (Read | Own) -> []
            | None, Mut when outlives written ->
                bug "a place lent `mut` that is not reached through a pointer"
            | None, _ ->
                (* The bits of a place that outlives the call, or a copy of a
                   part of a value that the method owns, which the ownership
                   check has shown is [Plain]. *)
                if not (outlives written || trivial st ty) then
                  bug "a lent part of %s that the method owns" (Ground.to_string ty);
                [])
        | Use _ | Take _ | Constant _ ->
            write_operand st operand destination;
            made ())
    | Built { variant; fields; type_; _ } ->
        let ty = ground st type_ in
        let field_types = List.assoc variant (variants_of st ty) in
        let built =
          List.map
            (fun (name, (field : Mir.yielded option)) ->
              let field_ty = List.assoc name field_types in
              let value = held st (Value field_ty) in
              let deferred =
                match field with
                | Some field -> write field value
                | None ->
                    let default, default_ty = field_default_place st ty ~variant ~field:name in
                    take st default default_ty ~destination:value;
                    if trivial st default_ty then [] else [ ([], Deferred_drop default_ty) ]
              in
              ( (name, if trivial st field_ty then Lowered.Copy value else Move value),
                List.map
                  (fun (inside, deferred) -> (field_of variant name :: inside, deferred))
                  deferred ))
            fields
        in
        emit st.builder (Assign (destination, Build { ty; variant; fields = List.map fst built }));
        let is_indirect variant =
          List.exists
            (fun (shape : Memory_layout.variant_shape) -> shape.name = variant && shape.indirect)
            (match Memory_layout.shape st.context.env ty with Sum shapes -> shapes | _ -> [])
        in
        (* The block is freed after the fields in it are dropped: the record
           runs the cleanup deferred last first. *)
        (match variant with
          | Some variant when is_indirect variant -> [ ([], Deferred_free variant) ]
          | _ -> [])
        @ List.concat_map snd built
  in
  let defer_call intrinsic arguments =
    emit st.builder
      (Call
         {
           target = Intrinsic intrinsic;
           arguments = lending.record :: arguments;
           result = Discarded;
         })
  in
  let address place : Lowered.operand = Address { place; writable = true } in
  let defer (slot : Lowered.place) (inside, deferred) =
    let target = List.fold_left ( / ) slot inside in
    match deferred with
    | Deferred_drop ty ->
        defer_call Lend_defer_drop [ Constant (Symbol_address (Drop ty)); address target ]
    | Deferred_write_back { source; ty } ->
        defer_call Lend_defer_write_back [ address source; address target; Constant (Size_of ty) ]
    | Deferred_free variant ->
        emit st.builder (Defer_free_block { lend = lending.record; place = target; variant })
  in
  match lending.slot with
  | None ->
      (* A part of zero size: its values take no storage and own nothing. *)
      ()
  | Some slot_pointer -> (
      let pointer : Lowered.operand =
        match part with
        | Part (Borrow { place = written; _ }) when lent_in_place written <> None ->
            Address { place = Option.get (lent_in_place written); writable = mode = Mut }
        | _ ->
            (* The caller's slot, or storage in its record where it has none. *)
            let has_no_slot = held st (Raw Bool) in
            emit st.builder (Assign (has_no_slot, Binary (Equal, Copy slot_pointer, Constant Null)));
            when_ st.builder (Copy has_no_slot) (fun () ->
                emit st.builder
                  (Call
                     {
                       target = Intrinsic Lend_allocate;
                       arguments =
                         [
                           lending.record;
                           Constant (Size_of lending.part);
                           Constant (Alignment_of lending.part);
                         ];
                       result = Returned slot_pointer;
                     }));
            let slot = slot_pointer / Deref in
            List.iter (defer slot) (write part slot);
            Address { place = slot; writable = mode = Mut }
      in
      match result_place st with
      | Some result -> emit st.builder (Assign (result, Use pointer))
      | None -> bug "a lending method with no result")

and terminator st region (ending : Mir.terminator) ~origin =
  match ending with
  | Goto target -> goto st region target
  | Branch { condition; yes; no; _ } ->
      let condition = in_statement st (fun () -> value st condition) in
      let yes = jump st region yes and no = jump st region no in
      Emit_c.Builder.branch st.builder condition ~yes ~no;
      start st.builder (block st.builder)
  | Switch_variant { place = tested; cases } ->
      let tested = place st tested in
      let cases = List.map (fun (variant, target) -> (variant, jump st region target)) cases in
      finish st.builder (Switch_variant { place = tested; cases; default = None });
      start st.builder (block st.builder)
  | Unreachable | Written_unreachable -> unreachable_block st
  | Todo ->
      let message = "todo reached" in
      finish st.builder
        (Fail
           {
             failure = Todo;
             message = Constant (Bytes message);
             length = usize (String.length message);
             site = site_of st origin;
             reported = None;
           });
      start st.builder (block st.builder)
  | Return returned ->
      (match (result_slot st, returned) with
      | Some _, Some (Use { place = { root = Local local; projections = [] }; _ })
        when List.mem local (mir st).returned ->
          (* The value is in the slot already. *)
          ()
      | Some slot, Some returned -> in_statement st (fun () -> write_operand st returned slot)
      | _ -> ());
      return_from_frame st
  | Iteration_end _ -> continue_loop st
  | Cancel { task; task_end; winner; number; returned } ->
      Option.iter
        (fun target ->
          let rec branch_region (around : region) =
            match (around.ending, task, around.enclosing) with
            | Some (fork, _), Branch { block; _ }, _ when fork = block -> around
            | _, _, Some enclosing -> branch_region enclosing
            | _, _, None -> bug "an early exit from a branch outside its block"
          in
          let branch = branch_region region in
          ignore (jump ~entry:branch.start st branch target))
        task_end;
      (* The task evaluates the return value into a local of its own before
         it cancels the group. Several tasks may do so at the same time:
         the first to cancel moves its value out, and the others drop
         theirs. *)
      let value =
        Option.map
          (fun (returned, slot) ->
            let ty = ground st (info st slot).type_ in
            let value = at (local st.builder ~name:"returned" (Value ty)) in
            write_operand st returned value;
            (value, ty, slot))
          returned
      in
      cancel st ~task ~winner ~number ~value
  | Resume { winner; exits; next } ->
      (* The group has ended: the exit that won goes on. *)
      let cases =
        List.mapi
          (fun index (exit : Mir.early_exit) -> (Z.of_int (index + 1), jump st region exit.resume))
          exits
      in
      finish st.builder
        (Switch
           { value = Copy (local_place st winner); cases; default = Some (jump st region next) });
      start st.builder (block st.builder)
  | Yield { mode; part; resume } ->
      (* The method returns a pointer to the part. Its scopes end before it
         returns, as after any value: no code of the caller's runs between. *)
      in_statement st (fun () -> lend_part st ~mode part);
      goto st region resume
  | For { iteration; part; body; after; loop; _ } ->
      claim st region after;
      for_loop st region ~iteration ~part ~body ~loop;
      goto st region after
  | Fork { fork; concurrent = true; branches; join } ->
      concurrent_block st region ~fork ~branches ~join
  | Fork { fork; concurrent = false; branches; join } -> (
      match branches with
      | [] -> unreachable_block st
      | first :: _ when not (may_fork st) -> goto st region first.entry
      | _ -> (
          let forked =
            List.map
              (fun (branch : Mir.branch) ->
                outlined st ~parts:[] (fun () ->
                    let end_block = block st.builder in
                    run_region st
                      (new_region st ~enclosing:region ~ending:(fork, end_block))
                      ~entry:(branch.entry, 0);
                    finish st.builder (Goto end_block);
                    start st.builder end_block;
                    finish st.builder (Return None)))
              branches
          in
          emit st.builder (Fork { branches = forked });
          match join with Some join -> goto st region join | None -> unreachable_block st))
  | Join { fork; next } -> (
      match region.ending with
      | Some (ending, end_block) when ending = fork ->
          finish st.builder (Goto end_block);
          start st.builder (block st.builder)
      | _ -> goto st region next)

(* Lowers a [for] loop's body as a region of its own, once [value] is the
   place of the element. *)
and loop_body st region ~part ~body (value : Lowered.place) =
  let caller = st.frame in
  st.frame <- region.region_frame;
  bind_local st part value;
  let inner = new_region ~enclosing:region st in
  st.frame <- caller;
  run_region st inner ~entry:(body, 0)

and for_loop st region ~(iteration : Mir.iteration) ~part ~body ~(loop : Mir.loop) =
  let origin = loop.origin in
  let each = loop_body st region ~part ~body in
  match loop.schedule with
  | Concurrent_loop ->
      (* The enclosing code runs the iteration and spawns one task for each
         value. *)
      with_group st (fun group ->
          let spawning =
            {
              origin;
              group;
              item = local st.builder ~name:"item" (Value (Monomorphic.builtin UInt64));
              element = ground st (info st part).type_;
            }
          in
          for_each st ~schedule:(Spawned spawning) ~iteration ~each)
  | Parallel_loop -> for_each st ~schedule:Chunked ~iteration ~each
  | Core.Sequential -> for_each st ~schedule:Sequential ~iteration ~each

(* Lowers a loop over [iteration]. [each] lowers the loop body for the
   place of one value. The loop is the innermost loop for the body: the end
   of an iteration starts the next one. *)
and for_each st ~(schedule : schedule) ~(iteration : Mir.iteration) ~(each : Lowered.place -> unit)
    =
  let schedule = match schedule with Chunked when not (may_fork st) -> Sequential | own -> own in
  (* How an iteration receives a value that the loop owns, such as one
     that a cursor's [next] returned. *)
  let owned_each =
    match schedule with
    | Spawned loop -> fun value -> spawn_with_item st loop value ~owned:true ~each
    | Sequential | Chunked -> each
  in
  match iteration with
  | Range { start = low; stop = high; inclusive } ->
      range_loop st ~schedule ~low ~high ~inclusive ~each
  | Pull { cursor; next } ->
      (* A cursor: its type's [next] is called until it gives [None]. *)
      let cursor = place st cursor in
      pull_loop st ~option:(result_type st next)
        ~call_next:(fun destination -> call_with_places st next [ cursor ] ~destination)
        ~body:owned_each

(* A loop over a range of integers or characters. *)
and range_loop st ~schedule ~(low : Mir.operand) ~(high : Mir.operand) ~inclusive ~each =
  (* The unit a range of a type counts in. A range of [Character] goes from
     U+D7FF to U+E000, since the surrogates between them are no
     characters. *)
  let element = operand_type st low in
  let scalar = scalar_of st element in
  let constant value : Lowered.operand =
    match scalar with
    | Integer integer -> constant_int integer (Z.of_int value)
    | Character -> Constant (Character value)
    | _ -> bug "a range of %s" (Ground.to_string element)
  in
  let characters = scalar = Character in
  let both first second =
    let answer = local st.builder (Raw Bool) in
    emit st.builder (Assign (at answer, Binary (Bit_and, first, second)));
    Lowered.Copy (at answer)
  in
  let compare op left right =
    let answer = local st.builder (Raw Bool) in
    emit st.builder (Assign (at answer, Binary (op, left, right)));
    Lowered.Copy (at answer)
  in
  match schedule with
  | Chunked ->
      let wide = Lowered.Raw (Integer UInt64) in
      let one = constant_int UInt64 Z.one in
      let first_value = binding st ~name:"start" element in
      let last_value = binding st element in
      emit st.builder (Assign (first_value, Use (value st low)));
      emit st.builder (Assign (last_value, Use (value st high)));
      let going = local st.builder (Raw Bool) in
      emit st.builder
        (Assign
           ( at going,
             Binary ((if inclusive then Less_equal else Less), Copy first_value, Copy last_value) ));
      let inside = block st.builder and after = block st.builder in
      let depth = List.length st.scopes in
      Emit_c.Builder.branch st.builder (Copy (at going)) ~yes:inside ~no:after;
      start st.builder inside;
      let first = local st.builder ~name:"first" wide
      and last = local st.builder ~name:"last" wide in
      let low_wide = local st.builder wide and high_wide = local st.builder wide in
      emit st.builder (Assign (at first, Use (constant_int UInt64 Z.zero)));
      emit st.builder (Assign (at low_wide, Convert (Copy first_value, Integer UInt64)));
      emit st.builder (Assign (at high_wide, Convert (Copy last_value, Integer UInt64)));
      emit st.builder (Assign (at last, Binary (Subtract, Copy (at high_wide), Copy (at low_wide))));
      if not inclusive then
        emit st.builder (Assign (at last, Binary (Subtract, Copy (at last), one)));
      if characters then
        when_ st.builder
          (both
             (compare Less (Copy first_value) (constant 0xD800))
             (compare Greater (Copy last_value) (constant 0xDFFF)))
          (fun () ->
            emit st.builder
              (Assign
                 (at last, Binary (Subtract, Copy (at last), constant_int UInt64 (Z.of_int 0x800)))));
      let body, environment =
        outlined st ~parts:[ first; last ] (fun () ->
            let index = local st.builder ~name:"index" wide in
            emit st.builder (Assign (at index, Use (Copy (at first))));
            let again = block st.builder and step = block st.builder and done_ = block st.builder in
            finish st.builder (Goto again);
            start st.builder again;
            in_scope st (fun () ->
                let offset = binding st element in
                let bound = binding st element in
                emit st.builder (Assign (offset, Convert (Copy (at index), scalar)));
                emit st.builder (Assign (bound, Binary (Add, Copy first_value, Copy offset)));
                if characters then
                  when_ st.builder
                    (both
                       (compare Less (Copy first_value) (constant 0xD800))
                       (compare Greater_equal (Copy bound) (constant 0xD800)))
                    (fun () ->
                      emit st.builder (Assign (bound, Binary (Add, Copy bound, constant 0x800))));
                looping st ~continue_:step ~break_:done_ ~depth (fun () -> each bound));
            finish st.builder (Goto step);
            start st.builder step;
            let ended = local st.builder (Raw Bool) in
            emit st.builder (Assign (at ended, Binary (Equal, Copy (at index), Copy (at last))));
            let next = block st.builder in
            Emit_c.Builder.branch st.builder (Copy (at ended)) ~yes:done_ ~no:next;
            start st.builder next;
            emit st.builder (Assign (at index, Binary (Add, Copy (at index), one)));
            finish st.builder (Goto again);
            start st.builder done_;
            finish st.builder (Return None))
      in
      emit st.builder
        (Fork_range { body; environment; first = Copy (at first); last = Copy (at last) });
      finish st.builder (Goto after);
      start st.builder after
  | Sequential | Spawned _ ->
      let loop_value ?name () = binding st ?name element in
      let index = loop_value ~name:"index" () in
      let stop = loop_value () in
      emit st.builder (Assign (index, Use (value st low)));
      emit st.builder (Assign (stop, Use (value st high)));
      let test = block st.builder
      and inside = block st.builder
      and step = block st.builder
      and after = block st.builder in
      let depth = List.length st.scopes in
      finish st.builder (Goto test);
      start st.builder test;
      let going = local st.builder (Raw Bool) in
      emit st.builder
        (Assign (at going, Binary ((if inclusive then Less_equal else Less), Copy index, Copy stop)));
      Emit_c.Builder.branch st.builder (Copy (at going)) ~yes:inside ~no:after;
      start st.builder inside;
      looping st ~continue_:step ~break_:after ~depth (fun () ->
          let run value =
            in_scope st (fun () ->
                let bound = loop_value () in
                emit st.builder (Assign (bound, value));
                each bound)
          in
          match schedule with
          | Spawned loop ->
              (* The task's argument is the index, converted to [UInt64]
                 and back. *)
              let item = at loop.item in
              emit st.builder (Assign (item, Convert (Copy index, Integer UInt64)));
              spawn_iteration st loop ~not_spawned:ignore (fun () ->
                  run (Convert (Copy item, scalar)))
          | Sequential | Chunked -> run (Use (Copy index)));
      finish st.builder (Goto step);
      start st.builder step;
      (* An inclusive range stops after its last value without adding one
         to it, which could overflow. *)
      if inclusive then begin
        let last = local st.builder (Raw Bool) in
        emit st.builder (Assign (at last, Binary (Equal, Copy index, Copy stop)));
        let next = block st.builder in
        Emit_c.Builder.branch st.builder (Copy (at last)) ~yes:after ~no:next;
        start st.builder next
      end;
      emit st.builder (Assign (index, Binary (Add, Copy index, constant 1)));
      if characters then
        when_ st.builder
          (compare Equal (Copy index) (constant 0xD800))
          (fun () -> emit st.builder (Assign (index, Use (constant 0xE000))));
      finish st.builder (Goto test);
      start st.builder after

let fill_defaults st (mask : Lowered.place) (body : Mir.body) (places : Lowered.place list) =
  let builder = st.builder in
  let bit = ref (-1) in
  List.map2
    (fun parameter arrived ->
      let mode, name, type_ = parameter_of body parameter in
      match List.assoc_opt parameter body.defaults with
      | None -> arrived
      | Some default ->
          incr bit;
          let bit = !bit in
          let ty = ground st type_ in
          let passed = local builder (Raw (Integer UInt64))
          and is_passed = local builder (Raw Bool) in
          emit builder
            (Assign
               (at passed, Binary (Bit_and, Copy mask, constant_int UInt64 (Z.shift_left Z.one bit))));
          emit builder
            (Assign (at is_passed, Binary (Not_equal, Copy (at passed), constant_int UInt64 Z.zero)));
          let fill = block builder and after = block builder in
          let unless_passed other =
            Emit_c.Builder.branch builder (Copy (at is_passed)) ~yes:other ~no:fill
          in
          let place =
            if mode = Own && not (trivial st ty) then begin
              let owned_here = at (local builder ~name (Value ty)) in
              let passed_block = block builder in
              unless_passed passed_block;
              start builder passed_block;
              emit builder (Assign (owned_here, Use (Move arrived)));
              finish builder (Goto after);
              start builder fill;
              in_statement st (fun () -> mir_into st default owned_here);
              owned_here
            end
            else begin
              unless_passed after;
              start builder fill;
              in_statement st (fun () ->
                  match arrived with
                  | { projections = [ Deref ]; root = Local pointer } ->
                      let value = binding st ty in
                      mir_into st default value;
                      emit builder
                        (Assign (at pointer, Use (Address { place = value; writable = true })))
                  | place when mode = Own || trivial st ty -> mir_into st default place
                  | place ->
                      let value = binding st ty in
                      mir_into st default value;
                      emit builder (Assign (place, Use (Copy value))));
              arrived
            end
          in
          finish builder (Goto after);
          start builder after;
          place)
    body.parameters places

(* Lowers the MIR of the code at [path] in the current frame, with its
   parameters in [parameters], in order. *)
let lower_code st path ~parameters ?lending () =
  let code_mir = Loop_parts.ended (mir_of st.context path) in
  let frame =
    frame_of_body st ~owner:(innermost_scope st) ?lending ~lambdas:code_mir.lambdas code_mir.body
  in
  st.frame <- { st.frame with mir = Some frame };
  Option.iter (fun (lending : lending) -> st.lend_record <- Some lending.record) lending;
  List.iter2 (bind_local st) code_mir.body.parameters parameters;
  make_owned_locals st;
  lower_body st frame
