(* Lowers a body from its MIR to the LIR, once {!Instance_mir} has inlined
   the lending and yielding methods it calls. The MIR has made every
   decision about the order of evaluation, the scope of temporaries and
   bindings, and the flow of patterns and loops, so this lowering decides
   only what is the LIR's: pointers, layout, the calling convention, drops,
   and the outlining of regions.

   A body is lowered as regions. A region is the code of one body that is
   lowered in one state of the scopes: a whole body, the body of a [for]
   loop, or a branch of a [concurrent] block. Each region lowers each of its
   blocks of the MIR once, the first time a jump reaches it. A jump to a
   block of an enclosing region of the same body leaves the scopes between,
   as a [break] does. *)

open Definitions
open Lowering
open Targets
open Lir_builder

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

(* Where a default's expression is, for a report about it. *)
let default_origin (default : Mir.t) =
  Array.fold_left
    (fun found (block : Mir.basic_block) ->
      match block.terminator with Return _ -> block.terminator_origin | _ -> found)
    0 default.body.blocks

let spans st =
  match demand st.context Names.spans st.frame.code.definition_key with
  | Some spans -> spans
  | None -> bug "no spans for %s" (Path.show st.frame.code.anchor)

let site_of st (origin : Core.origin) =
  let spans = spans st in
  if origin >= 0 && origin < Array.length spans then site st spans.(origin)
  else site st (Syntax.Span.make 0 0)

(* Where a check that fails in the code being lowered is reported: at the
   code's own position, or, for the standard library's code that is
   inlined into a program's, at the program's call. *)
let failure_site st (origin : Core.origin) =
  match st.frame.reported with Some site -> site | None -> site_of st origin

(* The MIR of one body, ready to lower: how many times each local that
   names a place is bound to one, which is more than once where several
   patterns bind it. *)
let frame_of_body ?owner ?returns_into ~lambdas (body : Mir.body) : mir_frame =
  let aliases = Hashtbl.create 8 and lent_values = Hashtbl.create 1 in
  Array.iter
    (fun (block : Mir.basic_block) ->
      List.iter
        (fun (statement : Mir.statement) ->
          match statement.kind with
          | Assign { target = { root = Local local; projections = [] }; value; _ } -> (
              (match (body.locals.(local).kind, value) with
              | ( (Lent (Read | Mut) | Source { mode = Read | Mut; _ }),
                  (Construct _ | Operand (Borrow _)) ) ->
                  Hashtbl.add lent_values local value
              | _ -> ());
              match value with
              | Operand (Borrow _) ->
                  Hashtbl.replace aliases local
                    (1 + Option.value ~default:0 (Hashtbl.find_opt aliases local))
              | _ -> ())
          | _ -> ())
        block.statements)
    body.blocks;
  let built = Hashtbl.create 1 in
  Hashtbl.iter
    (fun local _ ->
      let values = Hashtbl.find_all lent_values local in
      if List.exists (function Mir.Construct _ -> true | _ -> false) values then
        Hashtbl.replace built local values)
    lent_values;
  {
    body;
    lambdas;
    places = Hashtbl.create 32;
    aliases;
    built;
    owner;
    returns_into;
    forks = Hashtbl.create 1;
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
  }

let info st local = (mir st).body.locals.(local)

(* The core local a parameter or a binding of the MIR is, if it is one. *)
let core_local st local =
  match (info st local).kind with Source { local; _ } -> Some local | Temporary | Lent _ -> None

(* Whether a local of the MIR owns its value, so that its end drops it: a
   temporary, or a binding that took its value. Any other local is the place
   it was lent or bound to. *)
let owns st local =
  let frame = mir st in
  (not (Hashtbl.mem frame.aliases local))
  &&
  match (info st local).kind with
  | Temporary | Source { mode = Own; _ } -> true
  | Source { mode = Read | Mut; _ } | Lent _ -> false

(* Binds a local of the MIR to its place. The place of [self] is also the
   code's own, which the evidence of a capability it implements names. *)
let bind_local st local place =
  Hashtbl.replace (mir st).places local place;
  if core_local st local = Some Self then st.frame.self_place <- Some place

(* Where the value a [return] returns is written: the slot of the
   function's result, or of the value of an expression lowered on its own. *)
let result_slot st =
  match (mir st).returns_into with Some destination -> Some destination | None -> result_place st

(* A new LIR local for a local of the MIR, which the scope that owns the
   body's locals owns. A temporary that a [return] returns is the result's
   slot. *)
let rec fresh_place st local : Lir.place =
  match result_slot st with
  | Some slot when List.mem local (mir st).returned ->
      bind_local st local slot;
      slot
  | _ -> new_place st local

and new_place st local : Lir.place =
  let frame = mir st in
  let ty = ground st (info st local).type_ in
  let name = match core_local st local with Some _ -> Some "binding" | None -> None in
  let place =
    match (ty, frame.owner) with
    | Cursor yielding, Some scope when List.exists (Path.equal yielding.method_) st.frame.inlined ->
        (* A cursor over a method that the code is, or that is inlined
           around it, would hold itself, so it is in a block of the heap,
           which the scope that owns the local frees after it drops the
           value. *)
        let boxed = boxed_cursor st yielding in
        scope.owned <- Free_pointed boxed :: scope.owned;
        boxed / Deref
    | _ -> at (Lir_builder.local st.builder ?name (Value ty))
  in
  (match frame.owner with
  | Some scope when owns st local && not (trivial st ty) ->
      scope.owned <- Drop_value place :: scope.owned
  | _ -> ());
  bind_local st local place;
  place

(* The place of a local of the MIR: made when it first holds a value. A
   parameter and a capture are bound before the code runs. *)
let local_place st local : Lir.place =
  match Hashtbl.find_opt (mir st).places local with
  | Some place -> place
  | None -> fresh_place st local

let binary : Core.comparison -> Lir.binary = function
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

let place st (written : Mir.place) : Lir.place =
  let root =
    match written.root with
    | Local local -> local_place st local
    | Constant path -> static_constant st path
  in
  List.fold_left
    (fun place (projection : Mir.projection) ->
      match projection with
      | Field field -> project st place (Field field)
      | Variant_field { variant; field } -> project st place (Variant_field { variant; field }))
    root written.projections

(* The variants of a record or sum type, a record's as one with no name,
   each with its fields and their types. *)
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

(* Writes [build] for each variant that the value at [source], of type
   [ty], may have, with the variant's fields: once for a record, and for a
   sum type in a case of a switch on the variant. *)
let each_variant st ty (source : Lir.place) build =
  match variants_of st ty with
  | [ (None, fields) ] -> build None fields
  | variants ->
      let after = block st.builder in
      let cases =
        List.map
          (fun (variant, fields) ->
            let case = block st.builder in
            in_block st.builder case (fun () ->
                build variant fields;
                finish st.builder (Goto after));
            (Option.get variant, case))
          variants
      in
      finish st.builder (Switch_variant { place = source; cases; default = None });
      start st.builder after

let field_of variant field : Lir.projection =
  match variant with Some variant -> Variant_field { variant; field } | None -> Field field

(* The value at a place as a value of its type. A lent value there is
   copied into one. *)
let rec whole st (source : Lir.place) : Lir.place =
  match lent_at st source with Some lent -> copied_lent st lent source | None -> source

(* A lent value copied into a value of its type, which owns nothing: a
   variant's block, which the copy has and the lent value does not, is
   freed as the scope ends. Lent to be changed, each value is moved out of
   its place instead, and moved back as the scope ends, on every way out,
   so the caller's changes reach the place. The checker allows this only
   for a record, so the variant cannot change. *)
and copied_lent st (lent : Ground.lent) (source : Lir.place) : Lir.place =
  let ty = lent.base in
  let copy = at (local st.builder ~borrowed:(not lent.writable) (Value ty)) in
  let scope = innermost_scope st in
  if lent.writable then begin
    (match variants_of st ty with
    | [ (None, _) ] -> ()
    | _ -> bug "%s is lent to be changed" (Ground.to_string (Lent lent)));
    scope.owned <- Drop_value copy :: scope.owned
  end;
  each_variant st ty source (fun variant fields ->
      let fields =
        List.map
          (fun (name, field_ty) ->
            let field_place = whole st (project st source (field_of variant name)) in
            if lent.writable then begin
              scope.owned <-
                Write_back
                  {
                    destination = field_place;
                    source = copy / field_of variant name;
                    ty = field_ty;
                  }
                :: scope.owned;
              (name, owned st field_place field_ty)
            end
            else (name, Lir.Copy field_place))
          fields
      in
      emit st.builder (Assign (copy, Build { ty; variant; fields })));
  (match
     List.filter_map
       (fun (variant_shape : Memory_layout.variant_shape) ->
         if variant_shape.indirect then Some variant_shape.name else None)
       (match Memory_layout.shape st.context.env ty with Sum variants -> variants | _ -> [])
   with
  | [] -> ()
  | variants -> scope.owned <- Free_blocks { place = copy; variants } :: scope.owned);
  copy

(* Operands *)

(* The place of a compound assignment's target, whose old value an operator
   takes. The target holds nothing until the statement assigns it again, so
   that assignment drops nothing: an element's old value cannot be tracked
   by drop elaboration, and a drop would free it a second time. *)
let taken st (written : Mir.place) =
  let frame = mir st in
  frame.taken <- written :: frame.taken;
  place st written

let operand_types_ty (operand : Mir.operand) =
  match operand with
  | Use { type_; _ } | Borrow { type_; _ } | Take { type_; _ } | Constant { type_; _ } -> type_

(* The type an operand's value has in this instance. *)
let operand_type st operand = ground st (operand_types_ty operand)

let constant st ty (value : Mir.constant) : Lir.operand =
  match value with
  | Unit -> bug "a unit constant as a value"
  | Integer number -> constant_of st ty (Integer_value number)
  | Float number -> constant_of st ty (Float_value number)
  | Boolean truth -> Constant (Bool truth)
  | String _ -> bug "a string literal as an operand"

(* An operand as a value: copied, moved, or a constant. A string literal is
   written into a temporary first. *)
let value st (operand : Mir.operand) : Lir.operand =
  let ty = operand_type st operand in
  match operand with
  | Constant { value = String text; _ } ->
      let held = temporary st ty in
      string_literal st ty text ~destination:held;
      owned st held ty
  | Constant { value; _ } -> constant st ty value
  | Use { place = written; _ } -> owned st (whole st (place st written)) ty
  | Take { place = written; _ } -> owned st (taken st written) ty
  | Borrow { place = written; _ } -> Copy (whole st (place st written))

(* An operand as a place: where a borrowed place is, or a place that holds
   the value. *)
let operand_place st (operand : Mir.operand) : Lir.place =
  let ty = operand_type st operand in
  match operand with
  | Borrow { place = written; _ } -> whole st (place st written)
  | Use { place = { root = Local local; projections = [] } as written; _ }
    when (info st local).kind = Temporary ->
      place st written
  | Use { place = written; _ } ->
      let held = temporary st ty in
      take st (whole st (place st written)) ty ~destination:held;
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

(* An operand as a place that may hold a lent value: a borrowed place as
   the code names it. *)
let operand_part st (operand : Mir.operand) : Lir.place =
  match operand with
  | Borrow { place = written; _ } -> place st written
  | _ -> operand_place st operand

(* Writes an operand's value to [destination], which holds nothing. *)
let write_operand st (operand : Mir.operand) (destination : Lir.place) =
  let ty = operand_type st operand in
  match operand with
  | Constant { value = Unit; _ } -> ()
  | Constant { value = String text; _ } -> string_literal st ty text ~destination
  | Constant { value; _ } -> emit st.builder (Assign (destination, Use (constant st ty value)))
  | Use { place = written; _ } -> take st (whole st (place st written)) ty ~destination
  | Take { place = written; _ } -> take st (taken st written) ty ~destination
  | Borrow { place = written; _ } ->
      emit st.builder (Assign (destination, Use (Copy (whole st (place st written)))))

let discarded st = temporary st (Monomorphic.builtin Unit)

(* Regions *)

(* The state a block of the MIR starts in, which every jump to it shares:
   the evidence in force and the [provide]s around it. *)
type entry = { evidence : (Path.t * Lir.operand) list; provides : (Path.t * Lir.operand) list list }

type region = {
  region_frame : frame;  (** The frame whose code the region is *)
  region_body : mir_frame;
  lowered : (Mir.block, Lir.block) Hashtbl.t;
  mutable pending : (Mir.block * Lir.block * entry) list;
      (** The blocks reached and not yet lowered. The region lowers the first of them in the MIR's
          order, which is reverse postorder, so that every block is lowered after the blocks that
          jump to it, other than by a loop's back edge. A block's code can then read what an earlier
          block's lowering recorded, such as the rest of a lending call that a local's end runs. *)
  depth : int;  (** The number of scopes the region's blocks are lowered in *)
  start : entry;  (** The state the region's code starts in *)
  enclosing : region option;
  ending : (int * Lir.block) option;
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

(* The region of the same body around [region] that has lowered or will
   lower a block. *)
let rec owner_of region body block =
  if region.region_body == body && Hashtbl.mem region.lowered block then Some region
  else Option.bind region.enclosing (fun enclosing -> owner_of enclosing body block)

(* The LIR block a jump from [region] to a block of the MIR goes to. A jump
   to a block of an enclosing region leaves the scopes between. *)
let jump ?entry st region target : Lir.block =
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

(* Ends the current block with a jump to [target], and starts a block that
   nothing reaches. *)
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

(* Returns from the function, whose result is already written. In an
   expression lowered on its own, jumps to its end instead. *)
let return_from_frame st =
  (match st.frame.exit with
  | Some (exit, depth) ->
      leave_to st depth;
      finish st.builder (Goto exit)
  | None ->
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

(* A lending or yielding method a call reaches, with its MIR as the
   instance runs it, for inlining. *)
let inlinable st (callee : Mir.callee) : Instance_mir.callee option =
  match resolve_callee st callee with
  | Some (path, type_arguments) -> (
      match (signature_of st.context path).output with
      | Yields _ | Lends _ ->
          let code = code_of st.context path type_arguments in
          Some
            {
              path;
              type_arguments = List.map Monomorphic.back_argument type_arguments;
              mir = Instance_mir.substituted code.substitution (mir_of st.context path);
            }
      | Returns _ -> None)
  | None -> None

(* The frame a block's code is lowered in. A block of a method inlined into
   the body is the method's code, so that its origins find the method's
   text, and a check in the standard library's code reports the call that
   entered it from a program's code. *)
let block_frame st (base : frame) (chain : Mir.inlined list) =
  List.fold_right
    (fun (inlined : Mir.inlined) (outer : frame) ->
      let saved = st.frame in
      st.frame <- outer;
      let call_site = site_of st inlined.call in
      let type_arguments = List.map (ground_argument st) inlined.type_arguments in
      st.frame <- saved;
      {
        outer with
        code = code_of st.context inlined.method_ type_arguments;
        reported =
          (if Path.package inlined.method_ = Path.standard_package then
             Some (Option.value outer.reported ~default:call_site)
           else None);
        inlined = inlined.method_ :: outer.inlined;
      })
    chain base

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
  | Yields _ | Lends _ -> bug "%s does not return a value" (Path.show path)

(* Calls a function or a method with arguments that are already in places,
   one for each parameter in order. *)
let call_with_places st (callee : Mir.callee) (places : Lir.place list) ~destination =
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
   order. An omitted argument gets an uninitialized temporary, which the
   callee fills with the default. The returned mask has one bit for each
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
        | Default -> (mode, ty, temporary st ty)
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
  let pointer = Lir.Copy (shared / Field "value") in
  emit st.builder
    (Call { target = Intrinsic Shared_lock; arguments = [ pointer ]; result = Discarded });
  (* The pointer is [borrowed] so that drop elaboration does not track the
     value, which the [Shared] owns. *)
  let typed =
    local st.builder ~borrowed:true (Pointer { target = Value value_ty; writable = true })
  in
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
let intrinsic st (operation : Intrinsic.operation) ~type_arguments (arguments : Mir.argument list)
    ~destination ~site =
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
      Intrinsics.lower ~checks:st.context.checks ~value_arguments st.context.env st.builder
        st.context.types operation ~type_arguments arguments ~destination ~site

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
let tasks_call st name ?result (places : Lir.place list) : Lir.statement =
  let capability = Well_known.path Tasks in
  let slot, signature = capability_method st.context capability name in
  let lir_signature, convention = entry_signature st.context signature in
  Call
    {
      target =
        Evidence_call
          { evidence = evidence_of st capability; capability; slot; signature = lir_signature };
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
let tasks_bool st name places : Lir.operand =
  let result = at (local st.builder (Value st.context.bool)) in
  emit st.builder (tasks_call st name ~result places);
  Copy result

(* Opens a task group, runs [f] with it, and joins it. A scope owns the
   join, so an early exit from [f] joins the group too. The scope's other
   temporaries are dropped after the join, because a task may still read
   them until then. *)
let with_group st ~origin (f : Lir.place -> unit) =
  if st.pulling then
    unsupported ~at:(site_of st origin) "`concurrent` code in a yielding method that is pulled";
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
let task_function_type st : Lir.ty =
  let _, signature = capability_method st.context (Well_known.path Tasks) "spawn" in
  match signature.parameters with
  | [ _; work; _ ] -> Value (Monomorphic.ground st.context.monomorphic [] work.type_)
  | _ -> bug "Tasks.spawn does not take a group, a function, and an item"

(* Lowers the body of a task with [f]. The body starts at the region mark
   that the caller has just emitted. Every exit from the task jumps to
   [end_block], which is the current block when this returns. *)
let task_body st ~(id : Core.task) ~group ~early_exits (f : task -> unit) =
  let task =
    { id; group; early_exits; end_block = block st.builder; scope_depth = List.length st.scopes }
  in
  st.tasks <- task :: st.tasks;
  f task;
  st.tasks <- List.tl st.tasks;
  finish st.builder (Goto task.end_block);
  start st.builder task.end_block

(* Evidence for the capabilities of one [mut] implementation whose calls
   are mutually exclusive. The implementation's capabilities share one
   mutex, a word in this frame. The evidence for each capability has the
   capability's locking table, the mutex's address as its implementation
   pointer, and the implementation's own evidence and the evidence for
   [Tasks] as its outer evidence. *)
let locked_evidence st ~(tasks : Lir.operand) (evidence : (Path.t * Lir.operand) list) =
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
      (capability, Lir.Address { place = at slot; writable = false }))
    evidence

(* Lowers an early exit that still has to end [tasks], the enclosing tasks
   it leaves, innermost first. [value] holds the return value of a
   [return] that has one.

   With no task left, this is the plain exit. Otherwise the innermost task
   cancels its group. If it is the first to cancel, it records the exit's
   number and the return value for the code that joins the group. The task
   then ends, whether or not it was first. *)
let early_exit st region ~(tasks : (Core.task * Mir.statement list) list) ~(exit : Mir.task_exit)
    ~(value : Lir.place option) =
  match (tasks, st.tasks) with
  | [], _ -> (
      match exit with
      | Exit_return _ ->
          (match (value, result_place st, returned_type st) with
          | Some value, Some result, Some ty ->
              clear_result st;
              emit st.builder (Assign (result, Use (owned st value ty)))
          | _ -> ());
          return_from_frame st
      | Exit_to target -> goto st region target
      | Exit_iteration -> continue_loop st)
  | (id, ends) :: remaining, task :: _ when id = task.id ->
      let exits = task.early_exits in
      exits.exits <- { ends; remaining; exit } :: exits.exits;
      let number = List.length exits.exits in
      when_ st.builder (tasks_bool st "cancel" [ task.group ]) (fun () ->
          emit st.builder (Assign (exits.winner, Use (constant_int UInt32 (Z.of_int number))));
          match (value, returned_type st) with
          | Some value, Some ty ->
              let return_value =
                match exits.return_value with
                | Some return_value -> return_value
                | None ->
                    let return_value = owned_local st ~name:"return_value" exits.scope ty in
                    exits.return_value <- Some return_value;
                    return_value
              in
              (* Only one exit wins, so [return_value] is empty here. Drop
                 elaboration cannot prove that when a loop repeats this
                 code, so the assignment is lowered as a replacement. *)
              replace st return_value ty ~by:value
          | _ -> ());
      leave_to st task.scope_depth;
      finish st.builder (Goto task.end_block);
      start st.builder (block st.builder)
  | _ -> bug "an early exit leaves a task that is not the innermost enclosing task"

(* After a group is joined: if one of its tasks' early exits won, performs
   that exit in the enclosing code, once [lower_ends] has ended the scopes
   that the exit leaves around the task. *)
let resume_early_exit st region ~lower_ends (exits : early_exits) =
  match List.rev exits.exits with
  | [] -> ()
  | recorded ->
      let after = block st.builder in
      let targets = List.map (fun _ -> block st.builder) recorded in
      finish st.builder
        (Switch
           {
             value = Copy exits.winner;
             cases = List.mapi (fun index target -> (Z.of_int (index + 1), target)) targets;
             default = Some after;
           });
      (* Each exit is a path of its own, which starts with the evidence in
         force after the join. *)
      let evidence = st.evidence and provides = (mir st).provides in
      List.iter2
        (fun target (recorded : early_exit) ->
          st.evidence <- evidence;
          (mir st).provides <- provides;
          start st.builder target;
          lower_ends recorded.ends;
          let value = match recorded.exit with Exit_return _ -> exits.return_value | _ -> None in
          early_exit st region ~tasks:recorded.remaining ~exit:recorded.exit ~value;
          finish st.builder (Goto after))
        targets recorded;
      st.evidence <- evidence;
      (mir st).provides <- provides;
      start st.builder after

(* Spawns one iteration of a [concurrent for] loop as a task. [f] lowers
   the iteration's body, and the task's argument is the current value of
   [loop.item]. If the group is already cancelled, [spawn] returns false:
   [not_spawned] then drops the item, and the enclosing code breaks out of
   the loop that produces the items. *)
let spawn_iteration st (loop : spawn_loop) ~(not_spawned : unit -> unit) (f : unit -> unit) =
  let fork = fresh_fork st in
  let function_value = local st.builder ~name:"task" (task_function_type st) in
  emit st.builder (Region { fork; region = Task { function_value; item = loop.item } });
  task_body st
    ~id:(Iteration { loop = loop.origin })
    ~group:loop.group ~early_exits:loop.early_exits
    (fun task ->
      (* A [continue] of the loop ends the task. A [break] of the loop
         never jumps: it is an early exit that ends the task. *)
      looping st ~continue_:task.end_block ~break_:task.end_block ~depth:task.scope_depth f);
  emit st.builder (Regions_end { fork });
  let spawned = tasks_bool st "spawn" [ loop.group; at function_value; at loop.item ] in
  let next = block st.builder and cancelled = block st.builder in
  Lir_builder.branch st.builder spawned ~yes:next ~no:cancelled;
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
let spawn_with_item st (loop : spawn_loop) (value : Lir.place) ~owned:is_owned
    ~(each : Lir.place -> unit) =
  let ty = loop.element in
  let item = at loop.item in
  let boxed = not (is_zero_size st ty) in
  let move_or_copy place : Lir.operand = if is_owned then owned st place ty else Copy place in
  (* The block's address, read back from the item, and the value's place
     in the block. The pointer is [borrowed] so that drop elaboration does
     not track the block's contents. *)
  let block_of () : Lir.local * Lir.place =
    let pointer = local st.builder (Raw (Pointer Opaque)) in
    emit st.builder (Assign (at pointer, Convert (Copy item, Pointer Opaque)));
    let typed = local st.builder ~borrowed:true (Pointer { target = Value ty; writable = true }) in
    emit st.builder (Assign (at typed, Use (Copy (at pointer))));
    (pointer, { root = Local typed; projections = [ Deref ] })
  in
  (* Takes the value out of the block into a local and frees the block.
     The enclosing scope drops the local only if the value is owned. *)
  let unbox () : Lir.place =
    if boxed then begin
      let unboxed =
        if is_owned then binding st ty else at (local st.builder ~borrowed:true (Value ty))
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
    ~not_spawned:(fun () -> in_scope st (fun () -> ignore (unbox ())))
    (fun () -> in_scope st (fun () -> each (unbox ())))

(* Lent values *)

let lent_field (lent : Ground.lent) variant field =
  List.find_map
    (fun (lent_field : Ground.lent_field) ->
      if lent_field.variant = variant && lent_field.field = field then Some lent_field.holds
      else None)
    lent.fields

(* The type that the current frame's method yields. *)
let yielded_type_of_frame st =
  match st.frame.code.result with
  | Yields (_, ty) | Lends (_, ty) -> ground st ty
  | Returns _ -> bug "a yield in %s, which does not yield" (Path.show st.frame.code.anchor)

(* The type of a part built around places from [values], the values
   assigned to it. Each field that some value gives a place, or that has a
   type with something to drop, holds an address, and a field that some
   value gives a part built around places holds a lent value of its own. *)
let rec built_lent st ~writable ty (values : Mir.rvalue list) : Ground.lent =
  let built = (mir st).built in
  let lent_field_for variant (name, field_ty) : Ground.lent_field option =
    let fields =
      List.concat_map
        (fun (value : Mir.rvalue) ->
          match value with
          | Construct { variant = constructed; fields } when constructed = variant -> (
              match List.assoc_opt name fields with Some (Some field) -> [ field ] | _ -> [])
          | _ -> [])
        values
    in
    let nested =
      List.concat_map
        (fun (field : Mir.operand) ->
          match field with
          | Use { place = { root = Local part; projections = [] }; _ } ->
              Option.value (Hashtbl.find_opt built part) ~default:[]
          | _ -> [])
        fields
    in
    let holds : Ground.holds option =
      if nested <> [] then Some (Nested (built_lent st ~writable field_ty nested))
      else if
        List.exists (function Mir.Borrow _ -> true | _ -> false) fields
        || not (trivial st field_ty)
      then Some Address
      else None
    in
    Option.map (fun holds -> { Ground.variant; field = name; holds }) holds
  in
  {
    base = ty;
    writable;
    fields =
      List.concat_map
        (fun (variant, fields) -> List.filter_map (lent_field_for variant) fields)
        (variants_of st ty);
  }

(* The value at [source] as a lent value of type [lent], which lends its
   parts. *)
let rec lent_from st (lent : Ground.lent) (source : Lir.place) : Lir.place =
  match lent_at st source with
  | Some existing when Ground.compare (Lent existing) (Lent lent) = 0 -> source
  | Some existing -> lend_fields st lent (copied_lent st existing source)
  | None -> lend_fields st lent source

and lend_fields st (lent : Ground.lent) (source : Lir.place) : Lir.place =
  let built = at (local st.builder ~borrowed:true (Value (Lent lent))) in
  each_variant st lent.base source (fun variant fields ->
      let fields =
        List.map
          (fun (name, _) ->
            let field_place = source / field_of variant name in
            match lent_field lent variant name with
            | Some Address -> (name, Lir.Address { place = field_place; writable = lent.writable })
            | Some (Nested inner) -> (name, Copy (lent_from st inner field_place))
            | None -> (name, Copy field_place))
          fields
      in
      emit st.builder (Assign (built, Build { ty = Lent lent; variant; fields })));
  built

(* Lowering *)

(* Makes the locals that the current frame's code owns, so that the scope
   that owns them drops them on every way out: at a [return], and at the
   [stop] of a [yield] of a pulled method. A local the MIR has ended holds
   nothing there,
   and drop elaboration removes its drop. Where paths join, as they do where
   the rest of a lending method runs, a local may hold a value on only some
   of them, and the drop then takes a flag. *)
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
      if owns st local && (not (List.mem local frame.body.parameters)) && not (List.mem local parts)
      then ignore (local_place st local))
    frame.body.locals

(* Lowers [mir], the MIR of the code in the current frame, from its entry,
   into the current block. Leaves a block that nothing reaches. *)
let rec lower_body ?enclosing st (frame : mir_frame) =
  st.frame <- { st.frame with mir = Some frame };
  run_region st (new_region ?enclosing st) ~entry:(0, 0)

(* Lowers a region from the statement [index] of a block into the current
   block, and then every block that its code reaches. Leaves a block that
   nothing reaches. *)
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
  st.frame <- block_frame st region.region_frame basic.inlined;
  List.iteri
    (fun position (statement : Mir.statement) ->
      if position >= index then in_statement st (fun () -> lower_statement st statement))
    basic.statements;
  terminator st region basic.terminator ~origin:basic.terminator_origin

(* A [concurrent] block. Each branch is a [Task] region, which outlining
   turns into a nested function, and the code after the regions spawns each
   function as a task of one group. The block's end follows, if a branch
   reaches it. *)
and concurrent_block st region ~fork ~(branches : Mir.branch list) ~join =
  let function_type = task_function_type st in
  let item = local st.builder (Value (Monomorphic.builtin UInt64)) in
  emit st.builder (Assign (at item, Use (constant_int UInt64 Z.zero)));
  (* Each branch's early exits and function value are made before the first
     region, since the code around the regions reads them. *)
  let tasks =
    List.map (fun _ -> (new_early_exits st, local st.builder ~name:"task" function_type)) branches
  in
  with_group st ~origin:fork (fun group ->
      let lir_fork = fresh_fork st in
      List.iteri
        (fun index ((branch : Mir.branch), (early_exits, function_value)) ->
          emit st.builder (Region { fork = lir_fork; region = Task { function_value; item } });
          task_body st
            ~id:(Branch { block = fork; index })
            ~group ~early_exits
            (fun task ->
              let inner = new_region st ~enclosing:region ~ending:(fork, task.end_block) in
              run_region st inner ~entry:(branch.entry, 0)))
        (List.combine branches tasks);
      emit st.builder (Regions_end { fork = lir_fork });
      (* [spawn] returns false once the group is cancelled, and the branch
         then never runs. *)
      List.iter
        (fun (_, function_value) ->
          ignore (tasks_bool st "spawn" [ group; at function_value; at item ]))
        tasks);
  List.iter
    (fun (early_exits, _) -> resume_early_exit st region ~lower_ends:(lower_ends st) early_exits)
    tasks;
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
            clear st destination;
            destination
        | None -> discarded st
      in
      call_into st call destination ~origin
  | Lend { part; call } -> lend st part call ~origin
  | Slice { destination; call; _ } | Template { destination; call; _ } ->
      call_into st call (place st destination) ~origin
  | Pull { destination; cursor } -> (
      match mir_place_type st cursor with
      | Ground.Cursor yielding -> call_next st yielding (place st cursor) (place st destination)
      | _ -> bug "next on a place that is not a cursor")
  | Live _ | Loan_start _ | Loan_end _ | Ghost_assert _ | Matched _ | Proof _ -> ()
  | Dead locals -> List.iter (dead st) locals
  | Assert { condition; _ } ->
      let holds = value st condition in
      let failed = block st.builder and after = block st.builder in
      Lir_builder.branch st.builder holds ~yes:after ~no:failed;
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

(* Lowers the ends of scopes that a task's early exit leaves, once the task
   has ended. *)
and lower_ends st ends =
  List.iter
    (fun (statement : Mir.statement) -> in_statement st (fun () -> lower_statement st statement))
    ends

and lir_fork st fork =
  let forks = (mir st).forks in
  match Hashtbl.find_opt forks fork with
  | Some lowered -> lowered
  | None ->
      let lowered = fresh_fork st in
      Hashtbl.replace forks fork lowered;
      lowered

(* Drops the value at a place that is about to be written, if it holds
   one. *)
and clear st place =
  match place_type st place with
  | Some (Value ty) when not (trivial st ty) -> emit st.builder (Drop place)
  | _ -> ()

(* The end of a local: what its end runs, and the drop of what it owns. *)
and dead st local =
  (* A block can be lowered before the block that first assigns a local it
     ends, so the drop makes the local's place if it has none yet. Drop
     elaboration removes it where the local holds nothing. *)
  if owns st local then
    let ty = ground st (info st local).type_ in
    if not (trivial st ty) then emit st.builder (Drop (local_place st local))

and provide st (provided : Mir.provided list) ~can_use_tasks =
  (* The body runs with the evidence of each implementation added. *)
  let enclosing = st.evidence in
  let implementations =
    List.map
      (fun (implementation : Mir.provided) ->
        let place =
          match implementation.value with
          | Use { place = written; _ } | Borrow { place = written; _ } ->
              whole st (place st written)
          | value -> operand_place st value
        in
        let pointer =
          if is_zero_size st (ground st implementation.type_) then Lir.Constant Null
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
  | { root = Local part; projections = [] }, (Construct _ | Operand (Borrow _))
    when Hashtbl.mem frame.built part ->
      build_part st part value
  | { root = Local local; projections = [] }, Operand (Borrow { place = source; mode; _ })
    when Hashtbl.mem frame.aliases local ->
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
      (* The value is evaluated before the old one is dropped where it
         reads the target. *)
      let evaluated =
        if reads_target then begin
          let fresh = temporary st ty in
          into ?types_ty st value fresh ty ~origin;
          Some fresh
        end
        else None
      in
      let destination = whole st (place st target) in
      let frame = mir st in
      (* The result's slot is dropped too: a [return] on another path may
         have written it, where the rest of a lending method joins the
         paths. *)
      if List.mem target frame.taken then
        frame.taken <- List.filter (fun taken -> taken <> target) frame.taken
      else if not (trivial st ty) then emit st.builder (Drop destination);
      match evaluated with
      | Some fresh -> emit st.builder (Assign (destination, Use (owned st fresh ty)))
      | None -> into ?types_ty st value destination ty ~origin)

(* Binds a part built around places: a lent value whose fields hold the
   places' addresses, so that the caller reads and changes the places
   themselves. A constructor or a place assigned to a local that owns no
   value binds it; any other value assigned to it is written to its
   places. *)
and build_part st part (value : Mir.rvalue) =
  let slot =
    match Hashtbl.find_opt (mir st).places part with
    | Some slot -> slot
    | None ->
        let { Mir.kind; type_; _ } = info st part in
        let writable = match kind with Lent Mut | Source { mode = Mut; _ } -> true | _ -> false in
        let lent = built_lent st ~writable (ground st type_) (Hashtbl.find (mir st).built part) in
        let slot = at (local st.builder ~borrowed:true (Value (Lent lent))) in
        bind_local st part slot;
        slot
  in
  let lent =
    match lent_at st slot with Some lent -> lent | None -> bug "a built part with no lent value"
  in
  match value with
  | Construct { variant; fields } ->
      let fields =
        List.map
          (fun (name, (field : Mir.operand option)) ->
            let evaluated () =
              match field with
              | Some (Borrow { place = written; _ }) -> snapshot st (place st written)
              | Some (Use { place = { root = Local nested; projections = [] } as written; _ })
                when Hashtbl.mem (mir st).built nested ->
                  place st written
              | Some field -> operand_place st field
              | None -> fst (field_default_place st lent.base ~variant ~field:name)
            in
            match lent_field lent variant name with
            | Some (Nested inner) -> (name, Lir.Copy (lent_from st inner (evaluated ())))
            | Some Address ->
                (name, Address { place = whole st (evaluated ()); writable = lent.writable })
            | None -> (name, Copy (whole st (evaluated ()))))
          fields
      in
      emit st.builder (Assign (slot, Build { ty = Lent lent; variant; fields }))
  | Operand part ->
      emit st.builder (Assign (slot, Use (Copy (lent_from st lent (operand_part st part)))))
  | _ -> bug "a part built from a value that is no constructor or operand"

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

(* Binds a local to a place it does not own. A binding of the source that
   only reads a number or another scalar takes a copy, which needs no
   address; any other binding, and a borrow that an operation holds, stays
   the place, whose address a view may take. The checker keeps the place
   unchanged while the binding lives. A binding that several patterns bind,
   from different parts, is kept behind a pointer that each pattern sets. *)
and alias st local (source : Lir.place) ~writable =
  let ty = ground st (info st local).type_ in
  if Hashtbl.find (mir st).aliases local > 1 then begin
    let frame = mir st in
    let pointer =
      match Hashtbl.find_opt frame.places local with
      | Some { root = Local pointer; projections = [ Deref ] } -> pointer
      | _ ->
          let pointer =
            Lir_builder.local st.builder ~name:"binding" (Pointer { target = Value ty; writable })
          in
          bind_local st local (at pointer / Deref);
          pointer
    in
    emit st.builder (Assign (at pointer, Use (Address { place = whole st source; writable })))
  end
  else if
    (not writable)
    && (match (Memory_layout.of_type st.context.env ty).form with Scalar _ -> true | _ -> false)
    && lent_at st source = None
    && match (info st local).kind with Source _ -> true | Temporary | Lent _ -> false
  then begin
    let copy = at (Lir_builder.local st.builder ~name:"binding" (Value ty)) in
    emit st.builder (Assign (copy, Use (Copy source)));
    bind_local st local copy
  end
  else bind_local st local (snapshot st source)

(* Evaluates an rvalue and writes its value, of type [ty], to
   [destination], which holds nothing. [types_ty] is the type before it is
   made ground, where the destination is a local. *)
and into ?types_ty st (rvalue : Mir.rvalue) (destination : Lir.place) ty ~origin =
  let assign built = emit st.builder (Assign (destination, built)) in
  match rvalue with
  | Operand operand -> write_operand st operand destination
  | Operation { operation; type_arguments; operands } ->
      let type_arguments, value_arguments = split_arguments st type_arguments in
      ignore
        (Intrinsics.lower ~checks:st.context.checks ~value_arguments st.context.env st.builder
           st.context.types operation ~type_arguments
           (List.map
              (fun operand ->
                let operand_ty = operand_type st operand in
                if Storage.elements_of operand_ty <> None || Storage.viewed operand_ty <> None then
                  Intrinsics.Place (operand_place st operand)
                else Intrinsics.Value (value st operand))
              operands)
           ~destination:(Some destination) ~site:(failure_site st origin))
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
      if st.pulling then
        unsupported ~at:(site_of st origin) "a lambda in a yielding method that is pulled";
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
             (fun (capture : Mir.capture) ->
               (whole st (place st capture.place), ground st capture.type_))
             captures)
        ~body:(fun inner ~captures:capture_places parameter_places ->
          inner.frame <-
            {
              inner.frame with
              mir = Some (frame_of_body ~owner:(innermost_scope inner) ~lambdas lambda);
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
and expression_into ?(arguments = []) st (expression : Core.expression) (destination : Lir.place) =
  mir_into st
    (Mir.of_expression ~parameters:(List.map fst arguments) expression)
    ~arguments:(List.map snd arguments) destination

(* Lowers the MIR of one expression, with its parameters bound to
   [arguments], into [destination]. *)
and mir_into ?(arguments = []) st (expression_mir : Mir.t) (destination : Lir.place) =
  let expression_mir =
    Instance_mir.inlined ~resolve:(inlinable st) ~enclosing:st.frame.inlined expression_mir
  in
  let caller = st.frame in
  let exit = block st.builder in
  let frame =
    frame_of_body ~returns_into:destination ~lambdas:expression_mir.lambdas expression_mir.body
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
      | Yields _ ->
          (* A yielding method called outside a [for] loop makes a cursor,
             which holds its arguments. *)
          cursor_into st ~path ~type_arguments ~signature ~arguments ~mask destination
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
        let lir_signature, result = entry_signature st.context signature in
        let target =
          Lir.Evidence_call
            { evidence = evidence_of st capability; capability; slot; signature = lir_signature }
        in
        emit st.builder
          (Call
             {
               target;
               arguments =
                 List.filter_map (fun (mode, ty, place) -> pass st mode ty place) arguments;
               result = Convention.destination result destination;
             });
        if not lir_signature.returns then unreachable_block st
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
      (fun (parameter : Core.parameter) ((argument : Mir.argument), (_, _, place)) ->
        match (argument, parameter.default) with
        | Default, Some default -> expression_into st default place
        | Default, None -> bug "%s is omitted and has no default" parameter.name
        | Passed _, _ -> ())
      parameters
      (List.combine arguments evaluated);
    st.frame <- caller
  end

(* A call of a lending method or intrinsic: the part it lends is bound to
   [part]. Whatever the lend has left to do, such as the rest of the
   method, runs as [part] ends. *)
(* A lend of a part of a storage, which an intrinsic makes: the part is the
   place itself. *)
and lend st part (call : Mir.call) ~origin =
  match call.callee with
  | Intrinsic { operation; type_arguments } ->
      in_statement st (fun () ->
          match
            intrinsic st operation ~type_arguments call.arguments ~destination:None
              ~site:(failure_site st origin)
          with
          | Some place -> bind_local st part place
          | None -> bug "a lent place from an intrinsic that does not lend")
  | _ -> bug "a lending call that is not inlined"

(* For a cursor, whose caller keeps [next]'s result: a constructor that
   lends places, with a copy of each place in place of the place, which it
   owns. *)
and construct_copied st ty ~variant ~fields ~destination =
  let fields =
    List.map
      (fun (name, (field : Mir.yielded option)) ->
        match field with
        | Some (Part (Borrow { place = written; type_; _ })) ->
            let field_ty = ground st type_ in
            let fresh_copy = temporary st field_ty in
            Glue.copy_into st.context.glue st.builder ~destination:fresh_copy
              ~source:(whole st (place st written))
              field_ty;
            (name, owned st fresh_copy field_ty)
        | Some (Built { variant; fields; type_; _ }) ->
            let nested_ty = ground st type_ in
            let inner = at (local st.builder (Value nested_ty)) in
            construct_copied st nested_ty ~variant ~fields ~destination:inner;
            (name, owned st inner nested_ty)
        | Some (Part nested) -> (name, value st nested)
        | None ->
            let default, default_ty = field_default_place st ty ~variant ~field:name in
            (name, owned st default default_ty))
      fields
  in
  emit st.builder (Assign (destination, Build { ty; variant; fields }))

and terminator st region (ending : Mir.terminator) ~origin =
  match ending with
  | Goto target -> goto st region target
  | Branch { condition; yes; no; _ } ->
      let condition = in_statement st (fun () -> value st condition) in
      let yes = jump st region yes and no = jump st region no in
      Lir_builder.branch st.builder condition ~yes ~no;
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
  | Iteration_end -> continue_loop st
  | Exit_tasks { tasks = left; exit } ->
      let tasks = List.map (fun (left : Mir.left_task) -> (left.task, left.ends)) left in
      let task_end = match left with innermost :: _ -> innermost.task_end | [] -> None in
      (* The block where the task ends is lowered, so that the branch that
         follows the task is found from it. *)
      Option.iter
        (fun target ->
          (* The branch's region lowers the block, in the state the branch
             started in. *)
          let rec branch_region (around : region) =
            match (around.ending, tasks, around.enclosing) with
            | Some (fork, _), (Branch { block; _ }, _) :: _, _ when fork = block -> around
            | _, _, Some enclosing -> branch_region enclosing
            | _, _, None -> bug "an early exit from a branch outside its block"
          in
          let branch = branch_region region in
          ignore (jump ~entry:branch.start st branch target))
        task_end;
      (* The task evaluates the return value into a temporary of its own
         before it cancels the group. Several tasks may do so at the same
         time, and only the first to cancel moves its value out. *)
      let value =
        match (exit, st.frame.exit, returned_type st) with
        | Exit_return (Some returned), None, Some ty ->
            let value = temporary st ty in
            write_operand st returned value;
            Some value
        | _ -> None
      in
      early_exit st region ~tasks ~exit ~value
  | Yield { mode; part; resume } -> yield st region ~mode ~part ~resume ~origin
  | For { iteration; part; body; after; loop; _ } ->
      claim st region after;
      for_loop st region ~iteration ~part ~body ~loop;
      goto st region after
  | Fork { fork; concurrent = true; branches; join } ->
      concurrent_block st region ~fork ~branches ~join
  | Fork { fork; concurrent = false; branches; _ } -> (
      (* A [parallel] block's branches are regions of the code, which
         outlining runs at the same time. *)
      match branches with
      | first :: _ ->
          if may_fork st then emit st.builder (Region { fork = lir_fork st fork; region = Branch });
          goto st region first.entry
      | [] -> unreachable_block st)
  | Join { fork; next } -> (
      match region.ending with
      | Some (ending, end_block) when ending = fork ->
          finish st.builder (Goto end_block);
          start st.builder (block st.builder)
      | _ ->
          (if may_fork st then
             let is_branch =
               Array.exists
                 (fun (basic : Mir.basic_block) ->
                   match basic.terminator with
                   | Fork { fork = started; branches; _ } when started = fork ->
                       List.exists (fun (branch : Mir.branch) -> branch.entry = next) branches
                   | _ -> false)
                 (mir st).body.blocks
             in
             emit st.builder
               (if is_branch then Region { fork = lir_fork st fork; region = Branch }
                else Regions_end { fork = lir_fork st fork }));
          goto st region next)

(* A [yield] of the pulled version of a method, the only [yield] left once
   the methods a body runs are inlined: it stays in the code, and yield
   lowering makes it a state of the cursor. [next] gives its caller a value
   of its own: a value the method made, or a copy of a place it yields. *)
and yield st region ~mode ~part ~resume ~origin =
  if not st.pulling then bug "a yield outside a pulled method";
  let ty = yielded_type_of_frame st in
  let yielded =
    match part with
    | Built _ when mode = Mut ->
        unsupported ~at:(site_of st origin) "a cursor over a method that lends places to be changed"
    | Built { variant; fields; _ } ->
        let copy = temporary st ty in
        construct_copied st ty ~variant ~fields ~destination:copy;
        copy
    | Part (Borrow { place = written; _ }) when trivial st ty -> whole st (place st written)
    | Part (Borrow { place = written; _ }) ->
        let copy = temporary st ty in
        Glue.copy_into st.context.glue st.builder ~destination:copy
          ~source:(whole st (place st written))
          ty;
        copy
    | Part part -> operand_place st part
  in
  let resume = jump st region resume and stop = block st.builder in
  finish st.builder (Yield { value = owned st yielded ty; resume; stop = Some stop });
  (* On the [stop] path the cursor is dropped before it ended, so the
     method drops its owned values and returns. *)
  start st.builder stop;
  leave_to st 0;
  finish st.builder (Return None);
  start st.builder (block st.builder)

(* Lowers a [for] loop's body as a region of its own, once [value] is the
   place of the element. *)
and loop_body st region ~part ~body (value : Lir.place) =
  let caller = st.frame in
  st.frame <- region.region_frame;
  bind_local st part value;
  let inner = new_region ~enclosing:region st in
  st.frame <- caller;
  run_region st inner ~entry:(body, 0)

(* A loop over the cursor of a yielding method's call: the pulled method's
   [next] is called until it gives [None]. *)
and pull_cursor st (yielding : Ground.yielding) cursor ~(each : Lir.place -> unit) =
  pull_loop st
    ~option:(cursor_result st.context yielding)
    ~call_next:(fun destination -> call_next st yielding cursor destination)
    ~body:each

and for_loop st region ~(iteration : Mir.iteration) ~part ~body ~(loop : Mir.loop) =
  let origin = loop.origin in
  let each = loop_body st region ~part ~body in
  match loop.schedule with
  | Concurrent_loop ->
      (* The enclosing code runs the iteration and spawns one task for each
         value. *)
      let early_exits = new_early_exits st in
      with_group st ~origin (fun group ->
          let spawning =
            {
              origin;
              group;
              early_exits;
              item = local st.builder ~name:"item" (Value (Monomorphic.builtin UInt64));
              element = ground st (info st part).type_;
            }
          in
          for_each st ~schedule:(Spawned spawning) ~iteration ~each);
      resume_early_exit st region ~lower_ends:(lower_ends st) early_exits
  | Parallel_loop -> for_each st ~schedule:Chunked ~iteration ~each
  | Core.Sequential -> for_each st ~schedule:Sequential ~iteration ~each

(* Lowers a loop over [iteration]. [each] lowers the loop body for the
   place of one value. The loop is the innermost loop for the body: the end
   of an iteration starts the next one. *)
and for_each st ~(schedule : schedule) ~(iteration : Mir.iteration) ~(each : Lir.place -> unit) =
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
  | Yielding _ -> bug "a loop over a yielding method that is not inlined"
  | Pull { cursor; next = None } -> (
      match mir_place_type st cursor with
      | Ground.Cursor yielding -> pull_cursor st yielding (place st cursor) ~each:owned_each
      | _ -> bug "a loop over a place that is not a cursor")
  | Pull { cursor; next = Some next } ->
      (* A value of a type that implements [Cursor]: its own [next] is
         called until it gives [None]. *)
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
  let constant value : Lir.operand =
    match scalar with
    | Integer integer -> constant_int integer (Z.of_int value)
    | Character -> Constant (Character value)
    | _ -> bug "a range of %s" (Ground.to_string element)
  in
  let characters = scalar = Character in
  let both first second =
    let answer = local st.builder (Raw Bool) in
    emit st.builder (Assign (at answer, Binary (Bit_and, first, second)));
    Lir.Copy (at answer)
  in
  let compare op left right =
    let answer = local st.builder (Raw Bool) in
    emit st.builder (Assign (at answer, Binary (op, left, right)));
    Lir.Copy (at answer)
  in
  match schedule with
  | Chunked ->
      (* The loop is a region that covers a part of the range's indexes,
         counted from 0 as [UInt64], so that a range of any integer type
         has as many indexes as fit. As it is written here it covers them
         all; outlining has it run for parts of them at the same time. *)
      let wide = Lir.Raw (Integer UInt64) in
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
      Lir_builder.branch st.builder (Copy (at going)) ~yes:inside ~no:after;
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
      let fork = fresh_fork st in
      emit st.builder (Region { fork; region = Chunk { first; last } });
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
              (fun () -> emit st.builder (Assign (bound, Binary (Add, Copy bound, constant 0x800))));
          looping st ~continue_:step ~break_:done_ ~depth (fun () -> each bound));
      finish st.builder (Goto step);
      start st.builder step;
      let ended = local st.builder (Raw Bool) in
      emit st.builder (Assign (at ended, Binary (Equal, Copy (at index), Copy (at last))));
      let next = block st.builder in
      Lir_builder.branch st.builder (Copy (at ended)) ~yes:done_ ~no:next;
      start st.builder next;
      emit st.builder (Assign (at index, Binary (Add, Copy (at index), one)));
      finish st.builder (Goto again);
      start st.builder done_;
      emit st.builder (Regions_end { fork });
      finish st.builder (Goto after);
      start st.builder after
  | Sequential | Spawned _ ->
      let index = binding st ~name:"index" element in
      let stop = binding st element in
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
      Lir_builder.branch st.builder (Copy (at going)) ~yes:inside ~no:after;
      start st.builder inside;
      looping st ~continue_:step ~break_:after ~depth (fun () ->
          let run value =
            in_scope st (fun () ->
                let bound = binding st element in
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
        Lir_builder.branch st.builder (Copy (at last)) ~yes:after ~no:next;
        start st.builder next
      end;
      emit st.builder (Assign (index, Binary (Add, Copy index, constant 1)));
      if characters then
        when_ st.builder
          (compare Equal (Copy index) (constant 0xD800))
          (fun () -> emit st.builder (Assign (index, Use (constant 0xE000))));
      finish st.builder (Goto test);
      start st.builder after

(* Fills in each parameter whose argument the caller omitted, as the bits
   of [mask] say, by evaluating the default inside the function, so that
   changing a default compiles only the function again. An [own] parameter
   with a default may arrive holding nothing, so the function does not own
   it as it arrives: its name is bound to a local the function owns, which
   takes the argument or the default. A parameter that is a view is pointed
   at the default's value, or given its bits, and the function owns that
   value. *)
let fill_defaults st mask (body : Mir.body) (places : Lir.place list) =
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
               ( at passed,
                 Binary (Bit_and, Copy (at mask), constant_int UInt64 (Z.shift_left Z.one bit)) ));
          emit builder
            (Assign (at is_passed, Binary (Not_equal, Copy (at passed), constant_int UInt64 Z.zero)));
          let fill = block builder and after = block builder in
          let unless_passed other =
            Lir_builder.branch builder (Copy (at is_passed)) ~yes:other ~no:fill
          in
          let pulled reason =
            if st.pulling then
              unsupported
                ~at:(site_of st (default_origin default))
                "a default for %s, %s, in a yielding method that is pulled" name reason
          in
          let place =
            if mode = Own && not (trivial st ty) then begin
              let owned_here = binding st ~name ty in
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
                      pulled "which is passed by address";
                      let value = binding st ty in
                      mir_into st default value;
                      emit builder
                        (Assign (at pointer, Use (Address { place = value; writable = true })))
                  | place when not (trivial st ty) ->
                      pulled "which is a view";
                      let value = binding st ty in
                      mir_into st default value;
                      emit builder (Assign (place, Use (Copy value)))
                  | place -> mir_into st default place);
              arrived
            end
          in
          finish builder (Goto after);
          start builder after;
          place)
    body.parameters places

(* Lowers the MIR of the code at [path] in the current frame, with its
   parameters in [parameters], in order. *)
let lower_code st path ~parameters =
  let code_mir =
    Instance_mir.inlined ~resolve:(inlinable st) ~enclosing:st.frame.inlined
      (mir_of st.context path)
  in
  let frame = frame_of_body ~owner:(innermost_scope st) ~lambdas:code_mir.lambdas code_mir.body in
  st.frame <- { st.frame with mir = Some frame };
  List.iter2 (bind_local st) code_mir.body.parameters parameters;
  make_owned_locals st;
  lower_body st frame
