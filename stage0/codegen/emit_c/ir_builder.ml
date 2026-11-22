let raise_bug format = Compiler_bug.raise_bug ~stage:"Ir_builder" format
let ( ++ ) = C_text.( ++ )

module Locals = Set.Make (Int)
module Blocks = Set.Make (Int)

type local_info = { ty : Lowered.ty; name : string option; is_zeroed : bool }
type code = { emission : Emission.t; mutable nested : (int * Fragment.function_pieces) list }

type role =
  | Enclosing
  | Outlined of {
      index : int;
      parent : int;
      arrives : Lowered.local;
      parts : Lowered.local list;
      holder : Lowered.local;
      environment : Lowered.local;
    }

type prototype = { parameters : Lowered.local list; result : Lowered.ty option; returns : bool }

type function_ = {
  code : code;
  role : role;
  entry : Lowered.block;
  opening : Lowered.site option;
  mutable size : int;
}

type passing = By_value | By_address
type capture = { local : Lowered.local; field : string; passing : passing }

type block_body = {
  mutable statements : (Lowered.site option * Lowered.statement) list;
  mutable terminator : (Lowered.site option * Lowered.terminator) option;
}

type t = {
  env : Memory_layout.env;
  locals : local_info Dynarray.t;
  bodies : block_body Dynarray.t;
  owners : int option Dynarray.t;
  mutable current : Lowered.block;
  functions : function_ Dynarray.t;
  mutable function_ : int;
  mutable site : Lowered.site option;
}

let make_function ~code ~role ~entry ~opening = { code; role; entry; opening; size = 0 }

let make_builder env ~site =
  {
    env;
    locals = Dynarray.create ();
    bodies = Dynarray.create ();
    owners = Dynarray.create ();
    current = 0;
    functions = Dynarray.create ();
    function_ = 0;
    site;
  }

let make_empty_body () = { statements = []; terminator = None }

let allocate_block builder =
  Dynarray.add_last builder.bodies (make_empty_body ());
  Dynarray.add_last builder.owners None;
  Dynarray.length builder.bodies - 1

let start_function builder ~code =
  Dynarray.add_last builder.functions
    (make_function ~code ~role:Enclosing ~entry:0 ~opening:builder.site);
  builder

let create ?site env ~item =
  start_function (make_builder env ~site)
    ~code:{ emission = Emission.create env ~item; nested = [] }

let with_site builder site body =
  let enclosing = builder.site in
  builder.site <- Some site;
  let result = body () in
  builder.site <- enclosing;
  result

let allocate_local builder ?name ?(is_zeroed = false) ty =
  Dynarray.add_last builder.locals { ty; name; is_zeroed };
  Dynarray.length builder.locals - 1

let lookup_local_type builder local = (Dynarray.get builder.locals local).ty
let lookup_current_function builder = Dynarray.get builder.functions builder.function_

let start builder block =
  Dynarray.set builder.owners block (Some builder.function_);
  Dynarray.set builder.bodies block (make_empty_body ());
  builder.current <- block

let find_constant_truth : Lowered.test -> bool option = function
  | comparison, Constant (Integer (left_integer, left)), Constant (Integer (right_integer, right))
    when left_integer = right_integer -> (
      match comparison with
      | Greater -> Some (Z.gt left right)
      | Greater_equal -> Some (Z.geq left right)
      | Less -> Some (Z.lt left right)
      | Less_equal -> Some (Z.leq left right)
      | Equal -> Some (Z.equal left right)
      | Not_equal -> Some (not (Z.equal left right))
      | Ieee_equal | Ieee_less | Ieee_less_equal -> None)
  | Equal, Constant (Bool left), Constant (Bool right) -> Some (left = right)
  | Not_equal, Constant (Bool left), Constant (Bool right) -> Some (left <> right)
  | _ -> None

let fold_constants (rvalue : Lowered.rvalue) : Lowered.rvalue =
  match rvalue with
  | Compare test -> (
      match find_constant_truth test with
      | Some truth -> Use (Constant (Bool truth))
      | None -> rvalue)
  | Unary (Not, Constant (Bool truth)) -> Use (Constant (Bool (not truth)))
  | _ -> rvalue

let find_folded_statement (statement : Lowered.statement) : Lowered.statement option =
  match statement with
  | Assign (place, rvalue) -> Some (Assign (place, fold_constants rvalue))
  | Fail_obligation_when { test; _ } when find_constant_truth test = Some false -> None
  | _ -> Some statement

let emit builder statement =
  match find_folded_statement statement with
  | None -> ()
  | Some statement ->
      let function_ = lookup_current_function builder in
      function_.size <- function_.size + 1;
      let body = Dynarray.get builder.bodies builder.current in
      body.statements <- (builder.site, statement) :: body.statements

let finish builder terminator =
  let function_ = lookup_current_function builder in
  function_.size <- function_.size + 2;
  (Dynarray.get builder.bodies builder.current).terminator <- Some (builder.site, terminator)

let run_in_block builder block body =
  let current = builder.current in
  start builder block;
  body ();
  builder.current <- current

let emit_value builder ty (rvalue : Lowered.rvalue) : Lowered.operand =
  let temporary = allocate_local builder ty in
  emit builder (Assign (Lowered.make_local_place temporary, rvalue));
  Copy (Lowered.make_local_place temporary)

type condition =
  | Test of Lowered.test
  | Holds of Lowered.operand
  | Negation of condition
  | Conjunction of condition * condition
  | Disjunction of condition * condition

let make_holds_test operand : Lowered.test = (Not_equal, operand, Constant (Bool false))

let rec branch builder condition ~yes ~no =
  match condition with
  | Test test -> (
      match find_constant_truth test with
      | Some true -> finish builder (Goto yes)
      | Some false -> finish builder (Goto no)
      | None -> finish builder (Branch { test; yes; no }))
  | Holds operand -> branch builder (Test (make_holds_test operand)) ~yes ~no
  | Negation negated -> branch builder negated ~yes:no ~no:yes
  | Conjunction (first, second) ->
      let second_test = allocate_block builder in
      branch builder first ~yes:second_test ~no;
      start builder second_test;
      branch builder second ~yes ~no
  | Disjunction (first, second) ->
      let second_test = allocate_block builder in
      branch builder first ~yes ~no:second_test;
      start builder second_test;
      branch builder second ~yes ~no

let rec evaluate builder condition : Lowered.rvalue =
  match condition with
  | Test test -> Compare test
  | Holds operand -> Use operand
  | Negation negated -> Unary (Not, evaluate_operand builder negated)
  | Conjunction (first, second) ->
      let first = evaluate_operand builder first in
      Binary (Bit_and, first, evaluate_operand builder second)
  | Disjunction (first, second) ->
      let first = evaluate_operand builder first in
      Binary (Bit_or, first, evaluate_operand builder second)

and evaluate_operand builder condition =
  match evaluate builder condition with
  | Use operand -> operand
  | rvalue -> emit_value builder (Raw Bool) rvalue

let evaluate_test builder condition =
  match condition with
  | Test test -> test
  | Holds operand -> make_holds_test operand
  | Negation _ | Conjunction _ | Disjunction _ ->
      make_holds_test (evaluate_operand builder condition)

let emit_when builder condition then_ =
  let inside = allocate_block builder in
  let after = allocate_block builder in
  branch builder condition ~yes:inside ~no:after;
  start builder inside;
  then_ ();
  finish builder (Goto after);
  start builder after

let emit_if builder condition ~yes ~no =
  let when_true = allocate_block builder
  and when_false = allocate_block builder
  and after = allocate_block builder in
  branch builder condition ~yes:when_true ~no:when_false;
  start builder when_true;
  yes ();
  finish builder (Goto after);
  start builder when_false;
  no ();
  finish builder (Goto after);
  start builder after

let emit_loop builder ?(integer = Memory_layout.UInt64) ~count body =
  let make_constant number = Lowered.Constant (Integer (integer, Z.of_int number)) in
  let index = allocate_local builder (Raw (Integer integer)) in
  let test = allocate_block builder in
  let inside = allocate_block builder in
  let after = allocate_block builder in
  emit builder (Assign (Lowered.make_local_place index, Use (make_constant 0)));
  finish builder (Goto test);
  start builder test;
  branch builder (Test (Less, Copy (Lowered.make_local_place index), count)) ~yes:inside ~no:after;
  start builder inside;
  body index;
  emit builder
    (Assign
       ( Lowered.make_local_place index,
         Binary (Add, Copy (Lowered.make_local_place index), make_constant 1) ));
  finish builder (Goto test);
  start builder after

let write_in builder number body =
  let function_ = builder.function_ and current = builder.current in
  builder.function_ <- number;
  body ();
  builder.function_ <- function_;
  builder.current <- current

let outline builder ~index ~parts body =
  let code = (lookup_current_function builder).code in
  let holder = allocate_local builder (Environment index) in
  let arrives = allocate_local builder (Raw (Nullable_pointer Opaque)) in
  let environment =
    allocate_local builder (Pointer { target = Environment index; writable = false })
  in
  let entry = allocate_block builder in
  Dynarray.add_last builder.functions
    (make_function ~code
       ~role:(Outlined { index; parent = builder.function_; arrives; parts; holder; environment })
       ~entry ~opening:builder.site);
  let number = Dynarray.length builder.functions - 1 in
  write_in builder number (fun () ->
      start builder entry;
      body ());
  holder

let render_local_name builder local =
  C_values.render_local_name local (Dynarray.get builder.locals local).name

let make_context builder ~note : C_values.function_context =
 fun local ->
  note local;
  (Name (Local local), lookup_local_type builder local)

let mark_reached_blocks builder functions =
  let reached = Array.make (Dynarray.length builder.bodies) false in
  let jump_targets = ref Blocks.empty in
  let rec reach block =
    if not reached.(block) then begin
      reached.(block) <- true;
      match (Dynarray.get builder.bodies block).terminator with
      | Some (_, terminator) ->
          List.iter
            (fun target ->
              jump_targets := Blocks.add target !jump_targets;
              reach target)
            (Lowered.list_successors terminator)
      | None -> ()
    end
  in
  Array.iter (fun (function_ : function_) -> reach function_.entry) functions;
  (reached, !jump_targets)

let check_return ~result ~gives =
  match (gives, result) with
  | false, Some _ -> raise_bug "a return of nothing from a function with a result"
  | true, None -> raise_bug "a return of a value from a function with no result"
  | _ -> ()

let print_reached_blocks builder functions ~reached ~result_types ~contexts =
  Array.mapi
    (fun block is_reached ->
      match Dynarray.get builder.owners block with
      | Some number when is_reached ->
          let function_ = functions.(number) and body = Dynarray.get builder.bodies block in
          let emission = function_.code.emission and fc = contexts.(number) in
          let statements =
            List.map
              (fun (site, statement) ->
                C_text.Line_control site ++ C_code.render_statement emission fc statement)
              (List.rev body.statements)
          in
          let terminator =
            match body.terminator with
            | Some (site, (Return value as terminator)) ->
                check_return ~result:result_types.(number)
                  ~gives:
                    (match value with
                    | Some operand -> C_values.render_operand emission fc operand <> None
                    | None -> false);
                C_text.Line_control site ++ C_code.render_terminator emission fc terminator
            | Some (site, terminator) ->
                C_text.Line_control site ++ C_code.render_terminator emission fc terminator
            | None -> raise_bug "block %d is never finished" block
          in
          C_text.Concat (statements @ [ terminator ])
      | Some _ | None -> C_text.empty)
    reached

let find_storage_local (place : Lowered.place) =
  match place.root with
  | Local local when not (List.mem Lowered.Deref place.projections) -> Some local
  | Local _ | Static _ -> None

let rec list_operand_addressed : Lowered.operand -> Lowered.local list = function
  | Copy place | Move place -> list_index_addressed place
  | Address { place; _ } | Moved_address place -> list_place_written_or_addressed place
  | Constant _ -> []

and list_index_addressed (place : Lowered.place) =
  List.concat_map
    (function
      | Lowered.Index operand -> list_operand_addressed operand
      | Field _ | Variant_field _ | Deref -> [])
    place.projections

and list_place_written_or_addressed place =
  Option.to_list (find_storage_local place) @ list_index_addressed place

let list_operands_addressed operands = List.concat_map list_operand_addressed operands

let list_rvalue_addressed : Lowered.rvalue -> Lowered.local list = function
  | Use operand | Unary (_, operand) | Convert (operand, _) -> list_operand_addressed operand
  | Binary (_, left, right) | Compare (_, left, right) -> list_operands_addressed [ left; right ]
  | Build { fields; _ } -> list_operands_addressed (List.map snd fields)
  | Is_variant (place, _) -> list_index_addressed place
  | Function_value { environment; _ } -> list_operands_addressed (Option.to_list environment)
  | Data _ -> []

let list_target_operands : Lowered.target -> Lowered.operand list = function
  | Direct _ | Intrinsic _ | Foreign _ -> []
  | Indirect { code; environment; _ } -> [ code; environment ]
  | Evidence_call { evidence; _ } -> [ evidence ]
  | Table_call { table; value; _ } -> [ table; value ]

let list_failure_operands ~message ~length ~reported ~trace =
  message :: length :: (Option.to_list reported @ Option.to_list trace)

let list_destination_written_or_addressed : Lowered.destination -> Lowered.local list = function
  | Discarded -> []
  | Returned place | Written place -> list_place_written_or_addressed place

let list_statement_written_or_addressed : Lowered.statement -> Lowered.local list = function
  | Assign (place, rvalue) -> list_place_written_or_addressed place @ list_rvalue_addressed rvalue
  | Call { target; arguments; result } ->
      list_operands_addressed (list_target_operands target @ arguments)
      @ list_destination_written_or_addressed result
  | Drop place | Free_block { place; _ } -> list_place_written_or_addressed place
  | Defer_free_block { lend; arena; place; _ } ->
      list_operands_addressed [ lend; arena ] @ list_place_written_or_addressed place
  | Echo { text; length; _ } -> list_operands_addressed [ text; length ]
  | Fail_obligation_when { test = _, left, right; message; length; reported; trace; _ } ->
      list_operands_addressed
        (left :: right :: list_failure_operands ~message ~length ~reported ~trace)
  | Fork { branches } -> list_operands_addressed (List.map snd branches)
  | Fork_range { environment; first; last; _ } ->
      list_operands_addressed [ environment; first; last ]

let list_terminator_addressed : Lowered.terminator -> Lowered.local list = function
  | Goto _ | Unreachable -> []
  | Branch { test = _, left, right; _ } -> list_operands_addressed [ left; right ]
  | Switch { value; _ } -> list_operand_addressed value
  | Switch_variant { place; _ } -> list_index_addressed place
  | Return operand -> list_operands_addressed (Option.to_list operand)
  | Fail { message; length; reported; trace; _ } ->
      list_operands_addressed (list_failure_operands ~message ~length ~reported ~trace)

let compute_written_or_addressed builder functions =
  let own = Array.map (fun _ -> Locals.empty) functions in
  Dynarray.iteri
    (fun block (body : block_body) ->
      match Dynarray.get builder.owners block with
      | Some number ->
          let locals =
            List.concat_map
              (fun (_, statement) -> list_statement_written_or_addressed statement)
              body.statements
            @ Option.fold ~none:[]
                ~some:(fun (_, terminator) -> list_terminator_addressed terminator)
                body.terminator
          in
          own.(number) <- Locals.union (Locals.of_list locals) own.(number)
      | None -> ())
    builder.bodies;
  let within = Array.copy own in
  Array.iteri
    (fun number locals ->
      let rec reach number =
        match functions.(number).role with
        | Outlined { parent; _ } ->
            within.(parent) <- Locals.union locals within.(parent);
            reach parent
        | Enclosing -> ()
      in
      reach number)
    own;
  within

let find_homes functions ~mentioned =
  let read_parent number =
    match functions.(number).role with Enclosing -> number | Outlined { parent; _ } -> parent
  in
  let rec compute_depth number =
    match functions.(number).role with
    | Enclosing -> 0
    | Outlined { parent; _ } -> 1 + compute_depth parent
  in
  let rec compute_enclosing first second =
    if first = second then first
    else if compute_depth first >= compute_depth second then
      compute_enclosing (read_parent first) second
    else compute_enclosing first (read_parent second)
  in
  let home = Hashtbl.create 64 in
  Array.iteri
    (fun number (function_ : function_) ->
      Locals.iter
        (fun local ->
          match function_.role with
          | Outlined { parts; _ } when List.mem local parts -> ()
          | Enclosing | Outlined _ ->
              Hashtbl.replace home local
                (match Hashtbl.find_opt home local with
                | Some other -> compute_enclosing number other
                | None -> number))
        mentioned.(number))
    functions;
  home

let list_captures functions ~home ~mentioned ~written_or_addressed ~is_scalar ~is_local_to =
  let captured = Array.make (Array.length functions) Locals.empty in
  Array.iteri
    (fun number locals ->
      Locals.iter
        (fun local ->
          if not (is_local_to number local) then
            let owner = Hashtbl.find home local in
            let rec reach number =
              if number <> owner then begin
                captured.(number) <- Locals.add local captured.(number);
                match functions.(number).role with
                | Outlined { parent; _ } -> reach parent
                | Enclosing -> ()
              end
            in
            reach number)
        locals)
    mentioned;
  Array.mapi
    (fun number locals ->
      List.mapi
        (fun position local ->
          {
            local;
            field = Printf.sprintf "capture%d" position;
            passing =
              (if is_scalar local && not (Locals.mem local written_or_addressed.(number)) then
                 By_value
               else By_address);
          })
        (Locals.elements locals))
    captured

let is_scalar_type (emission : Emission.t) : Lowered.ty -> bool = function
  | Pointer _ | Raw _ -> true
  | Value ty -> not (C_types.is_struct emission.types ty)
  | Environment _ | Evidence _ | Capabilities _ | Trace | Lend | Lend_arena -> false

let make_address_type builder local : Lowered.ty =
  Pointer { target = lookup_local_type builder local; writable = true }

let register_environments builder functions ~captures =
  Array.iteri
    (fun number (function_ : function_) ->
      match function_.role with
      | Outlined { index; _ } ->
          C_types.add_environment function_.code.emission.types index
            (List.map
               (fun { local; field; _ } -> (field, make_address_type builder local))
               captures.(number))
      | Enclosing -> ())
    functions

let print_fills builder functions ~captures =
  let fills = Array.map (fun _ -> []) functions in
  let fc = make_context builder ~note:ignore in
  Array.iteri
    (fun number (function_ : function_) ->
      match function_.role with
      | Outlined { holder; parent; _ } ->
          List.iter
            (fun { local; field; _ } ->
              fills.(parent) <-
                C_code.render_statement functions.(parent).code.emission fc
                  (Assign
                     ( { root = Local holder; projections = [ Field field ] },
                       Use (Address { place = Lowered.make_local_place local; writable = true }) ))
                :: fills.(parent))
            captures.(number)
      | Enclosing -> ())
    functions;
  Array.map (fun fills -> C_text.Concat (List.rev fills)) fills

let render_address_name builder local = render_local_name builder local ^ "_address"

let name_local builder ~is_local ~captures local =
  if is_local local then render_local_name builder local
  else
    match List.find_opt (fun capture -> capture.local = local) captures with
    | Some { passing = By_value; _ } -> render_local_name builder local
    | Some { passing = By_address; _ } -> "(*" ^ render_address_name builder local ^ ")"
    | None -> raise_bug "local %d is neither local to the function nor captured by it" local

let render_local_declarations builder (emission : Emission.t) ~locals ~parameters =
  C_text.Concat
    (List.filter_map
       (fun local ->
         let ty = lookup_local_type builder local in
         if List.mem local parameters || Lowered.is_erased emission.types.env ty then None
         else
           let name : C_text.t = Name (Local local) in
           let initializer_ : C_text.t =
             if not (Dynarray.get builder.locals local).is_zeroed then Text ""
             else
               match ty with
               | Value ty when C_types.is_struct emission.types ty -> Text " = {0}"
               | Value _ | Pointer _ | Raw _ -> Text " = 0"
               | Lend -> Text " = {0}"
               | Lend_arena -> Text "; " ++ name ++ Text ".used = 0; " ++ name ++ Text ".top = 0"
               | Environment _ | Evidence _ | Capabilities _ | Trace ->
                   raise_bug "a zeroed environment, evidence slot, table, or link of the call chain"
           in
           Some
             (Text "  "
             ++ C_types.render_type emission.types ty
             ++ Text " " ++ name ++ initializer_ ++ Text ";\n"))
       locals)

let render_blocks builder number (function_ : function_) ~reached ~jump_targets ~texts =
  C_text.Concat
    (List.map
       (fun block ->
         Text (if Blocks.mem block jump_targets then Printf.sprintf "b%d:;\n" block else "")
         ++ texts.(block))
       (function_.entry
       :: List.filter
            (fun block ->
              block <> function_.entry
              && Dynarray.get builder.owners block = Some number
              && reached.(block))
            (List.init (Dynarray.length builder.bodies) Fun.id)))

let render_thunk_body builder (emission : Emission.t) ~index ~arrives ~parts ~environment ~captures
    =
  let field_address field = Text "(*" ++ Name (Local environment) ++ Text (").f_" ^ field) in
  let arguments =
    List.map
      (fun { field; passing; _ } ->
        match passing with
        | By_value -> Text "*" ++ field_address field
        | By_address -> field_address field)
      captures
    @ List.map (fun part : C_text.t -> Name (Local part)) parts
  in
  Text " {\n"
  ++ render_local_declarations builder emission ~locals:[ environment ] ~parameters:[]
  ++ C_code.render_statement emission
       (make_context builder ~note:ignore)
       (Assign (Lowered.make_local_place environment, Use (Copy (Lowered.make_local_place arrives))))
  ++ Text "  " ++ Name (Nested_body index) ++ Text "(" ++ C_text.join ", " arguments
  ++ Text ");\n}\n"

let make_pieces (function_ : function_) symbol ~names ~(signature : Lowered.signature) ~body
    ~name_local : Fragment.function_pieces =
  {
    symbol;
    header =
      C_values.render_prototype function_.code.emission (Name symbol) ~names ~linkage:External
        signature;
    opening = function_.opening;
    body;
    name_local;
  }

let write_functions builder ~enclosing_symbol { parameters; result; returns } =
  let functions = Dynarray.to_array builder.functions in
  let list_parameters number =
    match functions.(number).role with Enclosing -> parameters | Outlined { parts; _ } -> parts
  in
  let result_types =
    Array.map
      (fun (function_ : function_) ->
        match function_.role with Enclosing -> result | Outlined _ -> None)
      functions
  in
  let reached, jump_targets = mark_reached_blocks builder functions in
  let mentioned = Array.map (fun _ -> Locals.empty) functions in
  mentioned.(0) <- Locals.of_list parameters;
  let contexts =
    Array.mapi
      (fun number _ ->
        make_context builder ~note:(fun local ->
            mentioned.(number) <- Locals.add local mentioned.(number)))
      functions
  in
  let texts = print_reached_blocks builder functions ~reached ~result_types ~contexts in
  let home = find_homes functions ~mentioned in
  let is_local_to number local =
    List.mem local (list_parameters number)
    || Hashtbl.find_opt home local = Some number
    || Lowered.is_erased builder.env (lookup_local_type builder local)
  in
  let written_or_addressed = compute_written_or_addressed builder functions in
  let is_scalar local =
    is_scalar_type functions.(0).code.emission (lookup_local_type builder local)
  in
  let captures =
    list_captures functions ~home ~mentioned ~written_or_addressed ~is_scalar ~is_local_to
  in
  register_environments builder functions ~captures;
  let fills = print_fills builder functions ~captures in
  let render_body number (function_ : function_) =
    let locals =
      List.sort compare
        (Hashtbl.fold
           (fun local owner locals -> if owner = number then local :: locals else locals)
           home [])
    in
    Text " {\n"
    ++ render_local_declarations builder function_.code.emission ~locals
         ~parameters:(list_parameters number)
    ++ fills.(number)
    ++ render_blocks builder number function_ ~reached ~jump_targets ~texts
    ++ Text "}\n"
  in
  let name_parameters locals = List.map (fun local : C_text.t -> Name (Local local)) locals in
  let list_types locals = List.map (lookup_local_type builder) locals in
  Array.iteri
    (fun number (function_ : function_) ->
      match function_.role with
      | Outlined { index; arrives; parts; environment; _ } ->
          let capture_names, capture_types =
            List.split
              (List.map
                 (fun { local; passing; _ } : (C_text.t * Lowered.ty) ->
                   match passing with
                   | By_value -> (Name (Local local), lookup_local_type builder local)
                   | By_address ->
                       (Text (render_address_name builder local), make_address_type builder local))
                 captures.(number))
          in
          let body =
            make_pieces function_ (Nested_body index)
              ~names:(capture_names @ name_parameters parts)
              ~signature:
                { parameters = capture_types @ list_types parts; result = None; returns = true }
              ~body:(render_body number function_)
              ~name_local:
                (name_local builder ~is_local:(is_local_to number) ~captures:captures.(number))
          in
          let thunk_locals = arrives :: environment :: parts in
          let thunk =
            make_pieces function_ (Nested_function index)
              ~names:(name_parameters (arrives :: parts))
              ~signature:
                { parameters = list_types (arrives :: parts); result = None; returns = true }
              ~body:
                (render_thunk_body builder function_.code.emission ~index ~arrives ~parts
                   ~environment ~captures:captures.(number))
              ~name_local:
                (name_local builder
                   ~is_local:(fun local -> List.mem local thunk_locals)
                   ~captures:[])
          in
          function_.code.nested <- (index, body) :: (index, thunk) :: function_.code.nested
      | Enclosing -> ())
    functions;
  make_pieces functions.(0) enclosing_symbol ~names:(name_parameters parameters)
    ~signature:{ parameters = list_types parameters; result; returns }
    ~body:(render_body 0 functions.(0))
    ~name_local:(name_local builder ~is_local:(is_local_to 0) ~captures:captures.(0))

let build builder prototype =
  let enclosing = Dynarray.get builder.functions 0 in
  let { emission; _ } = enclosing.code in
  let enclosing_pieces =
    write_functions builder ~enclosing_symbol:(C_text.Item emission.item) prototype
  in
  let nested =
    List.sort (fun (first, _) (second, _) -> Int.compare first second) enclosing.code.nested
  in
  Fragment.make emission
    ~kind:(Functions { nested = List.length nested; weight = enclosing.size })
    ~references:(Emission.list_references emission)
    ~functions:(List.map snd nested @ [ enclosing_pieces ])
    ~definition:C_text.empty

let build_nested parent ~index ~environment build_body =
  let code = (lookup_current_function parent).code in
  C_types.add_environment code.emission.types index environment;
  let builder = start_function (make_builder parent.env ~site:parent.site) ~code in
  let prototype = build_body builder in
  code.nested <-
    (index, write_functions builder ~enclosing_symbol:(Nested_function index) prototype)
    :: code.nested
