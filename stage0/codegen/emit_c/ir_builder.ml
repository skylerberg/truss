let raise_bug format = Compiler_bug.raise_bug ~stage:"Ir_builder" format

module Locals = Set.Make (Int)
module Blocks = Set.Make (Int)

type local_info = { ty : Lowered.ty; name : string option; is_zeroed : bool }

type code = {
  item : Lowered.Item.t;
  emission : Emission.t;
  mutable nested : (int * (string * string)) list;
}

type role =
  | Enclosing
  | Outlined of {
      index : int;
      parent : int;
      parts : Lowered.local list;
      holder : Lowered.local;
      environment : Lowered.local;
    }

type prototype = { parameters : Lowered.local list; result : Lowered.ty option; returns : bool }

type function_ = {
  code : code;
  role : role;
  entry : Lowered.block;
  prologue : Lowered.statement list;
  mutable size : int;
}

type block_body = {
  mutable statements : Lowered.statement list;
  mutable terminator : Lowered.terminator option;
}

type t = {
  env : Memory_layout.env;
  locals : local_info Dynarray.t;
  bodies : block_body Dynarray.t;
  owners : int option Dynarray.t;
  mutable current : Lowered.block;
  functions : function_ Dynarray.t;
  mutable function_ : int;
}

let make_function ~code ~role ~entry ~prologue = { code; role; entry; prologue; size = 0 }

let make_builder env =
  {
    env;
    locals = Dynarray.create ();
    bodies = Dynarray.create ();
    owners = Dynarray.create ();
    current = 0;
    functions = Dynarray.create ();
    function_ = 0;
  }

let make_empty_body () = { statements = []; terminator = None }

let allocate_block builder =
  Dynarray.add_last builder.bodies (make_empty_body ());
  Dynarray.add_last builder.owners None;
  Dynarray.length builder.bodies - 1

let start_function builder ~code =
  Dynarray.add_last builder.functions (make_function ~code ~role:Enclosing ~entry:0 ~prologue:[]);
  builder

let create env ~item =
  let code =
    { item; emission = Emission.create env ~prefix:(Mangling.make_symbol item); nested = [] }
  in
  start_function (make_builder env) ~code

let allocate_local builder ?name ?(is_zeroed = false) ty =
  Dynarray.add_last builder.locals { ty; name; is_zeroed };
  Dynarray.length builder.locals - 1

let lookup_local_type builder local = (Dynarray.get builder.locals local).ty
let lookup_current_function builder = Dynarray.get builder.functions builder.function_

let start builder block =
  Dynarray.set builder.owners block (Some builder.function_);
  Dynarray.set builder.bodies block (make_empty_body ());
  builder.current <- block

let emit builder statement =
  let function_ = lookup_current_function builder in
  function_.size <- function_.size + 1;
  let body = Dynarray.get builder.bodies builder.current in
  body.statements <- statement :: body.statements

let finish builder terminator =
  let function_ = lookup_current_function builder in
  function_.size <- function_.size + 2;
  (Dynarray.get builder.bodies builder.current).terminator <- Some terminator

let run_in_block builder block body =
  let current = builder.current in
  start builder block;
  body ();
  builder.current <- current

let emit_temporary builder ty (rvalue : Lowered.rvalue) : Lowered.operand =
  let temporary = allocate_local builder ty in
  emit builder (Assign (Lowered.make_local_place temporary, rvalue));
  Copy (Lowered.make_local_place temporary)

let is_unsigned_zero : Lowered.operand -> bool = function
  | Constant (Integer ((UInt8 | UInt16 | UInt32 | UInt64), zero)) -> Z.sign zero = 0
  | _ -> false

let find_constant_truth : Lowered.rvalue -> bool option = function
  | Use (Constant (Bool truth)) -> Some truth
  | Binary (op, Constant (Integer (_, left)), Constant (Integer (_, right))) -> (
      match op with
      | Greater -> Some (Z.gt left right)
      | Greater_equal -> Some (Z.geq left right)
      | Less -> Some (Z.lt left right)
      | Less_equal -> Some (Z.leq left right)
      | Equal -> Some (Z.equal left right)
      | Not_equal -> Some (not (Z.equal left right))
      | _ -> None)
  | Binary (Greater, zero, _) when is_unsigned_zero zero -> Some false
  | Binary (Less, _, zero) when is_unsigned_zero zero -> Some false
  | Binary (Greater_equal, _, zero) when is_unsigned_zero zero -> Some true
  | Binary (Less_equal, zero, _) when is_unsigned_zero zero -> Some true
  | _ -> None

let branch builder condition ~yes ~no =
  match find_constant_truth condition with
  | Some true -> finish builder (Goto yes)
  | Some false -> finish builder (Goto no)
  | None ->
      let value =
        match condition with
        | Use operand -> operand
        | _ -> emit_temporary builder (Raw Bool) condition
      in
      finish builder (Switch { value; cases = [ (Z.one, yes) ]; default = no })

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
  branch builder (Binary (Less, Copy (Lowered.make_local_place index), count)) ~yes:inside ~no:after;
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
       ~role:
         (Outlined
            { index; parent = builder.function_; parts = arrives :: parts; holder; environment })
       ~entry
       ~prologue:
         [
           Assign
             (Lowered.make_local_place environment, Use (Copy (Lowered.make_local_place arrives)));
         ]);
  let number = Dynarray.length builder.functions - 1 in
  write_in builder number (fun () ->
      start builder entry;
      body ());
  holder

let render_local_placeholder local = Printf.sprintf "\001%d\002" local

let make_placeholder_context builder (function_ : function_) ~note_mention =
  {
    C_values.symbol = Mangling.make_symbol function_.code.item;
    render_local =
      (fun local ->
        note_mention local;
        (render_local_placeholder local, lookup_local_type builder local));
  }

let replace_local_placeholders text ~name =
  let buffer = Buffer.create (String.length text) in
  let length = String.length text in
  let rec scan position =
    if position < length then
      if text.[position] = '\001' then begin
        let stop = String.index_from text position '\002' in
        Buffer.add_string buffer
          (name (int_of_string (String.sub text (position + 1) (stop - position - 1))));
        scan (stop + 1)
      end
      else begin
        Buffer.add_char buffer text.[position];
        scan (position + 1)
      end
  in
  scan 0;
  Buffer.contents buffer

let render_nested_symbol (code : code) index =
  Printf.sprintf "%s_Nested_%d" (Mangling.make_symbol code.item) index

let mark_reached_blocks builder functions =
  let reached = Array.make (Dynarray.length builder.bodies) false in
  let jump_targets = ref Blocks.empty in
  let rec reach block =
    if not reached.(block) then begin
      reached.(block) <- true;
      match (Dynarray.get builder.bodies block).terminator with
      | Some terminator ->
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

let note_mention mentioned number local = mentioned.(number) <- Locals.add local mentioned.(number)

let print_reached_blocks builder functions ~reached ~result_types ~mentioned =
  Array.mapi
    (fun block is_reached ->
      match Dynarray.get builder.owners block with
      | Some number when is_reached ->
          let function_ = functions.(number) and body = Dynarray.get builder.bodies block in
          let emission = function_.code.emission
          and fc =
            make_placeholder_context builder functions.(number)
              ~note_mention:(note_mention mentioned number)
          in
          let buffer = Buffer.create 256 in
          List.iter (C_code.write_statement emission fc buffer) (List.rev body.statements);
          (match body.terminator with
          | Some (Return value as terminator) ->
              check_return ~result:result_types.(number)
                ~gives:
                  (match value with
                  | Some operand -> C_values.render_operand emission fc operand <> None
                  | None -> false);
              C_code.write_terminator emission fc buffer terminator
          | Some terminator -> C_code.write_terminator emission fc buffer terminator
          | None -> raise_bug "block %d is never finished" block);
          Buffer.contents buffer
      | Some _ | None -> "")
    reached

let print_prologues builder functions ~mentioned =
  Array.mapi
    (fun number (function_ : function_) ->
      let buffer = Buffer.create 64 in
      List.iter
        (C_code.write_statement function_.code.emission
           (make_placeholder_context builder function_ ~note_mention:(note_mention mentioned number))
           buffer)
        function_.prologue;
      Buffer.contents buffer)
    functions

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

let list_captures functions ~home ~mentioned ~is_local_to =
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
  Array.map
    (fun locals ->
      List.mapi
        (fun position local -> (local, Printf.sprintf "capture%d" position))
        (Locals.elements locals))
    captured

let register_environments builder functions ~captures =
  Array.iteri
    (fun number (function_ : function_) ->
      match function_.role with
      | Outlined { index; _ } ->
          C_types.add_environment function_.code.emission.types
            (Environment (Mangling.make_symbol function_.code.item, index))
            (List.map
               (fun (local, field) ->
                 ( field,
                   Lowered.Pointer { target = lookup_local_type builder local; writable = true } ))
               captures.(number))
      | Enclosing -> ())
    functions

let print_fills builder functions ~captures =
  let fills = Array.map (fun _ -> Buffer.create 64) functions in
  Array.iteri
    (fun number (function_ : function_) ->
      match function_.role with
      | Outlined { holder; parent; _ } ->
          let parent_function = functions.(parent) in
          List.iter
            (fun (local, field) ->
              C_code.write_statement parent_function.code.emission
                (make_placeholder_context builder parent_function ~note_mention:ignore)
                fills.(parent)
                (Assign
                   ( { root = Local holder; projections = [ Field field ] },
                     Use (Address { place = Lowered.make_local_place local; writable = true }) )))
            captures.(number)
      | Enclosing -> ())
    functions;
  Array.map Buffer.contents fills

let name_local builder (function_ : function_) ~is_local ~captures local =
  if is_local local then C_values.render_local_name local (Dynarray.get builder.locals local).name
  else
    match (function_.role, List.assoc_opt local captures) with
    | Outlined { environment; _ }, Some field ->
        Printf.sprintf "(*(*%s).f_%s)"
          (C_values.render_local_name environment (Dynarray.get builder.locals environment).name)
          field
    | _ -> raise_bug "local %d is neither local to the function nor in its environment" local

let render_local_declarations builder (function_ : function_) ~locals ~parameters ~name =
  let emission = function_.code.emission in
  let symbol = Mangling.make_symbol function_.code.item in
  String.concat ""
    (List.filter_map
       (fun local ->
         let ty = lookup_local_type builder local in
         if List.mem local parameters || Lowered.is_erased emission.types.env ty then None
         else
           let initializer_ =
             if not (Dynarray.get builder.locals local).is_zeroed then ""
             else
               match ty with
               | Value ty when C_types.is_struct emission.types ty -> " = {0}"
               | Value _ | Pointer _ | Raw _ -> " = 0"
               | Lend | Lend_mark -> " = {0}"
               | Environment _ | Evidence _ | Capabilities _ | Trace ->
                   raise_bug "a zeroed environment, evidence slot, table, or link of the call chain"
           in
           Some
             (Printf.sprintf "  %s %s%s;\n"
                (C_types.render_type emission.types symbol ty)
                (name local) initializer_))
       locals)

let render_blocks builder number (function_ : function_) ~reached ~jump_targets ~texts =
  String.concat ""
    (List.map
       (fun block ->
         (if Blocks.mem block jump_targets then Printf.sprintf "b%d:;\n" block else "")
         ^ texts.(block))
       (function_.entry
       :: List.filter
            (fun block ->
              block <> function_.entry
              && Dynarray.get builder.owners block = Some number
              && reached.(block))
            (List.init (Dynarray.length builder.bodies) Fun.id)))

let write_function_texts builder ~enclosing_symbol { parameters; result; returns } =
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
  let texts = print_reached_blocks builder functions ~reached ~result_types ~mentioned in
  let prologues = print_prologues builder functions ~mentioned in
  let home = find_homes functions ~mentioned in
  let is_local_to number local =
    List.mem local (list_parameters number)
    || Hashtbl.find_opt home local = Some number
    || Lowered.is_erased builder.env (lookup_local_type builder local)
  in
  let captures = list_captures functions ~home ~mentioned ~is_local_to in
  register_environments builder functions ~captures;
  let fills = print_fills builder functions ~captures in
  Array.mapi
    (fun number (function_ : function_) ->
      let name =
        name_local builder function_ ~is_local:(is_local_to number) ~captures:captures.(number)
      in
      let locals =
        List.sort compare
          (Hashtbl.fold
             (fun local owner locals -> if owner = number then local :: locals else locals)
             home [])
      in
      let body =
        " {\n"
        ^ render_local_declarations builder function_ ~locals ~parameters:(list_parameters number)
            ~name
        ^ prologues.(number) ^ fills.(number)
        ^ render_blocks builder number function_ ~reached ~jump_targets ~texts
        ^ "}\n"
      in
      let symbol =
        match function_.role with
        | Outlined { index; _ } -> render_nested_symbol function_.code index
        | Enclosing -> enclosing_symbol
      in
      let header =
        C_values.render_prototype function_.code.emission
          (Mangling.make_symbol function_.code.item)
          symbol
          ~names:(List.map name (list_parameters number))
          ~linkage:External
          {
            parameters = List.map (lookup_local_type builder) (list_parameters number);
            result = result_types.(number);
            returns = (match function_.role with Enclosing -> returns | Outlined _ -> true);
          }
      in
      (header, replace_local_placeholders body ~name))
    functions

let write_functions builder ~enclosing_symbol prototype =
  let functions = Dynarray.to_array builder.functions in
  let texts = write_function_texts builder ~enclosing_symbol prototype in
  Array.iteri
    (fun number (function_ : function_) ->
      match function_.role with
      | Outlined { index; _ } ->
          function_.code.nested <- (index, texts.(number)) :: function_.code.nested
      | Enclosing -> ())
    functions;
  texts.(0)

let build builder prototype =
  let enclosing = Dynarray.get builder.functions 0 in
  let enclosing_text =
    write_functions builder ~enclosing_symbol:(Mangling.make_symbol enclosing.code.item) prototype
  in
  let { item; emission; nested } = enclosing.code in
  let nested = List.sort compare nested in
  Fragment.make emission ~item
    ~kind:(Functions { nested = List.length nested; weight = enclosing.size })
    ~functions:(List.map snd nested @ [ enclosing_text ])
    ~definition:""
    ~references:(Emission.list_referenced_items emission ~referrer:item)

let build_nested parent ~index ~environment build_body =
  let code = (lookup_current_function parent).code in
  C_types.add_environment code.emission.types
    (Environment (Mangling.make_symbol code.item, index))
    environment;
  let builder = start_function (make_builder parent.env) ~code in
  let prototype = build_body builder in
  code.nested <-
    (index, write_functions builder ~enclosing_symbol:(render_nested_symbol code index) prototype)
    :: code.nested
