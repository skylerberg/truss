let raise_bug format = Compiler_bug.raise_bug ~stage:"Builder" format

module Locals = Set.Make (Int)
module Blocks = Set.Make (Int)

type local_info = { ty : Lowered.ty; name : string option; is_zeroed : bool }

type code = {
  item : Lowered.Item.t;
  context : C_types.context;
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
  prologue : Buffer.t;
  mutable mentioned : Locals.t;
  mutable returns : bool list;
  mutable size : int;
}

type facts = {
  mutable referenced_items : Lowered.Item.t list;
  mutable called : Lowered.Item.t list;
  mutable calls : (Path.t * int) list;
  mutable failures : (C_runtime.failure * Lowered.site) list;
}

let make_empty_facts () = { referenced_items = []; called = []; calls = []; failures = [] }

type t = {
  env : Memory_layout.env;
  locals : local_info Dynarray.t;
  texts : string option Dynarray.t;
  mentions : Locals.t Dynarray.t;
  successors : Lowered.block list Dynarray.t;
  facts : facts Dynarray.t;
  owners : int option Dynarray.t;
  mutable current : Lowered.block;
  mutable pending : Buffer.t;
  functions : function_ Dynarray.t;
  mutable function_ : int;
}

let make_function ~code ~role ~entry =
  {
    code;
    role;
    entry;
    prologue = Buffer.create 64;
    mentioned = Locals.empty;
    returns = [];
    size = 0;
  }

let make_builder env =
  let builder =
    {
      env;
      locals = Dynarray.create ();
      texts = Dynarray.create ();
      mentions = Dynarray.create ();
      successors = Dynarray.create ();
      facts = Dynarray.create ();
      owners = Dynarray.create ();
      current = 0;
      pending = Buffer.create 256;
      functions = Dynarray.create ();
      function_ = 0;
    }
  in
  builder

let allocate_block builder =
  Dynarray.add_last builder.texts None;
  Dynarray.add_last builder.mentions Locals.empty;
  Dynarray.add_last builder.successors [];
  Dynarray.add_last builder.facts (make_empty_facts ());
  Dynarray.add_last builder.owners None;
  Dynarray.length builder.texts - 1

let start_function builder ~code =
  Dynarray.add_last builder.functions (make_function ~code ~role:Enclosing ~entry:0);
  builder

let create env ~item =
  let code =
    { item; context = C_types.make_context env (Mangling.make_symbol item); nested = [] }
  in
  start_function (make_builder env) ~code

let allocate_local builder ?name ?(is_zeroed = false) ty =
  Dynarray.add_last builder.locals { ty; name; is_zeroed };
  Dynarray.length builder.locals - 1

let lookup_local_type builder local = (Dynarray.get builder.locals local).ty
let lookup_current_function builder = Dynarray.get builder.functions builder.function_
let render_token local = Printf.sprintf "\001%d\002" local

let make_function_context builder (function_ : function_) ~note_mention =
  {
    C_values.symbol = Mangling.make_symbol function_.code.item;
    render_local =
      (fun local ->
        note_mention local;
        (render_token local, lookup_local_type builder local));
  }

let make_block_context builder function_ =
  make_function_context builder function_ ~note_mention:(fun local ->
      Dynarray.set builder.mentions builder.current
        (Locals.add local (Dynarray.get builder.mentions builder.current)))

let make_prologue_context builder (function_ : function_) =
  make_function_context builder function_ ~note_mention:(fun local ->
      function_.mentioned <- Locals.add local function_.mentioned)

let start builder block =
  Dynarray.set builder.owners block (Some builder.function_);
  Dynarray.set builder.mentions block Locals.empty;
  Dynarray.set builder.facts block (make_empty_facts ());
  builder.current <- block;
  builder.pending <- Buffer.create 256

let with_block_facts builder (context : C_types.context) print =
  let facts = Dynarray.get builder.facts builder.current in
  let referenced_items = context.referenced_items
  and called = context.called
  and calls = context.calls
  and failures = context.failures in
  context.referenced_items <- facts.referenced_items;
  context.called <- facts.called;
  context.calls <- facts.calls;
  context.failures <- facts.failures;
  print ();
  facts.referenced_items <- context.referenced_items;
  facts.called <- context.called;
  facts.calls <- context.calls;
  facts.failures <- context.failures;
  context.referenced_items <- referenced_items;
  context.called <- called;
  context.calls <- calls;
  context.failures <- failures

let emit builder statement =
  let function_ = lookup_current_function builder in
  function_.size <- function_.size + 1;
  with_block_facts builder function_.code.context (fun () ->
      C_code.write_statement function_.code.context
        (make_block_context builder function_)
        builder.pending statement)

let finish builder (terminator : Lowered.terminator) =
  let function_ = lookup_current_function builder in
  let context = function_.code.context and fc = make_block_context builder function_ in
  (match terminator with
  | Return value ->
      let gives =
        match value with
        | Some operand -> C_values.render_operand context fc operand <> None
        | None -> false
      in
      function_.returns <- gives :: function_.returns
  | _ -> ());
  Dynarray.set builder.successors builder.current (Lowered.list_successors terminator);
  function_.size <- function_.size + 2;
  with_block_facts builder context (fun () ->
      C_code.write_terminator context fc builder.pending terminator);
  Dynarray.set builder.texts builder.current (Some (Buffer.contents builder.pending));
  builder.pending <- Buffer.create 256

let run_in_block builder block body =
  let current = builder.current and pending = builder.pending in
  start builder block;
  body ();
  builder.current <- current;
  builder.pending <- pending

let branch builder value ~yes ~no =
  finish builder (Switch { value; cases = [ (Z.one, yes) ]; default = no })

let emit_when builder condition then_ =
  let inside = allocate_block builder in
  let after = allocate_block builder in
  branch builder condition ~yes:inside ~no:after;
  start builder inside;
  then_ ();
  finish builder (Goto after);
  start builder after

let emit_loop builder ?(integer = Memory_layout.UInt64) ~count body =
  let make_constant number = Lowered.Constant (Integer (integer, Z.of_int number)) in
  let index = allocate_local builder (Raw (Integer integer)) in
  let going = allocate_local builder (Raw Bool) in
  let test = allocate_block builder in
  let inside = allocate_block builder in
  let after = allocate_block builder in
  emit builder (Assign (Lowered.make_local_place index, Use (make_constant 0)));
  finish builder (Goto test);
  start builder test;
  emit builder
    (Assign
       (Lowered.make_local_place going, Binary (Less, Copy (Lowered.make_local_place index), count)));
  branch builder (Copy (Lowered.make_local_place going)) ~yes:inside ~no:after;
  start builder inside;
  body index;
  emit builder
    (Assign
       ( Lowered.make_local_place index,
         Binary (Add, Copy (Lowered.make_local_place index), make_constant 1) ));
  finish builder (Goto test);
  start builder after

let write_in builder number body =
  let function_ = builder.function_ and current = builder.current and pending = builder.pending in
  builder.function_ <- number;
  body ();
  builder.function_ <- function_;
  builder.current <- current;
  builder.pending <- pending

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
       ~entry);
  let number = Dynarray.length builder.functions - 1 in
  let function_ = Dynarray.get builder.functions number in
  C_code.write_statement code.context
    (make_prologue_context builder function_)
    function_.prologue
    (Assign (Lowered.make_local_place environment, Use (Copy (Lowered.make_local_place arrives))));
  write_in builder number (fun () ->
      start builder entry;
      body ());
  holder

let resolve text name =
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

let write_function_texts builder ~enclosing_symbol { parameters; result; returns } =
  let functions = Dynarray.to_array builder.functions in
  let count = Array.length functions in
  let texts = Dynarray.to_array builder.texts and owners = Dynarray.to_array builder.owners in
  let successors = Dynarray.to_array builder.successors in
  let reached = Array.make (Array.length texts) false and targets = ref Blocks.empty in
  Array.iter
    (fun (function_ : function_) ->
      let rec reach block =
        if not reached.(block) then begin
          reached.(block) <- true;
          List.iter
            (fun target ->
              targets := Blocks.add target !targets;
              reach target)
            successors.(block)
        end
      in
      reach function_.entry)
    functions;
  let add item items =
    if List.exists (Lowered.Item.equal item) items then items else item :: items
  in
  Array.iteri
    (fun block is_reached ->
      match owners.(block) with
      | Some owner when is_reached ->
          let function_ = functions.(owner) in
          function_.mentioned <-
            Locals.union (Dynarray.get builder.mentions block) function_.mentioned;
          let facts = Dynarray.get builder.facts block and context = function_.code.context in
          context.referenced_items <-
            List.fold_right add facts.referenced_items context.referenced_items;
          context.called <- List.fold_right add facts.called context.called;
          context.calls <- facts.calls @ context.calls;
          context.failures <- facts.failures @ context.failures
      | Some _ | None -> ())
    reached;
  let enclosing = functions.(0) in
  enclosing.mentioned <-
    List.fold_left (fun set local -> Locals.add local set) enclosing.mentioned parameters;
  let list_parameters number =
    match functions.(number).role with Enclosing -> parameters | Outlined { parts; _ } -> parts
  in
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
        function_.mentioned)
    functions;
  let is_local_to number local =
    List.mem local (list_parameters number)
    || Hashtbl.find_opt home local = Some number
    || Lowered.is_erased builder.env (lookup_local_type builder local)
  in
  let captured = Array.make count Locals.empty in
  Array.iteri
    (fun number (function_ : function_) ->
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
        function_.mentioned)
    functions;
  let list_captures number =
    List.mapi
      (fun position local -> (local, Printf.sprintf "capture%d" position))
      (Locals.elements captured.(number))
  in
  Array.iteri
    (fun number (function_ : function_) ->
      match function_.role with
      | Outlined { index; _ } ->
          let context = function_.code.context in
          context.environments <-
            C_types.Keys.add
              (Environment (Mangling.make_symbol function_.code.item, index))
              (List.map
                 (fun (local, field) ->
                   ( field,
                     Lowered.Pointer { target = lookup_local_type builder local; writable = true }
                   ))
                 (list_captures number))
              context.environments
      | Enclosing -> ())
    functions;
  let fills = Array.init count (fun _ -> Buffer.create 64) in
  Array.iteri
    (fun number (function_ : function_) ->
      match function_.role with
      | Outlined { holder; parent = parent_number; _ } ->
          let parent = functions.(parent_number) in
          List.iter
            (fun (local, field) ->
              C_code.write_statement parent.code.context
                (make_prologue_context builder parent)
                fills.(parent_number)
                (Assign
                   ( { root = Local holder; projections = [ Field field ] },
                     Use (Address { place = Lowered.make_local_place local; writable = true }) )))
            (list_captures number)
      | Enclosing -> ())
    functions;
  Array.mapi
    (fun number (function_ : function_) ->
      let result = match function_.role with Enclosing -> result | Outlined _ -> None in
      List.iter
        (fun gives ->
          match (gives, result) with
          | false, Some _ -> raise_bug "a return of nothing from a function with a result"
          | true, None -> raise_bug "a return of a value from a function with no result"
          | _ -> ())
        function_.returns;
      let context = function_.code.context in
      let captures = list_captures number in
      let name local =
        if is_local_to number local then
          C_values.render_local_name local (Dynarray.get builder.locals local).name
        else
          match (function_.role, List.assoc_opt local captures) with
          | Outlined { environment; _ }, Some field ->
              Printf.sprintf "(*(*%s).f_%s)"
                (C_values.render_local_name environment
                   (Dynarray.get builder.locals environment).name)
                field
          | _ -> raise_bug "local %d is neither local to the function nor in its environment" local
      in
      let body = Buffer.create 1024 in
      Buffer.add_string body " {\n";
      let symbol = Mangling.make_symbol function_.code.item in
      List.iter
        (fun local ->
          let ty = lookup_local_type builder local in
          if (not (List.mem local (list_parameters number))) && not (C_values.is_erased context ty)
          then
            let initializer_ =
              if not (Dynarray.get builder.locals local).is_zeroed then ""
              else
                match ty with
                | Value ty when C_types.is_struct context ty -> " = {0}"
                | Value _ | Pointer _ | Raw _ -> " = 0"
                | Lend | Lend_mark -> " = {0}"
                | Environment _ | Evidence _ -> raise_bug "a zeroed environment or evidence slot"
            in
            Buffer.add_string body
              (Printf.sprintf "  %s %s%s;\n"
                 (C_types.render_type context symbol ty)
                 (name local) initializer_))
        (List.sort compare
           (Hashtbl.fold
              (fun local owner locals -> if owner = number then local :: locals else locals)
              home []));
      Buffer.add_buffer body function_.prologue;
      Buffer.add_buffer body fills.(number);
      let blocks =
        function_.entry
        :: List.filter
             (fun block ->
               block <> function_.entry && owners.(block) = Some number && reached.(block))
             (List.init (Array.length texts) Fun.id)
      in
      List.iter
        (fun block ->
          if Blocks.mem block !targets then Buffer.add_string body (Printf.sprintf "b%d:;\n" block);
          match texts.(block) with
          | Some text -> Buffer.add_string body text
          | None -> raise_bug "block %d is never finished" block)
        blocks;
      Buffer.add_string body "}\n";
      let symbol =
        match function_.role with
        | Outlined { index; _ } -> render_nested_symbol function_.code index
        | Enclosing -> enclosing_symbol
      in
      let parameters = list_parameters number in
      let header =
        C_values.render_prototype context
          (Mangling.make_symbol function_.code.item)
          symbol ~names:(List.map name parameters) ~linkage:External
          {
            parameters = List.map (lookup_local_type builder) parameters;
            result;
            returns = (match function_.role with Enclosing -> returns | Outlined _ -> true);
          }
      in
      (header, resolve (Buffer.contents body) name))
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
  let { item; context; nested } = enclosing.code in
  let nested = List.sort compare nested in
  Fragment.make context ~item
    ~kind:(Functions { nested = List.length nested; weight = enclosing.size })
    ~functions:(List.map snd nested @ [ enclosing_text ])
    ~definition:""
    ~references:(C_types.list_referenced_items context ~referrer:item)

let build_nested parent ~index ~environment build_body =
  let code = (lookup_current_function parent).code in
  code.context.environments <-
    C_types.Keys.add
      (Environment (Mangling.make_symbol code.item, index))
      environment code.context.environments;
  let builder = start_function (make_builder parent.env) ~code in
  let prototype = build_body builder in
  code.nested <-
    (index, write_functions builder ~enclosing_symbol:(render_nested_symbol code index) prototype)
    :: code.nested
