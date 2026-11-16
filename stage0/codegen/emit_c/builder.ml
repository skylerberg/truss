let bug format = Compiler_bug.bug ~stage:"Builder" format

module Locals = Set.Make (Int)
module Blocks = Set.Make (Int)

type local_info = { ty : Lowered.ty; name : string option; is_zeroed : bool }
type instance = C_instance.t

let instance_key (instance : instance) = instance.key

type code = {
  key : Instance.key;
  context : C_types.context;
  mutable nested : (int * (string * string)) list;
}

type role =
  | Own
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
  mutable instances : Instance.key list;
  mutable called : Instance.key list;
  mutable calls : (Path.t * int) list;
  mutable failures : (C_runtime.failure * Lowered.site) list;
}

let no_facts () = { instances = []; called = []; calls = []; failures = [] }

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

let new_function ~code ~role ~entry =
  {
    code;
    role;
    entry;
    prologue = Buffer.create 64;
    mentioned = Locals.empty;
    returns = [];
    size = 0;
  }

let new_builder env =
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

let block builder =
  Dynarray.add_last builder.texts None;
  Dynarray.add_last builder.mentions Locals.empty;
  Dynarray.add_last builder.successors [];
  Dynarray.add_last builder.facts (no_facts ());
  Dynarray.add_last builder.owners None;
  Dynarray.length builder.texts - 1

let start_function builder ~code =
  Dynarray.add_last builder.functions (new_function ~code ~role:Own ~entry:0);
  builder

let create env ~key =
  let code = { key; context = C_types.new_context env (Instance.symbol key); nested = [] } in
  start_function (new_builder env) ~code

let local builder ?name ?(is_zeroed = false) ty =
  Dynarray.add_last builder.locals { ty; name; is_zeroed };
  Dynarray.length builder.locals - 1

let local_type builder local = (Dynarray.get builder.locals local).ty
let current_function builder = Dynarray.get builder.functions builder.function_
let token local = Printf.sprintf "\001%d\002" local

let function_context builder (function_ : function_) ~name =
  {
    C_values.symbol = Instance.symbol function_.code.key;
    local =
      (fun local ->
        name local;
        (token local, local_type builder local));
  }

let block_context builder function_ =
  function_context builder function_ ~name:(fun local ->
      Dynarray.set builder.mentions builder.current
        (Locals.add local (Dynarray.get builder.mentions builder.current)))

let prologue_context builder (function_ : function_) =
  function_context builder function_ ~name:(fun local ->
      function_.mentioned <- Locals.add local function_.mentioned)

let start builder block =
  Dynarray.set builder.owners block (Some builder.function_);
  Dynarray.set builder.mentions block Locals.empty;
  Dynarray.set builder.facts block (no_facts ());
  builder.current <- block;
  builder.pending <- Buffer.create 256

let in_block_facts builder (context : C_types.context) print =
  let facts = Dynarray.get builder.facts builder.current in
  let instances = context.instances
  and called = context.called
  and calls = context.calls
  and failures = context.failures in
  context.instances <- facts.instances;
  context.called <- facts.called;
  context.calls <- facts.calls;
  context.failures <- facts.failures;
  print ();
  facts.instances <- context.instances;
  facts.called <- context.called;
  facts.calls <- context.calls;
  facts.failures <- context.failures;
  context.instances <- instances;
  context.called <- called;
  context.calls <- calls;
  context.failures <- failures

let emit builder statement =
  let function_ = current_function builder in
  function_.size <- function_.size + 1;
  in_block_facts builder function_.code.context (fun () ->
      C_code.statement_c function_.code.context (block_context builder function_) builder.pending
        statement)

let finish builder (terminator : Lowered.terminator) =
  let function_ = current_function builder in
  let context = function_.code.context and fc = block_context builder function_ in
  (match terminator with
  | Return value ->
      let gives =
        match value with
        | Some operand -> C_values.operand_c context fc operand <> None
        | None -> false
      in
      function_.returns <- gives :: function_.returns
  | _ -> ());
  Dynarray.set builder.successors builder.current (Lowered.successors terminator);
  function_.size <- function_.size + 2;
  in_block_facts builder context (fun () ->
      C_code.terminator_c context fc builder.pending terminator);
  Dynarray.set builder.texts builder.current (Some (Buffer.contents builder.pending));
  builder.pending <- Buffer.create 256

let in_block builder block body =
  let current = builder.current and pending = builder.pending in
  start builder block;
  body ();
  builder.current <- current;
  builder.pending <- pending

let at = Lowered.local_place
let constant_uint64 number = Lowered.Constant (Integer (UInt64, Z.of_int number))

let branch builder value ~yes ~no =
  finish builder (Switch { value; cases = [ (Z.one, yes) ]; default = no })

let when_ builder condition then_ =
  let inside = block builder in
  let after = block builder in
  branch builder condition ~yes:inside ~no:after;
  start builder inside;
  then_ ();
  finish builder (Goto after);
  start builder after

let loop builder ?(integer = Memory_layout.UInt64) ~count body =
  let constant number = Lowered.Constant (Integer (integer, Z.of_int number)) in
  let index = local builder ~name:"index" (Raw (Integer integer)) in
  let going = local builder (Raw Bool) in
  let test = block builder in
  let inside = block builder in
  let after = block builder in
  emit builder (Assign (at index, Use (constant 0)));
  finish builder (Goto test);
  start builder test;
  emit builder (Assign (at going, Binary (Less, Copy (at index), count)));
  branch builder (Copy (at going)) ~yes:inside ~no:after;
  start builder inside;
  body index;
  emit builder (Assign (at index, Binary (Add, Copy (at index), constant 1)));
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
  let code = (current_function builder).code in
  let holder = local builder ~name:"environment" (Environment index) in
  let arrives = local builder ~name:"environment" (Raw (Nullable_pointer Opaque)) in
  let environment = local builder (Pointer { target = Environment index; writable = false }) in
  let entry = block builder in
  Dynarray.add_last builder.functions
    (new_function ~code
       ~role:
         (Outlined
            { index; parent = builder.function_; parts = arrives :: parts; holder; environment })
       ~entry);
  let number = Dynarray.length builder.functions - 1 in
  let function_ = Dynarray.get builder.functions number in
  C_code.statement_c code.context
    (prologue_context builder function_)
    function_.prologue
    (Assign (at environment, Use (Copy (at arrives))));
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

let nested_symbol (code : code) index =
  Printf.sprintf "%s_Nested_%d" (Instance.symbol code.key) index

let write_function_texts builder ~own_symbol { parameters; result; returns } =
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
  let add key keys = if List.exists (Instance.equal key) keys then keys else key :: keys in
  Array.iteri
    (fun block is_reached ->
      match owners.(block) with
      | Some owner when is_reached ->
          let function_ = functions.(owner) in
          function_.mentioned <-
            Locals.union (Dynarray.get builder.mentions block) function_.mentioned;
          let facts = Dynarray.get builder.facts block and context = function_.code.context in
          context.instances <- List.fold_right add facts.instances context.instances;
          context.called <- List.fold_right add facts.called context.called;
          context.calls <- facts.calls @ context.calls;
          context.failures <- facts.failures @ context.failures
      | Some _ | None -> ())
    reached;
  let own = functions.(0) in
  own.mentioned <- List.fold_left (fun set local -> Locals.add local set) own.mentioned parameters;
  let parameters_of number =
    match functions.(number).role with Own -> parameters | Outlined { parts; _ } -> parts
  in
  let parent number =
    match functions.(number).role with Own -> number | Outlined { parent; _ } -> parent
  in
  let rec depth number =
    match functions.(number).role with Own -> 0 | Outlined { parent; _ } -> 1 + depth parent
  in
  let rec enclosing first second =
    if first = second then first
    else if depth first >= depth second then enclosing (parent first) second
    else enclosing first (parent second)
  in
  let home = Hashtbl.create 64 in
  Array.iteri
    (fun number (function_ : function_) ->
      Locals.iter
        (fun local ->
          match function_.role with
          | Outlined { parts; _ } when List.mem local parts -> ()
          | Own | Outlined _ ->
              Hashtbl.replace home local
                (match Hashtbl.find_opt home local with
                | Some other -> enclosing number other
                | None -> number))
        function_.mentioned)
    functions;
  let is_own number local =
    List.mem local (parameters_of number)
    || Hashtbl.find_opt home local = Some number
    || Lowered.erased builder.env (local_type builder local)
  in
  let captured = Array.make count Locals.empty in
  Array.iteri
    (fun number (function_ : function_) ->
      Locals.iter
        (fun local ->
          if not (is_own number local) then
            let owner = Hashtbl.find home local in
            let rec reach number =
              if number <> owner then begin
                captured.(number) <- Locals.add local captured.(number);
                match functions.(number).role with
                | Outlined { parent; _ } -> reach parent
                | Own -> ()
              end
            in
            reach number)
        function_.mentioned)
    functions;
  let captures number =
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
              (Environment (Instance.symbol function_.code.key, index))
              (List.map
                 (fun (local, field) ->
                   (field, Lowered.Pointer { target = local_type builder local; writable = true }))
                 (captures number))
              context.environments
      | Own -> ())
    functions;
  let fills = Array.init count (fun _ -> Buffer.create 64) in
  Array.iteri
    (fun number (function_ : function_) ->
      match function_.role with
      | Outlined { holder; parent = parent_number; _ } ->
          let parent = functions.(parent_number) in
          List.iter
            (fun (local, field) ->
              C_code.statement_c parent.code.context (prologue_context builder parent)
                fills.(parent_number)
                (Assign
                   ( { root = Local holder; projections = [ Field field ] },
                     Use (Address { place = at local; writable = true }) )))
            (captures number)
      | Own -> ())
    functions;
  Array.mapi
    (fun number (function_ : function_) ->
      let result = match function_.role with Own -> result | Outlined _ -> None in
      List.iter
        (fun gives ->
          match (gives, result) with
          | false, Some _ -> bug "a return of nothing from a function with a result"
          | true, None -> bug "a return of a value from a function with no result"
          | _ -> ())
        function_.returns;
      let context = function_.code.context in
      let captures = captures number in
      let name local =
        if is_own number local then
          C_values.local_name local (Dynarray.get builder.locals local).name
        else
          match (function_.role, List.assoc_opt local captures) with
          | Outlined { environment; _ }, Some field ->
              Printf.sprintf "(*(*%s).f_%s)"
                (C_values.local_name environment (Dynarray.get builder.locals environment).name)
                field
          | _ -> bug "local %d is neither a function's own nor in its environment" local
      in
      let body = Buffer.create 1024 in
      Buffer.add_string body " {\n";
      let symbol = Instance.symbol function_.code.key in
      List.iter
        (fun local ->
          let ty = local_type builder local in
          if (not (List.mem local (parameters_of number))) && not (C_values.erased context ty) then
            let initializer_ =
              if not (Dynarray.get builder.locals local).is_zeroed then ""
              else
                match ty with
                | Value ty when C_types.is_struct context ty -> " = {0}"
                | Value _ | Pointer _ | Raw _ -> " = 0"
                | Lend | Lend_mark -> " = {0}"
                | Environment _ | Evidence _ -> bug "a zeroed environment or evidence slot"
            in
            Buffer.add_string body
              (Printf.sprintf "  %s %s%s;\n" (C_types.c_ty context symbol ty) (name local)
                 initializer_))
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
          | None -> bug "block %d is never finished" block)
        blocks;
      Buffer.add_string body "}\n";
      let symbol =
        match function_.role with
        | Outlined { index; _ } -> nested_symbol function_.code index
        | Own -> own_symbol
      in
      let parameters = parameters_of number in
      let header =
        C_values.prototype context
          (Instance.symbol function_.code.key)
          symbol ~names:(List.map name parameters) ~linkage:External
          {
            parameters = List.map (local_type builder) parameters;
            result;
            returns = (match function_.role with Own -> returns | Outlined _ -> true);
          }
      in
      (header, resolve (Buffer.contents body) name))
    functions

let write_functions builder ~own_symbol prototype =
  let functions = Dynarray.to_array builder.functions in
  let texts = write_function_texts builder ~own_symbol prototype in
  Array.iteri
    (fun number (function_ : function_) ->
      match function_.role with
      | Outlined { index; _ } ->
          function_.code.nested <- (index, texts.(number)) :: function_.code.nested
      | Own -> ())
    functions;
  texts.(0)

let build builder prototype : instance =
  let own = Dynarray.get builder.functions 0 in
  let own_text = write_functions builder ~own_symbol:(Instance.symbol own.code.key) prototype in
  {
    key = own.code.key;
    context = own.code.context;
    own = own_text;
    nested = own.code.nested;
    weight = own.size;
  }

let build_nested parent ~index ~environment body =
  let code = (current_function parent).code in
  code.context.environments <-
    C_types.Keys.add
      (Environment (Instance.symbol code.key, index))
      environment code.context.environments;
  let builder = start_function (new_builder parent.env) ~code in
  let prototype = body builder in
  code.nested <-
    (index, write_functions builder ~own_symbol:(nested_symbol code index) prototype) :: code.nested
