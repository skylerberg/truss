open C_types
open C_values
open C_code

let bug format = Compiler_bug.bug ~stage:"Builder" format

module Locals = Set.Make (Int)
module Blocks = Set.Make (Int)

(* [is_zeroed] marks a local that is declared zeroed: a drop flag, which
   starts false, or a value that C must be given and that nothing reads,
   such as an omitted argument. *)
type local_info = { ty : Lowered.ty; name : string option; is_zeroed : bool }
type instance = C_instance.t

open C_instance

let instance_key (instance : instance) = instance.key

(* A function of the code a builder writes: the builder's own, number 0, or
   an outlined function. *)
type function_ = {
  code : instance;  (** The instance it is part of *)
  nested : int option;  (** Its number among the instance's nested functions *)
  parent : int;
  parts : Lowered.local list;  (** The locals of [parent] it takes as parameters *)
  holder : Lowered.local option;  (** The local of [parent] that holds its environment *)
  environment : Lowered.local option;  (** Its local that points to its environment *)
  entry : Lowered.block;
  prologue : Buffer.t;  (** Statements that run before its entry block *)
  mutable mentioned : Locals.t;  (** The locals its prologue names *)
  mutable returns : bool list;  (** For each [return], whether it gives a value *)
  mutable size : int;
}

type facts = {
  mutable instances : Instance.key list;
  mutable called : Instance.key list;
  mutable calls : (Path.t * int) list;
  mutable failures : (C_runtime.failure * C_runtime.site) list;
}

let no_facts () = { instances = []; called = []; calls = []; failures = [] }

(* The target of a block's [goto], and whether the block has no statements,
   so that a jump to it can go straight to the target. *)
type jump = { target : Lowered.block; is_empty : bool }

type t = {
  env : Memory_layout.env;
  locals : local_info Dynarray.t;
  texts : string option Dynarray.t;  (** Each block's C, once it is finished *)
  mentions : Locals.t Dynarray.t;  (** The locals each block's code names *)
  successors : Lowered.block list Dynarray.t;  (** The blocks each block goes to *)
  jumps : jump option Dynarray.t;  (** For a block that ends in a [goto], its target *)
  facts : facts Dynarray.t;
  owners : int Dynarray.t;
  mutable current : Lowered.block;
  mutable pending : Buffer.t;  (** The C of the current block's statements *)
  functions : function_ Dynarray.t;
  mutable function_ : int;  (** The function being written *)
}

let new_function ~code ~nested ~parent ~parts ~holder ~environment ~entry =
  {
    code;
    nested;
    parent;
    parts;
    holder;
    environment;
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
      jumps = Dynarray.create ();
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
  Dynarray.add_last builder.jumps None;
  Dynarray.add_last builder.facts (no_facts ());
  Dynarray.add_last builder.owners (-1);
  Dynarray.length builder.texts - 1

(* The builder's own function runs from block 0, the first block made. *)
let start_function builder ~code ~nested =
  Dynarray.add_last builder.functions
    (new_function ~code ~nested ~parent:(-1) ~parts:[] ~holder:None ~environment:None ~entry:0);
  builder

let create env ~key =
  let code = { key; context = new_context env (Instance.symbol key); functions = []; weight = 0 } in
  start_function (new_builder env) ~code ~nested:None

let nested parent ~index ~environment =
  let code = (Dynarray.get parent.functions parent.function_).code in
  code.context.environments <-
    Keys.add (Environment (Instance.symbol code.key, index)) environment code.context.environments;
  start_function (new_builder parent.env) ~code ~nested:(Some index)

let local builder ?name ?(is_zeroed = false) ty =
  Dynarray.add_last builder.locals { ty; name; is_zeroed };
  Dynarray.length builder.locals - 1

let local_type builder local = (Dynarray.get builder.locals local).ty
let current_function builder = Dynarray.get builder.functions builder.function_

(* A local's name in C stands as a token until the function is built, when
   it becomes the local itself or its place in the environment. *)
let token local = Printf.sprintf "\001%d\002" local

(* A block's label stands as a token until the function is built, when it
   becomes the label of the block that jumps to it lead to. *)
let label_token block = Printf.sprintf "\003%d\004" block
let goto_line block = Printf.sprintf "  goto %s;\n" (label_token block)

(* A function's context for printing code, which records each local the
   code names with [name]. *)
let function_context builder (function_ : function_) ~name =
  {
    symbol = Instance.symbol function_.code.key;
    local =
      (fun local ->
        name local;
        (token local, local_type builder local));
  }

(* The context for the current block's code. *)
let block_context builder function_ =
  function_context builder function_ ~name:(fun local ->
      Dynarray.set builder.mentions builder.current
        (Locals.add local (Dynarray.get builder.mentions builder.current)))

(* The context for code that runs before a function's blocks. *)
let prologue_context builder (function_ : function_) =
  function_context builder function_ ~name:(fun local ->
      function_.mentioned <- Locals.add local function_.mentioned)

let start builder block =
  Dynarray.set builder.owners block builder.function_;
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
      statement_c function_.code.context (block_context builder function_) builder.pending statement)

let finish builder (terminator : Lowered.terminator) =
  let function_ = current_function builder in
  let context = function_.code.context and fc = block_context builder function_ in
  (match terminator with
  | Return value ->
      let gives =
        match value with Some operand -> operand_c context fc operand <> None | None -> false
      in
      function_.returns <- gives :: function_.returns
  | _ -> ());
  Dynarray.set builder.successors builder.current (Lowered.successors terminator);
  Dynarray.set builder.jumps builder.current
    (match terminator with
    | Goto target -> Some { target; is_empty = Buffer.length builder.pending = 0 }
    | _ -> None);
  function_.size <- function_.size + 2;
  in_block_facts builder context (fun () ->
      terminator_c context fc ~label:label_token builder.pending terminator);
  Dynarray.set builder.texts builder.current (Some (Buffer.contents builder.pending));
  builder.pending <- Buffer.create 256

let in_block builder block body =
  let current = builder.current and pending = builder.pending in
  start builder block;
  body ();
  builder.current <- current;
  builder.pending <- pending

let at = Lowered.local_place

let ( / ) (place : Lowered.place) projection : Lowered.place =
  { place with projections = place.projections @ [ projection ] }

let usize number = Lowered.Constant (Integer (USize, Z.of_int number))

let branch builder value ~yes ~no =
  finish builder (Switch { value; cases = [ (Z.one, yes) ]; default = Some no })

let when_ builder condition then_ =
  let inside = block builder in
  let after = block builder in
  branch builder condition ~yes:inside ~no:after;
  start builder inside;
  then_ ();
  finish builder (Goto after);
  start builder after

let loop builder ?(integer = Memory_layout.USize) ~index_type ~count body =
  let constant number = Lowered.Constant (Integer (integer, Z.of_int number)) in
  let index = local builder ~name:"index" index_type in
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

(* Writes [body] in the function [number], then goes back to the block that
   was current, with its statements so far. *)
let write_in builder number body =
  let function_ = builder.function_ and current = builder.current and pending = builder.pending in
  builder.function_ <- number;
  body ();
  builder.function_ <- function_;
  builder.current <- current;
  builder.pending <- pending

let outline builder ~nested ~parts body =
  let code = (current_function builder).code in
  let holder = local builder ~name:"environment" (Environment nested) in
  let arrives = local builder ~name:"environment" (Raw (Nullable_pointer Opaque)) in
  let environment = local builder (Pointer { target = Environment nested; writable = false }) in
  let entry = block builder in
  Dynarray.add_last builder.functions
    (new_function ~code ~nested:(Some nested) ~parent:builder.function_ ~parts:(arrives :: parts)
       ~holder:(Some holder) ~environment:(Some environment) ~entry);
  let number = Dynarray.length builder.functions - 1 in
  let function_ = Dynarray.get builder.functions number in
  statement_c code.context
    (prologue_context builder function_)
    function_.prologue
    (Assign (at environment, Use (Copy (at arrives))));
  write_in builder number (fun () ->
      start builder entry;
      body ());
  holder

(* Replaces each token in a function's C with the text [local] gives its
   local or [label] gives its block. *)
let resolve text ~local ~label =
  let buffer = Buffer.create (String.length text) in
  let length = String.length text in
  let rec scan position =
    if position < length then
      match text.[position] with
      | ('\001' | '\003') as opening ->
          let closing = if opening = '\001' then '\002' else '\004' in
          let stop = String.index_from text position closing in
          let number = int_of_string (String.sub text (position + 1) (stop - position - 1)) in
          Buffer.add_string buffer (if opening = '\001' then local number else label number);
          scan (stop + 1)
      | character ->
          Buffer.add_char buffer character;
          scan (position + 1)
  in
  scan 0;
  Buffer.contents buffer

(* Each token of a block's label in a text. *)
let labels_named text =
  let rec scan position labels =
    match String.index_from_opt text position '\003' with
    | None -> labels
    | Some start ->
        let stop = String.index_from text start '\004' in
        scan (stop + 1) (int_of_string (String.sub text (start + 1) (stop - start - 1)) :: labels)
  in
  scan 0 []

(* Writes every function the builder holds as C.

   A local belongs to the innermost function that every function naming it
   is in, so that a local that one outlined function names alone belongs to
   each of its runs. An outlined function reaches a local of a function
   around it through its environment, which holds the local's address. The
   function that runs it fills the environment once, on entry: the
   addresses do not change, and a loop that runs the function again while
   tasks it spawned earlier read the environment does not write it again,
   which would be a data race. A local that takes no room is never shared:
   each function that names it has its own.

   A jump to a block that has no statements and ends in a [goto] goes
   straight to where that [goto] leads, so the block is written only where
   it is a function's entry. A [goto] to the block written right after it
   is left out, and a block has a label only where a [goto] names it. *)
let build ?(returns = true) builder ~parameters ~result =
  let functions = Dynarray.to_array builder.functions in
  let count = Array.length functions in
  let texts = Dynarray.to_array builder.texts and owners = Dynarray.to_array builder.owners in
  let successors = Dynarray.to_array builder.successors in
  let jumps = Dynarray.to_array builder.jumps in
  (* Where a jump to a block leads. A cycle of empty blocks is an endless
     loop, which keeps the block whose [goto] closes it. *)
  let destination block =
    let rec follow block seen =
      match jumps.(block) with
      | Some { target; is_empty = true } when not (Blocks.mem target seen) ->
          follow target (Blocks.add block seen)
      | _ -> block
    in
    follow block Blocks.empty
  in
  let reached = Array.make (Array.length texts) false in
  Array.iter
    (fun (function_ : function_) ->
      let rec reach block =
        if not reached.(block) then begin
          reached.(block) <- true;
          List.iter (fun target -> reach (destination target)) successors.(block)
        end
      in
      reach function_.entry)
    functions;
  let add key keys = if List.exists (Instance.equal key) keys then keys else key :: keys in
  Array.iteri
    (fun block is_reached ->
      if is_reached && owners.(block) >= 0 then begin
        let function_ = functions.(owners.(block)) in
        function_.mentioned <-
          Locals.union (Dynarray.get builder.mentions block) function_.mentioned;
        let facts = Dynarray.get builder.facts block and context = function_.code.context in
        context.instances <- List.fold_right add facts.instances context.instances;
        context.called <- List.fold_right add facts.called context.called;
        context.calls <- facts.calls @ context.calls;
        context.failures <- facts.failures @ context.failures
      end)
    reached;
  let main = functions.(0) in
  main.mentioned <- List.fold_left (fun set local -> Locals.add local set) main.mentioned parameters;
  let parameters_of number = if number = 0 then parameters else functions.(number).parts in
  let parent number = functions.(number).parent in
  let rec depth number = if number = 0 then 0 else 1 + depth (parent number) in
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
          if not (number > 0 && List.mem local function_.parts) then
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
                reach (parent number)
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
      match (function_.nested, function_.holder, captures number) with
      | Some nested, Some _, captures ->
          let context = function_.code.context in
          context.environments <-
            Keys.add
              (Environment (Instance.symbol function_.code.key, nested))
              (List.map
                 (fun (local, field) ->
                   (field, Lowered.Pointer { target = local_type builder local; writable = true }))
                 captures)
              context.environments
      | None, None, (local, _) :: _ ->
          if number > 0 then
            bug "a separate function names local %d of the function it is written in" local
      | _ -> ())
    functions;
  (* The statements that fill the environments of the functions outlined
     from each function. *)
  let fills = Array.init count (fun _ -> Buffer.create 64) in
  Array.iteri
    (fun number (function_ : function_) ->
      match function_.holder with
      | Some holder ->
          let parent = functions.(function_.parent) in
          List.iter
            (fun (local, field) ->
              statement_c parent.code.context (prologue_context builder parent)
                fills.(function_.parent)
                (Assign
                   ( { root = Local holder; projections = [ Field field ] },
                     Use (Address { place = at local; writable = true }) )))
            (captures number)
      | None -> ())
    functions;
  Array.iteri
    (fun number (function_ : function_) ->
      let result = if number = 0 then result else None in
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
        if is_own number local then local_name local (Dynarray.get builder.locals local).name
        else
          match (function_.environment, List.assoc_opt local captures) with
          | Some environment, Some field ->
              Printf.sprintf "(*(*%s).f_%s)"
                (local_name environment (Dynarray.get builder.locals environment).name)
                field
          | _ -> bug "local %d is neither a function's own nor in its environment" local
      in
      let body = Buffer.create 1024 in
      Buffer.add_string body " {\n";
      let symbol = Instance.symbol function_.code.key in
      (* A local is declared with no initializer, unless it is zeroed: the
         code writes every other local before it reads it, so zeroing it
         would only cost a store, and hide a read that the lowering got
         wrong. *)
      List.iter
        (fun local ->
          let ty = local_type builder local in
          if (not (List.mem local (parameters_of number))) && not (erased context ty) then
            let zero =
              match ty with
              | _ when not (Dynarray.get builder.locals local).is_zeroed -> ""
              | Value ty when is_struct context ty -> " = {0}"
              | Environment _ | Evidence _ -> bug "a zeroed environment or evidence slot"
              | Value _ | Pointer _ | Raw _ -> " = 0"
            in
            Buffer.add_string body
              (Printf.sprintf "  %s %s%s;\n" (c_ty context symbol ty) (name local) zero))
        (List.sort compare
           (Hashtbl.fold
              (fun local owner locals -> if owner = number then local :: locals else locals)
              home []));
      Buffer.add_buffer body function_.prologue;
      Buffer.add_buffer body fills.(number);
      let blocks =
        function_.entry
        :: List.filter
             (fun block -> block <> function_.entry && owners.(block) = number && reached.(block))
             (List.init (Array.length texts) Fun.id)
      in
      let text block =
        match texts.(block) with
        | Some text -> text
        | None -> bug "block %d is never finished" block
      in
      let rec written = function
        | [] -> []
        | block :: rest ->
            let text = text block in
            let text =
              match (jumps.(block), rest) with
              | Some { target; _ }, next :: _ when destination target = next ->
                  let goto = goto_line target in
                  if not (String.ends_with ~suffix:goto text) then
                    bug "block %d ends in a goto that its C does not end with" block;
                  String.sub text 0 (String.length text - String.length goto)
              | _ -> text
            in
            (block, text) :: written rest
      in
      let written = written blocks in
      let labelled =
        List.fold_left
          (fun labelled (_, text) ->
            List.fold_left
              (fun labelled block -> Blocks.add (destination block) labelled)
              labelled (labels_named text))
          Blocks.empty written
      in
      List.iter
        (fun (block, text) ->
          if Blocks.mem block labelled then Buffer.add_string body (Printf.sprintf "b%d:;\n" block);
          Buffer.add_string body text)
        written;
      Buffer.add_string body "}\n";
      let symbol =
        match function_.nested with
        | Some nested -> Printf.sprintf "%s_Nested_%d" (Instance.symbol function_.code.key) nested
        | None -> Instance.symbol function_.code.key
      in
      let parameters = parameters_of number in
      let header =
        prototype context
          (Instance.symbol function_.code.key)
          symbol ~names:(List.map name parameters) ~linkage:External
          {
            parameters = List.map (local_type builder) parameters;
            result;
            returns = (if number = 0 then returns else true);
          }
      in
      function_.code.functions <-
        ( function_.nested,
          ( header,
            resolve (Buffer.contents body) ~local:name ~label:(fun block ->
                Printf.sprintf "b%d" (destination block)) ) )
        :: function_.code.functions;
      (* A terminator counts 2 toward the size, so each block that a jump
         goes past, and is not written, takes 2 off. *)
      if number = 0 && function_.nested = None then
        let passed =
          List.length
            (List.filter
               (fun block ->
                 owners.(block) = number
                 && (not reached.(block))
                 && match jumps.(block) with Some { is_empty; _ } -> is_empty | None -> false)
               (List.init (Array.length texts) Fun.id))
        in
        function_.code.weight <- function_.size - (2 * passed))
    functions

let built builder = (Dynarray.get builder.functions 0).code
