(* The state of lowering one function: its frame, scopes, loops, and
   temporaries, and the small helpers every part of lowering shares. *)

open Definitions
open Lir_builder

(* Lowering one function *)

(* What leaving a scope does: drop what a place still owns, or free the
   heap block a pointer points at, once what is in it has been dropped. *)
type cleanup = Drop_value of Lir.place | Free_pointed of Lir.place
type scope = { mutable owned : cleanup list  (** Most recent first *) }

(* Where [continue] and [break] go, and how many scopes each keeps. *)
type loop = { continue_ : Lir.block; continue_depth : int; break_ : Lir.block; break_depth : int }

(* The code being lowered: the function's own body, or the body of a
   method inlined into it, each with its own tables and names. *)
type frame = {
  code : code;
  bindings : (S.id, Lir.place) Hashtbl.t;
  mutable self_place : Lir.place option;
  on_yield : (Lir.place -> resume:Lir.block -> stop:Lir.block -> unit) option;
      (** In an inlined lending or yielding method, what a [yield] of a place does *)
  inlined : Path.t list;  (** The methods inlined around this frame, to refuse recursion *)
  exit : (Lir.block * int) option;
      (** In an inlined method, where its [return] goes and how many scopes that keeps *)
}

(* Where a function's result goes: through the pointer it is given, into a
   local it returns, or nowhere. *)
type result_slot = Through of Lir.local | Returned_in of Lir.local | No_result

type state = {
  context : context;
  mutable frame : frame;
  b : Lir_builder.t;
  mutable scopes : scope list;  (** Innermost first *)
  mutable loops : loop list;
  mutable temporaries : Lir.place list list;
      (** Of each statement being lowered, innermost first *)
  mutable result : result_slot;
  nested : Lir.function_ option list ref;  (** The instance's lambdas, in order *)
  mutable evidence : (Path.t * Lir.operand) list;  (** The evidence for each capability available *)
  pulling : bool;  (** Whether this is a yielding method's pulled version, whose [yield]s stay *)
}

(* The code a function starts lowering: its own, with nothing bound yet. *)
let frame_of code ~inlined =
  { code; bindings = Hashtbl.create 16; self_place = None; on_yield = None; inlined; exit = None }

(* The state to write one function in: a builder of its own and the
   function's scope. A lambda shares [nested] with the function around it. *)
let enter context ?(pulling = false) ?(nested = ref []) frame =
  {
    context;
    frame;
    b = Lir_builder.create ();
    scopes = [ { owned = [] } ];
    loops = [];
    temporaries = [];
    result = No_result;
    nested;
    evidence = [];
    pulling;
  }

let ground st ty = Monomorphic.ground st.context.monomorphic st.frame.code.substitution ty

let type_of st (id : S.id) =
  match st.frame.code.checked.types.(id) with
  | Some ty -> ground st ty
  | None -> bug "no type for expression %d" id

let raw_type_of st (id : S.id) = st.frame.code.checked.types.(id)
let trivial st ty = Glue.trivial st.context.glue ty
let zero_size st ty = (Memory_layout.of_type st.context.env ty).size = 0

(* Whether a type is one of the built-in numbers, [Bool], or [Character],
   whose operators are primitive operations, never calls. *)
let primitive_methods =
  [
    ("add", "Add");
    ("subtract", "Subtract");
    ("multiply", "Multiply");
    ("divide", "Divide");
    ("remainder", "Remainder");
    ("negate", "Negate");
    ("equal", "Equal");
    ("compare", "Ordered");
  ]

let primitive (ty : Ground.ty) =
  match ty with
  | Named { path; arguments = [] } -> (
      match Intrinsic.builtin_of_path path with
      | Some
          ( Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64 | USize | ISize
          | Float32 | Float64 | Bool | Character ) ->
          true
      | _ -> false)
  | _ -> false

let site st (span : S.span) : Lir.site =
  let text = st.frame.code.text in
  let line = ref 0 and column = ref 1 in
  String.iteri
    (fun i c ->
      if i < span.start then
        if c = '\n' then begin
          incr line;
          column := 1
        end
        else incr column)
    text;
  { definition = st.frame.code.anchor; line = !line; column = !column }

(* A valid program stage0 cannot lower yet, at a place in the code being
   lowered. *)
let at_site ({ definition; line; column } : Lir.site) : Compiler_bug.site =
  { definition; line; column }

let unsupported st (span : S.span) format =
  Compiler_bug.unsupported ~at:(at_site (site st span)) format

let source st (span : S.span) =
  let text = st.frame.code.text in
  let start = min span.start (String.length text) in
  String.sub text start (min span.stop (String.length text) - start)

let new_local st ?name ty = at (local st.b ?name (Value ty))

(* A parameter of the function being written, as the calling convention
   passes it, or as [how] does: the local it arrives in, unless it has no
   size, and the place its value is read at. *)
let parameter st ?how (mode : Ground.mode) ty =
  let how = Option.value how ~default:(Convention.parameter st.context.env) in
  match how mode ty with
  | None -> (None, new_local st ty)
  | Some (Lir.Pointer _ as pointer) ->
      let arrives = local st.b pointer in
      (Some arrives, { Lir.root = Local arrives; projections = [ Deref ] })
  | Some passed ->
      let arrives = local st.b passed in
      (Some arrives, at arrives)

(* A parameter for the evidence of each capability, which the code then
   reaches by it. Gives the parameters, in order. *)
let evidence_parameters st capabilities =
  let arriving =
    List.map
      (fun capability -> (capability, local st.b ~name:"evidence" Convention.evidence))
      capabilities
  in
  st.evidence <- List.map (fun (capability, l) -> (capability, Lir.Copy (at l))) arriving;
  List.map snd arriving

(* Makes the slot for the function's result, as the convention passes one. *)
let result_slot st (convention : Convention.result) =
  st.result <-
    (match convention with
    | Through_pointer pointer -> Through (local st.b ~name:"result" pointer)
    | Returned ty -> Returned_in (local st.b ~name:"result" ty)
    | Nothing -> No_result)

(* Where the function's result is written, if it has one with a size. *)
let result_place st : Lir.place option =
  match st.result with
  | Through pointer -> Some { root = Local pointer; projections = [ Deref ] }
  | Returned_in local -> Some (at local)
  | No_result -> None

let return_result st : Lir.terminator =
  Return (match st.result with Returned_in local -> Some (Move (at local)) | _ -> None)

(* A temporary that holds an owned value for the rest of the statement. *)
let temporary st ty =
  let place = new_local st ty in
  (match st.temporaries with
  | current :: rest -> st.temporaries <- (place :: current) :: rest
  | [] -> ());
  place

let own_in_scope st place =
  match st.scopes with
  | scope :: _ -> scope.owned <- Drop_value place :: scope.owned
  | [] -> bug "no scope"

(* A heap block the scope frees as it ends, after the drops of what is in it,
   which are owned later and so come first. *)
let free_in_scope st pointer =
  match st.scopes with
  | scope :: _ -> scope.owned <- Free_pointed pointer :: scope.owned
  | [] -> bug "no scope"

let drop_scope st (scope : scope) =
  List.iter
    (function
      | Drop_value place -> emit st.b (Drop place)
      | Free_pointed pointer ->
          emit st.b
            (Call { target = Intrinsic Free; arguments = [ Copy pointer ]; result = Discarded }))
    scope.owned

let drop_temporaries st temporaries = List.iter (fun place -> emit st.b (Drop place)) temporaries

(* Drops everything owned in the scopes inside the [depth] outermost, and
   every pending temporary, as a [return], [break], or [continue] leaves
   them. *)
let leave_to st depth =
  List.iter (drop_temporaries st) st.temporaries;
  List.iteri
    (fun i scope -> if List.length st.scopes - i > depth then drop_scope st scope)
    st.scopes

(* A scope opened here and closed, with its drops, by [close_scope], for a
   condition's names, whose scope ends on more than one path. *)
let open_scope st =
  let scope = { owned = [] } in
  st.scopes <- scope :: st.scopes;
  scope

let close_scope st scope =
  drop_scope st scope;
  match st.scopes with
  | top :: rest when top == scope -> st.scopes <- rest
  | _ -> bug "a scope closed out of order"

let in_scope st f =
  let scope = open_scope st in
  let result = f () in
  close_scope st scope;
  result

(* Ends the function being written: what its scope still owns is dropped
   and its result returned. Its parameters are [first], which it is given
   before anything else, the pointer its result is written through, if it
   has one, and [rest]. *)
let finish_function st ?(returns = true) ~first ~rest () : Lir.function_ =
  (match st.scopes with [ scope ] -> drop_scope st scope | _ -> bug "a function ended in a scope");
  finish st.b (if returns then return_result st else Unreachable);
  let pointer = match st.result with Through pointer -> Some pointer | _ -> None in
  let result =
    match st.result with Returned_in local -> Some (local_type st.b local) | _ -> None
  in
  let built =
    Lir_builder.build st.b ?written_result:pointer
      ~parameters:(first @ Option.to_list pointer @ rest)
      ~result
  in
  { built with returns }

(* The lambdas the function made, in order. *)
let nested_functions st =
  Array.of_list
    (List.map (function Some f -> f | None -> bug "a lambda left unfinished") !(st.nested))

let unreachable_block st =
  finish st.b Unreachable;
  start st.b (block st.b)

(* An operand for an owned position: a [var], an [own] argument, a field, a
   returned value. The type checker has made sure a place there is a
   temporary or was marked [own], or copies implicitly. *)
let owned st place ty = if trivial st ty then Lir.Copy place else Lir.Move place
let constant_int integer value = Lir.Constant (Integer (integer, value))

let integer_of st ty =
  match (Memory_layout.of_type st.context.env ty).form with
  | Scalar (Integer integer) -> integer
  | _ -> bug "%s is not an integer type" (Ground.to_string ty)

let scalar_of st ty =
  match (Memory_layout.of_type st.context.env ty).form with
  | Scalar scalar -> scalar
  | _ -> bug "%s is not a number" (Ground.to_string ty)

(* Ends a statement: drops its temporaries. *)
let end_statement st =
  match st.temporaries with
  | current :: rest ->
      drop_temporaries st current;
      st.temporaries <- rest
  | [] -> ()
