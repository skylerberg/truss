(* A checked body as obligations. See PROVER.md, "Verification conditions".

   The body is executed symbolically, forward, in passive form: every value
   is a term, every fact is guarded by the condition of the path it holds
   on, and where paths join, each local that differs gets a fresh symbol
   that each path defines. So the verification condition grows with the
   body, not with its number of paths, as PROVER.md asks of [Vc].

   Each obligation becomes one query: the facts gathered before it, and its
   goal, guarded by its path. Once made, an obligation is a fact for the
   rest of the body, since its own query proves it.

   Anything this stage cannot translate soundly raises [Unsupported], and
   the definition's obligations are not proven at all: an obligation is
   never assumed because the prover could not read the code around it. *)

open Syntax
module T = Types
module C = Checked
module L = Logic
module Names = Resolve.Names
module Code = Diagnostic.Code
module Ids = Map.Make (Int)

exception Unsupported of span * string

let unsupported span format =
  Printf.ksprintf (fun message -> raise (Unsupported (span, message))) format

type obligation = {
  code : Code.prover;
  span : span;  (** Relative to the definition being proven. *)
  message : string;
  query : L.query;
  values : (string * string) list;  (** Each prover symbol a counterexample shows, with its name. *)
}

type outcome = {
  obligations : obligation list;  (** In the order made. *)
  unproven_clauses : (span * string) list;
      (** Clauses this stage does not prove yet, such as cost bounds, which the rest does not rely
          on. *)
}

(* A definition whose tables are being read: the one proven, or a callee
   whose clauses are translated at a call. *)
type source = { key : Names.key; checked : C.t; resolved : Resolve.resolved; text : string }

type loop_exits = { mutable breaks : frame list; mutable continues : frame list }

(* Where a path is: the value of each local, the values on entry for
   [old], the path's condition, and what [self] and [result] are. *)
and frame = {
  source : source;
  locals : L.term Ids.t;
  old_locals : L.term Ids.t;
  self : L.term option;
  old_self : L.term option;
  result : L.term option;
  condition : L.term;
  checking : bool;  (** Whether obligations are made here; not in a callee's clauses. *)
  bound : string list;  (** Symbols bound by quantifiers around this point. *)
  loop : loop_exits option;
}

type context = {
  database : Query.database;
  current : Path.t;
  terminates : bool;  (** Whether the definition proven has a [time] clause. *)
  measures : expression list;  (** Its [decreases], for its recursive calls. *)
  mutable declarations : L.declaration list;
  declared : (string, unit) Hashtbl.t;
  mutable facts : L.term list;  (** Reversed. *)
  mutable obligations : obligation list;  (** Reversed. *)
  mutable unproven : (span * string) list;
  mutable fresh : int;
  mutable values : (string * string) list;  (** For counterexamples. *)
  mutable returns : (frame * L.term option) list;
  mutable instantiating : Path.t list;  (** Contracts being assumed, to stop at recursion. *)
  fits : (int * T.ty) list;  (** The type checker's [Integer_fits] obligations, by expression. *)
}

(* Symbols and facts *)

let declare context declaration =
  let name = match declaration with L.Constant (name, _) | L.Function (name, _, _) -> name in
  if not (Hashtbl.mem context.declared name) then begin
    Hashtbl.replace context.declared name ();
    context.declarations <- declaration :: context.declarations
  end

let fresh context prefix sort =
  context.fresh <- context.fresh + 1;
  let name = Printf.sprintf "%s.%d" prefix context.fresh in
  declare context (L.Constant (name, sort));
  L.Symbol name

let assume context frame fact =
  if not (L.mentions frame.bound fact) then
    match fact with
    | L.Boolean true -> ()
    | _ -> context.facts <- L.( ==> ) frame.condition fact :: context.facts

(* An obligation is shown by its own query, and is a fact for what comes
   after it. Inside a quantifier there is no path to state it on, so it is
   left to the definition of the quantifier's body, which this stage does
   not check yet. *)
let oblige context frame code span message goal =
  if frame.checking && not (L.mentions frame.bound goal) then begin
    let guarded = L.( ==> ) frame.condition goal in
    context.obligations <-
      {
        code;
        span;
        message;
        query =
          {
            declarations = List.rev context.declarations;
            facts = List.rev context.facts;
            goal = guarded;
          };
        values = context.values;
      }
      :: context.obligations;
    assume context frame goal
  end

(* Source text, for messages. *)
let quote source (span : span) =
  if span.stop <= String.length source.text then
    String.sub source.text span.start (span.stop - span.start)
  else "this expression"

(* Types *)

let builtin ty = T.builtin_of ty

let bounds (ty : T.ty) =
  let power n = Z.shift_left Z.one n in
  let signed n = Some (Z.neg (power (n - 1)), Z.pred (power (n - 1))) in
  let unsigned n = Some (Z.zero, Z.pred (power n)) in
  match builtin ty with
  | Some Int8 -> signed 8
  | Some Int16 -> signed 16
  | Some Int32 -> signed 32
  | Some (Int64 | ISize) -> signed 64
  | Some UInt8 -> unsigned 8
  | Some UInt16 -> unsigned 16
  | Some UInt32 -> unsigned 32
  | Some (UInt64 | USize) -> unsigned 64
  | Some Character -> Some (Z.zero, Z.of_int 0x10FFFF)
  | _ -> None

let width (ty : T.ty) =
  match builtin ty with
  | Some (Int8 | UInt8) -> Some 8
  | Some (Int16 | UInt16) -> Some 16
  | Some (Int32 | UInt32) -> Some 32
  | Some (Int64 | UInt64 | USize | ISize) -> Some 64
  | _ -> None

let is_numeric (ty : T.ty) = match ty with T.Integer -> true | _ -> bounds ty <> None
let is_bool ty = T.is_builtin Bool ty

let sort_of (ty : T.ty) : L.sort =
  if is_numeric ty then Int else if is_bool ty then Bool else Uninterpreted (T.show ty)

let in_range ty term =
  match bounds ty with
  | Some (low, high) ->
      L.(Apply ("<=", [ Integer low; term ]) &&& Apply ("<=", [ term; Integer high ]))
  | None -> L.Boolean true

(* A value of a type that arrives from outside what is known: a parameter,
   a call's result, a loop's havocked local. *)
let arrive context frame prefix ty =
  let value = fresh context prefix (sort_of ty) in
  assume context frame (in_range ty value);
  value

let type_of source (expression : expression) =
  match source.checked.types.(expression.id) with
  | Some ty -> ty
  | None -> unsupported expression.span "an expression without a type"

(* Paths *)

let restrict frame condition = { frame with condition = L.( &&& ) frame.condition condition }

(* Joins paths: the condition is that one of them was taken, and each
   local whose values differ gets a fresh symbol each path defines. *)
let join context ?value_type frames =
  match frames with
  | [] -> None
  | [ (frame, value) ] -> Some (frame, value)
  | (first, _) :: _ ->
      let condition = L.disjunction (List.map (fun (frame, _) -> frame.condition) frames) in
      let merged = { first with condition } in
      let define prefix sort pick =
        let values = List.map (fun ((frame : frame), item) -> (frame, pick frame item)) frames in
        match values with
        | (_, Some term) :: rest when List.for_all (fun (_, other) -> other = Some term) rest ->
            Some term
        | _ when List.exists (fun (_, term) -> term = None) values -> None
        | _ ->
            let symbol = fresh context prefix sort in
            List.iter
              (fun ((frame : frame), term) ->
                match term with
                | Some term ->
                    context.facts <-
                      L.( ==> ) frame.condition (L.equal symbol term) :: context.facts
                | None -> ())
              values;
            Some symbol
      in
      let locals =
        Ids.mapi
          (fun id term ->
            let sort =
              match first.source.checked.local_types.(id) with
              | Some ty -> sort_of ty
              | None -> ( match term with L.Boolean _ -> L.Bool | _ -> L.Int)
            in
            match define "joined" sort (fun frame _ -> Ids.find_opt id frame.locals) with
            | Some joined -> joined
            | None -> term)
          first.locals
      in
      let value =
        match value_type with
        | Some ty -> define "value" (sort_of ty) (fun _ value -> value)
        | None -> None
      in
      Some ({ merged with locals }, value)

let join_frames context frames =
  Option.map fst (join context (List.map (fun frame -> (frame, None)) frames))

(* Calls: what a callee promises *)

type parameter_binding = Self_binding | Parameter_binding of name

type contract = {
  callee : source;
  binding : parameter_binding list;  (** In the order a call's arguments are numbered. *)
  defaults : (int * expression) list;
  requires : expression list;
  ensures : expression list;
  pure : bool;  (** Pure and terminating, so a function in the logic. *)
  unsupported_result : bool;  (** [yields] or [lends], whose contracts are not read yet. *)
}

let callee_source database (key : Names.key) =
  match
    ( Query.demand database Resolve.resolved key,
      Infer.clean database key,
      Query.demand database Names.text key )
  with
  | Some resolved, Some checked, Some text -> Some { key; checked; resolved; text }
  | _ -> None

let contract_of database (path : Path.t) =
  match Interface.Summary.definition database path with
  | None -> None
  | Some (key, definition) -> (
      let from parameters clauses ~receiver_first ~result =
        match callee_source database key with
        | None -> None
        | Some callee ->
            let named =
              List.filter_map
                (fun (parameter : parameter) ->
                  match parameter.kind with
                  | Named_parameter { name; default; _ } -> Some (name, default)
                  | Self_parameter _ | Parameter_error -> None)
                parameters
            in
            let has_self =
              List.exists
                (fun (parameter : parameter) ->
                  match parameter.kind with Self_parameter _ -> true | _ -> false)
                parameters
            in
            let offset = if has_self || receiver_first then 1 else 0 in
            let binding =
              (if has_self then [ Self_binding ] else [])
              @ List.map (fun (name, _) -> Parameter_binding name) named
            in
            let defaults =
              List.concat
                (List.mapi
                   (fun index (_, default) ->
                     match default with Some value -> [ (index + offset, value) ] | None -> [])
                   named)
            in
            let requires =
              List.filter_map
                (fun (clause : clause) ->
                  match clause.kind with Requires value -> Some value | _ -> None)
                clauses
            in
            let ensures =
              List.filter_map
                (fun (clause : clause) ->
                  match clause.kind with Ensures value -> Some value | _ -> None)
                clauses
            in
            let pure =
              match Query.demand database Interface.Environment.signature path with
              | Some (signature : T.signature) -> (
                  signature.uses = [] && signature.terminates
                  && List.for_all
                       (fun (info : T.parameter_info) -> info.mode = T.Read)
                       signature.parameters
                  && match signature.receiver with Some ((Mut | Own), _) -> false | _ -> true)
              | None -> false
            in
            Some
              {
                callee;
                binding;
                defaults;
                requires;
                ensures;
                pure;
                unsupported_result =
                  (match result with Some (Yields _ | Lends _) -> true | _ -> false);
              }
      in
      match definition.kind with
      | Function { signature; _ } ->
          from signature.parameters signature.clauses ~receiver_first:false ~result:signature.result
      | Theorem { parameters; clauses; _ } ->
          from parameters clauses ~receiver_first:false ~result:None
      | _ -> None)

(* Expressions *)

let literal_value frame (expression : expression) =
  match frame.source.checked.literals.(expression.id) with
  | Some (Integer_value value) -> Some (L.Integer value)
  | Some (Float_value _) -> unsupported expression.span "a float"
  | None -> None

let comparison operator =
  match operator with
  | Equal -> Some "="
  | Less -> Some "<"
  | Less_equal -> Some "<="
  | Greater -> Some ">"
  | Greater_equal -> Some ">="
  | _ -> None

let rec expression context frame (written : expression) : (frame * L.term) option =
  let result = expression_kind context frame written in
  (match (result, List.assoc_opt written.id context.fits) with
  | Some (after, value), Some ty ->
      oblige context after Fits written.span
        (Printf.sprintf "`%s` may not fit in `%s`." (quote frame.source written.span) (T.show ty))
        (in_range ty value)
  | _ -> ());
  result

and value context frame written =
  match expression context frame written with
  | Some (frame, term) -> (frame, term)
  | None -> unsupported written.span "an expression that never returns, used as a value"

and expression_kind context frame (written : expression) : (frame * L.term) option =
  let source = frame.source in
  match written.kind with
  | Integer _ -> (
      match literal_value frame written with
      | Some term -> Some (frame, term)
      | None -> unsupported written.span "an integer literal without a value")
  | Prefix (Negate, ({ kind = Integer _; _ } as inner)) -> (
      match literal_value frame written with
      | Some term -> Some (frame, term)
      | None -> (
          match literal_value frame inner with
          | Some (L.Integer value) -> Some (frame, L.Integer (Z.neg value))
          | _ -> unsupported written.span "a negated literal"))
  | True -> Some (frame, L.Boolean true)
  | False -> Some (frame, L.Boolean false)
  | Parenthesized inner | Echo inner -> expression context frame inner
  | Self_value -> (
      match frame.self with
      | Some self -> Some (frame, self)
      | None -> unsupported written.span "`self` outside a method")
  | Name path -> name context frame written path
  | Binary { operator = And; left; right; _ } ->
      let frame, left_value = value context frame left in
      let _, right_value = pure_operand context (restrict frame left_value) right in
      Some (frame, L.( &&& ) left_value right_value)
  | Binary { operator = Or; left; right; _ } ->
      let frame, left_value = value context frame left in
      let _, right_value = pure_operand context (restrict frame (L.not_ left_value)) right in
      Some (frame, L.( ||| ) left_value right_value)
  | Binary { operator = Implies; left; right; _ } ->
      let frame, left_value = value context frame left in
      let _, right_value = pure_operand context (restrict frame left_value) right in
      Some (frame, L.( ==> ) left_value right_value)
  | Binary { operator; left; right; _ } -> binary context frame written operator left right
  | Prefix (Not, inner) ->
      let frame, inner_value = value context frame inner in
      Some (frame, L.not_ inner_value)
  | Prefix (Negate, inner) ->
      let frame, inner_value = value context frame inner in
      let ty = type_of source written in
      let negated = L.Apply ("-", [ inner_value ]) in
      if bounds ty <> None then
        oblige context frame Overflow written.span
          (Printf.sprintf "`%s` may overflow `%s`." (quote source written.span) (T.show ty))
          (in_range ty negated)
      else if ty <> T.Integer then unsupported written.span "negating a value of `%s`" (T.show ty);
      Some (frame, negated)
  | Prefix (Complement, inner) ->
      let frame, inner_value = value context frame inner in
      let ty = type_of source written in
      Some (frame, opaque_operation context frame ty "complement" [ inner_value ])
  | If { condition; then_; else_ } -> if_ context frame written condition then_ else_
  | Block block_ -> block_value context frame block_
  | Return returned ->
      (match returned with
      | Some returned -> (
          match expression context frame returned with
          | Some (after, term) -> context.returns <- (after, Some term) :: context.returns
          | None -> ())
      | None -> context.returns <- (frame, None) :: context.returns);
      None
  | Unreachable ->
      oblige context frame Unreachable written.span "This `unreachable` may be reached."
        (L.Boolean false);
      None
  | Todo -> Some (frame, arrive context frame "todo" (type_of source written))
  | Break -> (
      match frame.loop with
      | Some exits ->
          exits.breaks <- frame :: exits.breaks;
          None
      | None -> unsupported written.span "`break` outside a loop")
  | Continue -> (
      match frame.loop with
      | Some exits ->
          exits.continues <- frame :: exits.continues;
          None
      | None -> unsupported written.span "`continue` outside a loop")
  | Quantified { quantifier; binder; body } ->
      quantified context frame written quantifier binder body
  | Call (callee, arguments) -> call context frame written callee arguments
  | Mode (_, inner) -> expression context frame inner
  | Member _ -> unsupported written.span "reading a field"
  | Bracket _ -> unsupported written.span "indexing"
  | Is _ -> unsupported written.span "`is`"
  | Match _ -> unsupported written.span "`match`"
  | Try _ -> unsupported written.span "`?`"
  | With _ -> unsupported written.span "`with`"
  | Lambda _ -> unsupported written.span "a lambda"
  | List _ | Map _ -> unsupported written.span "a collection literal"
  | String _ -> unsupported written.span "a string"
  | Float _ -> unsupported written.span "a float"
  | Range _ -> unsupported written.span "a range outside a `for` loop or a quantifier"
  | Any _ -> unsupported written.span "`any`"
  | Provide _ -> unsupported written.span "`provide`"
  | Self_type_value | Expression_error -> unsupported written.span "this expression"

(* The right side of [&&], [||], or [==>], which runs only on some paths:
   it may make obligations there, but not change a local, since the paths
   would then need joining. *)
and pure_operand context frame written =
  let after, term = value context frame written in
  if not (Ids.equal ( = ) after.locals frame.locals) then
    unsupported written.span "changing a variable on the right of `&&`, `||`, or `==>`";
  (after, term)

and name context frame (written : expression) (path : path) =
  let source = frame.source in
  match source.resolved.names.(path.last.id) with
  | Some Result_value -> (
      match frame.result with
      | Some result -> Some (frame, result)
      | None -> unsupported written.span "`result` here")
  | _ -> (
      match source.checked.meanings.(written.id) with
      | Some (Local_value id) -> (
          match Ids.find_opt id frame.locals with
          | Some term -> Some (frame, term)
          | None -> unsupported written.span "a local the prover did not bind")
      | Some (Generic_value parameter) ->
          let symbol = Printf.sprintf "generic.%s.%s" (Path.show parameter.owner) parameter.name in
          declare context (L.Constant (symbol, Int));
          Some (frame, L.Symbol symbol)
      | Some (Global _) -> unsupported written.span "a constant or a function as a value"
      | Some (Variant_value _) -> unsupported written.span "a variant"
      | _ -> unsupported written.span "this name")

(* An operation the solver knows only by the range of its result. *)
and opaque_operation context frame ty name arguments =
  let sorts = List.map (fun _ -> L.Int) arguments in
  let symbol = Printf.sprintf "operation.%s.%s" name (T.show ty) in
  declare context (L.Function (symbol, sorts, sort_of ty));
  let term = L.Apply (symbol, arguments) in
  assume context frame (in_range ty term);
  term

and binary context frame (written : expression) operator left right =
  let source = frame.source in
  let operand_type = type_of source left in
  let result_type = type_of source written in
  let primitive =
    (is_numeric operand_type || is_bool operand_type || T.is_builtin Character operand_type)
    && (is_numeric result_type || is_bool result_type)
  in
  if not primitive then begin
    (* An operator on another type is a call of its trait's method, known
       here only by its result's type. *)
    let frame, _ = value context frame left in
    let frame, _ = value context frame right in
    Some (frame, arrive context frame "operator" result_type)
  end
  else
    let frame, left_value = value context frame left in
    let frame, right_value = value context frame right in
    match (comparison operator, operator) with
    | Some symbol, _ -> Some (frame, L.Apply (symbol, [ left_value; right_value ]))
    | None, Not_equal -> Some (frame, L.not_ (L.equal left_value right_value))
    | None, (Add | Subtract | Multiply | Divide | Remainder) ->
        Some (frame, arithmetic context frame written result_type operator left_value right_value)
    | None, (Shift_left | Shift_right) ->
        (match width result_type with
        | Some bits ->
            oblige context frame Shift right.span
              (Printf.sprintf "The shift amount `%s` may not be less than %d."
                 (quote source right.span) bits)
              L.(Apply ("<", [ right_value; int bits ]))
        | None -> unsupported written.span "a shift of `%s`" (T.show result_type));
        let name = match operator with Shift_left -> "shift_left" | _ -> "shift_right" in
        Some (frame, opaque_operation context frame result_type name [ left_value; right_value ])
    | None, (Bit_and | Bit_or | Bit_xor) ->
        let name = match operator with Bit_and -> "and" | Bit_or -> "or" | _ -> "xor" in
        let term = opaque_operation context frame result_type name [ left_value; right_value ] in
        (match (operator, bounds result_type) with
        | Bit_and, Some (low, _) when Z.equal low Z.zero ->
            assume context frame
              L.(Apply ("<=", [ term; left_value ]) &&& Apply ("<=", [ term; right_value ]))
        | _ -> ());
        Some (frame, term)
    | None, _ -> unsupported written.span "this operator"

and arithmetic context frame (written : expression) ty operator left right =
  let source = frame.source in
  let exact =
    match operator with
    | Add -> L.Apply ("+", [ left; right ])
    | Subtract -> L.Apply ("-", [ left; right ])
    | Multiply -> L.Apply ("*", [ left; right ])
    | Divide -> L.truncated_divide left right
    | _ -> L.truncated_remainder left right
  in
  (match operator with
  | Divide | Remainder ->
      oblige context frame Division written.span
        (Printf.sprintf "The divisor in `%s` may be zero." (quote source written.span))
        (L.not_ (L.equal right (L.int 0)))
  | _ -> ());
  (match bounds ty with
  | Some (low, _) when operator = Divide || operator = Remainder ->
      if Z.sign low < 0 then
        oblige context frame Overflow written.span
          (Printf.sprintf "`%s` may overflow `%s`: the least value over -1."
             (quote source written.span) (T.show ty))
          (L.not_ L.(equal left (Integer low) &&& equal right (int (-1))))
  | Some _ ->
      oblige context frame Overflow written.span
        (Printf.sprintf "`%s` may overflow `%s`." (quote source written.span) (T.show ty))
        (in_range ty exact)
  | None -> ());
  exact

and if_ context frame (written : expression) condition then_ else_ =
  let frame, test = value context frame condition in
  let then_result = block_value context (restrict frame test) then_ in
  let otherwise = restrict frame (L.not_ test) in
  let else_result =
    match else_ with
    | Some (Else block_) -> block_value context otherwise block_
    | Some (Else_if inner) -> expression context otherwise inner
    | None -> Some (otherwise, L.Boolean true)
  in
  let ty = type_of frame.source written in
  let carries_value = else_ <> None && not (T.equal ty T.unit) in
  let reached = List.filter_map Fun.id [ then_result; else_result ] in
  if carries_value then
    match
      join context ~value_type:ty (List.map (fun (frame, term) -> (frame, Some term)) reached)
    with
    | Some (frame, Some term) -> Some (frame, term)
    | Some (frame, None) -> Some (frame, L.Boolean true)
    | None -> None
  else
    Option.map (fun frame -> (frame, L.Boolean true)) (join_frames context (List.map fst reached))

and quantified context frame (written : expression) quantifier binder body =
  let source = frame.source in
  let make bound_symbol sort premise body_frame =
    let _, body_value = value context { body_frame with checking = false } body in
    let bound = [ (bound_symbol, sort) ] in
    match quantifier with
    | Forall -> Some (frame, L.Forall (bound, L.( ==> ) premise body_value))
    | Exists -> Some (frame, L.Exists (bound, L.( &&& ) premise body_value))
  in
  context.fresh <- context.fresh + 1;
  let symbol = Printf.sprintf "bound.%d" context.fresh in
  let with_bound id ty =
    { frame with locals = Ids.add id (L.Symbol symbol) frame.locals; bound = symbol :: frame.bound }
    |> fun inner -> (inner, ty)
  in
  match binder with
  | Binder_type (name_, _) -> (
      match source.checked.local_types.(name_.id) with
      | Some ty when is_numeric ty || is_bool ty ->
          let inner, ty = with_bound name_.id ty in
          make symbol (sort_of ty) (in_range ty (L.Symbol symbol)) inner
      | _ -> unsupported written.span "a quantifier over this type")
  | Binder_in
      ( { kind = Binding_or_constant name_; _ },
        { kind = Range { start = Some start; stop = Some stop; inclusive; _ }; _ } ) ->
      let _, low = value context frame start in
      let _, high = value context frame stop in
      let ty =
        match source.checked.local_types.(name_.id) with Some ty -> ty | None -> T.Integer
      in
      let inner, _ = with_bound name_.id ty in
      let bound = L.Symbol symbol in
      let premise =
        L.(
          Apply ("<=", [ low; bound ]) &&& Apply ((if inclusive then "<=" else "<"), [ bound; high ]))
      in
      make symbol Int premise inner
  | Binder_in _ -> unsupported written.span "a quantifier over a collection"

(* Calls *)

and call context frame (written : expression) callee_expression arguments =
  let source = frame.source in
  match callee_expression.kind with
  | Name path when source.resolved.names.(path.last.id) = Some Old -> (
      match arguments with
      | [ { value = inner; _ } ] ->
          let entry = { frame with locals = frame.old_locals; self = frame.old_self } in
          let _, term = value context entry inner in
          Some (frame, term)
      | _ -> unsupported written.span "`old` with other than one argument")
  | _ -> (
      match source.checked.calls.(written.id) with
      | None -> unsupported written.span "a call the type checker did not resolve"
      | Some call_ -> resolved_call context frame written call_)

and resolved_call context frame (written : expression) (call_ : C.call) =
  let source = frame.source in
  (* Arguments run in the order written. *)
  let frame, values =
    List.fold_left
      (fun (frame, values) (argument : C.argument) ->
        let expression_ = find_expression written argument.expression in
        let frame, term = value context frame expression_ in
        (match argument.conversion with
        | Some From_integer -> ()
        | Some (From_never | Owned_to_view | Function_widening | To_integer) | None -> ());
        (frame, (argument, expression_, term) :: values))
      (frame, []) call_.arguments
  in
  let values = List.rev values in
  let result_type = call_.result in
  let havoc_mut frame =
    List.fold_left
      (fun frame ((argument : C.argument), (expression_ : expression), _) ->
        if argument.mode = T.Mut then
          match place_local frame expression_ with
          | Some (id, ty) ->
              { frame with locals = Ids.add id (arrive context frame "changed" ty) frame.locals }
          | None -> unsupported expression_.span "passing `mut` a place that is not a local"
        else frame)
      frame values
  in
  match call_.callee with
  | Function { path; _ } -> (
      match contract_of context.database path with
      | Some contract when not contract.unsupported_result ->
          Some (contract_call context frame written call_ path contract values ~havoc_mut)
      | Some _ -> unsupported written.span "a call to a lending or yielding method"
      | None ->
          let frame = havoc_mut frame in
          Some (frame, arrive context frame "result" result_type))
  | Trait_method _ | Capability_method _ | Constructor _ | Function_value | Intrinsic _
  | Built_in_operator ->
      let frame = havoc_mut frame in
      ignore source;
      Some (frame, arrive context frame "result" result_type)

and find_expression (written : expression) id =
  let found = ref None in
  let rec visit (expression_ : expression) =
    if expression_.id = id then found := Some expression_
    else if !found = None then
      Syntax_walk.expression_parts ~expression:visit ~statement:(fun _ -> ()) expression_
  in
  visit written;
  match !found with
  | Some expression_ -> expression_
  | None -> unsupported written.span "an argument"

(* The local a [mut] argument names, when it is a whole local. *)
and place_local frame (expression_ : expression) =
  match expression_.kind with
  | Mode (_, inner) | Parenthesized inner -> place_local frame inner
  | Name _ -> (
      match frame.source.checked.meanings.(expression_.id) with
      | Some (Local_value id) -> (
          match frame.source.checked.local_types.(id) with Some ty -> Some (id, ty) | None -> None)
      | _ -> None)
  | _ -> None

(* A call to a function whose contract the prover reads: its [requires]
   must hold, its [ensures] holds after, and a recursive call decreases. *)
and contract_call context frame (written : expression) (call_ : C.call) path contract values
    ~havoc_mut =
  let caller = frame.source in
  let argument_at index =
    List.find_map
      (fun ((argument : C.argument), _, term) ->
        if argument.parameter = index then Some term else None)
      values
  in
  let entry_bindings =
    List.mapi
      (fun index binding ->
        let term =
          match argument_at index with
          | Some term -> Some term
          | None -> (
              match List.assoc_opt index contract.defaults with
              | Some default ->
                  let empty =
                    { frame with source = contract.callee; locals = Ids.empty; checking = false }
                  in
                  Some (snd (value context empty default))
              | None -> None)
        in
        (binding, term))
      contract.binding
  in
  let bind bindings =
    List.fold_left
      (fun (locals, self) (binding, term) ->
        match (binding, term) with
        | Self_binding, Some term -> (locals, Some term)
        | Parameter_binding name_, Some term -> (Ids.add name_.id term locals, self)
        | _, None -> (locals, self))
      (Ids.empty, None) bindings
  in
  let entry_locals, entry_self = bind entry_bindings in
  let callee_frame =
    {
      frame with
      source = contract.callee;
      locals = entry_locals;
      old_locals = entry_locals;
      self = entry_self;
      old_self = entry_self;
      result = None;
      checking = false;
      bound = frame.bound;
      loop = None;
    }
  in
  (* Recursion must decrease. *)
  if Path.equal path context.current && context.terminates then
    begin match context.measures with
    | [] ->
        unsupported written.span
          "recursion without a `decreases` clause, since structural recursion is not proven yet"
    | measures ->
        let current_frame =
          { frame with checking = false; locals = frame.old_locals; self = frame.old_self }
        in
        let before = List.map (fun measure -> snd (value context current_frame measure)) measures in
        let after =
          List.map
            (fun measure ->
              snd
                (value context
                   { callee_frame with source = caller; locals = entry_locals; self = entry_self }
                   measure))
            measures
        in
        let rec smaller before after =
          match (before, after) with
          | [ b ], [ a ] -> L.(Apply ("<=", [ int 0; b ]) &&& Apply ("<", [ a; b ]))
          | b :: before, a :: after ->
              L.(
                Apply ("<=", [ int 0; b ])
                &&& (Apply ("<", [ a; b ]) ||| (equal a b &&& smaller before after)))
          | _ -> L.Boolean true
        in
        oblige context frame Termination written.span
          (Printf.sprintf "This recursive call may not decrease `%s`."
             (String.concat ", " (List.map (fun (m : expression) -> quote caller m.span) measures)))
          (smaller before after)
    end;
  (* Requires, at the call. *)
  List.iter
    (fun (clause : expression) ->
      let _, term = value context callee_frame clause in
      oblige context frame Requires written.span
        (Printf.sprintf "`%s` may not hold for this call to `%s`."
           (quote contract.callee clause.span)
           (Path.show path))
        term)
    contract.requires;
  let after = havoc_mut frame in
  let result =
    if contract.pure then begin
      let arguments = List.filter_map snd entry_bindings in
      let symbol = "function." ^ Path.show path in
      declare context
        (L.Function
           ( symbol,
             List.map
               (fun ((_ : C.argument), (expression_ : expression), _) ->
                 sort_of (type_of caller expression_))
               values,
             sort_of call_.result ));
      let term = L.Apply (symbol, arguments) in
      assume context after (in_range call_.result term);
      term
    end
    else arrive context after "result" call_.result
  in
  (* Ensures, after: [mut] parameters have their new values, and [old] the
     ones they had. *)
  if not (List.exists (Path.equal path) context.instantiating) then begin
    context.instantiating <- path :: context.instantiating;
    let exit_bindings =
      List.mapi
        (fun index (binding, term) ->
          let changed =
            List.find_map
              (fun ((argument : C.argument), expression_, _) ->
                if argument.parameter = index && argument.mode = T.Mut then
                  match place_local after expression_ with
                  | Some (id, _) -> Ids.find_opt id after.locals
                  | None -> None
                else None)
              values
          in
          (binding, match changed with Some term -> Some term | None -> term))
        entry_bindings
    in
    let exit_locals, exit_self = bind exit_bindings in
    let ensures_frame =
      {
        callee_frame with
        condition = after.condition;
        locals = exit_locals;
        self = exit_self;
        result = Some result;
      }
    in
    List.iter
      (fun (clause : expression) ->
        let _, term = value context ensures_frame clause in
        assume context after term)
      contract.ensures;
    context.instantiating <- List.tl context.instantiating
  end;
  (after, result)

(* Statements and blocks *)

and block_value context frame (written : block) =
  let rec go frame = function
    | [] -> Some (frame, L.Boolean true)
    | [ ({ kind = Expression last; _ } : statement) ] -> expression context frame last
    | statement_ :: rest -> (
        match statement context frame statement_ with Some frame -> go frame rest | None -> None)
  in
  match go frame written.statements with
  | Some (after, term) ->
      (* Locals declared inside the block end with it. *)
      let locals = Ids.filter (fun id _ -> Ids.mem id frame.locals) after.locals in
      Some ({ after with locals }, term)
  | None -> None

and statement context frame (written : statement) : frame option =
  match written.kind with
  | Expression value_ -> Option.map fst (expression context frame value_)
  | Let { pattern; value = initial; else_ = None; _ } -> (
      match expression context frame initial with
      | None -> None
      | Some (frame, term) -> (
          match pattern.kind with
          | Binding_or_constant name_ when frame.source.resolved.names.(name_.id) = Some Binding ->
              Some { frame with locals = Ids.add name_.id term frame.locals }
          | Wildcard -> Some frame
          | _ -> unsupported pattern.span "this pattern"))
  | Let { else_ = Some _; _ } -> unsupported written.span "`let ... else`"
  | Assignment { target; operator; value = assigned } ->
      assignment context frame written target operator assigned
  | While { condition; clauses; body } -> while_ context frame written condition clauses body
  | For { parallel = _; pattern; iterable; clauses; body } ->
      for_ context frame written pattern iterable clauses body
  | Assert asserted ->
      let frame, term = value context frame asserted in
      if is_test context then assume context frame term
      else
        oblige context frame Assertion asserted.span
          (Printf.sprintf "`%s` may not hold." (quote frame.source asserted.span))
          term;
      Some frame
  | Proof block_ -> (
      match block_value context frame block_ with
      | Some (after, _) -> Some { frame with locals = after.locals }
      | None -> None)
  | Parallel block_ ->
      (* Branches are disjoint, so they can run in order. *)
      List.fold_left
        (fun frame branch ->
          match frame with Some frame -> statement context frame branch | None -> None)
        (Some frame) block_.statements
  | Yield _ -> unsupported written.span "`yield`"
  | Statement_error -> unsupported written.span "this statement"

and is_test context = match context.current with Path.Test _ -> true | _ -> false

and assignment context frame (written : statement) target operator assigned =
  let source = frame.source in
  let id, ty =
    match place_local frame target with
    | Some place -> place
    | None -> unsupported target.span "assigning to a place that is not a local"
  in
  let frame, new_value =
    match operator with
    | Assign -> value context frame assigned
    | _ ->
        let frame, right = value context frame assigned in
        let current = Ids.find id frame.locals in
        let binary_operator : binary =
          match operator with
          | Add_assign -> Add
          | Subtract_assign -> Subtract
          | Multiply_assign -> Multiply
          | Divide_assign -> Divide
          | Remainder_assign -> Remainder
          | Bit_and_assign -> Bit_and
          | Bit_or_assign -> Bit_or
          | Bit_xor_assign -> Bit_xor
          | Shift_left_assign -> Shift_left
          | _ -> Shift_right
        in
        if not (is_numeric ty) then (
          ignore source;
          (frame, arrive context frame "operator" ty))
        else
          begin match binary_operator with
          | Add | Subtract | Multiply | Divide | Remainder ->
              ( frame,
                arithmetic context frame
                  { target with span = written.span }
                  ty binary_operator current right )
          | _ -> (frame, opaque_operation context frame ty "assignment" [ current; right ])
          end
  in
  Some { frame with locals = Ids.add id new_value frame.locals }

(* The locals a loop's body may change, which are havocked at its head. *)
and changed_locals frame (body : block) =
  let changed = ref [] in
  let rec visit_statement (statement_ : statement) =
    (match statement_.kind with
    | Assignment { target; _ } -> (
        match place_local frame target with Some (id, _) -> changed := id :: !changed | None -> ())
    | _ -> ());
    Syntax_walk.statement_parts ~expression:visit_expression ~statement:visit_statement statement_
  and visit_expression (expression_ : expression) =
    (match expression_.kind with
    | Mode (Mut, inner) -> (
        match place_local frame inner with Some (id, _) -> changed := id :: !changed | None -> ())
    | _ -> ());
    Syntax_walk.expression_parts ~expression:visit_expression ~statement:visit_statement expression_
  in
  List.iter visit_statement body.statements;
  List.sort_uniq compare (List.filter (fun id -> Ids.mem id frame.locals) !changed)

and havoc context frame ids =
  List.fold_left
    (fun frame id ->
      let ty =
        match frame.source.checked.local_types.(id) with Some ty -> ty | None -> T.Integer
      in
      { frame with locals = Ids.add id (arrive context frame "loop" ty) frame.locals })
    frame ids

and invariants (clauses : loop_clause list) =
  List.filter_map
    (fun (clause : loop_clause) ->
      match clause.kind with Invariant value -> Some value | _ -> None)
    clauses

and check_invariants context frame clauses ~when_ =
  List.iter
    (fun (invariant : expression) ->
      let _, term = value context frame invariant in
      oblige context frame Invariant invariant.span
        (Printf.sprintf "The loop invariant `%s` may not hold %s."
           (quote frame.source invariant.span)
           when_)
        term)
    (invariants clauses)

and assume_invariants context frame clauses =
  List.iter
    (fun (invariant : expression) ->
      let _, term = value context { frame with checking = false } invariant in
      assume context frame term)
    (invariants clauses)

and unproven_costs context (clauses : loop_clause list) =
  List.iter
    (fun (clause : loop_clause) ->
      match clause.kind with
      | Loop_cost _ ->
          context.unproven <- (clause.span, "a loop's `cost` clause") :: context.unproven
      | _ -> ())
    clauses

and while_ context frame (written : statement) condition clauses body =
  unproven_costs context clauses;
  check_invariants context frame clauses ~when_:"on entry to the loop";
  let changed = changed_locals frame body in
  let head = havoc context frame changed in
  assume_invariants context head clauses;
  let head, test = value context head condition in
  let exits = { breaks = []; continues = [] } in
  let inside = { (restrict head test) with loop = Some exits } in
  let measures =
    match
      List.find_map
        (fun (clause : loop_clause) ->
          match clause.kind with Loop_decreases measures -> Some measures | _ -> None)
        clauses
    with
    | Some measures -> `Written measures
    | None -> (
        match condition.kind with
        | Binary { operator = Less | Less_equal | Greater | Greater_equal; left; right; _ } ->
            `Guessed (left, right, condition)
        | _ -> `None)
  in
  let measure_terms (at : frame) =
    match measures with
    | `Written measures ->
        Some
          (List.map
             (fun measure -> snd (value context { at with checking = false } measure))
             measures)
    | `Guessed (left, right, (condition : expression)) -> (
        let _, l = value context { at with checking = false } left in
        let _, r = value context { at with checking = false } right in
        match condition.kind with
        | Binary { operator = Less; _ } -> Some [ L.Apply ("-", [ r; l ]) ]
        | Binary { operator = Less_equal; _ } ->
            Some [ L.Apply ("+", [ L.Apply ("-", [ r; l ]); L.int 1 ]) ]
        | Binary { operator = Greater; _ } -> Some [ L.Apply ("-", [ l; r ]) ]
        | _ -> Some [ L.Apply ("+", [ L.Apply ("-", [ l; r ]); L.int 1 ]) ])
    | `None -> None
  in
  let start_measures = if context.terminates then measure_terms inside else None in
  if context.terminates && start_measures = None then
    oblige context inside Termination written.span
      "This loop may not end: give it a `decreases` clause." (L.Boolean false);
  let finished = block_value context inside body in
  let ends = (match finished with Some (frame, _) -> [ frame ] | None -> []) @ exits.continues in
  List.iter
    (fun (end_ : frame) ->
      let end_ = { end_ with loop = frame.loop } in
      check_invariants context end_ clauses ~when_:"after an iteration";
      match (start_measures, measure_terms end_) with
      | Some before, Some after ->
          let rec smaller before after =
            match (before, after) with
            | [ b ], [ a ] -> L.(Apply ("<=", [ int 0; b ]) &&& Apply ("<", [ a; b ]))
            | b :: before, a :: after ->
                L.(
                  Apply ("<=", [ int 0; b ])
                  &&& (Apply ("<", [ a; b ]) ||| (equal a b &&& smaller before after)))
            | _ -> L.Boolean true
          in
          oblige context end_ Termination written.span "This loop's measure may not decrease."
            (smaller before after)
      | _ -> ())
    ends;
  let exit_ = { (restrict head (L.not_ test)) with loop = frame.loop } in
  join_frames context
    (exit_ :: List.map (fun (frame' : frame) -> { frame' with loop = frame.loop }) exits.breaks)
  |> Option.map (fun (joined : frame) ->
      { joined with locals = Ids.filter (fun id _ -> Ids.mem id frame.locals) joined.locals })

and for_ context frame (written : statement) pattern iterable clauses body =
  unproven_costs context clauses;
  match (frame.source.checked.loops.(written.id), iterable.kind, pattern.kind) with
  | ( Some (Integer_range { element; inclusive }),
      Range { start = Some start; stop = Some stop; _ },
      (Binding_or_constant _ | Wildcard) ) ->
      let frame, low = value context frame start in
      let frame, high = value context frame stop in
      check_invariants context frame clauses ~when_:"on entry to the loop";
      let changed = changed_locals frame body in
      let head = havoc context frame changed in
      assume_invariants context head clauses;
      let index = arrive context head "index" element in
      let in_range =
        L.(
          Apply ("<=", [ low; index ]) &&& Apply ((if inclusive then "<=" else "<"), [ index; high ]))
      in
      let exits = { breaks = []; continues = [] } in
      let inside = { (restrict head in_range) with loop = Some exits } in
      let inside =
        match pattern.kind with
        | Binding_or_constant name_ -> { inside with locals = Ids.add name_.id index inside.locals }
        | _ -> inside
      in
      let finished = block_value context inside body in
      let ends =
        (match finished with Some (frame, _) -> [ frame ] | None -> []) @ exits.continues
      in
      List.iter
        (fun (end_ : frame) ->
          check_invariants context { end_ with loop = frame.loop } clauses
            ~when_:"after an iteration")
        ends;
      join_frames context
        ({ head with loop = frame.loop }
        :: List.map (fun (f : frame) -> { f with loop = frame.loop }) exits.breaks)
      |> Option.map (fun (joined : frame) ->
          { joined with locals = Ids.filter (fun id _ -> Ids.mem id frame.locals) joined.locals })
  | _ -> unsupported written.span "a `for` loop over anything but a range of integers"

(* Definitions *)

let new_context database ~current ~terminates ~measures checked =
  {
    database;
    current;
    terminates;
    measures;
    declarations = [];
    declared = Hashtbl.create 64;
    facts = [];
    obligations = [];
    unproven = [];
    fresh = 0;
    values = [];
    returns = [];
    instantiating = [];
    fits =
      List.filter_map
        (function C.Integer_fits { expression; type_ } -> Some (expression, type_) | _ -> None)
        checked.C.obligations;
  }

let outcome context =
  { obligations = List.rev context.obligations; unproven_clauses = List.rev context.unproven }

let reject_checker_obligations (source : source) =
  List.iter
    (function
      | C.Integer_fits _ -> ()
      | C.Disjoint { first; _ } ->
          raise (Unsupported (Span.make 0 0, Printf.sprintf "disjoint indexes (at node %d)" first))
      | C.Costs_imply _ -> raise (Unsupported (Span.make 0 0, "a function value's costs"))
      | C.Guards_cover _ -> raise (Unsupported (Span.make 0 0, "a `match` with guards")))
    source.checked.obligations

let costs_unproven context (clauses : clause list) =
  List.iter
    (fun (clause : clause) ->
      match clause.kind with
      | Cost { resource = Time; bound = Finite; _ } -> ()
      | Cost _ -> context.unproven <- (clause.span, "a `cost` bound") :: context.unproven
      | _ -> ())
    clauses

(* A function, method, or theorem: its parameters arrive, its [requires]
   are assumed, its body runs, and its [ensures] are shown at each way it
   returns. *)
let function_ ?(proof = false) database (source : source) ~path (signature : signature)
    (body : block) =
  reject_checker_obligations source;
  (match signature.result with
  | Some (Yields _ | Lends _) -> unsupported body.span "a lending or yielding method"
  | _ -> ());
  let terminates =
    proof
    || List.exists
         (fun (clause : clause) ->
           match clause.kind with Cost { resource = Time; _ } -> true | _ -> false)
         signature.clauses
  in
  let measures =
    List.concat_map
      (fun (clause : clause) -> match clause.kind with Decreases measures -> measures | _ -> [])
      signature.clauses
  in
  let context = new_context database ~current:path ~terminates ~measures source.checked in
  costs_unproven context signature.clauses;
  let start =
    {
      source;
      locals = Ids.empty;
      old_locals = Ids.empty;
      self = None;
      old_self = None;
      result = None;
      condition = L.Boolean true;
      checking = true;
      bound = [];
      loop = None;
    }
  in
  let start =
    List.fold_left
      (fun frame (parameter : parameter) ->
        match parameter.kind with
        | Named_parameter { name = name_; _ } -> (
            match source.checked.local_types.(name_.id) with
            | Some ty ->
                let term = arrive context frame ("parameter." ^ name_.text) ty in
                (match term with
                | L.Symbol symbol -> context.values <- (symbol, name_.text) :: context.values
                | _ -> ());
                { frame with locals = Ids.add name_.id term frame.locals }
            | None -> unsupported parameter.span "a parameter without a type")
        | Self_parameter _ ->
            let self_type =
              match Query.demand database Interface.Environment.signature path with
              | Some { receiver = Some (_, ty); _ } -> ty
              | _ -> unsupported parameter.span "`self` without a type"
            in
            { frame with self = Some (arrive context frame "self" self_type) }
        | Parameter_error -> unsupported parameter.span "a parameter that did not parse")
      start signature.parameters
  in
  let start = { start with old_locals = start.locals; old_self = start.self } in
  let start =
    List.fold_left
      (fun frame (clause : clause) ->
        match clause.kind with
        | Requires value_ ->
            let frame, term = value context frame value_ in
            assume context frame term;
            frame
        | _ -> frame)
      start signature.clauses
  in
  let finished = block_value context start body in
  let returns =
    (match finished with Some (frame, term) -> [ (frame, Some term) ] | None -> [])
    @ List.rev context.returns
  in
  List.iter
    (fun ((frame : frame), returned) ->
      let frame = { frame with result = returned } in
      List.iter
        (fun (clause : clause) ->
          match clause.kind with
          | Ensures ensured ->
              let _, term = value context frame ensured in
              oblige context frame Ensures ensured.span
                (Printf.sprintf "`%s` may not hold when the function returns."
                   (quote source ensured.span))
                term
          | _ -> ())
        signature.clauses)
    returns;
  outcome context

let test database (source : source) ~path (body : block) =
  reject_checker_obligations source;
  let context = new_context database ~current:path ~terminates:false ~measures:[] source.checked in
  let start =
    {
      source;
      locals = Ids.empty;
      old_locals = Ids.empty;
      self = None;
      old_self = None;
      result = None;
      condition = L.Boolean true;
      checking = true;
      bound = [];
      loop = None;
    }
  in
  ignore (block_value context start body);
  outcome context

let theorem database source ~path ~parameters ~clauses body =
  function_ ~proof:true database source ~path
    {
      name = Plain_name { text = ""; span = Span.make 0 0; id = -1 };
      generics = [];
      parameters;
      result = None;
      clauses;
    }
    body
