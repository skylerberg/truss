(* Checking bodies: bidirectional, one statement at a time. See
   TYPECHECKER.md, "Checking bodies" and "Patterns".

   An expression is either checked against an expected type, which flows
   in from annotations, parameters, and operators, or has its type
   inferred. Unknown types within a statement are inference variables.
   When a statement ends, its literals take their defaults, every variable
   it made must be solved, and the types it recorded are final. Variables
   are numbered across the definition, so a statement inside a lambda leaves
   the enclosing statement's variables for that statement to settle. *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower

(* State *)

type local = { type_ : T.ty; mutable_ : bool; mode : T.mode }

(* Where a statement is: what [return] and [yield] check against, and
   whether it is a specification. *)
type env = {
  output : T.result option;
  specification : bool;
  self : T.ty option;  (** The type of [self]. *)
  self_mode : T.mode;  (** How the method takes [self]: only [mut self] can be assigned to. *)
}

type frame = {
  start : int;  (** The first inference variable the statement made. *)
  mutable nodes : int list;  (** Expressions whose types the statement recorded. *)
  mutable bindings : int list;  (** Locals it bound. *)
  mutable patterns : int list;  (** Patterns whose matched types it recorded. *)
  mutable pending : (unit -> bool) list;
      (** Checks that wait for types the statement has not decided yet; each says whether it is
          done. *)
  frame_specification : bool;
  span : span;
}

type state = {
  database : Query.database;
  key : Names.key;
  package : string;
  definition : definition;
  resolved : Resolve.resolved;
  context : Lower.context;
  text : string;  (** The definition's source text, for fixes. *)
  tables : C.t;
  mutable obligations : C.obligation list;
  mutable diagnostics : Diagnostic.t list;
  unifier : Unify.t;
  locals : (id, local) Hashtbl.t;
  mutable frames : frame list;
  mutable references : id list;  (** Locals read, newest first, for lambdas' captures. *)
  mutable receiver_modes : (id * T.mode) list;  (** Method calls whose receiver a mark covers. *)
  binding_spans : (id, span) Hashtbl.t;
      (** Where each name of the definition is, for lambdas' captures. *)
}

let report state ?(fixes = []) code (span : span) message =
  state.diagnostics <-
    Diagnostic.make ~fixes ~code:(Types code) (Source.span span.start span.stop) message
    :: state.diagnostics

let source state (span : span) =
  if span.stop <= String.length state.text then
    String.sub state.text span.start (span.stop - span.start)
  else ""

let fix title edits = Diagnostic.fix title edits
let replace (span : span) text = Diagnostic.replace (Source.span span.start span.stop) text
let insert position text = Diagnostic.insert position text
let current_frame state = match state.frames with frame :: _ -> Some frame | [] -> None

let record state (value : expression) type_ =
  state.tables.types.(value.id) <- Some type_;
  match current_frame state with Some frame -> frame.nodes <- value.id :: frame.nodes | None -> ()

let defer state check =
  match current_frame state with
  | Some frame -> if not (check ()) then frame.pending <- check :: frame.pending
  | None -> ignore (check ())

let resolve state type_ = Unify.resolve state.unifier type_
let zonk state type_ = Unify.zonk state.unifier type_
let fresh state = Unify.fresh state.unifier

let bounds state parameter =
  Option.value ~default:[] (Hashtbl.find_opt state.context.bounds parameter)

let normalize state type_ = Impls.normalize state.database ~bounds:(bounds state) (zonk state type_)
let unify state left right = Unify.unify state.unifier left right

let implements state type_ trait =
  Impls.implements state.database ~bounds:(bounds state) (zonk state type_)
    (Unify.zonk_trait state.unifier trait)

let copyable state type_ =
  Properties.copyable state.database ~bounds:(bounds state) (zonk state type_)

let plain state type_ = Properties.plain state.database ~bounds:(bounds state) (zonk state type_)

let evidence_of = function
  | Impls.From_impl { impl; substitution } -> C.Impl { impl; arguments = substitution }
  | Impls.From_bound parameter -> C.Bound parameter
  | Impls.From_any -> C.Dynamic
  | Impls.Built_in | Impls.Accepted -> C.Built_in

(* Standard paths *)

let standard modules name : Path.t = Top { module_ = { package = "standard"; modules }; name }
let core = standard [ "core" ]
let option_path = standard [ "option" ] "Option"
let result_path = standard [ "result" ] "Result"
let list_path = standard [ "list" ] "List"
let slice_path = standard [ "list" ] "Slice"
let string_path = standard [ "text" ] "String"
let string_slice_path = standard [ "text" ] "StringSlice"
let set_path = standard [ "set" ] "Set"
let map_path = standard [ "map" ] "Map"
let range_path = core "Range"

let trait_reference ?(arguments = []) trait : T.trait_reference =
  { trait; trait_arguments = arguments; associated = [] }

let string_type = T.Named { path = string_path; arguments = [] }

let is_named path type_ =
  match type_ with T.Named named -> Path.equal named.path path | _ -> false

let element_of = function
  | T.Named { arguments = T.Type element :: _; _ } -> Some element
  | _ -> None

(* Statements *)

(* Settles a statement's types. Literals it made that nothing decided take
   their defaults, and a variable it made that is still unsolved is an
   error. What still mentions an enclosing statement's variables is left to
   that statement. *)
let settle state frame =
  let run_pending () =
    let rec loop pending =
      let left = List.filter (fun check -> not (check ())) pending in
      if List.length left < List.length pending then loop left else left
    in
    frame.pending <- loop frame.pending
  in
  run_pending ();
  let types_of ids table = List.filter_map (fun id -> table.(id)) ids in
  let all_types () =
    types_of frame.nodes state.tables.types @ types_of frame.bindings state.tables.local_types
  in
  let rec default (type_ : T.ty) =
    match resolve state type_ with
    | Literal (kind, index) when index >= frame.start ->
        Hashtbl.replace state.unifier.types index
          (match kind with
          | Integer_literal -> if frame.frame_specification then T.Integer else T.builtin Int64
          | Float_literal -> T.builtin Float64)
    | Named { arguments; _ } | Cursor { arguments; _ } ->
        List.iter
          (function T.Type type_ -> default type_ | T.Value _ | T.Capabilities _ -> ())
          arguments
    | Function { inputs; output; _ } -> (
        List.iter (fun (_, type_) -> default type_) inputs;
        match output with Returns type_ | Yields (_, type_) | Lends (_, type_) -> default type_)
    | Projection { base; _ } -> default base
    | _ -> ()
  in
  List.iter default (all_types ());
  run_pending ();
  let rec unsolved (type_ : T.ty) =
    match resolve state type_ with
    | Variable index -> index >= frame.start
    | Named { arguments; _ } | Cursor { arguments; _ } ->
        List.exists
          (function T.Type type_ -> unsolved type_ | T.Value _ | T.Capabilities _ -> false)
          arguments
    | Function { inputs; output; _ } -> (
        List.exists (fun (_, type_) -> unsolved type_) inputs
        ||
        match output with
        | Returns type_ | Yields (_, type_) | Lends (_, type_) -> unsolved type_)
    | _ -> false
  in
  if List.exists unsolved (all_types ()) then begin
    report state Cannot_infer frame.span
      "The types in this statement cannot be worked out from it alone. Give the `let` a type, or \
       the call type arguments, such as `var names: List[String] = []`.";
    (* Every unsolved variable becomes an error, so it is reported once. *)
    let rec silence (type_ : T.ty) =
      match resolve state type_ with
      | Variable index when index >= frame.start ->
          Hashtbl.replace state.unifier.types index T.Error
      | Named { arguments; _ } | Cursor { arguments; _ } ->
          List.iter
            (function T.Type type_ -> silence type_ | T.Value _ | T.Capabilities _ -> ())
            arguments
      | Function { inputs; output; _ } -> (
          List.iter (fun (_, type_) -> silence type_) inputs;
          match output with Returns type_ | Yields (_, type_) | Lends (_, type_) -> silence type_)
      | _ -> ()
    in
    List.iter silence (all_types ())
  end;
  let parent = match state.frames with _ :: parent :: _ -> Some parent | _ -> None in
  let finish table ids keep =
    List.iter
      (fun id ->
        match table.(id) with
        | Some type_ -> (
            let type_ = Impls.normalize state.database ~bounds:(bounds state) (zonk state type_) in
            table.(id) <- Some type_;
            if T.contains_unsolved type_ then
              match parent with Some parent -> keep parent id | None -> ())
        | None -> ())
      ids
  in
  finish state.tables.types frame.nodes (fun parent id -> parent.nodes <- id :: parent.nodes);
  finish state.tables.local_types frame.bindings (fun parent id ->
      parent.bindings <- id :: parent.bindings);
  match parent with Some parent -> parent.pending <- frame.pending @ parent.pending | None -> ()

let in_statement state env (span : span) body =
  let frame =
    {
      start = state.unifier.next + 1;
      nodes = [];
      bindings = [];
      patterns = [];
      pending = [];
      frame_specification = env.specification;
      span;
    }
  in
  state.frames <- frame :: state.frames;
  let result = body () in
  settle state frame;
  state.frames <- List.tl state.frames;
  result

(* Locals *)

let declare state (name : name) type_ ~mutable_ ~mode =
  Hashtbl.replace state.locals name.id { type_; mutable_; mode };
  state.tables.local_types.(name.id) <- Some type_;
  match current_frame state with
  | Some frame -> frame.bindings <- name.id :: frame.bindings
  | None -> ()

let target state (name : name) = state.resolved.names.(name.id)

(* Showing types and fixes *)

let show state type_ = T.show (zonk state type_)

let mismatch state (span : span) ~expected ~found =
  let expected = zonk state expected and found = zonk state found in
  let fixes, message =
    match (resolve state found, expected) with
    | T.Literal (Integer_literal, _), _ when T.is_float_type expected ->
        ( [ fix "Write it as a float." [ insert span.stop ".0" ] ],
          Printf.sprintf "An integer literal is never a float, and `%s` is expected here."
            (T.show expected) )
    | _ -> ([], Printf.sprintf "Expected `%s`, found `%s`." (T.show expected) (T.show found))
  in
  report state ~fixes Mismatch span message

(* Places *)

(* Whether an expression is a place: a local, a parameter, [self], or a
   constant, followed by fields and indexes. *)
let rec is_place state (value : expression) =
  match value.kind with
  | Name path -> (
      match target state path.last with
      | Some (Local _ | Field _) -> true
      | Some (Definition (Top _ as path_)) ->
          Interface.Summary.kind_of state.database path_ = Some Constant
      | _ -> false)
  | Self_value -> true
  | Member (base, _) -> is_place state base
  | Bracket (base, _) -> (
      match state.resolved.brackets.(value.id) with
      | Some Index -> is_place state base
      | Some Method_bracket -> (
          match base.kind with Member _ -> is_place state base | _ -> false)
      | _ -> false)
  | Parenthesized inner -> is_place state inner
  | _ -> false

let rec place_root state (value : expression) =
  match value.kind with
  | Name path -> (
      match target state path.last with Some (Local id) -> Some (`Local id) | _ -> None)
  | Self_value -> Some `Self
  | Member (base, _) | Bracket (base, _) | Parenthesized base -> place_root state base
  | _ -> None

(* The first method call in a marked expression whose receiver is the
   place, which the mark gives its mode. *)
let rec marked_call state (value : expression) =
  match value.kind with
  | Call ({ kind = Member (base, _); _ }, _)
  | Call ({ kind = Bracket ({ kind = Member (base, _); _ }, _); _ }, _) ->
      if is_place state base then Some value.id else marked_call state base
  | Member (base, _) | Bracket (base, _) | Try base -> marked_call state base
  | _ -> None

(* Static references: an expression that names a type or a trait rather
   than a value, before a [.] or a [(]. *)
type static_ = Static_type of T.ty | Static_trait of Path.t | Static_capability of Path.t

let fresh_arguments state (path : Path.t) =
  match Query.demand state.database Environment.type_interface path with
  | Some interface ->
      List.map
        (fun (generic : T.generic) ->
          match generic.kind with
          | Value_generic -> T.Value (Unify.fresh_value state.unifier)
          | Type_generic _ -> T.Type (fresh state)
          | Capability_generic -> T.Capabilities [])
        interface.type_generics
  | None -> []

let rec static_ state (value : expression) : static_ option =
  match value.kind with
  | Self_type_value -> Option.map (fun self -> Static_type self) state.context.self_type
  | Parenthesized inner -> static_ state inner
  | Name path -> (
      match target state path.last with
      | Some (Definition definition_path) -> (
          match Intrinsic.builtin_of_path definition_path with
          | Some Never -> Some (Static_type T.Never)
          | Some Integer -> Some (Static_type T.Integer)
          | Some _ ->
              Some
                (Static_type
                   (T.Named
                      { path = definition_path; arguments = fresh_arguments state definition_path }))
          | None -> (
              match Interface.Summary.kind_of state.database definition_path with
              | Some Type ->
                  Some
                    (Static_type
                       (T.Named
                          {
                            path = definition_path;
                            arguments = fresh_arguments state definition_path;
                          }))
              | Some Trait -> Some (Static_trait definition_path)
              | Some Capability -> Some (Static_capability definition_path)
              | _ -> None))
      | Some (Generic id) -> (
          match Hashtbl.find_opt state.context.parameters id with
          | Some parameter when path.last.text.[0] >= 'A' && path.last.text.[0] <= 'Z' ->
              Some (Static_type (T.Parameter parameter))
          | _ -> None)
      | _ -> None)
  | Bracket (base, items) when state.resolved.brackets.(value.id) = Some Type_arguments -> (
      match static_ state base with
      | Some (Static_type (Named { path; _ })) ->
          let arguments =
            List.filter_map
              (function
                | Item item -> Some (type_argument_of_expression state item)
                | Item_constraint _ -> None)
              items
          in
          Some (Static_type (Named { path; arguments }))
      | other -> other)
  | _ -> None

(* A type written as an expression, as in [List[String].with_capacity]. *)
and type_argument_of_expression state (value : expression) : T.argument =
  match value.kind with
  | Integer value -> T.Value (Known value)
  | Name path -> (
      match target state path.last with
      | Some (Generic id) when path.last.text.[0] >= 'a' && path.last.text.[0] <= 'z' -> (
          match Hashtbl.find_opt state.context.parameters id with
          | Some parameter -> T.Value (Value_parameter parameter)
          | None -> T.Type T.Error)
      | Some (Definition path_) when Interface.Summary.kind_of state.database path_ = Some Constant
        -> (
          match Query.demand state.database Interface.Constants.value_of path_ with
          | Some value -> T.Value (Known value)
          | None -> T.Type T.Error)
      | _ -> (
          match static_ state value with
          | Some (Static_type type_) -> T.Type type_
          | _ -> T.Type T.Error))
  | _ -> (
      match static_ state value with
      | Some (Static_type type_) -> T.Type type_
      | _ -> T.Type T.Error)

(* Instantiating signatures *)

type instance = {
  signature : T.signature;
  substitution : T.substitution;
  type_arguments : T.argument list;
}

let instantiate state ?(extra = []) (signature : T.signature) =
  let substitution =
    List.map
      (fun (generic : T.generic) ->
        ( generic.generic,
          match generic.kind with
          | Value_generic -> T.Value (Unify.fresh_value state.unifier)
          | Type_generic _ -> T.Type (fresh state)
          (* Solved from what the call's lambdas use, by the capability check. *)
          | Capability_generic -> T.Capabilities [ T.Capability_parameter generic.generic ] ))
      signature.generics
    @ extra
  in
  let substitute = T.substitute substitution in
  let output =
    match signature.output with
    | Returns type_ -> T.Returns (substitute type_)
    | Yields (mode, type_) -> T.Yields (mode, substitute type_)
    | Lends (mode, type_) -> T.Lends (mode, substitute type_)
  in
  {
    signature =
      {
        signature with
        receiver =
          Option.map (fun (receiver, type_) -> (receiver, substitute type_)) signature.receiver;
        parameters =
          List.map
            (fun (parameter : T.parameter_info) ->
              { parameter with type_ = substitute parameter.type_ })
            signature.parameters;
        output;
        uses =
          (T.substitute_function substitution
             { inputs = []; output; uses = signature.uses; costs = [] })
            .uses;
      };
    substitution;
    type_arguments =
      List.map
        (fun (generic : T.generic) -> List.assoc generic.generic substitution)
        signature.generics;
  }

let output_type = function T.Returns type_ | Yields (_, type_) | Lends (_, type_) -> type_

let intrinsic_signature path =
  Option.map Intrinsic_signatures.signature (Intrinsic.operation_of_path path)

let function_signature state (path : Path.t) =
  match intrinsic_signature path with
  | Some signature -> Some signature
  | None -> Query.demand state.database Environment.signature path

(* Arguments and modes *)

type argument_form = Marked of T.mode * expression | Place | Temporary

let argument_form state (value : expression) =
  match value.kind with
  | Mode (mode, inner) when Option.is_none (marked_call state inner) ->
      Marked ((match mode with Mut -> Mut | Own -> Own), inner)
  | _ -> if is_place state value then Place else Temporary

let mark_span (value : expression) (inner : expression) =
  Span.make value.span.start inner.span.start

let check_mode state (value : expression) (parameter : T.parameter_info) type_ =
  let name = parameter.name in
  match (parameter.mode, argument_form state value) with
  | Read, (Place | Temporary) -> ()
  | Read, Marked (_, inner) ->
      report state Redundant_mark value.span
        ~fixes:
          [
            fix "Remove the mark."
              [ Diagnostic.delete (Source.span value.span.start inner.span.start) ];
          ]
        (Printf.sprintf "`%s` only reads its argument, so it takes no mark." name)
  | Mut, Marked (Mut, _) -> ()
  | Mut, Place ->
      report state Missing_mark value.span
        ~fixes:[ fix "Mark it `mut`." [ insert value.span.start "mut " ] ]
        (Printf.sprintf "`%s` may change its argument, so the call marks it `mut`." name)
  | Mut, (Temporary | Marked (Own, _)) ->
      report state Wrong_mark value.span
        (Printf.sprintf "`%s` changes its argument in place, so it must be a place marked `mut`."
           name)
  | Own, Marked (Own, inner) ->
      if plain state type_ then
        report state Redundant_mark value.span
          ~fixes:
            [
              fix "Remove the mark."
                [
                  Diagnostic.delete
                    (Source.span (mark_span value inner).start (mark_span value inner).stop);
                ];
            ]
          (Printf.sprintf "`%s` copies implicitly, so it needs no `own`." (show state type_))
  | Own, Temporary -> ()
  | Own, Place ->
      if not (plain state type_) then
        report state Missing_mark value.span
          ~fixes:
            (fix "Give it up with `own`." [ insert value.span.start "own " ]
            ::
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else []))
          (Printf.sprintf
             "`%s` takes ownership of its argument. Give the place up with `own`, or pass a copy."
             name)
  | Own, Marked (Mut, _) ->
      report state Wrong_mark value.span
        (Printf.sprintf "`%s` takes ownership of its argument, so it is marked `own`, not `mut`."
           name)
  | (Mut | Own), Marked (Read, _) -> ()

(* The checking itself *)

let rec expression state env ?expected (value : expression) : T.ty =
  let type_ = expression_kind state env ?expected value in
  record state value type_;
  type_

and check state env (value : expression) (expected : T.ty) =
  let found = expression state env ~expected value in
  coerce state value ~found ~expected

and coerce state (value : expression) ~found ~expected =
  match resolve state found with
  | Never -> ()
  | _ -> if not (unify state expected found) then mismatch state value.span ~expected ~found

and literal_type state ~expected kind =
  match Option.map (resolve state) expected with
  | Some expected when Unify.literal_fits kind expected -> expected
  | _ -> Unify.fresh_literal state.unifier kind

and expression_kind state env ?expected (value : expression) : T.ty =
  match value.kind with
  | Integer number ->
      state.tables.literals.(value.id) <- Some (Integer_value number);
      let type_ = literal_type state ~expected Integer_literal in
      check_literal_fits state value number type_;
      type_
  | Float number ->
      let type_ = literal_type state ~expected Float_literal in
      let float =
        Float.of_string
          (Printf.sprintf "%se%s" (Z.to_string number.significand) (Z.to_string number.exponent))
      in
      state.tables.literals.(value.id) <- Some (Float_value float);
      defer state (fun () ->
          match resolve state type_ with
          | T.Literal _ | T.Variable _ -> false
          | resolved ->
              if T.is_builtin Float32 resolved then
                state.tables.literals.(value.id) <-
                  Some (Float_value (Int32.float_of_bits (Int32.bits_of_float float)));
              if Float.is_integer float = false && not (Float.is_finite float) then
                report state Literal_out_of_range value.span
                  "This float literal is too large for its type.";
              true);
      type_
  | String literal -> string_literal state env ?expected literal
  | True | False -> T.bool
  | Todo -> ( match expected with Some expected -> expected | None -> T.Hole)
  | Unreachable | Break | Continue -> T.Never
  | Self_value -> ( match env.self with Some self -> self | None -> T.Error)
  | Self_type_value ->
      report state Not_a_value value.span
        "`Self` is a type. Build a value of it, or call one of its methods.";
      T.Error
  | Name path -> name state env value path
  | Member (base, member) -> member_value state env value base member
  | Bracket (base, items) -> bracket state env ?expected value base items
  | Call (callee, arguments) -> call state env ?expected value callee arguments
  | Try inner -> try_ state env value inner
  | With (base, updates) -> with_ state env value base updates
  | Prefix (operator, inner) -> prefix state env ?expected value operator inner
  | Mode (mode, inner) ->
      (match marked_call state inner with
      | Some call_id ->
          state.receiver_modes <-
            (call_id, match mode with Mut -> T.Mut | Own -> T.Own) :: state.receiver_modes
      | None -> ());
      expression state env ?expected inner
  | Any inner -> any_ state env ?expected value inner
  | Binary { operator; left; right; _ } -> binary state env ?expected value operator left right
  | Is { value = tested; pattern = written; _ } ->
      let tested_type = expression state env tested in
      pattern state env written tested_type ~mode:T.Read;
      T.bool
  | Range { start; stop; inclusive = _; _ } ->
      let element =
        match (start, stop) with
        | Some start, Some stop ->
            let element = expression state env start in
            let stop_type = expression state env ~expected:element stop in
            literal_operands state ~left:element ~right:stop_type;
            if not (unify state element stop_type) then
              mismatch state stop.span ~expected:element ~found:stop_type;
            element
        | Some only, None | None, Some only -> expression state env only
        | None, None -> fresh state
      in
      T.Named { path = range_path; arguments = [ T.Type element ] }
  | Quantified { binder; body; _ } ->
      (match binder with
      | Binder_in (written, collection) ->
          let element = element_of_collection state env collection in
          pattern state env written element ~mode:T.Read
      | Binder_type (bound, written) ->
          declare state bound (Lower.type_ state.context written) ~mutable_:false ~mode:T.Read);
      check state env body T.bool;
      T.bool
  | Echo inner -> expression state env ?expected inner
  | Return inner ->
      (match (inner, env.output) with
      | Some inner, Some (Returns output) -> check state env inner output
      | None, Some (Returns output) ->
          if not (unify state output T.unit) then
            mismatch state value.span ~expected:output ~found:T.unit
      | Some inner, _ -> ignore (expression state env inner)
      | None, _ -> ());
      T.Never
  | Parenthesized inner -> expression state env ?expected inner
  | List items -> list_literal state env ?expected value items
  | Map entries -> map_literal state env ?expected value entries
  | Lambda { parameters; body } -> lambda state env ?expected value parameters body
  | If { condition = test; then_; else_ } -> if_ state env ?expected test then_ else_
  | Match { scrutinees; arms } -> match_ state env ?expected value scrutinees arms
  | Provide { implementations; body } ->
      List.iter (fun implementation -> ignore (expression state env implementation)) implementations;
      block_value state env ?expected body
  | Block body -> block_value state env ?expected body
  | Expression_error -> T.Error

and check_literal_fits state (value : expression) number type_ =
  defer state (fun () ->
      match resolve state type_ with
      | T.Literal _ | T.Variable _ -> false
      | resolved ->
          (match builtin_range resolved with
          | Some (low, high) when Z.lt number low || Z.gt number high ->
              report state Literal_out_of_range value.span
                (Printf.sprintf "`%s` does not fit in `%s`, which holds %s to %s."
                   (Z.to_string number) (T.show resolved) (Z.to_string low) (Z.to_string high))
          | _ -> ());
          true)

and builtin_range type_ =
  let bits signed width =
    if signed then
      Some (Z.neg (Z.shift_left Z.one (width - 1)), Z.pred (Z.shift_left Z.one (width - 1)))
    else Some (Z.zero, Z.pred (Z.shift_left Z.one width))
  in
  match T.builtin_of type_ with
  | Some Int8 -> bits true 8
  | Some Int16 -> bits true 16
  | Some Int32 -> bits true 32
  | Some (Int64 | ISize) -> bits true 64
  | Some UInt8 -> bits false 8
  | Some UInt16 -> bits false 16
  | Some UInt32 -> bits false 32
  | Some (UInt64 | USize) -> bits false 64
  | _ -> None

(* Names *)

and name state env (value : expression) (path : path) =
  match target state path.last with
  | Some (Local id) -> (
      state.references <- id :: state.references;
      state.tables.meanings.(value.id) <- Some (Local_value id);
      match Hashtbl.find_opt state.locals id with Some local -> local.type_ | None -> T.Error)
  | Some (Generic id) -> (
      match Hashtbl.find_opt state.context.parameters id with
      | Some parameter when path.last.text.[0] >= 'a' && path.last.text.[0] <= 'z' ->
          state.tables.meanings.(value.id) <- Some (Generic_value parameter);
          T.builtin USize
      | _ ->
          report state Not_a_value value.span
            (Printf.sprintf "`%s` is a type, not a value." path.last.text);
          T.Error)
  | Some (Definition definition_path) -> (
      match intrinsic_signature definition_path with
      | Some signature ->
          let instance = instantiate state signature in
          state.tables.meanings.(value.id) <-
            Some (Global { path = definition_path; type_arguments = instance.type_arguments });
          T.Function (T.function_type_of instance.signature)
      | None -> (
          match Interface.Summary.kind_of state.database definition_path with
          | Some (Function | Theorem) -> (
              match function_signature state definition_path with
              | Some signature ->
                  let instance = instantiate state signature in
                  state.tables.meanings.(value.id) <-
                    Some
                      (Global { path = definition_path; type_arguments = instance.type_arguments });
                  T.Function (T.function_type_of instance.signature)
              | None -> T.Error)
          | Some Constant -> (
              state.tables.meanings.(value.id) <-
                Some (Global { path = definition_path; type_arguments = [] });
              match Query.demand state.database Environment.constant_type definition_path with
              | Some type_ -> type_
              | None -> T.Error)
          | Some (Type | Trait | Capability) | None ->
              if Intrinsic.builtin_of_path definition_path = Some Unit then begin
                state.tables.meanings.(value.id) <-
                  Some (Variant_value { type_ = T.unit; variant = "Unit" });
                T.unit
              end
              else begin
                (match Interface.Summary.kind_of state.database definition_path with
                | Some Type -> (
                    match Members.shape state.database definition_path with
                    | Some (Record []) -> ()
                    | _ ->
                        report state Not_a_value value.span
                          (Printf.sprintf "`%s` is a type. Build a value with `%s(...)`."
                             path.last.text path.last.text))
                | _ ->
                    report state Not_a_value value.span
                      (Printf.sprintf "`%s` is not a value." path.last.text));
                T.Error
              end
          | Some _ -> T.Error))
  | Some (Variant (type_path, variant)) ->
      variant_value state value type_path variant ~arguments:(fresh_arguments state type_path)
  | Some (Field field) -> (
      match env.self with
      | Some (T.Named { path = self_path; arguments }) -> (
          match Members.fields state.database self_path arguments with
          | Some fields -> (
              match
                List.find_opt (fun (written : T.field) -> written.field_name = field) fields
              with
              | Some written -> written.field_type
              | None -> T.Error)
          | None -> T.Error)
      | _ -> T.Error)
  | Some Result_value -> (
      state.tables.meanings.(value.id) <- Some Specification_value;
      match env.output with Some output -> output_type output | None -> T.Error)
  | Some (Old | Cost_function _) ->
      state.tables.meanings.(value.id) <- Some Specification_value;
      T.Error
  | Some (Binding | Module _ | Unknown) | None -> T.Error

(* A variant used as a value: one with no fields is a value, and one with
   fields is a function that builds it. *)
and variant_value state (value : expression) type_path variant ~arguments =
  let type_ = T.Named { path = type_path; arguments } in
  state.tables.meanings.(value.id) <- Some (Variant_value { type_; variant });
  match Members.variants state.database type_path arguments with
  | Some variants -> (
      match
        List.find_opt (fun (written : T.variant) -> written.variant_name = variant) variants
      with
      | Some { fields = None; _ } -> type_
      | Some { fields = Some fields; _ } ->
          T.Function
            {
              inputs = List.map (fun (field : T.field) -> (T.Own, field.field_type)) fields;
              output = Returns type_;
              uses = [];
              costs = [ { amortized = false; resource = "time"; bound = "O(...)" } ];
            }
      | None ->
          report state Unknown_variant value.span
            (Printf.sprintf "`%s` has no variant `%s`." (T.show type_) variant);
          T.Error)
  | None -> T.Error

(* [receiver.name] read as a value: a field, or a static member of a type. *)
and member_value state env (value : expression) (base : expression) (member : name) =
  match static_ state base with
  | Some (Static_type type_) -> static_member state value type_ member
  | Some (Static_trait _ | Static_capability _) ->
      report state Not_a_value value.span
        (Printf.sprintf "`%s` is a method; call it with `(...)`." member.text);
      T.Error
  | None -> (
      let base_type = normalize state (expression state env base) in
      match base_type with T.Error | T.Hole -> base_type | _ -> field state value base_type member)

and field state (value : expression) base_type (member : name) =
  let unknown candidates =
    report state Unknown_member member.span
      ~fixes:
        (match Resolve.closest member.text candidates with
        | Some candidate ->
            [ fix (Printf.sprintf "Write `%s`." candidate) [ replace member.span candidate ] ]
        | None -> [])
      (Printf.sprintf "`%s` has no field `%s`." (show state base_type) member.text);
    T.Error
  in
  match base_type with
  | T.Named { path; arguments } -> (
      match Members.fields state.database path arguments with
      | Some fields -> (
          match
            List.find_opt (fun (written : T.field) -> written.field_name = member.text) fields
          with
          | Some written ->
              if not (Members.fields_visible state.database ~package:state.package path) then begin
                report state Private_field member.span
                  (Printf.sprintf
                     "`%s` is opaque, so its fields can be read only in its own package."
                     (show state base_type));
                T.Error
              end
              else begin
                state.tables.meanings.(value.id) <-
                  Some (Field_read { type_ = base_type; field = member.text });
                written.field_type
              end
          | None ->
              if Members.own_methods state.database path member.text <> [] then begin
                report state Not_a_value member.span
                  (Printf.sprintf "`%s` is a method, so it is called: `%s()`." member.text
                     member.text);
                T.Error
              end
              else unknown (List.map (fun (written : T.field) -> written.field_name) fields))
      | None ->
          if Members.own_methods state.database path member.text <> [] then begin
            report state Not_a_value member.span
              (Printf.sprintf "`%s` is a method, so it is called: `%s()`." member.text member.text);
            T.Error
          end
          else unknown [])
  | _ -> unknown []

(* [Type.name] read as a value: a variant, a constant under the type, or a
   method as a function. *)
and static_member state (value : expression) type_ (member : name) =
  match type_ with
  | T.Named { path; arguments } ->
      if member.text.[0] >= 'A' && member.text.[0] <= 'Z' then
        variant_value state value path member.text ~arguments
      else
        begin match Members.own_constant state.database path member.text with
        | Some constant -> (
            state.tables.meanings.(value.id) <-
              Some (Global { path = constant; type_arguments = [] });
            match Query.demand state.database Environment.constant_type constant with
            | Some type_ -> type_
            | None -> T.Error)
        | None -> (
            match Members.own_methods state.database path member.text with
            | (_, method_path) :: _ -> (
                match function_signature state method_path with
                | Some signature ->
                    let instance = instantiate state signature in
                    (match instance.signature.receiver with
                    | Some (_, receiver) -> ignore (unify state receiver type_)
                    | None -> ());
                    state.tables.meanings.(value.id) <-
                      Some (Global { path = method_path; type_arguments = instance.type_arguments });
                    T.Function (T.function_type_of instance.signature)
                | None -> T.Error)
            | [] ->
                report state Unknown_member member.span
                  (Printf.sprintf "`%s` has no member `%s`." (show state type_) member.text);
                T.Error)
        end
  | _ -> T.Error

(* Brackets *)

and bracket state env ?expected (value : expression) (base : expression) items =
  match state.resolved.brackets.(value.id) with
  | Some Type_arguments -> (
      (* A generic function with explicit type arguments, as a value. *)
      match base.kind with
      | Name path -> (
          match target state path.last with
          | Some (Definition definition_path) -> (
              match function_signature state definition_path with
              | Some signature ->
                  let instance = instantiate state signature in
                  explicit_type_arguments state value instance items;
                  state.tables.meanings.(value.id) <-
                    Some
                      (Global { path = definition_path; type_arguments = instance.type_arguments });
                  T.Function (T.function_type_of instance.signature)
              | None ->
                  report state Not_a_value value.span "A type is not a value.";
                  T.Error)
          | _ -> T.Error)
      | _ -> T.Error)
  | Some Method_bracket -> (
      (* Resolution cannot tell a field from a method before the dot; a
         field followed by brackets is indexed. *)
      match base.kind with
      | Member (inner, member)
        when Option.is_none (static_ state inner) && is_field state env inner member ->
          index state env ?expected value base items
      | _ ->
          report state Not_a_value value.span
            "A method with type arguments is called: write `(...)` after it.";
          T.Error)
  | Some Index | None -> index state env ?expected value base items

and is_field state env (inner : expression) (member : name) =
  let base_type =
    match state.tables.types.(inner.id) with
    | Some type_ -> type_
    | None -> expression state env inner
  in
  match normalize state base_type with
  | T.Named { path; arguments } -> (
      match Members.fields state.database path arguments with
      | Some fields -> List.exists (fun (field : T.field) -> field.field_name = member.text) fields
      | None -> false)
  | _ -> false

and explicit_type_arguments state (value : expression) instance items =
  let given =
    List.filter_map
      (function
        | Item item -> Some (type_argument_of_expression state item) | Item_constraint _ -> None)
      items
  in
  let own =
    List.filteri
      (fun index _ -> index >= List.length instance.type_arguments - List.length given)
      instance.type_arguments
  in
  if List.length given > List.length instance.type_arguments then
    report state Arity value.span "There are more type arguments here than the function takes."
  else
    List.iter2
      (fun given own ->
        match (given, own) with
        | T.Type given, T.Type own -> ignore (unify state given own)
        | T.Value given, T.Value own -> ignore (Unify.unify_value state.unifier given own)
        | _ -> ())
      given own

and index state env ?expected:_ (value : expression) (base : expression) items =
  let base_type = normalize state (expression state env base) in
  match items with
  | [ Item ({ kind = Range { start; stop; _ }; _ } as range) ] -> (
      (* Slicing: a view of part of the collection. *)
      Option.iter (fun start -> check state env start (T.builtin USize)) start;
      Option.iter (fun stop -> check state env stop (T.builtin USize)) stop;
      record state range (T.Named { path = range_path; arguments = [ T.Type (T.builtin USize) ] });
      match base_type with
      | T.Named { path; arguments = T.Type element :: _ }
        when Path.equal path list_path || Path.equal path slice_path
             || Intrinsic.builtin_of_path path = Some Array ->
          T.Named { path = slice_path; arguments = [ T.Type element ] }
      | T.Named { path; _ } when Path.equal path string_path || Path.equal path string_slice_path ->
          report state Not_indexable value.span
            "Strings cannot be indexed: say which you mean with `bytes()` or `characters()`.";
          T.Error
      | T.Error | T.Hole -> base_type
      | _ ->
          report state Not_indexable value.span
            (Printf.sprintf "`%s` cannot be sliced." (show state base_type));
          T.Error)
  | [ Item key ] -> (
      if is_named string_path base_type || is_named string_slice_path base_type then begin
        report state Not_indexable value.span
          "Strings cannot be indexed: say which you mean with `bytes()` or `characters()`.";
        T.Error
      end
      else
        match base_type with
        | T.Error | T.Hole ->
            ignore (expression state env key);
            base_type
        | _ -> (
            let index_trait = trait_reference (core "Index") in
            match implements state base_type index_trait with
            | Some evidence ->
                let associated name =
                  Option.value ~default:T.Error
                    (Impls.associated_type state.database ~bounds:(bounds state) base_type
                       index_trait name)
                in
                let key_type = associated "Key" and output = associated "Output" in
                if env.specification then
                  let found = expression state env ~expected:key_type key in
                  if resolve state found = T.Integer && T.is_integer_type key_type then
                    state.obligations <-
                      Integer_fits { expression = key.id; type_ = key_type } :: state.obligations
                  else coerce state key ~found ~expected:key_type
                else check state env key key_type;
                state.tables.calls.(value.id) <-
                  Some
                    {
                      callee =
                        Trait_method
                          {
                            trait = index_trait;
                            name = "at";
                            receiver = Read;
                            self_type = base_type;
                            type_arguments = [];
                            evidence = evidence_of evidence;
                          };
                      arguments =
                        [ { expression = key.id; parameter = 1; mode = Read; conversion = None } ];
                      defaults_left_out = [];
                      uses = [];
                      capability_arguments = [];
                      result = output;
                    };
                output
            | None ->
                ignore (expression state env key);
                report state Not_indexable value.span
                  (Printf.sprintf "`%s` cannot be indexed." (show state base_type));
                T.Error))
  | _ ->
      report state Not_indexable value.span "An index is one value.";
      T.Error

(* Calls *)

and call state env ?expected (value : expression) (callee : expression) arguments : T.ty =
  match callee.kind with
  | Name { modules = []; last } when target state last = Some Old -> (
      match arguments with
      | [ argument ] -> expression state env ?expected argument.value
      | _ -> T.Error)
  | Name { modules = []; last }
    when match target state last with Some (Cost_function _) -> true | _ -> false ->
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      T.Integer
  | Member (base, member) -> (
      match static_ state base with
      | Some (Static_type type_) -> static_call state env ?expected value type_ member arguments
      | Some (Static_trait trait) -> trait_call_in_full state env value trait member arguments
      | Some (Static_capability capability) ->
          capability_call state env value capability member arguments
      | None -> method_call state env ?expected value base member ~type_arguments:[] arguments)
  | Bracket ({ kind = Member (base, member); _ }, items)
    when state.resolved.brackets.(callee.id) = Some Method_bracket ->
      method_call state env ?expected value base member ~type_arguments:items arguments
  | Name path -> (
      match target state path.last with
      | Some (Definition definition_path) -> (
          match Interface.Summary.kind_of state.database definition_path with
          | Some Type -> construct state env ?expected value definition_path None arguments
          | _ -> (
              match function_signature state definition_path with
              | Some signature ->
                  named_call state env ?expected value definition_path signature ~type_arguments:[]
                    arguments
              | None -> function_value_call state env value callee arguments))
      | Some (Variant (type_path, variant)) ->
          construct state env ?expected value type_path (Some variant) arguments
      | _ -> function_value_call state env value callee arguments)
  | Bracket ({ kind = Name path; _ }, items)
    when state.resolved.brackets.(callee.id) = Some Type_arguments -> (
      match target state path.last with
      | Some (Definition definition_path) -> (
          match Interface.Summary.kind_of state.database definition_path with
          | Some Type -> (
              match static_ state callee with
              | Some (Static_type (Named { arguments = type_arguments; _ })) ->
                  construct state env ?expected ~type_arguments value definition_path None arguments
              | _ -> T.Error)
          | _ -> (
              match function_signature state definition_path with
              | Some signature ->
                  named_call state env ?expected value definition_path signature
                    ~type_arguments:items arguments
              | None -> T.Error))
      | _ -> T.Error)
  | _ -> function_value_call state env value callee arguments

(* A call through a function value: by position, with no labels. *)
and function_value_call state env (value : expression) (callee : expression) arguments =
  let callee_type = normalize state (expression state env callee) in
  match callee_type with
  | T.Function function_type ->
      if List.length function_type.inputs <> List.length arguments then
        report state Too_many_arguments value.span
          (Printf.sprintf "This function takes %d arguments, and %d are given."
             (List.length function_type.inputs)
             (List.length arguments));
      let pairs =
        List.filteri (fun index _ -> index < List.length function_type.inputs) arguments
      in
      let checked =
        List.mapi
          (fun index (argument : argument) ->
            (match argument.label with
            | Some label ->
                report state Unknown_label label.span
                  ~fixes:
                    [
                      fix "Remove the label."
                        [
                          Diagnostic.delete (Source.span label.span.start argument.value.span.start);
                        ];
                    ]
                  "A call through a function value passes its arguments by position, without \
                   labels."
            | None -> ());
            let mode, input = List.nth function_type.inputs index in
            let parameter : T.parameter_info =
              { name = "the function value"; mode; type_ = input; has_default = false }
            in
            argument_value state env argument.value parameter;
            { C.expression = argument.value.id; parameter = index; mode; conversion = None })
          pairs
      in
      let result = output_type function_type.output in
      state.tables.calls.(value.id) <-
        Some
          {
            callee = Function_value;
            arguments = checked;
            defaults_left_out = [];
            uses = function_type.uses;
            capability_arguments = [];
            result;
          };
      result
  | T.Error | T.Hole ->
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      callee_type
  | _ ->
      report state Not_callable callee.span
        (Printf.sprintf "`%s` is not a function, so it cannot be called." (show state callee_type));
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      T.Error

(* One argument: checked against its parameter's type, with its mark, and
   with the one implicit conversion, from an owned collection to its view. *)
and argument_value state env (value : expression) (parameter : T.parameter_info) =
  let inner =
    match value.kind with
    | Mode (_, inner) when Option.is_none (marked_call state inner) -> inner
    | _ -> value
  in
  let found = expression state env ~expected:parameter.type_ inner in
  if inner != value then record state value found;
  let expected = normalize state parameter.type_ and found_resolved = normalize state found in
  let to_view =
    (is_named slice_path expected && is_named list_path found_resolved)
    || (is_named string_slice_path expected && is_named string_path found_resolved)
  in
  if to_view then
    begin match (expected, found_resolved) with
    | T.Named { arguments = expected_arguments; _ }, T.Named { arguments = found_arguments; _ } ->
        if not (Unify.unify_arguments state.unifier expected_arguments found_arguments) then
          mismatch state value.span ~expected ~found
    | _ -> ()
    end
  else if env.specification && resolve state found = T.Integer && T.is_integer_type expected then
    state.obligations <-
      Integer_fits { expression = value.id; type_ = expected } :: state.obligations
  else if
    env.specification && T.is_integer_type found_resolved && resolve state expected = T.Integer
  then ()
  else coerce state inner ~found ~expected:parameter.type_;
  check_mode state value parameter found

(* Matches arguments to parameters: a label, a bare name that matches a
   parameter, or the first argument, in that order; then the arguments
   must come in the order of the parameters. *)
and match_arguments state (value : expression) (parameters : T.parameter_info list)
    (arguments : argument list) ~record =
  let named =
    List.mapi (fun index (parameter : T.parameter_info) -> (parameter.name, index)) parameters
  in
  let bare_name (argument : argument) =
    let rec name_of (expression : expression) =
      match expression.kind with
      | Name { modules = []; last } -> Some last.text
      | Mode (_, inner) -> name_of inner
      | _ -> None
    in
    name_of argument.value
  in
  let assigned = Hashtbl.create 8 in
  let matched =
    List.mapi
      (fun position (argument : argument) ->
        let found =
          match argument.label with
          | Some label -> (
              match List.assoc_opt label.text named with
              | Some index -> Some index
              | None ->
                  report state Unknown_label label.span
                    ~fixes:
                      (match Resolve.closest label.text (List.map fst named) with
                      | Some candidate ->
                          [
                            fix
                              (Printf.sprintf "Write `%s`." candidate)
                              [ replace label.span candidate ];
                          ]
                      | None -> [])
                    (Printf.sprintf "No parameter is named `%s`." label.text);
                  None)
          | None -> (
              match Option.bind (bare_name argument) (fun name -> List.assoc_opt name named) with
              | Some index -> Some index
              | None ->
                  if position = 0 && (not record) && parameters <> [] then Some 0
                  else if record && List.length parameters = 1 && List.length arguments = 1 then
                    Some 0
                  else begin
                    let open_parameters =
                      List.filter (fun (_, index) -> not (Hashtbl.mem assigned index)) named
                    in
                    let fixes =
                      match
                        List.find_opt (fun (_, index) -> index > 0 || record) open_parameters
                      with
                      | Some (label, _) ->
                          [
                            fix
                              (Printf.sprintf "Label it `%s`." label)
                              [ insert argument.value.span.start (label ^ ": ") ];
                          ]
                      | None -> []
                    in
                    report state Missing_label argument.value.span ~fixes
                      (if record then
                         "Every field after the first needs a label or a variable of its name, \
                          since fields have no order."
                       else
                         "Every argument after the first needs a label, or a variable with its \
                          parameter's name.");
                    None
                  end)
        in
        (match found with
        | Some index ->
            if Hashtbl.mem assigned index then begin
              report state Repeated_argument argument.value.span
                (Printf.sprintf "`%s` is given more than once." (List.nth parameters index).name)
            end
            else Hashtbl.replace assigned index ()
        | None -> ());
        (argument, found))
      arguments
  in
  (* Arguments come in the order of the parameters, except a record's. *)
  (if not record then
     let indexes = List.filter_map snd matched in
     let sorted = List.sort compare indexes in
     if indexes <> sorted && List.length matched = List.length indexes then
       match (arguments, List.rev arguments) with
       | first :: _, last :: _ ->
           let ordered =
             List.map fst
               (List.sort
                  (fun (_, left) (_, right) -> compare left right)
                  (List.map (fun (argument, index) -> (argument, Option.get index)) matched))
           in
           let written (argument : argument) =
             let start =
               match argument.label with
               | Some label -> label.span.start
               | None -> argument.value.span.start
             in
             source state (Span.make start argument.value.span.stop)
           in
           let start =
             match first.label with
             | Some label -> label.span.start
             | None -> first.value.span.start
           in
           report state Out_of_order value.span
             ~fixes:
               [
                 fix "Put the arguments in the order of the parameters."
                   [
                     replace
                       (Span.make start last.value.span.stop)
                       (String.concat ", " (List.map written ordered));
                   ];
               ]
             "The arguments must come in the order of the parameters."
       | _ -> ());
  let missing =
    List.filter
      (fun (_, index) ->
        (not (Hashtbl.mem assigned index)) && not (List.nth parameters index).has_default)
      named
  in
  (* When an argument went to no parameter, which one was meant is not
     known, so the parameters left open are not reported too. *)
  if List.for_all (fun (_, found) -> Option.is_some found) matched then
    List.iter
      (fun (name, _) ->
        report state Missing_argument value.span
          (Printf.sprintf "`%s` is not given, and has no default." name))
      missing;
  let left_out =
    List.filter_map
      (fun (name, index) ->
        if (not (Hashtbl.mem assigned index)) && (List.nth parameters index).has_default then
          Some name
        else None)
      named
  in
  ( List.filter_map
      (fun (argument, found) -> Option.map (fun index -> (argument, index)) found)
      matched,
    left_out )

(* Checks matched arguments: every argument that is not a lambda first, in
   order, then each lambda, whose parameters then have their types. *)
and check_arguments state env (parameters : T.parameter_info list) matched ~offset =
  let is_lambda ((argument : argument), _) =
    match argument.value.kind with Lambda _ -> true | _ -> false
  in
  let check ((argument : argument), index) =
    let parameter = List.nth parameters index in
    argument_value state env argument.value parameter;
    {
      C.expression = argument.value.id;
      parameter = index + offset;
      mode = parameter.mode;
      conversion = None;
    }
  in
  let first = List.map check (List.filter (fun pair -> not (is_lambda pair)) matched) in
  let lambdas = List.map check (List.filter is_lambda matched) in
  let order = List.map (fun ((argument : argument), _) -> argument.value.id) matched in
  List.filter_map
    (fun id ->
      List.find_opt (fun (checked : C.argument) -> checked.expression = id) (first @ lambdas))
    order

and finish_call state (value : expression) callee (instance : instance) arguments left_out =
  let result = output_type instance.signature.output in
  state.tables.calls.(value.id) <-
    Some
      {
        callee;
        arguments;
        defaults_left_out = left_out;
        uses = instance.signature.uses;
        capability_arguments = [];
        result;
      };
  (* A call to a [yields] method outside a [for] loop makes a cursor. *)
  match instance.signature.output with
  | Yields _ -> cursor_type state callee instance
  | _ -> result

and cursor_type _state callee (instance : instance) =
  match callee with
  | C.Function { path; _ } -> T.Cursor { method_ = path; arguments = instance.type_arguments }
  | C.Trait_method { trait; name; receiver; _ } ->
      T.Cursor
        {
          method_ = Method { owner = trait.trait; name; receiver };
          arguments = instance.type_arguments;
        }
  | _ -> T.Error

and named_call state env ?expected (value : expression) path (signature : T.signature)
    ~type_arguments arguments =
  let instance = instantiate state signature in
  explicit_type_arguments state value instance type_arguments;
  (match (expected, instance.signature.output) with
  | Some expected, Returns output -> ignore (unify state output expected)
  | _ -> ());
  let matched, left_out =
    match_arguments state value instance.signature.parameters arguments ~record:false
  in
  let checked = check_arguments state env instance.signature.parameters matched ~offset:0 in
  let callee =
    match Intrinsic.operation_of_path path with
    | Some operation -> C.Intrinsic { operation; type_arguments = instance.type_arguments }
    | None -> C.Function { path; type_arguments = instance.type_arguments }
  in
  check_specification_call state env value signature;
  finish_call state value callee instance checked left_out

and check_specification_call state env (value : expression) (signature : T.signature) =
  if signature.specification_only && not env.specification then
    report state Specification_only value.span
      "This function mentions `Integer`, so it can be called only in specifications."

(* Building a record or a variant: fields by name, in any order. *)
and construct state env ?expected ?type_arguments (value : expression) type_path variant arguments =
  let type_arguments =
    match type_arguments with Some given -> given | None -> fresh_arguments state type_path
  in
  let type_ = T.Named { path = type_path; arguments = type_arguments } in
  (match expected with Some expected -> ignore (unify state type_ expected) | None -> ());
  let fields =
    match variant with
    | None -> (
        match Members.fields state.database type_path type_arguments with
        | Some fields -> Some fields
        | None ->
            (match Members.shape state.database type_path with
            | Some Error_shape -> ()
            | _ ->
                report state Not_a_record value.span
                  (Printf.sprintf "`%s` is not a record, so it cannot be built this way."
                     (show state type_)));
            None)
    | Some variant -> (
        match Members.variants state.database type_path type_arguments with
        | Some variants -> (
            match
              List.find_opt (fun (written : T.variant) -> written.variant_name = variant) variants
            with
            | Some { fields = Some fields; _ } -> Some fields
            | Some { fields = None; _ } ->
                report state Too_many_arguments value.span
                  (Printf.sprintf "`%s` has no fields." variant);
                None
            | None ->
                report state Unknown_variant value.span
                  (Printf.sprintf "`%s` has no variant `%s`." (show state type_) variant);
                None)
        | None -> None)
  in
  if not (Members.fields_visible state.database ~package:state.package type_path) then
    report state Private_field value.span
      (Printf.sprintf "`%s` is opaque, so only its own package can build it." (show state type_));
  match fields with
  | None ->
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      type_
  | Some fields ->
      let parameters =
        List.map
          (fun (field : T.field) ->
            {
              T.name = field.field_name;
              mode = Own;
              type_ = field.field_type;
              has_default = field.field_has_default;
            })
          fields
      in
      let matched, left_out = match_arguments state value parameters arguments ~record:true in
      let checked = check_arguments state env parameters matched ~offset:0 in
      state.tables.calls.(value.id) <-
        Some
          {
            callee = Constructor { type_ = type_path; variant; type_arguments };
            arguments = checked;
            defaults_left_out = left_out;
            uses = [];
            capability_arguments = [];
            result = type_;
          };
      type_

(* [Type.name(...)]: a variant, a method without [self], or a method
   written in full with its receiver first. *)
and static_call state env ?expected (value : expression) type_ (member : name) arguments =
  match type_ with
  | T.Named { path; arguments = type_arguments }
    when member.text.[0] >= 'A' && member.text.[0] <= 'Z' ->
      construct state env ?expected ~type_arguments value path (Some member.text) arguments
  | T.Named { path; _ } -> (
      match Members.own_methods state.database path member.text with
      | [] -> (
          (* A trait method written through the type, as [Int64.from(count)]. *)
          match trait_static_method state path member.text with
          | Some (trait, method_) ->
              trait_method_through_type state env ?expected value type_ trait method_ arguments
          | None ->
              report state Unknown_member member.span
                (Printf.sprintf "`%s` has no method `%s`." (show state type_) member.text);
              List.iter
                (fun (argument : argument) -> ignore (expression state env argument.value))
                arguments;
              T.Error)
      | versions -> (
          let static_version = List.assoc_opt Path.Static versions in
          match static_version with
          | Some method_path -> (
              match function_signature state method_path with
              | Some signature ->
                  let instance = instantiate state signature in
                  (* The type's arguments, as written or inferred, are the
                     head's generic arguments. *)
                  let head =
                    List.filteri
                      (fun index _ ->
                        index
                        < List.length
                            (match type_ with T.Named { arguments; _ } -> arguments | _ -> []))
                      instance.type_arguments
                  in
                  ignore
                    (Unify.unify_arguments state.unifier head
                       (match type_ with T.Named { arguments; _ } -> arguments | _ -> []));
                  (match (expected, instance.signature.output) with
                  | Some expected, Returns output -> ignore (unify state output expected)
                  | _ -> ());
                  let matched, left_out =
                    match_arguments state value instance.signature.parameters arguments
                      ~record:false
                  in
                  let checked =
                    check_arguments state env instance.signature.parameters matched ~offset:0
                  in
                  finish_call state value
                    (C.Function { path = method_path; type_arguments = instance.type_arguments })
                    instance checked left_out
              | None -> T.Error)
          | None -> (
              (* A method with [self], written in full: the first argument is the receiver. *)
              match arguments with
              | receiver :: rest ->
                  let receiver_type = expression state env receiver.value in
                  ignore (unify state receiver_type type_);
                  let method_path = snd (List.hd versions) in
                  method_with_receiver state env ?expected value ~receiver:receiver.value
                    ~receiver_type method_path rest
              | [] ->
                  report state Missing_argument value.span
                    "A method written in full takes its receiver as its first argument.";
                  T.Error)))
  | T.Parameter parameter -> (
      match
        List.find_map
          (fun (bound : T.trait_reference) ->
            List.find_map
              (fun (method_ : T.trait_method) ->
                if method_.method_name = member.text then Some (bound, method_) else None)
              (Members.trait_methods state.database bound.trait member.text))
          (Properties.known_bounds state.database ~bounds:(bounds state) (T.Parameter parameter))
      with
      | Some (trait, method_) ->
          trait_method_through_type state env ?expected value type_ trait method_ arguments
      | None ->
          report state Unknown_member member.span
            (Printf.sprintf "`%s` has no method `%s`." parameter.name member.text);
          T.Error)
  | _ -> T.Error

and trait_static_method state path name =
  List.find_map
    (fun package ->
      List.find_map
        (fun trait ->
          match
            List.find_opt
              (fun (method_ : T.trait_method) -> method_.method_name = name)
              (Members.trait_methods state.database trait name)
          with
          | Some method_ ->
              let reference = trait_reference trait in
              if
                (match Query.demand state.database Environment.trait_interface trait with
                  | Some interface -> interface.trait_generics <> []
                  | None -> false)
                || Option.is_some
                     (implements state
                        (T.Named { path; arguments = fresh_arguments state path })
                        reference)
              then Some (reference, method_)
              else None
          | None -> None)
        (Query.demand state.database Members.traits_declaring (package, name)))
    (Members.visible_packages state.database state.package)

(* A trait method called through a type, with [Self] that type: a
   constructor such as [Int64.from(count)] or [Self.empty()]. The trait's
   own arguments are worked out from the call's arguments, never from the
   expected type. *)
and trait_method_through_type state env ?expected:_ (value : expression) self_type
    (trait : T.trait_reference) (method_ : T.trait_method) arguments =
  let trait_generics =
    match Query.demand state.database Environment.trait_interface trait.trait with
    | Some interface -> interface.trait_generics
    | None -> []
  in
  let trait_arguments = List.map (fun (_ : T.generic) -> T.Type (fresh state)) trait_generics in
  let extra =
    (({ owner = trait.trait; name = "Self" } : T.parameter), T.Type self_type)
    :: List.combine
         (List.map (fun (generic : T.generic) -> generic.generic) trait_generics)
         trait_arguments
  in
  let instance = instantiate state ~extra method_.method_signature in
  let parameters = instance.signature.parameters in
  let receiver_offset, parameters, arguments =
    match instance.signature.receiver with
    | Some (receiver, receiver_type) -> (
        match arguments with
        | first :: rest ->
            let parameter : T.parameter_info =
              {
                name = "self";
                mode = (match receiver with Mut -> Mut | Own -> Own | _ -> Read);
                type_ = receiver_type;
                has_default = false;
              }
            in
            argument_value state env first.value parameter;
            (1, parameters, rest)
        | [] -> (1, parameters, []))
    | None -> (0, parameters, arguments)
  in
  let matched, left_out = match_arguments state value parameters arguments ~record:false in
  let checked = check_arguments state env parameters matched ~offset:receiver_offset in
  let reference = { trait with trait_arguments } in
  let result = output_type instance.signature.output in
  let own_arguments =
    List.filteri
      (fun index _ -> index < List.length method_.method_signature.generics)
      instance.type_arguments
  in
  state.tables.calls.(value.id) <-
    Some
      {
        callee =
          Trait_method
            {
              trait = reference;
              name = method_.method_name;
              receiver = method_.method_receiver;
              self_type;
              type_arguments = own_arguments;
              evidence = Built_in;
            };
        arguments = checked;
        defaults_left_out = left_out;
        uses = instance.signature.uses;
        capability_arguments = [];
        result;
      };
  resolve_evidence state value self_type reference;
  normalize_result state result

(* The [impl] a trait method call means is found once its types are known,
   which may be at the end of the statement. *)
and resolve_evidence state (value : expression) self_type (reference : T.trait_reference) =
  defer state (fun () ->
      let self_type = zonk state self_type
      and reference = Unify.zonk_trait state.unifier reference in
      if
        T.contains_unsolved self_type
        || List.exists
             (function T.Type type_ -> T.contains_unsolved type_ | _ -> false)
             reference.trait_arguments
      then false
      else begin
        (match implements state self_type reference with
        | Some evidence -> (
            match state.tables.calls.(value.id) with
            | Some ({ callee = Trait_method method_; _ } as call) ->
                state.tables.calls.(value.id) <-
                  Some
                    {
                      call with
                      callee =
                        Trait_method
                          { method_ with trait = reference; evidence = evidence_of evidence };
                    }
            | _ -> ())
        | None ->
            if self_type <> T.Error then
              report state No_impl value.span
                (Printf.sprintf "`%s` does not implement `%s`." (T.show self_type)
                   (T.show_trait reference)));
        true
      end)

and normalize_result state result =
  match normalize state result with
  | T.Projection _ as projection -> projection
  | normalized -> normalized

(* [Ordered.compare(first, second)]: a trait method written in full, with
   its receiver first. *)
and trait_call_in_full state env (value : expression) trait (member : name) arguments =
  match Members.trait_methods state.database trait member.text with
  | method_ :: _ -> (
      match arguments with
      | receiver :: _ ->
          let receiver_type = normalize state (expression state env receiver.value) in
          trait_method_through_type state env value receiver_type (trait_reference trait) method_
            arguments
      | [] ->
          let self = fresh state in
          trait_method_through_type state env value self (trait_reference trait) method_ arguments)
  | [] ->
      report state Unknown_member member.span
        (Printf.sprintf "`%s` has no method `%s`." (Path.show trait) member.text);
      T.Error

(* [Clock.now()]: a call to a capability's method. *)
and capability_call state env (value : expression) capability (member : name) arguments =
  match Members.trait_methods state.database capability member.text with
  | method_ :: _ ->
      let instance = instantiate state method_.method_signature in
      let matched, left_out =
        match_arguments state value instance.signature.parameters arguments ~record:false
      in
      let checked = check_arguments state env instance.signature.parameters matched ~offset:0 in
      let result = output_type instance.signature.output in
      state.tables.calls.(value.id) <-
        Some
          {
            callee = Capability_method { capability; name = member.text };
            arguments = checked;
            defaults_left_out = left_out;
            uses = [ T.Capability capability ];
            capability_arguments = [];
            result;
          };
      result
  | [] ->
      report state Unknown_member member.span
        (Printf.sprintf "`%s` has no method `%s`." (Path.show capability) member.text);
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      T.Error

(* [receiver.name(...)]: the type's own method, or a trait's. *)
and method_call state env ?expected (value : expression) (base : expression) (member : name)
    ~type_arguments arguments =
  let receiver_type = normalize state (expression state env base) in
  let wanted : Path.receiver =
    match List.assoc_opt value.id state.receiver_modes with
    | Some Mut -> Mut
    | Some Own -> Own
    | _ -> Read
  in
  let marked = List.mem_assoc value.id state.receiver_modes in
  let place = is_place state base in
  let choose versions =
    (* No mark picks the read-only version; on a temporary, the [own]
       version if there is one; a [Plain] place may give its [own] version a
       copy. *)
    match List.assoc_opt wanted versions with
    | Some found -> Some (wanted, found)
    | None when (not marked) && ((not place) || plain state receiver_type) -> (
        match List.assoc_opt Path.Own versions with
        | Some found -> Some (Path.Own, found)
        | None -> None)
    | None -> None
  in
  let choose_temporary versions =
    if (not marked) && not place then
      match List.assoc_opt Path.Own versions with
      | Some found -> Some (Path.Own, found)
      | None -> choose versions
    else choose versions
  in
  let wrong_receiver versions =
    let shown = function
      | Path.Read -> "`self`"
      | Mut -> "`mut self`"
      | Own -> "`own self`"
      | Static -> "no `self`"
    in
    report state Wrong_receiver member.span
      (Printf.sprintf "`%s` has no version that takes %s here; it has %s." member.text
         (shown wanted)
         (String.concat ", " (List.map (fun (receiver, _) -> shown receiver) versions)))
  in
  (* A place that calls a method with only a [mut] or [own] version is
     missing its mark, which the fix adds. *)
  let missing_receiver_mark : 'a. (Path.receiver * 'a) list -> unit =
   fun versions ->
    let has receiver = List.exists (fun (found, _) -> found = receiver) versions in
    if (not marked) && place && (has Path.Mut || has Path.Own) then begin
      let mark = if has Path.Mut then "mut" else "own" in
      report state Missing_mark base.span
        ~fixes:[ fix (Printf.sprintf "Mark it `%s`." mark) [ insert base.span.start (mark ^ " ") ] ]
        (Printf.sprintf "`%s` takes `%s self`, so the call marks its receiver `%s`." member.text
           mark mark)
    end
    else wrong_receiver (List.map (fun (receiver, _) -> (receiver, ())) versions)
  in
  match receiver_type with
  | T.Error | T.Hole ->
      List.iter
        (fun (argument : argument) -> ignore (expression state env argument.value))
        arguments;
      receiver_type
  | _ -> (
      let own =
        match receiver_type with
        | T.Named { path; _ } ->
            List.filter
              (fun (receiver, _) -> receiver <> Path.Static)
              (Members.own_methods state.database path member.text)
        | _ -> []
      in
      match own with
      | _ :: _ -> (
          match choose_temporary own with
          | Some (_, method_path) ->
              method_with_receiver state env ?expected ~type_arguments value ~receiver:base
                ~receiver_type method_path arguments
          | None ->
              missing_receiver_mark own;
              T.Error)
      | [] -> (
          match trait_candidates state receiver_type member.text with
          | [ (trait, versions) ] -> (
              match
                choose_temporary
                  (List.map
                     (fun (method_ : T.trait_method) -> (method_.method_receiver, method_))
                     versions)
              with
              | Some (_, method_) ->
                  trait_method_call state env value ~receiver:base ~receiver_type trait method_
                    ~type_arguments arguments
              | None ->
                  missing_receiver_mark
                    (List.map
                       (fun (method_ : T.trait_method) -> (method_.method_receiver, ()))
                       versions);
                  T.Error)
          | [] ->
              let candidates =
                match receiver_type with
                | T.Named { path; arguments } -> (
                    match Members.fields state.database path arguments with
                    | Some fields -> List.map (fun (field : T.field) -> field.field_name) fields
                    | None -> [])
                | _ -> []
              in
              report state Unknown_member member.span
                ~fixes:
                  (match Resolve.closest member.text candidates with
                  | Some candidate ->
                      [
                        fix
                          (Printf.sprintf "Write `%s`." candidate)
                          [ replace member.span candidate ];
                      ]
                  | None -> [])
                (Printf.sprintf "`%s` has no method `%s`." (show state receiver_type) member.text);
              List.iter
                (fun (argument : argument) -> ignore (expression state env argument.value))
                arguments;
              T.Error
          | several ->
              let receiver_text = source state base.span in
              report state Ambiguous_method member.span
                ~fixes:
                  (List.map
                     (fun ((trait : T.trait_reference), _) ->
                       let name =
                         match trait.trait with Top { name; _ } -> name | path -> Path.show path
                       in
                       fix
                         (Printf.sprintf "Call `%s`'s `%s`." name member.text)
                         [
                           replace
                             (Span.make base.span.start member.span.stop)
                             (Printf.sprintf "%s.%s(%s" name member.text receiver_text);
                         ])
                     several)
                (Printf.sprintf
                   "More than one trait gives `%s` a method `%s`. Write the call in full to say \
                    which."
                   (show state receiver_type) member.text);
              T.Error))

(* The traits that give a type a method with a name. *)
and trait_candidates state receiver_type name =
  let with_method (trait : T.trait_reference) =
    match
      List.filter
        (fun (method_ : T.trait_method) -> method_.method_receiver <> Path.Static)
        (Members.trait_methods state.database trait.trait name)
    with
    | [] -> None
    | methods -> Some (trait, methods)
  in
  let unique candidates =
    List.fold_left
      (fun acc ((trait : T.trait_reference), methods) ->
        if
          List.exists
            (fun ((other : T.trait_reference), _) -> Path.equal other.trait trait.trait)
            acc
        then acc
        else acc @ [ (trait, methods) ])
      [] candidates
  in
  match receiver_type with
  | T.Parameter parameter ->
      unique
        (List.filter_map with_method
           (Properties.known_bounds state.database ~bounds:(bounds state) (T.Parameter parameter)))
  | T.Any trait ->
      unique
        (List.filter_map with_method
           (Properties.bound_closure state.database ~self:receiver_type trait))
  | _ ->
      unique
        (List.concat_map
           (fun package ->
             List.filter_map
               (fun trait ->
                 let reference = trait_reference trait in
                 let has_generics =
                   match Query.demand state.database Environment.trait_interface trait with
                   | Some interface -> interface.trait_generics <> []
                   | None -> false
                 in
                 if has_generics || Option.is_some (implements state receiver_type reference) then
                   with_method reference
                 else None)
               (Query.demand state.database Members.traits_declaring (package, name)))
           (Members.visible_packages state.database state.package))

and method_with_receiver state env ?expected ?(type_arguments = []) (value : expression)
    ~(receiver : expression) ~receiver_type method_path arguments =
  match function_signature state method_path with
  | None -> T.Error
  | Some signature ->
      let instance = instantiate state signature in
      explicit_type_arguments state value instance type_arguments;
      (match instance.signature.receiver with
      | Some (_, self_type) ->
          if not (unify state self_type receiver_type) then
            mismatch state receiver.span ~expected:self_type ~found:receiver_type
      | None -> ());
      (match (expected, instance.signature.output) with
      | Some expected, Returns output -> ignore (unify state output expected)
      | _ -> ());
      let matched, left_out =
        match_arguments state value instance.signature.parameters arguments ~record:false
      in
      let checked = check_arguments state env instance.signature.parameters matched ~offset:1 in
      let receiver_argument =
        {
          C.expression = receiver.id;
          parameter = 0;
          mode =
            (match signature.receiver with
            | Some (Mut, _) -> Mut
            | Some (Own, _) -> Own
            | _ -> Read);
          conversion = None;
        }
      in
      check_specification_call state env value signature;
      finish_call state value
        (C.Function { path = method_path; type_arguments = instance.type_arguments })
        instance (receiver_argument :: checked) left_out

and trait_method_call state env (value : expression) ~(receiver : expression) ~receiver_type
    (trait : T.trait_reference) (method_ : T.trait_method) ~type_arguments arguments =
  let trait_generics =
    match Query.demand state.database Environment.trait_interface trait.trait with
    | Some interface -> interface.trait_generics
    | None -> []
  in
  let trait_arguments =
    if List.length trait.trait_arguments = List.length trait_generics then trait.trait_arguments
    else List.map (fun (_ : T.generic) -> T.Type (fresh state)) trait_generics
  in
  let extra =
    (({ owner = trait.trait; name = "Self" } : T.parameter), T.Type receiver_type)
    :: List.combine
         (List.map (fun (generic : T.generic) -> generic.generic) trait_generics)
         trait_arguments
  in
  let instance = instantiate state ~extra method_.method_signature in
  explicit_type_arguments state value instance type_arguments;
  let matched, left_out =
    match_arguments state value instance.signature.parameters arguments ~record:false
  in
  let checked = check_arguments state env instance.signature.parameters matched ~offset:1 in
  let reference = { trait with trait_arguments } in
  let result = output_type instance.signature.output in
  let receiver_argument =
    {
      C.expression = receiver.id;
      parameter = 0;
      mode = (match method_.method_receiver with Mut -> Mut | Own -> Own | _ -> Read);
      conversion = None;
    }
  in
  let evidence = match receiver_type with T.Any _ -> C.Dynamic | _ -> C.Built_in in
  state.tables.calls.(value.id) <-
    Some
      {
        callee =
          Trait_method
            {
              trait = reference;
              name = method_.method_name;
              receiver = method_.method_receiver;
              self_type = receiver_type;
              type_arguments = instance.type_arguments;
              evidence;
            };
        arguments = receiver_argument :: checked;
        defaults_left_out = left_out;
        uses = instance.signature.uses;
        capability_arguments = [];
        result;
      };
  (match receiver_type with
  | T.Any _ -> ()
  | _ -> resolve_evidence state value receiver_type reference);
  match instance.signature.output with
  | Yields _ ->
      T.Cursor
        {
          method_ =
            Method
              {
                owner = trait.trait;
                name = method_.method_name;
                receiver = method_.method_receiver;
              };
          arguments = instance.type_arguments;
        }
  | _ -> normalize_result state result

(* [?]: a [Result] whose error is the function's, or an [Option] in a
   function that returns one. *)
and try_ state env (value : expression) (inner : expression) =
  let inner_type = normalize state (expression state env inner) in
  let output =
    match env.output with Some (Returns output) -> Some (normalize state output) | _ -> None
  in
  match (inner_type, output) with
  | ( T.Named { path; arguments = [ T.Type ok; T.Type error ] },
      Some (T.Named { path = output_path; arguments = [ _; T.Type output_error ] }) )
    when Path.equal path result_path && Path.equal output_path result_path ->
      if not (unify state error output_error) then
        report state Wrong_try value.span
          (Printf.sprintf
             "`?` returns the error unchanged, so it needs the function's error type `%s`, not \
              `%s`. Convert it first with `map_error`."
             (show state output_error) (show state error));
      ok
  | T.Named { path; arguments = [ T.Type some ] }, Some (T.Named { path = output_path; _ })
    when Path.equal path option_path && Path.equal output_path option_path ->
      some
  | (T.Error | T.Hole), _ -> inner_type
  | _ ->
      report state Wrong_try value.span
        "`?` works on a `Result` in a function that returns a `Result`, and on an `Option` in a \
         function that returns an `Option`. Convert between them with `ok_or` or `ok`.";
      T.Error

(* [base with (field: value)]: a record with some fields changed. *)
and with_ state env (value : expression) (base : expression) updates =
  ignore value;
  let base_type = normalize state (expression state env base) in
  List.iter
    (fun (update : update) ->
      match update.kind with
      | Update { field = first; path = rest; value = new_value } -> (
          let rec field_type type_ (names : name list) =
            match (names, normalize state type_) with
            | [], type_ -> Some type_
            | (name : name) :: rest, (T.Named { path; arguments } as record_type) -> (
                match Members.fields state.database path arguments with
                | Some fields -> (
                    match
                      List.find_opt
                        (fun (written : T.field) -> written.field_name = name.text)
                        fields
                    with
                    | Some written -> field_type written.field_type rest
                    | None ->
                        report state Unknown_member name.span
                          (Printf.sprintf "`%s` has no field `%s`." (show state record_type)
                             name.text);
                        None)
                | None ->
                    report state Not_a_record name.span
                      (Printf.sprintf "`with` works on records, and `%s` is not one."
                         (show state record_type));
                    None)
            | _, _ -> None
          in
          match field_type base_type (first :: rest) with
          | Some type_ -> (
              match new_value with
              | Some new_value -> check state env new_value type_
              | None -> (
                  match target state first with
                  | Some (Local id) -> (
                      match Hashtbl.find_opt state.locals id with
                      | Some local ->
                          if not (unify state type_ local.type_) then
                            mismatch state first.span ~expected:type_ ~found:local.type_
                      | None -> ())
                  | _ -> ()))
          | None -> Option.iter (fun new_value -> ignore (expression state env new_value)) new_value
          )
      | Update_error -> ())
    updates;
  base_type

and prefix state env ?expected (value : expression) operator (inner : expression) =
  match operator with
  | Not ->
      check state env inner T.bool;
      T.bool
  | Complement ->
      let type_ = expression state env ?expected inner in
      if
        not
          (T.is_integer_type (normalize state type_)
          || match resolve state type_ with T.Literal (Integer_literal, _) -> true | _ -> false)
      then
        report state No_impl value.span
          (Printf.sprintf "`~` works on built-in integers, not `%s`." (show state type_));
      type_
  | Negate -> (
      match inner.kind with
      | Integer number ->
          (* A literal negated directly is checked after the negation, so
             [-128] fits an [Int8]. *)
          state.tables.literals.(inner.id) <- Some (Integer_value number);
          let type_ = literal_type state ~expected Integer_literal in
          record state inner type_;
          check_literal_fits state value (Z.neg number) type_;
          defer state (fun () ->
              match resolve state type_ with
              | T.Literal _ | T.Variable _ -> false
              | resolved ->
                  if T.is_integer_type resolved && not (T.is_signed resolved) then
                    report state Negated_unsigned value.span
                      (Printf.sprintf "`%s` is unsigned, so it cannot be negated." (T.show resolved));
                  true);
          type_
      | _ ->
          let type_ = expression state env ?expected inner in
          let resolved = normalize state type_ in
          if T.is_integer_type resolved && not (T.is_signed resolved) then begin
            report state Negated_unsigned value.span
              (Printf.sprintf "`%s` is unsigned, so it cannot be negated." (T.show resolved));
            type_
          end
          else if env.specification && (T.is_integer_type resolved || resolved = T.Integer) then
            T.Integer
          else
            operator_call state value ~trait:(core "Negate") ~method_:"negate" ~left:type_
              ~right:None)

(* An operator that is a trait method: the [impl] is chosen by the types of
   both operands, once known, and the result is its [Output]. *)
and operator_call state (value : expression) ~trait ~method_ ~left ~right =
  let arguments = match right with Some right -> [ T.Type right ] | None -> [] in
  let reference = trait_reference ~arguments trait in
  let result = fresh state in
  state.tables.calls.(value.id) <-
    Some
      {
        callee =
          Trait_method
            {
              trait = reference;
              name = method_;
              receiver = Read;
              self_type = left;
              type_arguments = [];
              evidence = Built_in;
            };
        arguments = [];
        defaults_left_out = [];
        uses = [];
        capability_arguments = [];
        result;
      };
  defer state (fun () ->
      let left = normalize state left in
      let reference = Unify.zonk_trait state.unifier reference in
      if
        T.contains_unsolved left
        || List.exists
             (function T.Type type_ -> T.contains_unsolved type_ | _ -> false)
             reference.trait_arguments
      then false
      else begin
        (match implements state left reference with
        | Some evidence ->
            let output =
              Option.value ~default:T.Error
                (Impls.associated_type state.database ~bounds:(bounds state) left reference "Output")
            in
            ignore (unify state result output);
            state.tables.calls.(value.id) <-
              Some
                {
                  callee =
                    Trait_method
                      {
                        trait = reference;
                        name = method_;
                        receiver = Read;
                        self_type = left;
                        type_arguments = [];
                        evidence = evidence_of evidence;
                      };
                  arguments = [];
                  defaults_left_out = [];
                  uses = [];
                  capability_arguments = [];
                  result = output;
                }
        | None ->
            ignore (unify state result T.Error);
            if left <> T.Error then
              report state No_impl value.span
                (Printf.sprintf "`%s` does not implement `%s`, so the operator does not apply."
                   (T.show left) (T.show_trait reference)));
        true
      end);
  result

(* A literal operand takes the other operand's type when it can be that
   type, as Go's untyped constants do. *)
and literal_operands state ~left ~right =
  match (resolve state left, resolve state right) with
  | T.Literal (kind, _), other when Unify.literal_fits kind other -> ignore (unify state left right)
  | other, T.Literal (kind, _) when Unify.literal_fits kind other -> ignore (unify state left right)
  | T.Literal (left_kind, _), T.Literal (right_kind, _) when left_kind = right_kind ->
      ignore (unify state left right)
  | _ -> ()

and is_string state type_ =
  let type_ = normalize state type_ in
  is_named string_path type_ || is_named string_slice_path type_

and binary state env ?expected (value : expression) operator (left : expression)
    (right : expression) =
  match operator with
  | And | Or | Implies ->
      check state env left T.bool;
      check state env right T.bool;
      T.bool
  | Bit_and | Bit_or | Bit_xor ->
      let left_type = expression state env ?expected left in
      let right_type = expression state env ~expected:left_type right in
      literal_operands state ~left:left_type ~right:right_type;
      if not (unify state left_type right_type) then
        mismatch state right.span ~expected:left_type ~found:right_type;
      defer state (fun () ->
          match normalize state left_type with
          | T.Literal _ | T.Variable _ -> false
          | resolved ->
              if not (T.is_integer_type resolved || resolved = T.Error) then
                report state No_impl value.span
                  (Printf.sprintf "Bitwise operators work on built-in integers, not `%s`."
                     (T.show resolved));
              true);
      left_type
  | Shift_left | Shift_right ->
      let left_type = expression state env ?expected left in
      let right_type = expression state env right in
      (match resolve state right_type with
      | T.Literal (Integer_literal, _) -> ignore (unify state right_type (T.builtin USize))
      | _ -> ());
      defer state (fun () ->
          match (normalize state left_type, normalize state right_type) with
          | (T.Literal _ | T.Variable _), _ | _, (T.Literal _ | T.Variable _) -> false
          | left_resolved, right_resolved ->
              if not (T.is_integer_type left_resolved || left_resolved = T.Error) then
                report state No_impl left.span
                  (Printf.sprintf "Shifts work on built-in integers, not `%s`."
                     (T.show left_resolved));
              if
                not
                  ((T.is_integer_type right_resolved && not (T.is_signed right_resolved))
                  || right_resolved = T.Error)
              then
                report state Mismatch right.span
                  (Printf.sprintf "A shift amount is an unsigned integer, not `%s`."
                     (T.show right_resolved));
              true);
      left_type
  | Equal | Not_equal | Less | Less_equal | Greater | Greater_equal ->
      let left_type = expression state env left in
      let right_type = expression state env ~expected:left_type right in
      literal_operands state ~left:left_type ~right:right_type;
      let integers type_ =
        let type_ = normalize state type_ in
        T.is_integer_type type_ || type_ = T.Integer
        || match resolve state type_ with T.Literal (Integer_literal, _) -> true | _ -> false
      in
      if env.specification && integers left_type && integers right_type then T.bool
      else begin
        if not (unify state left_type right_type) then
          mismatched_operands state value left right ~left_type ~right_type;
        let trait, method_ =
          match operator with
          | Equal | Not_equal -> (core "Equal", "equal")
          | _ -> (core "Ordered", "compare")
        in
        state.tables.calls.(value.id) <-
          Some
            {
              callee =
                Trait_method
                  {
                    trait = trait_reference trait;
                    name = method_;
                    receiver = Read;
                    self_type = left_type;
                    type_arguments = [];
                    evidence = Built_in;
                  };
              arguments = [];
              defaults_left_out = [];
              uses = [];
              capability_arguments = [];
              result = T.bool;
            };
        resolve_evidence state value left_type (trait_reference trait);
        T.bool
      end
  | Add | Subtract | Multiply | Divide | Remainder ->
      let left_type = expression state env left in
      let right_type = expression state env ~expected:left_type right in
      literal_operands state ~left:left_type ~right:right_type;
      if operator = Add && (is_string state left_type || is_string state right_type) then begin
        let piece (side : expression) =
          match side.kind with
          | String { tag = None; first; rest = []; _ } -> first.value
          | _ -> "${" ^ source state side.span ^ "}"
        in
        report state String_addition value.span
          ~fixes:
            [
              fix "Join them with interpolation."
                [ replace value.span (Printf.sprintf "\"%s%s\"" (piece left) (piece right)) ];
            ]
          "Strings have no `+`. Join them with interpolation, or with methods such as `push`.";
        string_type
      end
      else begin
        let integers type_ =
          let type_ = normalize state type_ in
          T.is_integer_type type_ || type_ = T.Integer
          || match resolve state type_ with T.Literal (Integer_literal, _) -> true | _ -> false
        in
        if env.specification && integers left_type && integers right_type then begin
          ignore
            (match resolve state left_type with
            | T.Literal _ -> unify state left_type T.Integer
            | _ -> true);
          ignore
            (match resolve state right_type with
            | T.Literal _ -> unify state right_type T.Integer
            | _ -> true);
          T.Integer
        end
        else
          let same_builtin =
            match (resolve state left_type, resolve state right_type) with
            | T.Literal (left_kind, _), T.Literal (right_kind, _) -> left_kind = right_kind
            | left_resolved, right_resolved ->
                (T.is_integer_type left_resolved || T.is_float_type left_resolved)
                && T.equal left_resolved right_resolved
          in
          let trait, method_ =
            match operator with
            | Add -> (core "Add", "add")
            | Subtract -> (core "Subtract", "subtract")
            | Multiply -> (core "Multiply", "multiply")
            | Divide -> (core "Divide", "divide")
            | _ -> (core "Remainder", "remainder")
          in
          if
            (T.is_integer_type (normalize state left_type)
            && T.is_integer_type (normalize state right_type))
            && not (T.equal (normalize state left_type) (normalize state right_type))
          then begin
            mismatched_operands state value left right ~left_type ~right_type;
            T.Error
          end
          else begin
            let result =
              operator_call state value ~trait ~method_ ~left:left_type ~right:(Some right_type)
            in
            if same_builtin then begin
              ignore (unify state result left_type);
              left_type
            end
            else result
          end
      end

and mismatched_operands state (value : expression) (left : expression) (right : expression)
    ~left_type ~right_type =
  let left_type = normalize state left_type and right_type = normalize state right_type in
  if T.is_integer_type left_type && T.is_integer_type right_type then begin
    let from = trait_reference ~arguments:[ T.Type right_type ] (core "From") in
    let fixes =
      if Option.is_some (implements state left_type from) then
        [
          fix
            (Printf.sprintf "Convert the right side to `%s`." (T.show left_type))
            [
              replace right.span
                (Printf.sprintf "%s.from(%s)" (T.show left_type) (source state right.span));
            ];
        ]
      else if
        Option.is_some
          (implements state right_type
             (trait_reference ~arguments:[ T.Type left_type ] (core "From")))
      then
        [
          fix
            (Printf.sprintf "Convert the left side to `%s`." (T.show right_type))
            [
              replace left.span
                (Printf.sprintf "%s.from(%s)" (T.show right_type) (source state left.span));
            ];
        ]
      else []
    in
    report state Mismatched_integers value.span ~fixes
      (Printf.sprintf
         "Integer types never convert implicitly: this compares or combines `%s` with `%s`."
         (T.show left_type) (T.show right_type))
  end
  else mismatch state right.span ~expected:left_type ~found:right_type

(* [any value] *)
and any_ state env ?expected (value : expression) (inner : expression) =
  match Option.map (normalize state) expected with
  | Some (T.Any trait as any_type) ->
      let inner_type = expression state env inner in
      defer state (fun () ->
          let inner_type = normalize state inner_type in
          if T.contains_unsolved inner_type then false
          else begin
            if Option.is_none (implements state inner_type { trait with associated = [] }) then
              report state No_impl value.span
                (Printf.sprintf "`%s` does not implement `%s`." (T.show inner_type)
                   (T.show_trait trait));
            true
          end);
      any_type
  | _ ->
      ignore (expression state env inner);
      report state Cannot_infer value.span
        "`any value` needs an expected type `any Trait`, from an annotation or a parameter.";
      T.Error

(* Strings and templates *)

and string_literal state env ?expected (literal : string_literal) =
  let parts = List.map (fun (part, _) -> (part, expression state env part)) literal.rest in
  match literal.tag with
  | None ->
      List.iter
        (fun ((part : expression), part_type) ->
          defer state (fun () ->
              let part_type = normalize state part_type in
              if T.contains_unsolved part_type then false
              else begin
                if Option.is_none (implements state part_type (trait_reference (core "Display")))
                then
                  report state No_impl part.span
                    (Printf.sprintf
                       "`%s` does not implement `Display`, so it cannot be interpolated."
                       (T.show part_type));
                true
              end))
        parts;
      string_type
  | Some tag -> (
      match target state tag.last with
      | Some (Definition tag_path) ->
          let tag_type = T.Named { path = tag_path; arguments = fresh_arguments state tag_path } in
          (match expected with
          | Some expected -> ignore (unify state tag_type expected)
          | None -> ());
          let template = trait_reference (standard [ "text" ] "FromTemplate") in
          defer state (fun () ->
              let tag_type = normalize state tag_type in
              if T.contains_unsolved tag_type then false
              else begin
                (match implements state tag_type template with
                | Some _ ->
                    let part =
                      Option.value ~default:T.Error
                        (Impls.associated_type state.database ~bounds:(bounds state) tag_type
                           template "Part")
                    in
                    List.iter
                      (fun ((part_expression : expression), part_type) ->
                        let part_type = normalize state part_type in
                        if
                          (not (T.equal part_type part))
                          && Option.is_none
                               (implements state part
                                  (trait_reference ~arguments:[ T.Type part_type ] (core "From")))
                        then
                          report state No_impl part_expression.span
                            (Printf.sprintf "`%s` cannot become a `%s`, the part type of `%s`."
                               (T.show part_type) (T.show part) (T.show tag_type)))
                      parts
                | None ->
                    if tag_type <> T.Error then
                      report state No_impl literal.span
                        (Printf.sprintf
                           "`%s` does not implement `FromTemplate`, so it is not a tag."
                           (T.show tag_type)));
                true
              end);
          tag_type
      | _ -> T.Error)

(* Collections *)

and list_literal state env ?expected (value : expression) items =
  let expected = Option.map (normalize state) expected in
  let element, make =
    match expected with
    | Some (T.Named { path; arguments = T.Type element :: rest })
      when Path.equal path set_path || Path.equal path list_path ->
        (element, fun element -> T.Named { path; arguments = T.Type element :: rest })
    | Some (T.Named { path; arguments = [ T.Type element; count ] })
      when Intrinsic.builtin_of_path path = Some Array ->
        (match count with
        | T.Value (Known count) when Z.to_int count <> List.length items ->
            report state Mismatch value.span
              (Printf.sprintf "This array has %d elements, and its type says %s."
                 (List.length items) (Z.to_string count))
        | _ -> ());
        (element, fun element -> T.Named { path; arguments = [ T.Type element; count ] })
    | _ ->
        let element = fresh state in
        (element, fun element -> T.Named { path = list_path; arguments = [ T.Type element ] })
  in
  List.iter (fun item -> check state env item element) items;
  make element

and map_literal state env ?expected (_ : expression) entries =
  let key, value_type =
    match Option.map (normalize state) expected with
    | Some (T.Named { path; arguments = [ T.Type key; T.Type value_type ] })
      when Path.equal path map_path ->
        (key, value_type)
    | _ -> (fresh state, fresh state)
  in
  List.iter
    (fun (entry_key, entry_value) ->
      check state env entry_key key;
      check state env entry_value value_type)
    entries;
  T.Named { path = map_path; arguments = [ T.Type key; T.Type value_type ] }

(* Lambdas: their types come only from where they are used. *)
and lambda state env ?expected (value : expression) parameters body =
  let references_before = state.references in
  let expected = Option.map (normalize state) expected in
  let result =
    match expected with
    | Some (T.Function function_type) when List.length function_type.inputs = List.length parameters
      ->
        List.iter2
          (fun written (mode, input) -> pattern state env written input ~mode)
          parameters function_type.inputs;
        let output = output_type function_type.output in
        let lambda_env = { env with output = Some (Returns output) } in
        let body_type = block_value state lambda_env ~expected:output body in
        (match resolve state body_type with
        | T.Never -> ()
        | _ ->
            if not (unify state output body_type) then
              mismatch state body.span ~expected:output ~found:body_type);
        T.Function function_type
    | Some (T.Function function_type) ->
        report state Mismatch value.span
          (Printf.sprintf "This lambda takes %d parameters, and `%s` takes %d."
             (List.length parameters)
             (T.show (T.Function function_type))
             (List.length function_type.inputs));
        T.Error
    | _ ->
        report state Lambda_needs_type value.span
          "A lambda's parameter types come from where it is used, and nothing here gives them. \
           Give the `let` a function type, or the call type arguments.";
        List.iter (fun written -> pattern state env written T.Error ~mode:T.Read) parameters;
        ignore (block_value state env body);
        T.Error
  in
  (* The outer locals the lambda reads, in the order it first reads them. *)
  let rec newer acc list =
    if list == references_before then acc
    else match list with [] -> acc | id :: rest -> newer (id :: acc) rest
  in
  let read = newer [] state.references in
  let inside = Span.make value.span.start value.span.stop in
  let outer id =
    match Hashtbl.find_opt state.binding_spans id with
    | Some (span : span) -> span.start < inside.start || span.start >= inside.stop
    | None -> true
  in
  let captures =
    List.fold_left
      (fun acc id -> if outer id && not (List.mem id acc) then acc @ [ id ] else acc)
      [] read
  in
  state.tables.captures.(value.id) <- Some captures;
  result

and if_ state env ?expected test then_ else_ =
  let condition_type = expression state env test in
  coerce state test ~found:condition_type ~expected:T.bool;
  match else_ with
  | None ->
      let then_type = block_value state env ~expected:T.unit then_ in
      (match resolve state then_type with
      | T.Never -> ()
      | _ ->
          if not (unify state then_type T.unit) then
            mismatch state then_.span ~expected:T.unit ~found:then_type);
      T.unit
  | Some branch ->
      let then_type = block_value state env ?expected then_ in
      let else_type, else_span =
        match branch with
        | Else block -> (block_value state env ?expected block, block.span)
        | Else_if branch_expression ->
            (expression state env ?expected branch_expression, branch_expression.span)
      in
      join state ~expected [ (then_type, then_.span); (else_type, else_span) ]

(* The type of branches together: arms of type [Never] are left out. *)
and join state ~expected branches =
  let live = List.filter (fun (type_, _) -> resolve state type_ <> T.Never) branches in
  match (live, expected) with
  | [], _ -> T.Never
  | (first, _) :: rest, _ ->
      let target = match expected with Some expected -> expected | None -> first in
      List.iter
        (fun (type_, span) ->
          if not (unify state target type_) then mismatch state span ~expected:target ~found:type_)
        (match expected with Some _ -> live | None -> rest);
      target

and match_ state env ?expected (value : expression) scrutinees arms =
  (* When the guards cover everything, the [match] ends with
     [_ => unreachable], which the prover shows is never reached. *)
  (match List.rev arms with
  | { patterns; guard = None; body = { kind = Expression { kind = Unreachable; _ }; _ }; _ }
    :: earlier
    when List.for_all (fun (written : pattern) -> written.kind = Wildcard) patterns
         && List.exists (fun (arm : arm) -> Option.is_some arm.guard) earlier ->
      state.obligations <- Guards_cover { match_ = value.id } :: state.obligations
  | _ -> ());
  let types = List.map (fun scrutinee -> (scrutinee, expression state env scrutinee)) scrutinees in
  let mode_of (scrutinee : expression) =
    match scrutinee.kind with
    | Mode (Own, _) -> T.Own
    | Mode (Mut, _) -> T.Mut
    | _ -> if is_place state scrutinee then T.Read else T.Own
  in
  let branch_types =
    List.map
      (fun (arm : arm) ->
        if List.length arm.patterns <> List.length types then
          report state Mismatch arm.span
            (Printf.sprintf "This arm has %d patterns, and the `match` has %d values."
               (List.length arm.patterns) (List.length types))
        else
          List.iter2
            (fun written (scrutinee, type_) ->
              pattern state env written type_ ~mode:(mode_of scrutinee))
            arm.patterns types;
        Option.iter (fun guard -> check state env guard T.bool) arm.guard;
        (arm_value state env ?expected arm.body, arm.body.span))
      arms
  in
  join state ~expected branch_types

(* An arm's body is a statement. As a value, a body that is not an
   expression has type [Unit]. *)
and arm_value state env ?expected (body : statement) =
  match body.kind with
  | Expression value -> expression state env ?expected value
  | _ ->
      ignore (statement state env body ~last:false);
      T.unit

and element_of_collection state env (collection : expression) =
  let collection_type = normalize state (expression state env collection) in
  match collection_type with
  | T.Named { path; arguments = [ T.Type element ] } when Path.equal path range_path -> element
  | T.Error | T.Hole -> collection_type
  | _ -> (
      match yielded state collection_type T.Read with
      | Some element -> element
      | None ->
          report state Not_indexable collection.span
            (Printf.sprintf "`%s` cannot be looped over." (T.show collection_type));
          T.Error)

(* What a value's [each] yields for a loop's mode. *)
and yielded state type_ mode =
  let receiver : Path.receiver = match mode with T.Read -> Read | Mut -> Mut | Own -> Own in
  match type_ with
  | T.Named { path; _ } -> (
      match List.assoc_opt receiver (Members.own_methods state.database path "each") with
      | Some method_path -> (
          match function_signature state method_path with
          | Some signature -> (
              let instance = instantiate state signature in
              (match instance.signature.receiver with
              | Some (_, self_type) -> ignore (unify state self_type type_)
              | None -> ());
              match instance.signature.output with Yields (_, element) -> Some element | _ -> None)
          | None -> None)
      | None -> None)
  | _ -> None

(* Blocks *)

(* A block used as a value: its last expression is checked against the
   block's expected type, in the enclosing statement. *)
and block_value state env ?expected (written : block) =
  let rec go = function
    | [] -> T.unit
    | [ (last : statement) ] -> (
        match last.kind with
        | Expression value -> expression state env ?expected value
        | _ ->
            ignore (statement state env last ~last:true);
            if statement_never state last then T.Never else T.unit)
    | (first : statement) :: rest ->
        ignore (in_statement state env first.span (fun () -> statement state env first ~last:false));
        go rest
  in
  go written.statements

and statement_never state (written : statement) =
  match written.kind with
  | Expression value -> (
      match state.tables.types.(value.id) with
      | Some type_ -> resolve state type_ = T.Never
      | None -> false)
  | While { condition = { kind = True; _ }; body; _ } -> not (contains_break body)
  | _ -> false

and contains_break (written : block) =
  let found = ref false in
  let rec statement (written : statement) =
    match written.kind with
    | For _ | While _ -> ()
    | _ -> Syntax_walk.statement_parts ~expression ~statement written
  and expression (value : expression) =
    match value.kind with
    | Break -> found := true
    | Lambda _ -> ()
    | _ -> Syntax_walk.expression_parts ~expression ~statement value
  in
  List.iter statement written.statements;
  !found

(* A statement. A statement that is not the last of its block must have
   type [Unit] or [Never]: any other value is unused. *)
and statement state env (written : statement) ~last : unit =
  match written.kind with
  | Expression value ->
      let type_ = expression state env value in
      if not last then
        defer state (fun () ->
            match normalize state type_ with
            | T.Variable _ | T.Literal _ -> false
            | resolved ->
                if
                  not
                    (resolved = T.unit || resolved = T.Never || resolved = T.Error
                   || resolved = T.Hole)
                then
                  report state Unused_value value.span
                    ~fixes:[ fix "Discard it on purpose." [ insert value.span.start "let _ = " ] ]
                    (Printf.sprintf
                       "This value of type `%s` is not used. Use it, or discard it with `let _ =`."
                       (T.show resolved));
                true)
  | Let { mutable_; pattern = written_pattern; annotation; value; else_ } ->
      let type_ =
        match annotation with
        | Some annotation ->
            let annotated = Lower.type_ state.context annotation in
            check state env value annotated;
            annotated
        | None -> expression state env value
      in
      (match else_ with
      | Some block -> (
          let else_type = block_value state env block in
          match resolve state else_type with
          | T.Never -> ()
          | _ ->
              report state Mismatch block.span
                "The `else` of a `let` must leave the block, with `return`, `break`, `continue`, \
                 or `unreachable`.")
      | None -> ());
      let mode = if mutable_ then T.Own else if is_place state value then T.Read else T.Own in
      binding_pattern state env written_pattern type_ ~mutable_ ~mode
  | Assignment { target = written_target; operator; value } -> (
      let target_type = expression state env written_target in
      check_assignable state env written_target;
      match operator with
      | Assign -> check state env value target_type
      | _ -> (
          let right_type = expression state env ~expected:target_type value in
          literal_operands state ~left:target_type ~right:right_type;
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
            | Shift_right_assign -> Shift_right
            | Assign -> Add
          in
          match binary_operator with
          | Add | Subtract | Multiply | Divide | Remainder ->
              let trait, method_ =
                match binary_operator with
                | Add -> (core "Add", "add")
                | Subtract -> (core "Subtract", "subtract")
                | Multiply -> (core "Multiply", "multiply")
                | Divide -> (core "Divide", "divide")
                | _ -> (core "Remainder", "remainder")
              in
              let fake : expression =
                { kind = Expression_error; span = written.span; id = written.id }
              in
              let result =
                operator_call state fake ~trait ~method_ ~left:target_type ~right:(Some right_type)
              in
              if not (unify state result target_type) then
                mismatch state value.span ~expected:target_type ~found:result
          | _ ->
              if not (unify state target_type right_type) then
                mismatch state value.span ~expected:target_type ~found:right_type))
  | For { pattern = written_pattern; iterable; clauses; body; _ } ->
      let mode, inner =
        match iterable.kind with
        | Mode (Mut, inner) when Option.is_none (marked_call state inner) -> (T.Mut, inner)
        | Mode (Own, inner) when Option.is_none (marked_call state inner) -> (T.Own, inner)
        | _ -> (T.Read, iterable)
      in
      let element = loop_iterable state env written ~mode inner in
      (if inner != iterable then
         match state.tables.types.(inner.id) with
         | Some type_ -> record state iterable type_
         | None -> ());
      binding_pattern state env written_pattern element ~mutable_:false ~mode;
      List.iter (loop_clause state env) clauses;
      loop_body state env body
  | While { condition = test; clauses; body } ->
      check state env test T.bool;
      List.iter (loop_clause state env) clauses;
      loop_body state env body
  | Parallel body ->
      List.iter
        (fun (branch : statement) ->
          in_statement state env branch.span (fun () -> statement state env branch ~last:false))
        body.statements
  | Proof body -> loop_body state { env with specification = true } body
  | Assert value -> check state env value T.bool
  | Yield value -> (
      match env.output with
      | Some (Yields (_, element) | Lends (_, element)) ->
          let inner =
            match value.kind with
            | Mode (_, inner) when Option.is_none (marked_call state inner) -> inner
            | _ -> value
          in
          let found = expression state env ~expected:element inner in
          if inner != value then record state value found;
          coerce state inner ~found ~expected:element
      | _ ->
          ignore (expression state env value);
          report state Wrong_yield written.span
            "Only a method whose signature `yields` or `lends` can `yield`.")
  | Statement_error -> ()

and loop_body state env (body : block) =
  List.iter
    (fun (written : statement) ->
      in_statement state env written.span (fun () -> statement state env written ~last:false))
    body.statements

and loop_clause state env (clause : loop_clause) =
  let env = { env with specification = true } in
  match clause.kind with
  | Invariant value -> check state env value T.bool
  | Loop_decreases measures ->
      List.iter (fun measure -> ignore (expression state env measure)) measures

(* What a [for] loop drives: a range of built-in integers, a call to a
   [yields] method, a cursor, or the [each] method of the loop's mode. *)
and loop_iterable state env (written : statement) ~mode (iterable : expression) =
  match iterable.kind with
  | Range { start = Some _; stop = Some _; inclusive; _ } -> (
      let range_type = normalize state (expression state env iterable) in
      match range_type with
      | T.Named { arguments = [ T.Type element ]; _ } ->
          defer state (fun () ->
              let element = normalize state element in
              if T.contains_unsolved element then false
              else begin
                if T.is_integer_type element then
                  state.tables.loops.(written.id) <- Some (Integer_range { element; inclusive })
                else if not (element = T.Error) then
                  report state Not_indexable iterable.span
                    (Printf.sprintf "A `for` loop's range is of integers, not `%s`."
                       (T.show element));
                true
              end);
          element
      | _ -> T.Error)
  | _ -> (
      let type_ = normalize state (expression state env iterable) in
      match (type_, state.tables.calls.(iterable.id)) with
      | T.Cursor _, Some call when match iterable.kind with Call _ -> true | _ -> false -> (
          (* A call to a [yields] method drives the loop directly. *)
          state.tables.loops.(written.id) <- Some (Yielding { call; mode });
          match function_output state call with
          | Some (T.Yields (_, element)) -> element
          | _ -> T.Error)
      | T.Error, _ | T.Hole, _ -> type_
      | _ -> (
          match each_call state type_ mode with
          | Some (call, element) ->
              state.tables.loops.(written.id) <- Some (Yielding { call; mode });
              element
          | None -> (
              let cursor = trait_reference (core "Cursor") in
              match implements state type_ cursor with
              | Some _ ->
                  state.tables.loops.(written.id) <- Some (Pulled { cursor = type_ });
                  Option.value ~default:T.Error
                    (Impls.associated_type state.database ~bounds:(bounds state) type_ cursor
                       "Element")
              | None ->
                  report state Not_indexable iterable.span
                    (Printf.sprintf
                       "`%s` has no `each` that takes %s, so a `for` loop cannot go over it this \
                        way."
                       (T.show type_)
                       (match mode with
                       | T.Read -> "`self`"
                       | Mut -> "`mut self`"
                       | Own -> "`own self`"));
                  T.Error)))

and function_output state (call : C.call) =
  match call.callee with
  | Function { path; _ } ->
      Option.map (fun (signature : T.signature) -> signature.output) (function_signature state path)
  | Trait_method _ -> Some (T.Yields (Read, call.result))
  | _ -> None

and each_call state type_ mode =
  let receiver : Path.receiver = match mode with T.Read -> Read | Mut -> Mut | Own -> Own in
  match type_ with
  | T.Named { path; _ } -> (
      match List.assoc_opt receiver (Members.own_methods state.database path "each") with
      | Some method_path -> (
          match function_signature state method_path with
          | Some signature -> (
              let instance = instantiate state signature in
              (match instance.signature.receiver with
              | Some (_, self_type) -> ignore (unify state self_type type_)
              | None -> ());
              match instance.signature.output with
              | Yields (_, element) ->
                  Some
                    ( {
                        C.callee =
                          Function { path = method_path; type_arguments = instance.type_arguments };
                        arguments = [];
                        defaults_left_out = [];
                        uses = instance.signature.uses;
                        capability_arguments = [];
                        result = element;
                      },
                      element )
              | _ -> None)
          | None -> None)
      | None -> None)
  | T.Parameter _ | T.Any _ -> (
      match trait_candidates state type_ "each" with
      | [ (trait, methods) ] -> (
          match
            List.find_opt
              (fun (method_ : T.trait_method) -> method_.method_receiver = receiver)
              methods
          with
          | Some method_ -> (
              let instance =
                instantiate state
                  ~extra:[ ({ owner = trait.trait; name = "Self" }, T.Type type_) ]
                  method_.method_signature
              in
              match instance.signature.output with
              | Yields (_, element) ->
                  let element = normalize state element in
                  Some
                    ( {
                        C.callee =
                          Trait_method
                            {
                              trait;
                              name = "each";
                              receiver;
                              self_type = type_;
                              type_arguments = [];
                              evidence =
                                (match type_ with
                                | T.Any _ -> Dynamic
                                | T.Parameter parameter -> Bound parameter
                                | _ -> Built_in);
                            };
                        arguments = [];
                        defaults_left_out = [];
                        uses = [];
                        capability_arguments = [];
                        result = element;
                      },
                      element )
              | _ -> None)
          | None -> None)
      | _ -> None)
  | _ -> None

(* An assignment's left side must be a place that may change. *)
and check_assignable state env (written : expression) =
  let rec root (value : expression) =
    match value.kind with
    | Name path -> (
        match target state path.last with
        | Some (Local id) -> (
            match Hashtbl.find_opt state.locals id with
            | Some local ->
                if local.mutable_ || local.mode = Mut then `Ok else `Fixed path.last.text
            | None -> `Ok)
        | Some (Definition _) -> `Fixed path.last.text
        | _ -> `Ok)
    | Self_value -> if env.self_mode = T.Mut then `Ok else `Fixed "self"
    | Member (base, _) -> root base
    | Bracket (base, _) -> root base
    | Parenthesized inner -> root inner
    | _ -> `Not_a_place
  in
  match root written with
  | `Ok -> ()
  | `Fixed name ->
      report state Not_assignable written.span
        (Printf.sprintf
           "`%s` cannot change here: only a `var`, a `mut` parameter, or `mut self`, and their \
            parts, can be assigned."
           name)
  | `Not_a_place ->
      report state Not_assignable written.span
        "Only a place, such as a variable, a field, or an element, can be assigned."

(* Patterns *)

and binding_pattern state env written type_ ~mutable_ ~mode =
  pattern_with state env written type_ ~mutable_ ~mode

and pattern state env written type_ ~mode =
  pattern_with state env written type_ ~mutable_:false ~mode

and pattern_with state env (written : pattern) type_ ~mutable_ ~mode =
  let type_ = normalize state type_ in
  state.tables.pattern_types.(written.id) <- Some type_;
  (match current_frame state with
  | Some frame -> frame.patterns <- written.id :: frame.patterns
  | None -> ());
  let recurse = pattern_with state env ~mutable_ ~mode in
  match written.kind with
  | Wildcard | Pattern_error -> ()
  | Binding_or_constant bound -> (
      match target state bound with
      | Some Binding -> declare state bound type_ ~mutable_ ~mode
      | Some (Local _) -> ()
      | Some (Definition path) -> (
          state.tables.patterns.(written.id) <- Some (Constant_pattern path);
          match Query.demand state.database Environment.constant_type path with
          | Some constant_type ->
              if not (unify state constant_type type_) then
                mismatch state written.span ~expected:type_ ~found:constant_type
          | None -> ())
      | Some (Generic _) ->
          if not (unify state (T.builtin USize) type_) then
            mismatch state written.span ~expected:type_ ~found:(T.builtin USize)
      | _ -> ())
  | Qualified_constant _ -> ()
  | Literal literal -> literal_pattern state env written literal type_
  | Pattern_range { start; stop; _ } ->
      List.iter
        (fun (end_ : range_end) ->
          match end_.kind with
          | End_literal literal -> literal_pattern state env written literal type_
          | End_constant _ -> ()
          | End_name bound -> (
              match target state bound with
              | Some (Definition path) -> (
                  match Query.demand state.database Environment.constant_type path with
                  | Some constant_type ->
                      if not (unify state constant_type type_) then
                        mismatch state end_.span ~expected:type_ ~found:constant_type
                  | None -> ())
              | _ -> ()))
        [ start; stop ]
  | Variant { name = variant_name; fields } -> (
      match type_ with
      | T.Named { path; arguments } -> (
          if not (Members.fields_visible state.database ~package:state.package path) then
            report state Private_field written.span
              (Printf.sprintf "`%s` is opaque, so only its own package can match on it."
                 (T.show type_));
          match Members.variants state.database path arguments with
          | Some variants -> (
              match
                List.find_opt
                  (fun (variant : T.variant) -> variant.variant_name = variant_name.last.text)
                  variants
              with
              | Some variant ->
                  state.tables.patterns.(written.id) <-
                    Some (Variant_pattern { type_; variant = variant.variant_name });
                  pattern_fields state env written
                    (Option.value ~default:[] variant.fields)
                    (Option.value ~default:[] fields) ~mutable_ ~mode
              | None ->
                  report state Unknown_variant variant_name.last.span
                    ~fixes:
                      (match
                         Resolve.closest variant_name.last.text
                           (List.map (fun (variant : T.variant) -> variant.variant_name) variants)
                       with
                      | Some candidate ->
                          [
                            fix
                              (Printf.sprintf "Write `%s`." candidate)
                              [ replace variant_name.last.span candidate ];
                          ]
                      | None -> [])
                    (Printf.sprintf "`%s` has no variant `%s`." (T.show type_)
                       variant_name.last.text))
          | None -> (
              match Members.shape state.database path with
              | Some Error_shape -> ()
              | _ ->
                  report state Unknown_variant written.span
                    (Printf.sprintf "`%s` has no variants." (T.show type_))))
      | T.Error | T.Hole -> ()
      | _ ->
          report state Unknown_variant written.span
            (Printf.sprintf "`%s` has no variants." (show state type_)))
  | Record fields -> (
      match type_ with
      | T.Named { path; arguments } -> (
          match Members.fields state.database path arguments with
          | Some record_fields ->
              state.tables.patterns.(written.id) <- Some (Record_pattern { type_ });
              pattern_fields state env written record_fields fields ~mutable_ ~mode
          | None ->
              report state Not_a_record written.span
                (Printf.sprintf "`%s` is not a record." (show state type_)))
      | T.Error | T.Hole -> ()
      | _ ->
          report state Not_a_record written.span
            (Printf.sprintf "`%s` is not a record." (show state type_)))
  | Alternatives alternatives ->
      List.iter (fun alternative -> recurse alternative type_) alternatives

and pattern_fields state env (written : pattern) (fields : T.field list)
    (written_fields : pattern_field list) ~mutable_ ~mode =
  let bare_name (inner : pattern) =
    match inner.kind with Binding_or_constant name -> Some name.text | _ -> None
  in
  List.iter
    (fun (field : pattern_field) ->
      match field.kind with
      | Rest -> ()
      | Named_field (name, inner) -> (
          match
            List.find_opt (fun (declared : T.field) -> declared.field_name = name.text) fields
          with
          | Some declared -> pattern_with state env inner declared.field_type ~mutable_ ~mode
          | None ->
              report state Unknown_member name.span
                ~fixes:
                  (match
                     Resolve.closest name.text
                       (List.map (fun (declared : T.field) -> declared.field_name) fields)
                   with
                  | Some candidate ->
                      [
                        fix (Printf.sprintf "Write `%s`." candidate) [ replace name.span candidate ];
                      ]
                  | None -> [])
                (Printf.sprintf "There is no field `%s` here." name.text))
      | Field inner -> (
          let named =
            Option.bind (bare_name inner) (fun name ->
                List.find_opt (fun (declared : T.field) -> declared.field_name = name) fields)
          in
          match (named, fields) with
          | Some declared, _ -> pattern_with state env inner declared.field_type ~mutable_ ~mode
          | None, [ only ] -> pattern_with state env inner only.field_type ~mutable_ ~mode
          | None, _ ->
              let names =
                String.concat ", "
                  (List.map (fun (declared : T.field) -> "`" ^ declared.field_name ^ "`") fields)
              in
              report state Unknown_member inner.span
                (Printf.sprintf
                   "A bare pattern must name a field, since this has %d fields: %s. Truss has no \
                    tuples, so fields match by name."
                   (List.length fields) names)))
    written_fields

and literal_pattern state env (written : pattern) literal type_ =
  ignore env;
  match literal with
  | Literal_integer number -> (
      state.tables.literals.(written.id) <- Some (Integer_value number);
      if not (T.is_integer_type type_ || type_ = T.Error || type_ = T.Hole) then
        report state Mismatch written.span
          (Printf.sprintf "An integer pattern matches an integer, not `%s`." (T.show type_))
      else
        match builtin_range type_ with
        | Some (low, high) when Z.lt number low || Z.gt number high ->
            report state Literal_out_of_range written.span
              (Printf.sprintf "`%s` does not fit in `%s`." (Z.to_string number) (T.show type_))
        | _ -> ())
  | Literal_true | Literal_false ->
      if not (unify state type_ T.bool) then
        mismatch state written.span ~expected:type_ ~found:T.bool
  | Literal_string _ ->
      if not (is_named string_path type_ || is_named string_slice_path type_ || type_ = T.Error)
      then
        report state Mismatch written.span
          (Printf.sprintf "A string pattern matches a string, not `%s`." (T.show type_))
