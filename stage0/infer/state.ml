(* What checking a body works with: the state of a definition's check and
   of each statement in it, the environment of a body, and what every part
   of checking shares: reporting, recording types, unifying, the standard
   library's paths, places, instantiating signatures, and modes at calls.
   See [Expressions] for how checking proceeds. *)

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
  mutable lambdas : span list;  (** The lambdas being checked, innermost first. *)
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

(* Projections whose base is known are normalized first, so [C.Key] meets
   the type the [impl] chooses. *)
let unify state left right =
  let normalize type_ =
    Impls.normalize state.database ~bounds:(bounds state) (Unify.zonk state.unifier type_)
  in
  Unify.unify state.unifier (normalize left) (normalize right)

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
let sequence_path = standard [ "specification" ] "Sequence"
let finite_set_path = standard [ "specification" ] "FiniteSet"
let finite_map_path = standard [ "specification" ] "FiniteMap"
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
  let unknowns () = List.concat_map (Unify.unknowns state.unifier) (all_types ()) in
  (* The literals the statement made that nothing decided take their
     defaults: [Int64] and [Float64], or [Integer] in a specification. *)
  List.iter
    (function
      | Unify.Unknown_literal (kind, index) when index >= frame.start ->
          Hashtbl.replace state.unifier.types index
            (match kind with
            | Integer_literal -> if frame.frame_specification then T.Integer else T.builtin Int64
            | Float_literal -> T.builtin Float64)
      | _ -> ())
    (unknowns ());
  run_pending ();
  let unsolved =
    List.filter
      (function
        | Unify.Unknown_type index | Unknown_value index | Unknown_literal (_, index) ->
            index >= frame.start)
      (unknowns ())
  in
  if unsolved <> [] then begin
    report state Cannot_infer frame.span
      "The types in this statement cannot be worked out from it alone. Give the `let` a type, or \
       the call type arguments, such as `var names: List[String] = []`.";
    (* Every unsolved variable becomes an error, so it is reported once. *)
    List.iter
      (function
        | Unify.Unknown_type index | Unknown_literal (_, index) ->
            Hashtbl.replace state.unifier.types index T.Error
        | Unknown_value _ -> ())
      unsolved;
    (* What waits on them never runs, and needs not: the error is reported. *)
    frame.pending <- []
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
  match (resolve state found, expected) with
  | T.Literal (Integer_literal, _), _ when T.is_float_type expected ->
      report state Integer_for_float span
        ~fixes:[ fix "Write it as a float." [ insert span.stop ".0" ] ]
        (Printf.sprintf "An integer literal is never a float, and `%s` is expected here."
           (T.show expected))
  | _ ->
      report state Mismatch span
        (Printf.sprintf "Expected `%s`, found `%s`." (T.show expected) (T.show found))

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

(* The call an expression is, under a mark and parentheses. *)
let rec called (value : expression) =
  match value.kind with
  | Call _ -> Some value
  | Mode (_, inner) | Parenthesized inner -> called inner
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
          (match Query.demand state.database Interface.Summary.generics_of path with
          | Some expected when List.length expected <> List.length arguments ->
              report state Arity value.span
                (Printf.sprintf "`%s` takes %d %s, and %d %s given."
                   (T.show (Named { path; arguments = [] }))
                   (List.length expected)
                   (if List.length expected = 1 then "argument" else "arguments")
                   (List.length arguments)
                   (if List.length arguments = 1 then "is" else "are"))
          | _ -> ());
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

let instantiate state ?span ?(extra = []) (signature : T.signature) =
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
  (* Each type argument must meet its parameter's bounds, once the
     statement has worked it out. *)
  (match span with
  | Some (span : span) ->
      List.iter
        (fun (generic : T.generic) ->
          match (generic.kind, List.assoc_opt generic.generic substitution) with
          | Type_generic generic_bounds, Some (T.Type argument) ->
              List.iter
                (fun bound ->
                  defer state (fun () ->
                      let argument = normalize state argument in
                      let bound = T.substitute_trait substitution bound in
                      if Unify.unknowns state.unifier argument <> [] then false
                      else begin
                        if Option.is_none (implements state argument bound) then
                          report state Unsatisfied_bound span
                            (Printf.sprintf "This call needs `%s: %s`, which does not hold."
                               (T.show argument)
                               (T.show_trait (Unify.zonk_trait state.unifier bound)));
                        true
                      end))
                generic_bounds
          | _ -> ())
        signature.generics
  | None -> ());
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
