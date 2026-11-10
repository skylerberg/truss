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
  loop_element : T.ty option;
      (** In a [for] loop's clauses, what each iteration receives, which [yielded] is a sequence of.
      *)
  own : T.parameter list;
      (** The capability parameters of the function being checked. Each stands for itself throughout
          the body, in a call of the function by itself too. *)
}

type frame = {
  start : int;  (** The first inference variable the statement made. *)
  mutable nodes : int list;  (** Expressions whose types the statement recorded. *)
  mutable bindings : int list;  (** Locals it bound. *)
  mutable patterns : int list;  (** Patterns whose matched types it recorded. *)
  mutable pending : (unit -> bool) list;
      (** Checks that wait for types the statement has not decided yet; each says whether it is
          done. *)
  mutable unmet : (T.ty * T.trait_reference) list;
      (** The bounds reported as not holding, each with its type, so that a statement reports one
          once however many of its parts need it. *)
  frame_specification : bool;
  span : span;
}

type state = {
  database : Query.context;
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
  mutable unsolved : Diagnostic.reported option;
      (** The report of the first statement whose types could not be worked out. *)
  widened : (id, T.capability list * T.capability list) Hashtbl.t;
      (** By its expression, each function value that uses more than the function type it meets
          lists: that type's [uses], which have a capability parameter of what an enclosing call
          calls, and the capabilities they do not list, which the call's check takes as passed for
          the parameter. *)
}

let reported state ?(fixes = []) code (span : span) message =
  let diagnostic =
    Diagnostic.make ~fixes ~code:(Types code) (Source.span span.start span.stop) message
  in
  state.diagnostics <- diagnostic :: state.diagnostics;
  Diagnostic.reported diagnostic

let report state ?fixes code span message = ignore (reported state ?fixes code span message)

(* What resolution, the interfaces, and checking agree on cannot fail; if it
   does, that is a bug in the compiler, and stopping is better than
   accepting the code. *)
let bug format = Compiler_bug.bug ~stage:"Infer" format

(* The type of what did not check: its report is what lets everything be
   accepted of it. *)
let error state ?fixes code span message = T.Error (reported state ?fixes code span message)

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

let copyable state type_ = Impls.copyable state.database ~bounds:(bounds state) (zonk state type_)
let plain state type_ = Impls.plain state.database ~bounds:(bounds state) (zonk state type_)

(* The associated type the [impl] of a trait for a type gives. An [impl]
   that leaves one out has that reported as its own error, which is the
   report here too. *)
let associated state type_ (trait : T.trait_reference) name ~(at : span) =
  match Impls.associated_type state.database ~bounds:(bounds state) type_ trait name with
  | Some found -> found
  | None -> (
      let of_impl =
        match implements state type_ trait with
        | Some (Impls.From_impl { impl; _ }) -> Interface.Check.reported state.database impl
        | _ -> None
      in
      match of_impl with
      | Some report -> T.Error report
      | None ->
          error state Unknown_associated_type at
            (Printf.sprintf "`%s` gives no `%s` as a `%s`." (T.show type_) name (T.show_trait trait))
      )

let evidence_of = function
  | Impls.From_impl { impl; substitution } -> C.Impl { impl; arguments = substitution }
  | Impls.From_bound -> C.Bound
  | Impls.From_any -> C.Dynamic
  | Impls.Built_in | Impls.Accepted _ -> C.Built_in

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
  (* A call's type arguments count too: one that no parameter or result
     mentions is in no expression's type. *)
  let call_arguments () =
    List.concat_map
      (fun id ->
        match state.tables.calls.(id) with
        | Some
            {
              callee =
                ( Function { type_arguments; _ }
                | Trait_method { type_arguments; _ }
                | Constructor { type_arguments; _ }
                | Intrinsic { type_arguments; _ } );
              _;
            } ->
            type_arguments
        | _ -> [])
      frame.nodes
  in
  let unknowns () =
    List.concat_map (Unify.unknowns state.unifier) (all_types ())
    @ List.concat_map (Unify.argument_unknowns state.unifier) (call_arguments ())
  in
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
    let report =
      reported state Cannot_infer frame.span
        "The types in this statement cannot be worked out from it alone. Give the `let` a type, or \
         the call type arguments, such as `var names: List[String] = []`."
    in
    if Option.is_none state.unsolved then state.unsolved <- Some report;
    (* Every unsolved variable becomes an error, so it is reported once. *)
    List.iter
      (function
        | Unify.Unknown_type index | Unknown_literal (_, index) ->
            Hashtbl.replace state.unifier.types index (T.Error report)
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
      unmet = [];
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

(* A literal that is a receiver has its default type, as in
   [5.wrapping_add(3)], since nothing else can decide it before the method
   is looked up. *)
let default_literal state type_ =
  let decide default =
    ignore (Unify.unify state.unifier type_ default);
    default
  in
  match Unify.resolve state.unifier type_ with
  | T.Literal (Integer_literal, _) -> decide (T.builtin Int64)
  | T.Literal (Float_literal, _) -> decide (T.builtin Float64)
  | _ -> type_

(* What an expression names, when it is a name: the one reading of it that
   every part of checking shares. *)
let head state (value : expression) = Resolve.head state.resolved value

(* A name after a dot is a variant when it is written as a type is. *)
let names_variant (member : name) =
  member.text <> "" && member.text.[0] >= 'A' && member.text.[0] <= 'Z'

(* Showing types and fixes *)

let show state type_ = T.show (zonk state type_)

let mismatched state (span : span) ~expected ~found =
  let expected = zonk state expected and found = zonk state found in
  match (resolve state found, expected) with
  | T.Literal (Integer_literal, _), _ when T.is_float_type expected ->
      reported state Integer_for_float span
        ~fixes:[ fix "Write it as a float." [ insert span.stop ".0" ] ]
        (Printf.sprintf "An integer literal is never a float, and `%s` is expected here."
           (T.show expected))
  | _ ->
      reported state Mismatch span
        (Printf.sprintf "Expected `%s`, found `%s`." (T.show expected) (T.show found))

let mismatch state span ~expected ~found = ignore (mismatched state span ~expected ~found)

(* Places *)

(* Whether an expression is a place: a local, a parameter, [self], or a
   constant, followed by fields and indexes. *)
let rec is_place state (value : expression) =
  match value.kind with
  | Name path -> (
      match target state path.last with
      | Some (Local _ | Field _ | Definition (Constant, _)) -> true
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

(* The error of an expression that is not what its place needs: the name's
   own report when resolution found nothing by it, so that is the one
   report, and a new one otherwise. *)
let error_at state ?fixes code (value : expression) message =
  match head state value with
  | Some { target = Unknown report; _ } -> T.Error report
  | _ -> error state ?fixes code value.span message

(* Static references: an expression that names a type or a trait rather
   than a value, before a [.] or a [(]. *)
type static_ =
  | Static_type of T.ty
  | Static_trait of Path.t * T.argument list option
      (** With the trait's arguments, when they are written. *)
  | Static_capability of Path.t

(* Where a value of one type goes where another is expected, which is the
   one place a type converts, and the conversion made:

   - [Never] becomes any type.
   - A function value becomes a function type with more [uses] or weaker
     costs. A capability the expected type does not list is allowed only
     when the type has a capability parameter of another function, which a
     call of that function solves as what is passed for it: the value is
     noted for the check of capabilities, which knows the call. Costs that
     the types' constants do not show to be weaker are the prover's to
     show: of what is passed for a parameter where it checks the call, and
     of [expression] elsewhere, as an obligation.
   - Where a value is passed for a parameter, an owned collection becomes
     its view and, in a specification, a built-in integer becomes an
     [Integer] or an [Integer] a built-in integer that it fits.

   Anything else must be the type expected. *)
let convert state env ?(argument = false) ?expression (span : span) ~found ~expected :
    C.conversion option =
  let given = normalize state found and wanted = normalize state expected in
  let refused () =
    mismatch state span ~expected ~found;
    None
  in
  match (given, wanted, expression) with
  | T.Never, _, _ -> Some From_never
  | T.Named given_named, T.Named wanted_named, _
    when argument
         && List.exists
              (fun (owned, view) ->
                Path.equal given_named.path owned && Path.equal wanted_named.path view)
              [ (list_path, slice_path); (string_path, string_slice_path) ] ->
      if not (Unify.unify_arguments state.unifier wanted_named.arguments given_named.arguments) then
        mismatch state span ~expected ~found;
      Some Owned_to_view
  | T.Integer, _, Some expression when argument && env.specification && T.is_integer_type wanted ->
      state.obligations <- Integer_fits { expression; type_ = wanted } :: state.obligations;
      Some From_integer
  | _, T.Integer, _ when argument && env.specification && T.is_integer_type given -> Some To_integer
  | T.Function given_function, T.Function wanted_function, _
    when not (T.same_clauses given_function wanted_function) ->
      let unlisted =
        List.filter
          (fun capability -> not (List.mem capability wanted_function.uses))
          given_function.uses
      in
      let solved_by_a_call =
        List.exists
          (function
            | T.Capability_parameter parameter -> not (List.mem parameter env.own)
            | T.Capability _ -> false)
          wanted_function.uses
      in
      let proven = T.costs_imply ~given:given_function.costs ~wanted:wanted_function.costs in
      if
        Unify.unify state.unifier wanted
          (T.Function
             { given_function with uses = wanted_function.uses; costs = wanted_function.costs })
        && (unlisted = [] || (solved_by_a_call && Option.is_some expression))
        && (proven || argument || Option.is_some expression)
      then begin
        Option.iter
          (fun expression ->
            if unlisted <> [] then
              Hashtbl.replace state.widened expression (wanted_function.uses, unlisted);
            if not (proven || argument) then
              state.obligations <-
                Costs_imply { expression; given = given_function; expected = wanted_function }
                :: state.obligations)
          expression;
        Some Function_widening
      end
      else refused ()
  | _ -> if Unify.unify state.unifier wanted given then None else refused ()

(* Bounds *)

(* Holds a type to a bound, once the statement has worked the type out. The
   type must implement the trait, and each associated type the bound fixes
   must equal the one the [impl] gives, which can be what works out the
   rest of the statement. [unmet] reports the type with [None] when it does
   not implement the trait, and with an associated type's name and what
   the [impl] gives when that is another type. *)
let require state type_ (bound : T.trait_reference) ~unmet =
  let trait = { bound with associated = [] } in
  defer state (fun () ->
      let type_ = normalize state type_ in
      if Unify.unknowns state.unifier type_ <> [] then false
      else begin
        (match implements state type_ trait with
        | None -> unmet type_ None
        | Some _ ->
            List.iter
              (fun (name, wanted) ->
                match
                  Impls.associated_type state.database ~bounds:(bounds state) type_ trait name
                with
                | Some given when not (unify state given wanted) -> unmet type_ (Some (name, given))
                | _ -> ())
              bound.associated);
        true
      end)

(* Holds what stands for a definition's generic parameters to their
   bounds. [of_type] is the type whose parameters they are, and without it
   they are those of what a call calls. *)
let require_bounds state (span : span) ?of_type generics substitution =
  List.iter
    (fun (argument, bound) ->
      require state argument bound ~unmet:(fun argument other ->
          let bound = Unify.zonk_trait state.unifier bound in
          let reported =
            match current_frame state with
            | Some frame ->
                let reported = List.mem (argument, bound) frame.unmet in
                frame.unmet <- (argument, bound) :: frame.unmet;
                reported
            | None -> false
          in
          if not reported then
            let needs =
              Printf.sprintf "%s needs `%s: %s`"
                (match of_type with
                | Some type_ -> Printf.sprintf "`%s`" (show state type_)
                | None -> "This")
                (T.show argument) (T.show_trait bound)
            in
            report state Unsatisfied_bound span
              (match other with
              | None -> needs ^ ", which does not hold."
              | Some (name, given) ->
                  Printf.sprintf "%s, and its `%s` is `%s`." needs name (show state given))))
    (Impls.required generics substitution)

(* Instantiating types *)

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

let require_type_bounds state span path arguments =
  match Query.demand state.database Environment.type_interface path with
  | Some interface ->
      Option.iter
        (require_bounds state span ~of_type:(T.Named { path; arguments }) interface.type_generics)
        (T.substitution_of interface.type_generics arguments)
  | None -> ()

(* Unknown arguments for a type, which the statement works out, each held to
   the bounds of its parameter. *)
let instantiate_type state span path =
  let arguments = fresh_arguments state path in
  require_type_bounds state span path arguments;
  arguments

let rec static_ state (value : expression) : static_ option =
  match (value.kind, head state value) with
  | Self_type_value, _ -> Option.map (fun self -> Static_type self) state.context.self_type
  | _, Some { target = Definition (Type, path); type_arguments; _ } ->
      Some (Static_type (named_type state value path type_arguments))
  | _, Some { target = Type_parameter id; name; type_arguments } ->
      if Option.is_some type_arguments then
        report state Arity value.span
          (Printf.sprintf "`%s` is a generic parameter, which takes no arguments." name.text);
      Some (Static_type (T.Parameter (Lower.declared state.context id name)))
  | _, Some { target = Definition (Trait, path); type_arguments; _ } ->
      Some (Static_trait (path, Option.map (written_arguments state) type_arguments))
  | _, Some { target = Definition (Capability, path); _ } -> Some (Static_capability path)
  | Parenthesized inner, None -> static_ state inner
  | _ -> None

(* A type named in an expression: with the arguments written after it, or
   with unknown ones for the statement to work out. *)
and named_type state (value : expression) path type_arguments =
  let type_ arguments =
    match Intrinsic.builtin_of_path path with
    | Some Never -> T.Never
    | Some Integer -> T.Integer
    | _ -> T.Named { path; arguments }
  in
  match type_arguments with
  | None -> type_ (instantiate_type state value.span path)
  | Some items ->
      let arguments = written_arguments state items in
      (match Query.demand state.database Interface.Summary.generics_of path with
      | Some expected when List.length expected <> List.length arguments ->
          report state Arity value.span
            (Printf.sprintf "`%s` takes %d %s, and %d %s given."
               (T.show (Named { path; arguments = [] }))
               (List.length expected)
               (if List.length expected = 1 then "argument" else "arguments")
               (List.length arguments)
               (if List.length arguments = 1 then "is" else "are"))
      | _ -> require_type_bounds state value.span path arguments);
      type_ arguments

(* Type arguments written in an expression, as in [List[String].new()]. *)
and written_arguments state items =
  List.filter_map
    (function
      | Item item -> Some (type_argument_of_expression state item)
      | Item_constraint (name, _) ->
          report state Arity name.span
            "An associated type is fixed where a type is written, as in `any Trait[Name = Type]`, \
             not among type arguments in an expression.";
          None)
    items

and type_argument_of_expression state (value : expression) : T.argument =
  match (value.kind, head state value) with
  | Integer value, _ -> T.Value (Known value)
  | _, Some { target = Value_parameter id; name; _ } ->
      T.Value (Value_parameter (Lower.declared state.context id name))
  | _, Some { target = Definition (Constant, path); name; _ } -> (
      match Query.demand state.database Interface.Constants.value_of path with
      | Some value -> T.Value (Known value)
      | None ->
          T.Type
            (error state Arity value.span
               (Printf.sprintf
                  "The value of `%s` cannot be worked out: a constant used in a type cannot refer \
                   to itself, and is made of literals, arithmetic, and other such constants."
                  name.text)))
  | _ -> (
      match static_ state value with
      | Some (Static_type type_) -> T.Type type_
      | Some (Static_trait _ | Static_capability _) | None ->
          T.Type (error_at state Not_a_type value "A type argument is a type, or a `USize` value."))

(* Instantiating signatures *)

type instance = {
  signature : T.signature;
  substitution : T.substitution;
  type_arguments : T.argument list;
}

(* What a signature is where it is used: unknowns for its generic
   parameters, which the statement works out, each held to its bounds. *)
let instantiate state (span : span) ?(extra = []) (signature : T.signature) =
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
  require_bounds state span signature.generics substitution;
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

(* A function's signature, or the report of why it has none, when its
   header did not parse. *)
let function_signature state (path : Path.t) =
  match intrinsic_signature path with
  | Some signature -> Some (Ok signature)
  | None -> Environment.signature_or_report state.database path

(* Lending *)

(* A call of a lending method is the part the method gives, lent for the
   rest of the caller's statement. It is not a temporary: it is never moved,
   and what may be done with it follows how it is lent. *)
let note_lending state (value : expression) (output : T.result) =
  match output with
  | Lends (mode, _) -> state.tables.lends.(value.id) <- Some mode
  | Returns _ | Yields _ -> ()

(* How an expression is lent, when it is what a lending call gives or a
   part of that, a field or an element. A mark before it is the mark of the
   place it is lent from. *)
let rec lent state (value : expression) : T.mode option =
  match value.kind with
  | Call _ -> state.tables.lends.(value.id)
  | Member (base, _) | Parenthesized base -> lent state base
  | Bracket (base, _) when state.resolved.brackets.(value.id) <> Some Type_arguments ->
      lent state base
  | Mode (_, inner) when Option.is_some (marked_call state inner) -> lent state inner
  | _ -> None

(* Whether a value is borrowed where it is: a place, or a part that is
   lent. What binds it views it, and what matches it binds views of its
   parts. *)
let borrowed state (value : expression) = is_place state value || Option.is_some (lent state value)

(* A place that is assigned or lent [mut]: each index on its way is the
   [mut] version of [at], which lends its element [mut]. *)
let rec mutable_place state (value : expression) =
  match value.kind with
  | Member (base, _) | Parenthesized base | Mode (_, base) -> mutable_place state base
  | Bracket (base, _) ->
      (match state.tables.calls.(value.id) with
      | Some ({ callee = Trait_method ({ name = "at"; _ } as method_); arguments; _ } as call) ->
          state.tables.calls.(value.id) <-
            Some
              {
                call with
                callee = Trait_method { method_ with receiver = Mut };
                arguments =
                  List.map
                    (fun (argument : C.argument) ->
                      if argument.parameter = 0 then { argument with mode = T.Mut } else argument)
                    arguments;
              }
      | _ -> ());
      mutable_place state base
  | _ -> ()

(* Arguments and modes *)

type argument_form = Marked of T.mode * expression | Place | Lent of T.mode | Temporary

let argument_form state (value : expression) =
  match value.kind with
  | Mode (mode, inner) when Option.is_none (marked_call state inner) ->
      Marked ((match mode with Mut -> Mut | Own -> Own), inner)
  | _ -> (
      match lent state value with
      | Some mode -> Lent mode
      | None -> if is_place state value then Place else Temporary)

let mark_span (value : expression) (inner : expression) =
  Span.make value.span.start inner.span.start

let check_mode state (value : expression) (parameter : T.parameter_info) type_ =
  let name = parameter.name in
  match (parameter.mode, argument_form state value) with
  | Read, (Place | Temporary | Lent _) -> ()
  | Read, Marked (_, inner) ->
      report state Redundant_mark value.span
        ~fixes:
          [
            fix "Remove the mark."
              [ Diagnostic.delete (Source.span value.span.start inner.span.start) ];
          ]
        (Printf.sprintf "`%s` only reads its argument, so it takes no mark." name)
  | Mut, Marked (Mut, inner) -> mutable_place state inner
  | Mut, Place ->
      report state Missing_mark value.span
        ~fixes:[ fix "Mark it `mut`." [ insert value.span.start "mut " ] ]
        (Printf.sprintf "`%s` may change its argument, so the call marks it `mut`." name)
  | Mut, Lent Mut -> mutable_place state value
  | Mut, Lent (Read | Own) ->
      report state Wrong_mark value.span
        (Printf.sprintf
           "`%s` may change its argument, and this part is lent read-only. Mark the place it is \
            lent from `mut`, so that it is lent `mut`."
           name)
  | Own, Lent _ ->
      if not (plain state type_) then
        report state Missing_mark value.span
          ~fixes:
            (if copyable state type_ then
               [ fix "Pass a copy." [ insert value.span.stop ".copy()" ] ]
             else [])
          (Printf.sprintf
             "`%s` takes ownership of its argument, and a part that is lent cannot be given up. \
              Pass a copy."
             name)
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
