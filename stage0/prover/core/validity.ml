(* What holds of a value because of its type, and of a callback because of its
   parameter: a type's invariants, a function-typed parameter's clauses, and
   the places that must be disjoint. *)

open Core
open State
open Facts
open Contracts

(* An index or a range read, which the ownership check may have paired
   with another: the two must reach different elements. Two indexes of one
   collection that are lent together, or used by two branches of
   [parallel], must differ, which the ownership check left to the prover.
   Each is read as it is evaluated, and the pair is shown once both are. *)
let note_place context frame origin place =
  if
    frame.source.key = Some context.home
    && List.exists (fun (first, second) -> first = origin || second = origin) context.disjoint
  then begin
    context.indexes <- (origin, (place, span_of frame.source origin)) :: context.indexes;
    let outside index start stop =
      Logic.(Operation ("<", [ index; start ]) ||| Operation ("<=", [ stop; index ]))
    in
    List.iter
      (fun (first, second) ->
        if first = origin || second = origin then
          match (List.assoc_opt first context.indexes, List.assoc_opt second context.indexes) with
          | Some (left, (first_span : span)), Some (right, (second_span : span)) ->
              let apart =
                match (left, right) with
                | One left, One right -> Logic.not_ (Logic.equal left right)
                | One index, Run (start, stop) | Run (start, stop), One index ->
                    outside index start stop
                | Run (start, stop), Run (other_start, other_stop) ->
                    Logic.disjunction
                      [
                        Logic.Operation ("<=", [ stop; other_start ]);
                        Logic.Operation ("<=", [ other_stop; start ]);
                        Logic.Operation ("<=", [ stop; start ]);
                        Logic.Operation ("<=", [ other_stop; other_start ]);
                      ]
              in
              let text (span : span) =
                let source_text = Lazy.force frame.source.text in
                if span.stop <= String.length source_text then
                  String.sub source_text span.start (span.stop - span.start)
                else "this expression"
              in
              oblige context frame Disjoint (span_of frame.source origin)
                (Printf.sprintf
                   "`%s` and `%s` may reach the same elements, which are used together."
                   (text first_span) (text second_span))
                apart
          | _ -> ())
      context.disjoint
  end

(* Reading code that never runs, as a specification, which spends nothing. *)
let without_costs : 'a. _ -> (unit -> 'a) -> 'a =
 fun context read ->
  let saved = context.counters in
  context.counters <- [];
  Fun.protect ~finally:(fun () -> context.counters <- saved) read

(* The value of a formula of a specification, which never runs, so it
   spends nothing whatever it calls. *)
let specification_value context frame (formula : Mir.formula) =
  without_costs context (fun () -> context.formula_term frame formula ~arguments:[])

let selected context ty variant field term =
  match (term, constructors context ty) with
  | Logic.Apply (name, arguments), Some shape when name = constructor_name ty variant -> (
      let fields = Option.value (List.assoc_opt variant shape) ~default:[] in
      match List.find_index (fun (named, _) -> named = field) fields with
      | Some index when index < List.length arguments -> List.nth arguments index
      | _ -> Logic.Apply (selector_name ty variant field, [ term ]))
  | _ -> Logic.Apply (selector_name ty variant field, [ term ])

(* A frame for reading a type's own clauses about a value of it. *)
let type_frame context frame source (ty : Types.ty) ~self =
  let substitution = match visible_type context ty with Some (_, symbol) -> symbol | None -> [] in
  {
    frame with
    source;
    locals = Locals.empty;
    types = Locals.empty;
    old_locals = Locals.empty;
    self;
    old_self = self;
    self_type = Some ty;
    result = None;
    checking = false;
    substitution;
  }

(* The form of a type, which holds its fields' defaults, its invariants,
   and its potential. *)
let type_source context (ty : Types.ty) =
  match ty with
  | Types.Named { path; _ } when Interface.Summary.kind_of context.database path = Some Type ->
      Option.map (fun (source, _, _) -> source) (source_at context.database path)
  | _ -> None

(* What a type states of its values, and the form to read it in. *)
let type_clauses context (ty : Types.ty) =
  match (ty, type_source context ty) with
  | Types.Named { path; _ }, Some source ->
      Option.map
        (fun (clauses : Mir.type_clauses) -> (source, clauses))
        (Query.demand context.database Mir.type_clauses_of_path path)
  | _ -> None

let invariants (clauses : Mir.loop_clause list) =
  List.filter_map (function Mir.Invariant value -> Some value | _ -> None) clauses

(* A type's invariants, and the form to read them in. *)
let invariants_of context (ty : Types.ty) =
  match type_clauses context ty with
  | Some (source, { invariants = _ :: _ as invariants; _ }) ->
      Some (source, List.map (fun (invariant : Mir.requirement) -> invariant.clause) invariants)
  | _ -> None

(* Whether a value meets its type's invariants, and with [deep] its
   fields' too, each read with [self] as the value. The invariant of a type
   whose fields this package does not see is a fact about the value only:
   a value of it comes from the type's own package, which shows it, so
   here it is assumed where a value arrives and shown where one leaves, and
   never unfolded. *)
let rec validity context frame ~assuming ?(deep = true) ?(own = true) ?(seen = []) ty term =
  if List.exists (Types.equal ty) seen || List.exists (Types.equal ty) context.validating then
    Logic.Boolean true
  else
    let validating = context.validating in
    context.validating <- ty :: validating;
    Fun.protect ~finally:(fun () -> context.validating <- validating) @@ fun () ->
    let own =
      match invariants_of context ty with
      | _ when not own -> Logic.Boolean true
      | Some _ when constructors context ty = None ->
          let symbol = Symbol.Valid (type_key ty) in
          declare context (Logic.Function (symbol, [ sort_of context ty ], Logic.Bool));
          Logic.Apply (symbol, [ term ])
      | Some (source, written) -> (
          let inner = type_frame context frame source ty ~self:(Some term) in
          try
            Logic.conjunction
              (List.map
                 (fun invariant -> snd (specification_value context inner invariant))
                 written)
          with Unsupported _ | Foreign_unsupported _ when assuming -> Logic.Boolean true)
      | None -> Logic.Boolean true
    in
    let fields =
      if not deep then Logic.Boolean true
      else
        match constructors context ty with
        | Some shape ->
            Logic.conjunction
              (List.concat_map
                 (fun (variant, fields) ->
                   List.map
                     (fun (field, field_type) ->
                       let part =
                         validity context frame ~assuming ~deep ~seen:(ty :: seen) field_type
                           (selected context ty variant field term)
                       in
                       match (variant, part) with
                       | _, Logic.Boolean true -> part
                       | Some name_, _ ->
                           Logic.( ==> ) (Logic.Is (constructor_name ty (Some name_), term)) part
                       | None, _ -> part)
                     fields)
                 shape)
        | None -> Logic.Boolean true
    in
    Logic.( &&& ) own fields

let assume_valid context frame ty term =
  assume context frame (validity context frame ~assuming:true ty term)

(* A function-typed parameter whose type has a [requires], read as a value
   other than to call it or pass it to a parameter: the value's type keeps
   no [requires], so the [requires] must hold for every argument. *)
(* Fresh valid arguments for a callback's inputs. *)
let callback_arguments context frame inputs =
  List.map
    (fun (_, input) ->
      let input = substituted context frame input in
      let term = arrive context frame "argument" input in
      assume_valid context frame input term;
      term)
    inputs

(* The frame a callback parameter's [requires] is read in: its inputs bound
   to [arguments], over the caller's state on entry. *)
let callback_contract_frame frame inputs arguments =
  let locals =
    List.fold_left2
      (fun locals (input, _) term -> Locals.add input term locals)
      frame.old_locals inputs arguments
  in
  { frame with locals; self = frame.old_self; checking = false }

(* The clauses that a function-typed parameter of the definition proven
   states, with the parameter's name. *)
let own_callback context local =
  List.find_map
    (fun (parameter, name, callback) -> if parameter = local then Some (name, callback) else None)
    context.callbacks

(* That a function-typed parameter's [requires], read with its parameters
   as they were on entry, holds wherever [promised] does. *)
let check_callback_contract context frame span ~name inputs requires arguments ~promised ~why =
  let inside = callback_contract_frame frame inputs arguments in
  List.iter
    (fun (clause : Mir.formula) ->
      oblige context (restrict frame promised) Requires span
        (Printf.sprintf "`%s` %s, so its `%s` may not hold." name why
           (quote frame.source clause.origin))
        (snd (specification_value context inside clause)))
    requires

let escaping_callback context frame local =
  match (own_callback context local, local_type context frame local) with
  | ( Some (name, ({ inputs; requires = _ :: _ as requires } : Mir.callback)),
      Some (Types.Function function_type) )
    when List.length inputs = List.length function_type.inputs ->
      let arguments = callback_arguments context frame function_type.inputs in
      check_callback_contract context frame
        (span_of frame.source (List.hd requires).origin)
        ~name inputs requires arguments ~promised:(Logic.Boolean true)
        ~why:"is used as a value whose type promises nothing of its arguments"
  | _ -> ()

let reading_callback : 'a. _ -> (unit -> 'a) -> 'a =
 fun context read ->
  let saved = context.reading_callback in
  context.reading_callback <- true;
  Fun.protect ~finally:(fun () -> context.reading_callback <- saved) read

(* A part's frame, for reading its clauses, with its parameters bound to
   the given terms by position. *)
let part_frame frame (part : part) ~arguments ~substitution =
  let locals, types, self =
    List.fold_left
      (fun (locals, types, self) (position, (parameter : Mir.parameter)) ->
        match (parameter.local, List.assoc_opt position arguments) with
        | Self, Some term -> (locals, types, Some (term, parameter.type_))
        | local, Some term ->
            (Locals.add local term locals, Locals.add local parameter.type_ types, self)
        | _, None -> (locals, types, self))
      (Locals.empty, Locals.empty, None)
      (List.mapi (fun position parameter -> (position, parameter)) part.parameters)
  in
  {
    frame with
    source = part.callee;
    locals;
    types;
    old_locals = locals;
    self = Option.map fst self;
    old_self = Option.map fst self;
    self_type = Option.map (fun (_, ty) -> Types.substitute substitution ty) self;
    result = None;
    checking = false;
    substitution;
  }

(* A callee's promise to the lambda passed for one parameter: that
   parameter's [requires], read in the callee with the call's other
   arguments, and the lambda's arguments for the inputs it names. *)
let callback_facts context frame (invocation : Invocation.t) position known arguments =
  match invocation.callee with
  | Function { path; type_arguments } -> (
      match
        Option.bind (source_at context.database path) (fun (callee, _, _) ->
            part_of context.database path callee)
      with
      | Some part -> (
          match List.assoc_opt position part.callbacks with
          | Some { inputs; requires } when List.length inputs = List.length arguments ->
              let substitution =
                match Interface.Impls.signature context.database path with
                | Some (signature : Types.signature) ->
                    callee_substitution frame signature type_arguments
                | None -> []
              in
              let inside = part_frame frame part ~arguments:known ~substitution in
              let inside =
                {
                  inside with
                  locals =
                    List.fold_left2
                      (fun locals (local, _) term -> Locals.add local term locals)
                      inside.locals inputs arguments;
                }
              in
              List.map (fun clause -> snd (specification_value context inside clause)) requires
          | _ -> [])
      | None -> [])
  | _ -> []

(* The type of a callee's parameter, by its position, with the call's type
   arguments. *)
let parameter_type context frame (invocation : Invocation.t) index =
  match invocation.callee with
  | Function { path; type_arguments } -> (
      match Interface.Impls.signature context.database path with
      | Some (signature : Types.signature) ->
          let types =
            (match signature.receiver with
              | Some ((Read | Mut | Own), ty) -> [ ty ]
              | Some (Static, _) | None -> [])
            @ List.map (fun (info : Types.parameter_info) -> info.type_) signature.parameters
          in
          Option.map
            (Types.substitute (callee_substitution frame signature type_arguments))
            (List.nth_opt types index)
      | None -> None)
  | _ -> None

(* A function-typed parameter passed on for another callee's parameter:
   that parameter's promise about its arguments must imply this one's
   [requires]. *)
let check_forwarded_callback context frame (site : Invocation.site) (invocation : Invocation.t)
    (passed : passed) local values =
  match own_callback context local with
  | Some (name, ({ inputs; requires = _ :: _ as requires } : Mir.callback)) -> (
      match parameter_type context frame invocation passed.position with
      | Some (Types.Function expected) when List.length expected.inputs = List.length inputs ->
          let arguments = callback_arguments context frame expected.inputs in
          let known = List.map (fun (passed : passed) -> (passed.position, passed.term)) values in
          check_callback_contract context frame
            (span_of frame.source site.origin)
            ~name inputs requires arguments
            ~promised:
              (Logic.conjunction
                 (callback_facts context frame invocation passed.position known arguments))
            ~why:"is passed for a parameter that may not promise its `requires`"
      | _ -> escaping_callback context frame local)
  | _ -> ()
