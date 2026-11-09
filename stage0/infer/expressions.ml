(* Checking bodies: bidirectional, one statement at a time. See
   TYPECHECKER.md, "Checking bodies" and "Patterns".

   An expression is either checked against an expected type, which flows
   in from annotations, parameters, and operators, or has its type
   inferred. Unknown types within a statement are inference variables.
   When a statement ends, its literals take their defaults, every variable
   it made must be solved, and the types it recorded are final. Variables
   are numbered across the definition, so a statement inside a lambda leaves
   the enclosing statement's variables for that statement to settle. *)

(* This file holds the dispatch on an expression's kind, literals, names,
   members, and brackets. The other parts are files of their own, in the
   order they call each other: [Lookups], [Pattern_typing], [Calls],
   [Methods], [Operators], [Statements], and [Values]. A part calls one
   after it through [Hooks], which this file sets. *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower
open State
open Lookups
open Pattern_typing
open Methods
open Operators
open Statements
open Values

let rec expression state env ?expected (value : expression) : T.ty =
  let type_ = expression_kind state env ?expected value in
  record state value type_;
  type_

and check state env (value : expression) (expected : T.ty) =
  let found = expression state env ~expected value in
  coerce state value ~found ~expected

and expression_kind state env ?expected (value : expression) : T.ty =
  match value.kind with
  | Integer number ->
      state.tables.literals.(value.id) <- Some (Integer_value number);
      let type_ = literal_type state ~expected Integer_literal in
      check_literal_fits state value number type_;
      type_
  | Float number ->
      let type_ = literal_type state ~expected Float_literal in
      let significand = number.significand and exponent = number.exponent in
      (* Rounded once, from the exact decimal, to the type the statement
         decides. *)
      defer state (fun () ->
          match resolve state type_ with
          | T.Literal _ | T.Variable _ -> false
          | resolved ->
              let rounded =
                if T.is_builtin Float32 resolved then Literals.float32 ~significand ~exponent
                else Literals.float64 ~significand ~exponent
              in
              (match rounded with
              | Some rounded_value ->
                  state.tables.literals.(value.id) <- Some (Float_value rounded_value)
              | None ->
                  report state Literal_out_of_range value.span
                    (Printf.sprintf
                       "This literal is too large for `%s`; it would round to infinity."
                       (T.show resolved)));
              true);
      type_
  | String literal -> (
      match character_tag state literal with
      | Some builtin -> character_literal state value.id literal builtin
      | None -> string_literal state env ?expected literal)
  | True | False -> T.bool
  | Todo -> ( match expected with Some expected -> expected | None -> T.Hole)
  | Unreachable | Break | Continue -> T.Never
  | Self_value -> (
      (* A lambda that reads [self] captures it, named by the definition's id. *)
      state.references <- state.definition.id :: state.references;
      match env.self with Some self -> self | None -> T.Error)
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
      let type_ = expression state env ?expected inner in
      if mode = Mut && Option.is_none (marked_call state inner) then mutable_place state inner;
      type_
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

(* Explicit type arguments give the function's own generic parameters, in
   order, after those of a method's type head: exactly one for each, of its
   kind. *)

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
                        [
                          { expression = base.id; parameter = 0; mode = Read; conversion = None };
                          { expression = key.id; parameter = 1; mode = Read; conversion = None };
                        ];
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

let () =
  Hooks.expression_hook := expression;
  Hooks.check_hook := check
