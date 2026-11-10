(* Checking bodies: bidirectional, one statement at a time.

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
      match env.self with
      | Some self -> self
      | None ->
          error state Not_a_value value.span
            "`self` is a method's receiver, and this is not a method that takes one.")
  | Self_type_value ->
      error state Not_a_value value.span
        "`Self` is a type. Build a value of it, or call one of its methods."
  | Name path -> (
      match head state value with
      | Some found -> named state env value found
      | None -> bug "the name `%s` is not resolved" path.last.text)
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
          if not env.specification then
            report state Specification_only value.span
              "A quantifier over a whole type cannot run, so it is only for specifications and the \
               bodies of functions for specifications only. Quantify over a range or a collection.";
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
  | Expression_error -> T.Error (Resolve.Parts.error_node value.span)

(* [receiver.name] read as a value: a field, or a static member of a type. *)
and member_value state env (value : expression) (base : expression) (member : name) =
  match static_ state base with
  | Some (Static_type type_) -> static_member state value type_ member
  | Some (Static_trait _ | Static_capability _) ->
      error state Not_a_value value.span
        (Printf.sprintf "`%s` is a method; call it with `(...)`." member.text)
  | None -> (
      let base_type = normalize state (expression state env base) in
      match base_type with
      | T.Error _ | T.Hole -> base_type
      | _ -> field state value base_type member)

and bracket state env ?expected (value : expression) (base : expression) items =
  match state.resolved.brackets.(value.id) with
  | Some Type_arguments -> (
      (* A name with type arguments, as a value. *)
      match head state value with
      | Some found -> named state env value found
      | None -> bug "type arguments are written after what is not a name")
  | Some Method_bracket -> (
      (* Resolution cannot tell a field from a method before the dot; a
         field followed by brackets is indexed. *)
      match base.kind with
      | Member (inner, member)
        when Option.is_none (static_ state inner) && is_field state env inner member ->
          index state env ?expected value base items
      | _ ->
          error state Not_a_value value.span
            "A method with type arguments is called: write `(...)` after it.")
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
          error state Not_indexable value.span
            "Strings cannot be indexed: say which you mean with `bytes()` or `characters()`."
      | T.Error _ | T.Hole -> base_type
      | _ ->
          error state Not_indexable value.span
            (Printf.sprintf "`%s` cannot be sliced." (show state base_type)))
  | [ Item key ] -> (
      if is_named string_path base_type || is_named string_slice_path base_type then begin
        error state Not_indexable value.span
          "Strings cannot be indexed: say which you mean with `bytes()` or `characters()`."
      end
      else
        match base_type with
        | T.Error _ | T.Hole ->
            ignore (expression state env key);
            base_type
        | _ -> (
            let index_trait = trait_reference (core "Index") in
            match implements state base_type index_trait with
            | Some evidence ->
                let associated name = associated state base_type index_trait name ~at:value.span in
                let key_type = associated "Key" and output = associated "Output" in
                let key_conversion : C.conversion option =
                  if env.specification then
                    let found = expression state env ~expected:key_type key in
                    if resolve state found = T.Integer && T.is_integer_type key_type then begin
                      state.obligations <-
                        Integer_fits { expression = key.id; type_ = key_type } :: state.obligations;
                      Some From_integer
                    end
                    else if
                      T.is_integer_type (normalize state found)
                      && resolve state key_type = T.Integer
                    then
                      (* A built-in integer is an [Integer] in a specification. *)
                      Some To_integer
                    else begin
                      coerce state key ~found ~expected:key_type;
                      None
                    end
                  else begin
                    check state env key key_type;
                    None
                  end
                in
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
                          {
                            expression = key.id;
                            parameter = 1;
                            mode = Read;
                            conversion = key_conversion;
                          };
                        ];
                      defaults_left_out = [];
                      uses = [];
                      capability_arguments = [];
                      result = output;
                    };
                output
            | None ->
                ignore (expression state env key);
                error state Not_indexable value.span
                  (Printf.sprintf "`%s` cannot be indexed." (show state base_type))))
  | _ -> error state Not_indexable value.span "An index is one value."

let () =
  Hooks.expression_hook := expression;
  Hooks.check_hook := check
