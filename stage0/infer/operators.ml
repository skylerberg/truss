(* Checks operators: [?], [with], prefix and binary operators (built in, or
   resolved to a trait method), and [any]. *)

open Syntax
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower
open State
open Instantiation
open Hooks
open Lookups
open Pattern_typing

(* [?] takes a [Result] whose error type is the function's error type, or an
   [Option] in a function that returns an [Option]. *)
let rec try_ state env (value : expression) (inner : expression) =
  let inner_type = normalize state (expression state env inner) in
  let output =
    match env.output with Some (Returns output) -> Some (normalize state output) | _ -> None
  in
  register_expression state value (fun () ->
      match output with
      | Some output ->
          Form.try_ state value inner ~output:(final_type state output)
            ~exited_tasks:(tasks_exited_by Return_exit env.enclosing)
      | None -> bug "`?` where nothing is returned");
  match (inner_type, output) with
  | ( Types.Named { path; arguments = [ Types.Type ok; Types.Type error ] },
      Some (Types.Named { path = output_path; arguments = [ _; Types.Type output_error ] }) )
    when Well_known.is Result path && Well_known.is Result output_path ->
      if not (unify state error output_error) then
        report state Wrong_try value.span
          (Printf.sprintf
             "`?` returns the error unchanged, so it needs the function's error type `%s`, not \
              `%s`. Convert it first with `map_error`."
             (show state output_error) (show state error));
      ok
  | ( Types.Named { path; arguments = [ Types.Type some ] },
      Some (Types.Named { path = output_path; _ }) )
    when Well_known.is Option path && Well_known.is Option output_path ->
      some
  | (Types.Error _ | Types.Hole), _ -> inner_type
  | _ ->
      error state Wrong_try value.span
        "`?` works on a `Result` in a function that returns a `Result`, and on an `Option` in a \
         function that returns an `Option`. Convert between them with `ok_or` or `ok`."

(* [base with (field: value)]: a copy of a record with some fields replaced. *)
and with_ state env (value : expression) (base : expression) updates =
  let base_type = normalize state (expression state env base) in
  (match base_type with
  | Types.Named { path; _ }
    when not (Members.fields_visible state.database ~package:state.package path) ->
      report state Private_field value.span
        (Printf.sprintf "`%s` is opaque, so only its own package can update its fields."
           (Types.show base_type))
  | _ -> ());
  List.iter
    (fun (update : update) ->
      match update.kind with
      | Update { field = first; path = rest; value = new_value } -> (
          let rec field_type type_ (names : name list) =
            match (names, normalize state type_) with
            | [], type_ -> Some type_
            | (name : name) :: rest, (Types.Named { path; arguments } as record_type) -> (
                match Members.fields state.database path arguments with
                | Some fields -> (
                    match
                      List.find_opt
                        (fun (written : Types.field) -> written.field_name = name.text)
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
                            mismatch state first.span ~expected:type_ ~actual:local.type_
                      | None -> ())
                  | _ -> ()))
          | None -> Option.iter (fun new_value -> ignore (expression state env new_value)) new_value
          )
      | Update_error -> ())
    updates;
  register_expression state value (fun () ->
      let base = build_expression state base in
      Record_update
        {
          base;
          updates =
            List.filter_map
              (fun (update : update) ->
                match update.kind with
                | Update { field = first; path = rest; value = new_value } ->
                    Some
                      ( List.map (fun (name : name) -> name.text) (first :: rest),
                        match (new_value, target state first) with
                        | Some new_value, _ -> build_expression state new_value
                        | None, Some (Local id) ->
                            synthetic_expression state ~origin:update.id (Form.local_type state id)
                              (Form.local_use state ~origin:update.id id)
                        | None, _ -> bug "`with (%s)` names no local" first.text )
                | Update_error -> None)
              updates;
        });
  base_type

and prefix state env ?expected (value : expression) operator (inner : expression) =
  match operator with
  | Not ->
      check state env inner Types.bool;
      built_in_operator state value [ inner ] Types.bool;
      register_expression state value (fun () -> Not (build_expression state inner));
      Types.bool
  | Complement ->
      let type_ = expression state env ?expected inner in
      built_in_operator state value [ inner ] type_;
      register_expression state value (fun () -> Form.operator state value Complement [ inner ]);
      if
        not
          (integer_type state (normalize state type_)
          ||
          match resolve state type_ with
          | Types.Literal (Integer_literal, _) -> true
          | _ -> false)
      then
        report state No_impl value.span
          (Printf.sprintf "`~` works on built-in integers, not `%s`." (show state type_));
      type_
  | Negate -> (
      match inner.kind with
      | Integer number ->
          (* A negated literal is range-checked after the negation, so
             [-128] fits an [Int8]. *)
          (* The negated literal is one literal: [-128]. *)
          state.tables.literals.(inner.id) <- Some (Integer_value number);
          state.tables.literals.(value.id) <- Some (Integer_value (Z.neg number));
          register_expression state value (fun () -> Form.numeric_literal state value.id);
          let type_ = literal_type state ~expected Integer_literal in
          record state inner type_;
          defer state (fun () ->
              match resolve state type_ with
              | Types.Literal _ | Types.Variable _ -> false
              | resolved ->
                  (* A negated literal of an unsigned type gets only this
                     diagnostic, and no second one for a value out of range. *)
                  if
                    integer_type state resolved
                    && (not (signed_type state resolved))
                    && not (Z.equal number Z.zero)
                  then
                    report state Negated_unsigned value.span
                      (Printf.sprintf "`%s` is unsigned, so it cannot be negated."
                         (Types.show resolved))
                  else check_literal_fits state value (Z.neg number) type_;
                  true);
          type_
      | _ ->
          let type_ = expression state env ?expected inner in
          let resolved = normalize state type_ in
          if resolved = Types.Hole then Types.Hole
          else if integer_type state resolved && not (signed_type state resolved) then begin
            report state Negated_unsigned value.span
              (Printf.sprintf "`%s` is unsigned, so it cannot be negated." (Types.show resolved));
            type_
          end
          else if env.specification && (integer_type state resolved || resolved = Types.Integer)
          then begin
            register_expression state value (fun () -> Form.operator state value Negate [ inner ]);
            Types.Integer
          end
          else begin
            Form.register_call state value;
            operator_call
              ~operands:
                [
                  {
                    Tables.expression = inner.id;
                    parameter_index = 0;
                    mode = Types.Read;
                    mark = None;
                  };
                ]
              state value ~trait:(Well_known.path Negate) ~method_:"negate" ~left:type_ ~right:None
          end)

(* An operator that resolves to a trait method. The [impl] is found once the
   types of both operands are inferred, and the result type is the [impl]'s
   [Output]. *)
and operator_call ?(operands = []) state (value : expression) ~trait ~method_ ~left ~right =
  let arguments = match right with Some right -> [ Types.Type right ] | None -> [] in
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
        arguments = operands;
        omitted_defaults = [];
        uses = [];
        callee_result = result;
      };
  defer state (fun () ->
      let left = normalize state left in
      let reference = Unify.zonk_trait state.unifier reference in
      if
        Types.contains_unsolved left
        || List.exists
             (function Types.Type type_ -> Types.contains_unsolved type_ | _ -> false)
             reference.trait_arguments
      then false
      else begin
        (match implements state left reference with
        | Some evidence ->
            let output = associated state left reference "Output" ~at:value.span in
            (* The result type that the statement inferred must unify with
               the [Output] of the [impl]. *)
            let decided = zonk state result in
            if not (unify state result output) then
              report state Mismatch value.span
                (Printf.sprintf "This operator gives `%s`, and `%s` is expected."
                   (Types.show (zonk state output))
                   (Types.show decided));
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
                  arguments = operands;
                  omitted_defaults = [];
                  uses = [];
                  callee_result = output;
                }
        | None ->
            let unknown =
              if Types.is_error left then left
              else
                error state No_impl value.span
                  (Printf.sprintf "`%s` does not implement `%s`, so the operator does not apply."
                     (Types.show left) (Types.show_trait reference))
            in
            ignore (unify state result unknown));
        true
      end);
  result

(* A literal operand takes the type of the other operand if the literal can
   have that type, as an untyped constant does in Go. *)
and literal_operands state ~left ~right =
  match (resolve state left, resolve state right) with
  | Types.Literal (kind, _), other when Unify.literal_fits state.unifier kind other ->
      ignore (unify state left right)
  | other, Types.Literal (kind, _) when Unify.literal_fits state.unifier kind other ->
      ignore (unify state left right)
  | Types.Literal (left_kind, _), Types.Literal (right_kind, _) when left_kind = right_kind ->
      ignore (unify state left right)
  | _ -> ()

(* [&&], [||], [!], [~], the bitwise operators, and the shifts are built in
   on built-in types. *)
and built_in_operator state (value : expression) (operands : expression list) result =
  state.tables.calls.(value.id) <-
    Some
      {
        callee = Built_in_operator;
        arguments =
          List.mapi
            (fun index (operand : expression) ->
              { Tables.expression = operand.id; parameter_index = index; mode = Read; mark = None })
            operands;
        omitted_defaults = [];
        uses = [];
        callee_result = result;
      }

and is_hole state type_ = resolve state type_ = Types.Hole

(* Checks both operands, the right against the type of the left. Returns
   whether the type of either is a hole left by a [todo]. *)
and operands_hole state env (left : expression) (right : expression) =
  let left_type = expression state env left in
  let right_type = expression state env ~expected:left_type right in
  is_hole state left_type || is_hole state right_type

and is_string state type_ =
  let type_ = normalize state type_ in
  Types.is_well_known String type_ || Types.is_well_known String_slice type_

and binary state env ?expected (value : expression) operator (left : expression)
    (right : expression) =
  match operator with
  | And | Or | Implies ->
      if operator = Implies && not env.specification then
        report state Specification_only value.span
          "`==>` is only for specifications and the bodies of functions for specifications only; \
           in code, write `!a || b`.";
      check state env left Types.bool;
      check state env right Types.bool;
      built_in_operator state value [ left; right ] Types.bool;
      register_expression state value (fun () ->
          let first = build_expression state left in
          let second = build_expression state right in
          match operator with
          | And -> And (first, second)
          | Or -> Or (first, second)
          | _ -> Implies (first, second));
      Types.bool
  | Bit_and | Bit_or | Bit_xor ->
      let left_type = expression state env ?expected left in
      let right_type = expression state env ~expected:left_type right in
      built_in_operator state value [ left; right ] left_type;
      register_expression state value (fun () ->
          Form.operator state value (Form.operation_of operator) [ left; right ]);
      literal_operands state ~left:left_type ~right:right_type;
      if not (unify state left_type right_type) then
        mismatch state right.span ~expected:left_type ~actual:right_type;
      defer state (fun () ->
          match normalize state left_type with
          | Types.Literal _ | Types.Variable _ -> false
          | resolved ->
              if not (integer_type state resolved || Types.is_error resolved) then
                report state No_impl value.span
                  (Printf.sprintf "Bitwise operators work on built-in integers, not `%s`."
                     (Types.show resolved));
              true);
      left_type
  | Shift_left | Shift_right ->
      let left_type = expression state env ?expected left in
      let right_type = expression state env right in
      built_in_operator state value [ left; right ] left_type;
      register_expression state value (fun () ->
          Form.operator state value (Form.operation_of operator) [ left; right ]);
      (match resolve state right_type with
      | Types.Literal (Integer_literal, _) -> ignore (unify state right_type (Types.builtin USize))
      | _ -> ());
      defer state (fun () ->
          match (normalize state left_type, normalize state right_type) with
          | (Types.Literal _ | Types.Variable _), _ | _, (Types.Literal _ | Types.Variable _) ->
              false
          | left_resolved, right_resolved ->
              if not (integer_type state left_resolved || Types.is_error left_resolved) then
                report state No_impl left.span
                  (Printf.sprintf "Shifts work on built-in integers, not `%s`."
                     (Types.show left_resolved));
              if
                not
                  ((integer_type state right_resolved && not (signed_type state right_resolved))
                  || Types.is_error right_resolved)
              then
                report state Mismatch right.span
                  (Printf.sprintf "A shift amount is an unsigned integer, not `%s`."
                     (Types.show right_resolved));
              true);
      left_type
  | (Equal | Not_equal | Less | Less_equal | Greater | Greater_equal)
    when operands_hole state env left right ->
      register_expression state value (fun () -> Form.built_in_comparison state operator left right);
      Types.bool
  | Equal | Not_equal | Less | Less_equal | Greater | Greater_equal ->
      let left_type = Option.get state.tables.types.(left.id) in
      let right_type = Option.get state.tables.types.(right.id) in
      literal_operands state ~left:left_type ~right:right_type;
      let integers type_ =
        let type_ = normalize state type_ in
        integer_type state type_ || type_ = Types.Integer
        || match resolve state type_ with Types.Literal (Integer_literal, _) -> true | _ -> false
      in
      if env.specification && integers left_type && integers right_type then begin
        register_expression state value (fun () ->
            Form.built_in_comparison state operator left right);
        Types.bool
      end
      else begin
        register_expression state value (fun () -> Form.comparison state value operator left right);
        if not (unify state left_type right_type) then
          ignore (mismatched_operands state value left right ~left_type ~right_type);
        (* An ordering operator calls [compare] and tests the resulting
           [Ordering]. *)
        let trait, method_, result =
          match operator with
          | Equal | Not_equal -> (Well_known.path Equal, "equal", Types.bool)
          | _ -> (Well_known.path Ordered, "compare", Types.named (Well_known.path Ordering) [])
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
              arguments =
                [
                  { expression = left.id; parameter_index = 0; mode = Read; mark = None };
                  { expression = right.id; parameter_index = 1; mode = Read; mark = None };
                ];
              omitted_defaults = [];
              uses = [];
              callee_result = result;
            };
        resolve_evidence state value left_type (trait_reference trait);
        Types.bool
      end
  | (Add | Subtract | Multiply | Divide | Remainder) when operands_hole state env left right ->
      (* Any operation on a hole is accepted, and its type is a hole. *)
      register_expression state value (fun () ->
          Form.operator state value (Form.operation_of operator) [ left; right ]);
      Types.Hole
  | Add | Subtract | Multiply | Divide | Remainder ->
      let left_type = Option.get state.tables.types.(left.id) in
      let right_type = Option.get state.tables.types.(right.id) in
      literal_operands state ~left:left_type ~right:right_type;
      if operator = Add && (is_string state left_type || is_string state right_type) then begin
        (* The fix splices a plain string literal into the other string as
           written, between its quotes, so its escapes are kept. Any other
           operand is interpolated. A raw string cannot be spliced into an
           ordinary one, so then there is no fix. *)
        let piece (side : expression) =
          match side.kind with
          | String { tag = None; form = Ordinary; first; rest = []; _ } ->
              Some (source state first.span)
          | String _ -> None
          | _ -> Some ("${" ^ source state side.span ^ "}")
        in
        let fixes =
          match (piece left, piece right) with
          | Some left, Some right ->
              [
                fix "Join them with interpolation."
                  [ replace value.span (Printf.sprintf "\"%s%s\"" left right) ];
              ]
          | _ -> []
        in
        report state String_addition value.span ~fixes
          "Strings have no `+`. Join them with interpolation, or with methods such as `push`.";
        string_type
      end
      else begin
        let integers type_ =
          let type_ = normalize state type_ in
          integer_type state type_ || type_ = Types.Integer
          ||
          match resolve state type_ with
          | Types.Literal (Integer_literal, _) -> true
          | _ -> false
        in
        if env.specification && integers left_type && integers right_type then begin
          ignore
            (match resolve state left_type with
            | Types.Literal _ -> unify state left_type Types.Integer
            | _ -> true);
          ignore
            (match resolve state right_type with
            | Types.Literal _ -> unify state right_type Types.Integer
            | _ -> true);
          register_expression state value (fun () ->
              Form.operator state value (Form.operation_of operator) [ left; right ]);
          Types.Integer
        end
        else
          let same_builtin =
            match (resolve state left_type, resolve state right_type) with
            | Types.Literal (left_kind, _), Types.Literal (right_kind, _) -> left_kind = right_kind
            | left_resolved, right_resolved ->
                (integer_type state left_resolved || Types.is_float_type left_resolved)
                && Types.equal left_resolved right_resolved
          in
          let trait, method_ =
            match operator with
            | Add -> (Well_known.path Add, "add")
            | Subtract -> (Well_known.path Subtract, "subtract")
            | Multiply -> (Well_known.path Multiply, "multiply")
            | Divide -> (Well_known.path Divide, "divide")
            | _ -> (Well_known.path Remainder, "remainder")
          in
          if
            (integer_type state (normalize state left_type)
            && integer_type state (normalize state right_type))
            && not (Types.equal (normalize state left_type) (normalize state right_type))
          then Types.Error (mismatched_operands state value left right ~left_type ~right_type)
          else begin
            Form.register_call state value;
            let result =
              operator_call
                ~operands:
                  [
                    {
                      Tables.expression = left.id;
                      parameter_index = 0;
                      mode = Types.Read;
                      mark = None;
                    };
                    {
                      Tables.expression = right.id;
                      parameter_index = 1;
                      mode = Types.Read;
                      mark = None;
                    };
                  ]
                state value ~trait ~method_ ~left:left_type ~right:(Some right_type)
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
  if integer_type state left_type && integer_type state right_type then begin
    let from = trait_reference ~arguments:[ Types.Type right_type ] (Well_known.path From) in
    let fixes =
      if Option.is_some (implements state left_type from) then
        [
          fix
            (Printf.sprintf "Convert the right side to `%s`." (Types.show left_type))
            [
              replace right.span
                (Printf.sprintf "%s.from(%s)" (Types.show left_type) (source state right.span));
            ];
        ]
      else if
        Option.is_some
          (implements state right_type
             (trait_reference ~arguments:[ Types.Type left_type ] (Well_known.path From)))
      then
        [
          fix
            (Printf.sprintf "Convert the left side to `%s`." (Types.show right_type))
            [
              replace left.span
                (Printf.sprintf "%s.from(%s)" (Types.show right_type) (source state left.span));
            ];
        ]
      else []
    in
    reported state Mismatched_integers value.span ~fixes
      (Printf.sprintf
         "Integer types never convert implicitly: this compares or combines `%s` with `%s`."
         (Types.show left_type) (Types.show right_type))
  end
  else mismatched state right.span ~expected:left_type ~actual:right_type

(* [any value] *)
and any_ state env ?expected (value : expression) (inner : expression) =
  match Option.map (normalize state) expected with
  | Some (Types.Any trait as any_type) ->
      let inner_type = expression state env inner in
      register_expression state value (fun () ->
          let inner = build_expression state inner in
          match (Form.type_of state value, implements state inner.type_ trait) with
          | Types.Any trait, Some implementation ->
              To_any { value = inner; trait; evidence = Form.evidence (evidence_of implementation) }
          | _ -> bug "`any` of a value whose type does not implement the trait");
      require state ~at:value.span inner_type trait ~unmet:(fun inner_type other ->
          report state No_impl value.span
            (match other with
            | None ->
                Printf.sprintf "`%s` does not implement `%s`." (Types.show inner_type)
                  (Types.show_trait trait)
            | Some (name, associated_type) ->
                Printf.sprintf "`%s` is expected, and the `%s` of `%s` is `%s`."
                  (Types.show any_type) name (Types.show inner_type) (show state associated_type)));
      (* Code that holds the [any] value calls its methods without the
         capabilities of the type that it hides, so that type's associated
         capability sets must be empty. Otherwise a method would use a
         capability that no caller declares. *)
      defer state (fun () ->
          let inner_type = normalize state inner_type in
          Unify.unknowns state.unifier inner_type = []
          && begin
            if Option.is_some (implements state inner_type trait) then
              List.iter
                (fun (bound : Types.trait_reference) ->
                  match Query.demand state.database Environment.trait_interface bound.trait with
                  | Some interface ->
                      List.iter
                        (fun name ->
                          match
                            Impls.capability_set state.database ~bounds:(bounds state) inner_type
                              { bound with associated = [] } name
                          with
                          | [] -> ()
                          | set ->
                              report state No_impl value.span
                                (Printf.sprintf
                                   "`%s` cannot be an `%s`: its `%s` is %s, and code that holds an \
                                    `any` value has no capability to give to its methods."
                                   (Types.show inner_type) (Types.show any_type) name
                                   (String.concat ", "
                                      (List.map
                                         (fun capability ->
                                           "`" ^ Types.show_capability capability ^ "`")
                                         set))))
                        interface.associated_capabilities
                  | None -> ())
                (Interface.Properties.bound_closure state.database ~self:inner_type trait);
            true
          end);
      any_type
  | _ ->
      ignore (expression state env inner);
      error state Cannot_infer value.span
        "`any value` needs an expected type `any Trait`, from an annotation or a parameter."
