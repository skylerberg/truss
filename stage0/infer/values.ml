(* Checks expressions that build values: strings and tagged strings,
   collection literals, lambdas, [if], and [match]. *)

open Syntax
module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower
open State
open Hooks
open Lookups
open Pattern_typing
open Statements

let rec string_literal state env ?expected (value : expression) (literal : string_literal) =
  let parts = List.map (fun (part, _) -> (part, expression state env part)) literal.rest in
  let template : C.template =
    {
      from_template = None;
      part_conversions = List.map (fun _ -> None) parts;
      interpolated = parts <> [];
    }
  in
  state.tables.templates.(literal.id) <- Some template;
  let set_part index call =
    match state.tables.templates.(literal.id) with
    | Some template ->
        state.tables.templates.(literal.id) <-
          Some
            {
              template with
              part_conversions =
                List.mapi
                  (fun other existing -> if other = index then Some call else existing)
                  template.part_conversions;
            }
    | None -> ()
  in
  let trait_call trait name receiver self_type evidence arguments result : C.call =
    {
      callee =
        Trait_method
          { trait; name; receiver; self_type; type_arguments = []; evidence = evidence_of evidence };
      arguments =
        List.mapi
          (fun index (written : expression) ->
            { C.expression = written.id; parameter_index = index; mode = T.Read; mark = None })
          arguments;
      omitted_defaults = [];
      uses = [];
      callee_result = result;
    }
  in
  match literal.tag with
  | None ->
      register_expression state value (fun () ->
          Form.untagged_string state ~origin:value.id literal);
      (* Each interpolated value of an untagged string is converted with its
         [Display]. *)
      List.iteri
        (fun index ((part : expression), part_type) ->
          defer state (fun () ->
              let part_type = normalize state part_type in
              if T.contains_unsolved part_type then false
              else begin
                let display = trait_reference (Well_known.path Display) in
                (match implements state part_type display with
                | Some evidence ->
                    set_part index
                      (trait_call display "display" Path.Read part_type evidence [ part ] T.unit)
                | None ->
                    report state No_impl part.span
                      (Printf.sprintf
                         "`%s` does not implement `Display`, so it cannot be interpolated."
                         (T.show part_type)));
                true
              end))
        parts;
      string_type
  | Some tag -> (
      match target state tag.last with
      | Some (Definition (Type, tag_path)) ->
          let tag_type =
            T.Named { path = tag_path; arguments = instantiate_type state tag.last.span tag_path }
          in
          (* Each part goes into the template that the tag receives. *)
          List.iter (fun (part, part_type) -> check_owned state env part part_type) parts;
          (match expected with
          | Some expected -> ignore (unify state tag_type expected)
          | None -> ());
          let template_trait = trait_reference (Well_known.path From_template) in
          let part_type = ref None in
          register_expression state value (fun () ->
              match !part_type with
              | Some part -> Form.tagged_string state value literal ~part:(final state part)
              | None -> bug "a tagged string's part type was not worked out");
          defer state (fun () ->
              let tag_type = normalize state tag_type in
              if T.contains_unsolved tag_type then false
              else begin
                (match implements state tag_type template_trait with
                | Some evidence ->
                    (match state.tables.templates.(literal.id) with
                    | Some template ->
                        state.tables.templates.(literal.id) <-
                          Some
                            {
                              template with
                              from_template =
                                Some
                                  (trait_call template_trait "from_template" Path.Static tag_type
                                     evidence [] tag_type);
                            }
                    | None -> ());
                    let part = associated state tag_type template_trait "Part" ~at:literal.span in
                    part_type := Some part;
                    (* Each interpolated value is converted to the tag's
                       [Part] type with [From], selected by the value's
                       type. *)
                    List.iteri
                      (fun index ((part_expression : expression), part_type) ->
                        let part_type = normalize state part_type in
                        if not (T.equal part_type part) then
                          let from =
                            trait_reference ~arguments:[ T.Type part_type ] (Well_known.path From)
                          in
                          match implements state part from with
                          | Some evidence ->
                              set_part index
                                (trait_call from "from" Path.Static part evidence
                                   [ part_expression ] part)
                          | None ->
                              report state No_impl part_expression.span
                                (Printf.sprintf "`%s` cannot become a `%s`, the part type of `%s`."
                                   (T.show part_type) (T.show part) (T.show tag_type)))
                      parts
                | None ->
                    if not (T.is_error tag_type) then
                      report state No_impl literal.span
                        (Printf.sprintf
                           "`%s` does not implement `FromTemplate`, so it is not a tag."
                           (T.show tag_type)));
                true
              end);
          tag_type
      | Some (Unknown report) -> T.Error report
      | _ -> error state Not_a_type tag.last.span "A string's tag is a type.")

and list_literal state env ?expected (value : expression) items =
  let expected = Option.map (normalize state) expected in
  let element, make =
    match expected with
    | Some (T.Named { path; arguments = T.Type element :: rest })
      when Well_known.is Set path || Well_known.is List path || Well_known.is Sequence path
           || Well_known.is Finite_set path ->
        (element, fun element -> T.Named { path; arguments = T.Type element :: rest })
    | Some (T.Named { path; arguments = [ T.Type element; count ] })
      when Intrinsic.builtin_of_path path = Some Array ->
        (match count with
        | T.Value (Known count) when (not (Z.fits_int count)) || Z.to_int count <> List.length items
          ->
            report state Mismatch value.span
              (Printf.sprintf "This array has %d elements, and its type says %s."
                 (List.length items) (Z.to_string count))
        | _ -> ());
        (element, fun element -> T.Named { path; arguments = [ T.Type element; count ] })
    | _ ->
        let element = fresh state in
        ( element,
          fun element -> T.Named { path = Well_known.path List; arguments = [ T.Type element ] } )
  in
  List.iter (fun item -> check state env item element) items;
  List.iter (fun item -> check_owned state env item element) items;
  register_expression state value (fun () ->
      Form.collection_literal state value (List.map (build_expression state) items));
  make element

and map_literal state env ?expected (value : expression) entries =
  let key, value_type =
    match Option.map (normalize state) expected with
    | Some (T.Named { path; arguments = [ T.Type key; T.Type value_type ] })
      when Well_known.is Map path || Well_known.is Finite_map path ->
        (key, value_type)
    | _ -> (fresh state, fresh state)
  in
  let map_type =
    match Option.map (normalize state) expected with
    | Some (T.Named { path; _ }) when Well_known.is Finite_map path -> Well_known.path Finite_map
    | _ -> Well_known.path Map
  in
  List.iter
    (fun (entry_key, entry_value) ->
      check state env entry_key key;
      check state env entry_value value_type;
      check_owned state env entry_key key;
      check_owned state env entry_value value_type)
    entries;
  register_expression state value (fun () ->
      Form.map_literal state value
        (List.map
           (fun (entry_key, entry_value) ->
             let entry_key = build_expression state entry_key in
             (entry_key, build_expression state entry_value))
           entries));
  T.Named { path = map_type; arguments = [ T.Type key; T.Type value_type ] }

(* A lambda. Its parameter types come only from the expected type. *)
and lambda state env ?expected (value : expression) parameters body =
  let references_before = state.references in
  state.lambdas <- value.span :: state.lambdas;
  let expected = Option.map (normalize state) expected in
  (* A lambda with no known parameter types is still checked, so that its
     own errors are reported. Its parameters get the unknown type. *)
  let untyped unknown =
    List.iter (fun written -> pattern state env written unknown ~mode:T.Read) parameters;
    ignore (block_value state env body);
    unknown
  in
  let result =
    match expected with
    | Some (T.Function function_type) when List.length function_type.inputs = List.length parameters
      ->
        List.iter2
          (fun written (mode, input) -> pattern state env written input ~mode)
          parameters function_type.inputs;
        let output = output_type function_type.output in
        let lambda_env = { env with output = Some (Returns output); enclosing = [] } in
        let body_type = block_value state lambda_env ~expected:output body in
        convert state lambda_env ?expression:(block_end body) body.span ~found:body_type
          ~expected:output;
        T.Function function_type
    | Some (T.Function function_type) ->
        untyped
          (error state Mismatch value.span
             (Printf.sprintf "This lambda takes %d parameters, and `%s` takes %d."
                (List.length parameters)
                (T.show (T.Function function_type))
                (List.length function_type.inputs)))
    | Some ((T.Error _ | T.Hole) as unknown) -> untyped unknown
    | _ ->
        untyped
          (error state Lambda_needs_type value.span
             "A lambda's parameter types come from where it is used, and nothing here gives them. \
              Give the `let` a function type, or the call type arguments.")
  in
  state.lambdas <- List.tl state.lambdas;
  (* The locals of the enclosing function that the lambda reads, in order of
     first use. *)
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
  register_expression state value (fun () ->
      let parameters = List.map (build_pattern state) parameters in
      Lambda
        {
          parameters;
          captures =
            List.filter_map
              (fun id : Core.capture option ->
                if id = state.definition.id then
                  Some { local = Self; type_ = Form.self_type state env }
                else if was_hole state (fun tables -> tables.local_types) id then None
                else Some { local = Named id; type_ = Form.local_type state id })
              captures;
          body = build_block state body;
          result =
            (match Form.type_of state value with
            | T.Function function_type -> output_type function_type.output
            | type_ -> bug "a lambda of type `%s`" (T.show type_));
        });
  result

and if_ state env ?expected (value : expression) (test : expression) then_ else_ =
  let condition_type = in_statement state env test.span (fun () -> expression state env test) in
  coerce state env test ~found:condition_type ~expected:T.bool;
  register_expression state value (fun () ->
      let condition = build_expression state test in
      let then_ = build_block state then_ in
      If
        {
          condition;
          then_;
          else_ =
            Option.map
              (function
                | Else block -> build_block state block
                | Else_if branch ->
                    let branch = build_expression state branch in
                    { Core.statements = []; value = Some branch; diverges = branch.type_ = T.Never })
              else_;
        });
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
      let else_type, else_span, else_end =
        match branch with
        | Else block -> (block_value state env ?expected block, block.span, block_end block)
        | Else_if branch_expression ->
            ( expression state env ?expected branch_expression,
              branch_expression.span,
              Some branch_expression.id )
      in
      join state env ~expected
        [ (then_type, then_.span, block_end then_); (else_type, else_span, else_end) ]

(* The last expression of a block, which is the block's value. *)
and block_end (written : block) =
  match List.rev written.statements with
  | { kind = Expression value; _ } :: _ -> Some value.id
  | _ -> None

(* The type of an [if] or a [match]: the common type of its branches. A
   branch of type [Never] does not count. If a type is expected, each
   branch's value is checked against it. Otherwise the branches must have
   the same type. *)
and join state env ~expected branches =
  let live = List.filter (fun (type_, _, _) -> resolve state type_ <> T.Never) branches in
  match (live, expected) with
  | [], _ -> T.Never
  | _, Some expected ->
      List.iter
        (fun (found, span, expression) -> convert state env ?expression span ~found ~expected)
        live;
      expected
  | (first, _, _) :: rest, None ->
      List.iter
        (fun (type_, span, _) ->
          if not (unify state first type_) then mismatch state span ~expected:first ~found:type_)
        rest;
      first

and match_ state env ?expected (value : expression) scrutinees arms =
  (* A [match] whose guards cover every case ends with [_ => unreachable].
     The prover shows that this arm is never reached. *)
  let guards_exhaustive =
    match List.rev arms with
    | { patterns; guard = None; body = { kind = Expression { kind = Unreachable; _ }; _ }; _ }
      :: earlier ->
        List.for_all (fun (written : pattern) -> written.kind = Wildcard) patterns
        && List.exists (fun (arm : arm) -> Option.is_some arm.guard) earlier
    | _ -> false
  in
  (* The types of the scrutinees are inferred before the arms are checked. *)
  let types =
    List.map
      (fun (scrutinee : expression) ->
        (scrutinee, in_statement state env scrutinee.span (fun () -> expression state env scrutinee)))
      scrutinees
  in
  register_expression state value (fun () ->
      let scrutinees =
        List.map
          (fun scrutinee ->
            Form.operand (scrutinee_mode state scrutinee) (build_expression state scrutinee))
          scrutinees
      in
      Match
        {
          scrutinees;
          arms =
            List.map
              (fun (arm : arm) : Core.arm ->
                let patterns = List.map (build_pattern state) arm.patterns in
                let guard = Option.map (build_expression state) arm.guard in
                {
                  patterns;
                  guard;
                  body =
                    build_block state
                      { statements = [ arm.body ]; span = arm.body.span; id = arm.body.id };
                  origin = arm.id;
                })
              arms;
          guards_exhaustive;
        });
  let branch_types =
    List.map
      (fun (arm : arm) ->
        if List.length arm.patterns <> List.length types then
          let unknown =
            error state Mismatch arm.span
              (Printf.sprintf "This arm has %d patterns, and the `match` has %d values."
                 (List.length arm.patterns) (List.length types))
          in
          List.iter (fun written -> pattern state env written unknown ~mode:T.Read) arm.patterns
        else
          List.iter2
            (fun written (scrutinee, type_) ->
              pattern state env written type_ ~mode:(scrutinee_mode state scrutinee))
            arm.patterns types;
        Option.iter (fun guard -> check state env guard T.bool) arm.guard;
        ( arm_value state env ?expected arm.body,
          arm.body.span,
          match arm.body.kind with Expression value -> Some value.id | _ -> None ))
      arms
  in
  join state env ~expected branch_types

(* The body of an arm is a statement. A body that is not an expression has
   type [Unit]. *)
and arm_value state env ?expected (body : statement) =
  match body.kind with
  | Expression value -> expression state env ?expected value
  | _ ->
      ignore (statement state env body ~last:false);
      T.unit

(* The element type of a quantifier's range or collection. In executable
   code, a quantifier over a collection is a loop, so the call of the
   collection's [each] is recorded for the quantifier, as for a [for] loop. *)
and element_of_collection state env ~(quantifier : expression) (collection : expression) =
  let collection_type = normalize state (expression state env collection) in
  match collection_type with
  | T.Named { path; arguments = [ T.Type element ] } when Well_known.is Range path -> element
  | T.Error _ | T.Hole -> collection_type
  | _ -> (
      match each_call state collection.span collection_type T.Read with
      | Some (call, element) ->
          if runs env then
            state.tables.loops.(quantifier.id) <- Some (Yielding { call; mode = Read });
          element
      | None ->
          error state Not_indexable collection.span
            (Printf.sprintf "`%s` cannot be looped over." (T.show collection_type)))
