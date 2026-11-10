(* Values built from parts: strings and tagged templates, collection
   literals, lambdas, [if], and [match]. *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower
open State
open Hooks
open Lookups
open Pattern_typing
open Statements

let rec string_literal state env ?expected (literal : string_literal) =
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
            { C.expression = written.id; parameter = index; mode = T.Read; conversion = None })
          arguments;
      defaults_left_out = [];
      uses = [];
      capability_arguments = [];
      result;
    }
  in
  match literal.tag with
  | None ->
      (* Each part of a plain string is written out with its [Display]. *)
      List.iteri
        (fun index ((part : expression), part_type) ->
          defer state (fun () ->
              let part_type = normalize state part_type in
              if T.contains_unsolved part_type then false
              else begin
                let display = trait_reference (core "Display") in
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
          (match expected with
          | Some expected -> ignore (unify state tag_type expected)
          | None -> ());
          let template_trait = trait_reference (standard [ "text" ] "FromTemplate") in
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
                    (* Each part becomes the tag's [Part] through [From], chosen by
                       the part's type. *)
                    List.iteri
                      (fun index ((part_expression : expression), part_type) ->
                        let part_type = normalize state part_type in
                        if not (T.equal part_type part) then
                          let from =
                            trait_reference ~arguments:[ T.Type part_type ] (core "From")
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
      when Path.equal path set_path || Path.equal path list_path || Path.equal path sequence_path
           || Path.equal path finite_set_path ->
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
        (element, fun element -> T.Named { path = list_path; arguments = [ T.Type element ] })
  in
  List.iter (fun item -> check state env item element) items;
  make element

and map_literal state env ?expected (_ : expression) entries =
  let key, value_type =
    match Option.map (normalize state) expected with
    | Some (T.Named { path; arguments = [ T.Type key; T.Type value_type ] })
      when Path.equal path map_path || Path.equal path finite_map_path ->
        (key, value_type)
    | _ -> (fresh state, fresh state)
  in
  let map_type =
    match Option.map (normalize state) expected with
    | Some (T.Named { path; _ }) when Path.equal path finite_map_path -> finite_map_path
    | _ -> map_path
  in
  List.iter
    (fun (entry_key, entry_value) ->
      check state env entry_key key;
      check state env entry_value value_type)
    entries;
  T.Named { path = map_type; arguments = [ T.Type key; T.Type value_type ] }

(* Lambdas: their types come only from where they are used. *)
and lambda state env ?expected (value : expression) parameters body =
  let references_before = state.references in
  state.lambdas <- value.span :: state.lambdas;
  let expected = Option.map (normalize state) expected in
  (* A lambda whose types are not known is still checked, for its own
     errors, with what it binds as unknown as it is. *)
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
        let lambda_env = { env with output = Some (Returns output) } in
        let body_type = block_value state lambda_env ~expected:output body in
        ignore
          (convert state lambda_env ?expression:(block_end body) body.span ~found:body_type
             ~expected:output);
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

and if_ state env ?expected (test : expression) then_ else_ =
  let condition_type = in_statement state env test.span (fun () -> expression state env test) in
  ignore (coerce state env test ~found:condition_type ~expected:T.bool);
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

(* The expression a block ends with, whose value is the block's. *)
and block_end (written : block) =
  match List.rev written.statements with
  | { kind = Expression value; _ } :: _ -> Some value.id
  | _ -> None

(* The type of branches together: arms of type [Never] are left out. Each
   branch's value, the expression it ends with, meets the type expected of
   them all, and with none expected the branches have one type. *)
and join state env ~expected branches =
  let live = List.filter (fun (type_, _, _) -> resolve state type_ <> T.Never) branches in
  match (live, expected) with
  | [], _ -> T.Never
  | _, Some expected ->
      List.iter
        (fun (found, span, expression) ->
          ignore (convert state env ?expression span ~found ~expected))
        live;
      expected
  | (first, _, _) :: rest, None ->
      List.iter
        (fun (type_, span, _) ->
          if not (unify state first type_) then mismatch state span ~expected:first ~found:type_)
        rest;
      first

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
  (* The values a [match] matches settle before its arms, as a header. *)
  let types =
    List.map
      (fun (scrutinee : expression) ->
        (scrutinee, in_statement state env scrutinee.span (fun () -> expression state env scrutinee)))
      scrutinees
  in
  let mode_of (scrutinee : expression) =
    match scrutinee.kind with
    | Mode (Own, _) -> T.Own
    | Mode (Mut, _) -> T.Mut
    | _ -> if borrowed state scrutinee then T.Read else T.Own
  in
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
              pattern state env written type_ ~mode:(mode_of scrutinee))
            arm.patterns types;
        Option.iter (fun guard -> check state env guard T.bool) arm.guard;
        ( arm_value state env ?expected arm.body,
          arm.body.span,
          match arm.body.kind with Expression value -> Some value.id | _ -> None ))
      arms
  in
  join state env ~expected branch_types

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
  | T.Error _ | T.Hole -> collection_type
  | _ -> (
      match yielded state collection.span collection_type T.Read with
      | Some element -> element
      | None ->
          error state Not_indexable collection.span
            (Printf.sprintf "`%s` cannot be looped over." (T.show collection_type)))
