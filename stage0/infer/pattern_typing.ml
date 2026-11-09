(* Typing patterns: what each binds and with which mode, constants and
   literals in patterns, and the values of character and byte literals. See
   TYPECHECKER.md, "Typing patterns". *)

open Syntax
module T = Types
module C = Checked
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Properties = Interface.Properties
module Lower = Interface.Lower
open State

let rec binding_pattern state env written type_ ~mutable_ ~mode =
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
      | Some (Local id) -> (
          (* A later alternative's name binds what the first one's does, with
             the same type. *)
          match Hashtbl.find_opt state.locals id with
          | Some local ->
              if not (unify state local.type_ type_) then
                report state Mismatch bound.span
                  (Printf.sprintf
                     "`%s` is a `%s` in the first alternative, and a `%s` here; every alternative \
                      binds it with one type."
                     bound.text (show state local.type_) (show state type_))
          | None -> ())
      | Some (Definition path) -> constant_pattern state written.id written.span path type_
      | Some (Generic _) ->
          if not (unify state (T.builtin USize) type_) then
            mismatch state written.span ~expected:type_ ~found:(T.builtin USize)
      | _ -> ())
  | Qualified_constant constant -> qualified_constant state written.id written.span constant type_
  | Literal literal -> literal_pattern state written.id written.span literal type_
  | Pattern_range { start; stop; _ } -> (
      (* Only integers and characters are ordered so that a range of them
         can be matched; a range of anything else is one error, and its ends
         are not checked against the type. *)
      match resolve state type_ with
      | (T.Named _ | T.Function _ | T.Any _ | T.Cursor _ | T.Parameter _) as resolved
        when not (T.is_integer_type resolved || T.is_builtin Character resolved) ->
          report state Mismatch written.span
            (Printf.sprintf "A range pattern matches an integer or a `Character`, not `%s`."
               (show state resolved))
      | _ ->
          List.iter
            (fun (end_ : range_end) ->
              match end_.kind with
              | End_literal literal -> literal_pattern state end_.id end_.span literal type_
              | End_constant constant -> qualified_constant state end_.id end_.span constant type_
              | End_name bound -> (
                  match target state bound with
                  | Some (Definition path) -> constant_pattern state end_.id end_.span path type_
                  | _ -> ()))
            [ start; stop ])
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
                  (match (variant.fields, fields) with
                  | Some (_ :: _), None ->
                      report state Missing_argument written.span
                        ~fixes:
                          [ fix "Match its fields with `..`." [ insert written.span.stop "(..)" ] ]
                        (Printf.sprintf
                           "`%s` has fields, so its pattern names them, or writes `(..)`."
                           variant.variant_name)
                  | _ -> ());
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
              if not (Members.fields_visible state.database ~package:state.package path) then
                report state Private_field written.span
                  (Printf.sprintf "`%s` is opaque, so only its own package can match on it."
                     (T.show type_));
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
  (* A pattern names every field, or writes [..] for the rest. *)
  let named =
    List.filter_map
      (fun (field : pattern_field) ->
        match field.kind with
        | Named_field (name, _) -> Some name.text
        | Field inner -> (
            match bare_name inner with
            | Some name
              when List.exists (fun (declared : T.field) -> declared.field_name = name) fields ->
                Some name
            | _ -> ( match fields with [ only ] -> Some only.field_name | _ -> None))
        | Rest -> None)
      written_fields
  in
  let rest = List.exists (fun (field : pattern_field) -> field.kind = Rest) written_fields in
  let all_matched =
    List.length named
    = List.length (List.filter (fun (field : pattern_field) -> field.kind <> Rest) written_fields)
  in
  (if (not rest) && all_matched then
     match
       List.filter (fun (declared : T.field) -> not (List.mem declared.field_name named)) fields
     with
     | [] -> ()
     | missing ->
         if written_fields <> [] || List.length fields > 0 then
           report state Missing_argument written.span
             (Printf.sprintf "This pattern does not match %s. Name %s, or write `..` for the rest."
                (String.concat ", "
                   (List.map (fun (declared : T.field) -> "`" ^ declared.field_name ^ "`") missing))
                (if List.length missing = 1 then "it" else "them")));
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

(* A constant in a pattern, or a range's end: recorded by the node's id, and
   of the matched type. *)
and constant_pattern state id span path type_ =
  state.tables.patterns.(id) <- Some (Constant_pattern path);
  match Query.demand state.database Environment.constant_type path with
  | Some constant_type ->
      if not (unify state constant_type type_) then
        mismatch state span ~expected:type_ ~found:constant_type
  | None -> ()

and qualified_constant state id span constant type_ =
  let path =
    match constant with
    | Module_constant written_path -> (
        match target state written_path.last with Some (Definition path) -> Some path | _ -> None)
    | Type_constant (written_path, member) -> (
        match target state written_path.last with
        | Some (Definition owner) -> Members.own_constant state.database owner member.text
        | _ -> None)
  in
  match path with
  | Some path -> constant_pattern state id span path type_
  | None -> report state Unknown_member span "This names no constant."

and check_literal_fits state (value : expression) number type_ =
  defer state (fun () ->
      match resolve state type_ with
      | T.Literal _ | T.Variable _ -> false
      | resolved ->
          (match builtin_range ~usize_bits:(usize_bits state) resolved with
          | Some (low, high) when Z.lt number low || Z.gt number high ->
              report state Literal_out_of_range value.span
                (Printf.sprintf "`%s` does not fit in `%s`, which holds %s to %s."
                   (Z.to_string number) (T.show resolved) (Z.to_string low) (Z.to_string high))
          | _ -> ());
          true)

(* The width of [USize] and [ISize] the package's code must hold for: 32
   bits unless its manifest says [usize_bits = 64], so that code checked
   once holds on every target. See DESIGN.md, "Integers". *)
and usize_bits state =
  match Workspace.package state.database state.package with
  | Some package -> package.usize_bits
  | None -> 32

and builtin_range ?(usize_bits = 64) type_ =
  let bits signed width =
    if signed then
      Some (Z.neg (Z.shift_left Z.one (width - 1)), Z.pred (Z.shift_left Z.one (width - 1)))
    else Some (Z.zero, Z.pred (Z.shift_left Z.one width))
  in
  match T.builtin_of type_ with
  | Some Int8 -> bits true 8
  | Some Int16 -> bits true 16
  | Some Int32 -> bits true 32
  | Some Int64 -> bits true 64
  | Some ISize -> bits true usize_bits
  | Some UInt8 -> bits false 8
  | Some UInt16 -> bits false 16
  | Some UInt32 -> bits false 32
  | Some UInt64 -> bits false 64
  | Some USize -> bits false usize_bits
  | _ -> None

(* [Character"a"] and [UInt8"\n"]: a single character or byte is a tagged
   string, of one Unicode scalar value or one ASCII character, without
   [${...}]. See SYNTAX.md, "Characters and bytes". *)
and character_tag state (literal : string_literal) =
  match literal.tag with
  | Some tag -> (
      match target state tag.last with
      | Some (Definition path) -> (
          match Intrinsic.builtin_of_path path with
          | Some ((Character | UInt8) as builtin) -> Some builtin
          | _ -> None)
      | _ -> None)
  | None -> None

(* The value of a character or byte literal, recorded by [id], or an error. *)
and character_value state id (literal : string_literal) (builtin : Intrinsic.builtin) =
  let text = literal.first.value in
  let scalars =
    let rec count index found =
      if index >= String.length text then List.rev found
      else
        let decoded = String.get_utf_8_uchar text index in
        count (index + Uchar.utf_decode_length decoded) (Uchar.utf_decode_uchar decoded :: found)
    in
    count 0 []
  in
  let value =
    match (literal.rest, scalars, builtin) with
    | [], [ scalar ], Character -> Some (Uchar.to_int scalar)
    | [], [ scalar ], UInt8 when Uchar.to_int scalar < 128 -> Some (Uchar.to_int scalar)
    | _ -> None
  in
  match value with
  | Some value -> state.tables.literals.(id) <- Some (Integer_value (Z.of_int value))
  | None ->
      report state Bad_character literal.span
        (match builtin with
        | Character ->
            "`Character\"...\"` holds exactly one Unicode scalar value, with no `${...}`."
        | _ -> "`UInt8\"...\"` holds exactly one ASCII character, with no `${...}`.")

and character_literal state id literal builtin =
  character_value state id literal builtin;
  T.builtin builtin

(* A literal in a pattern, or a range's end: recorded by the node's id, and
   of the matched type. *)
and literal_pattern state id (span : span) literal type_ =
  match literal with
  | Literal_integer number -> (
      state.tables.literals.(id) <- Some (Integer_value number);
      if not (T.is_integer_type type_ || type_ = T.Error || type_ = T.Hole) then
        report state Mismatch span
          (Printf.sprintf "An integer pattern matches an integer, not `%s`." (T.show type_))
      else
        match builtin_range ~usize_bits:(usize_bits state) type_ with
        | Some (low, high) when Z.lt number low || Z.gt number high ->
            report state Literal_out_of_range span
              (Printf.sprintf "`%s` does not fit in `%s`." (Z.to_string number) (T.show type_))
        | _ -> ())
  | Literal_true | Literal_false ->
      if not (unify state type_ T.bool) then mismatch state span ~expected:type_ ~found:T.bool
  | Literal_string tagged -> (
      match character_tag state tagged with
      | Some builtin ->
          character_value state id tagged builtin;
          if not (unify state type_ (T.builtin builtin)) then
            mismatch state span ~expected:type_ ~found:(T.builtin builtin)
      | None -> string_pattern state span type_)

(* A string literal in a pattern matches a string. *)
and string_pattern state span type_ =
  if not (is_named string_path type_ || is_named string_slice_path type_ || type_ = T.Error) then
    report state Mismatch span
      (Printf.sprintf "A string pattern matches a string, not `%s`." (T.show type_))
