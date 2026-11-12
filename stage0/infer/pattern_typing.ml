(* Checks patterns: the names each pattern binds and their modes, constants
   and literals in patterns, and the values of character and byte literals. *)

open Syntax
module T = Types
module C = Tables
module Names = Resolve.Names
module Environment = Interface.Environment
module Impls = Interface.Impls
module Lower = Interface.Lower
open State

let rec binding_pattern state env written type_ ~mutable_ ~mode =
  pattern_with state env written type_ ~mutable_ ~mode

and pattern state env written type_ ~mode =
  pattern_with state env written type_ ~mutable_:false ~mode

and pattern_with state env (written : pattern) type_ ~mutable_ ~mode =
  let type_ = normalize state type_ in
  state.tables.scrutinee_types.(written.id) <- Some type_;
  (match current_frame state with
  | Some frame -> frame.patterns <- written.id :: frame.patterns
  | None -> ());
  let recurse = pattern_with state env ~mutable_ ~mode in
  let unknown type_ = unknown_pattern state env written type_ ~mutable_ ~mode in
  let binds id (bound : name) =
    register_pattern state written (fun () ->
        Bind { local = Named id; name = bound.text; mutable_; mode })
  in
  let constant () =
    register_pattern state written (fun () ->
        Form.equal_to_pattern state ~origin:written.id
          (Form.pattern_type state written.id)
          (Form.pattern_constant state written.id))
  in
  match written.kind with
  | Wildcard | Pattern_error -> register_pattern state written (fun () -> Wildcard)
  | Binding_or_constant bound -> (
      match target state bound with
      | Some Binding ->
          binds bound.id bound;
          declare state bound type_ ~mutable_ ~mode
      | Some (Local id) -> (
          binds id bound;
          (* A name in a later alternative is the same local as the name in
             the first alternative, and has the same type. *)
          match Hashtbl.find_opt state.locals id with
          | Some local ->
              if not (unify state local.type_ type_) then
                report state Mismatch bound.span
                  (Printf.sprintf
                     "`%s` is a `%s` in the first alternative, and a `%s` here; every alternative \
                      binds it with one type."
                     bound.text (show state local.type_) (show state type_))
          | None -> ())
      | Some (Definition (Constant, path)) ->
          constant ();
          constant_pattern state written.id written.span path type_
      | Some (Value_parameter parameter) ->
          register_pattern state written (fun () ->
              Literal
                (synthetic_expression state ~origin:written.id (T.builtin USize)
                   (Value_parameter parameter)));
          if not (unify state (T.builtin USize) type_) then
            mismatch state written.span ~expected:type_ ~found:(T.builtin USize)
      | _ -> ())
  | Qualified_constant written_constant ->
      constant ();
      qualified_constant state written.id written.span written_constant type_
  | Literal literal ->
      register_pattern state written (fun () ->
          Form.equal_to_pattern state ~origin:written.id
            (Form.pattern_type state written.id)
            (Form.pattern_literal state written.id literal));
      literal_pattern state written.id written.span literal type_
  | Pattern_range { start; stop; inclusive } -> (
      register_pattern state written (fun () ->
          let end_ (written_end : range_end) =
            synthetic_expression state ~origin:written_end.id
              (Form.pattern_type state written.id)
              (match written_end.kind with
              | End_literal literal -> Form.pattern_literal state written_end.id literal
              | End_constant _ | End_name _ -> Form.pattern_constant state written_end.id)
          in
          let start = end_ start in
          Range { start; stop = end_ stop; inclusive });
      (* A range pattern is only for integers and characters. A range of any
         other type is one error, and its bounds are not checked against the
         type. *)
      match resolve state type_ with
      | (T.Named _ | T.Function _ | T.Any _ | T.Cursor _ | T.Parameter _) as resolved
        when not (integer_type state resolved || T.is_builtin Character resolved) ->
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
                  | Some (Definition (Constant, path)) ->
                      constant_pattern state end_.id end_.span path type_
                  | _ -> ()))
            [ start; stop ])
  | Variant { name = variant_name; fields } -> (
      match type_ with
      | T.Named { path; arguments } -> (
          match Members.variants state.database path arguments with
          | Some variants -> (
              if not (Members.fields_visible state.database ~package:state.package path) then
                report state Private_field written.span
                  (Printf.sprintf "`%s` is opaque, so only its own package can match on it."
                     (T.show type_));
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
                  let declared = Option.value ~default:[] variant.fields in
                  let matched =
                    pattern_fields state env written declared (Option.value ~default:[] fields)
                      ~mutable_ ~mode
                  in
                  register_pattern state written (fun () ->
                      Variant
                        {
                          variant = variant.variant_name;
                          fields = Form.pattern_fields state declared matched;
                        })
              | None ->
                  unknown
                  @@ error state Unknown_variant variant_name.last.span
                       ~fixes:
                         (match
                            Diagnostic.closest variant_name.last.text
                              (List.map
                                 (fun (variant : T.variant) -> variant.variant_name)
                                 variants)
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
              match Members.broken state.database path with
              | Some report -> unknown (T.Error report)
              | None ->
                  unknown
                    (error state Unknown_variant written.span
                       (Printf.sprintf "`%s` has no variants." (T.show type_)))))
      | T.Error _ | T.Hole -> unknown type_
      | _ ->
          unknown
            (error state Unknown_variant written.span
               (Printf.sprintf "`%s` has no variants." (show state type_))))
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
              let matched = pattern_fields state env written record_fields fields ~mutable_ ~mode in
              register_pattern state written (fun () ->
                  Record (Form.pattern_fields state record_fields matched))
          | None -> (
              match Members.broken state.database path with
              | Some report -> unknown (T.Error report)
              | None ->
                  unknown
                    (error state Not_a_record written.span
                       (Printf.sprintf "`%s` is not a record." (show state type_)))))
      | T.Error _ | T.Hole -> unknown type_
      | _ ->
          unknown
            (error state Not_a_record written.span
               (Printf.sprintf "`%s` is not a record." (show state type_))))
  | Alternatives alternatives ->
      List.iter (fun alternative -> recurse alternative type_) alternatives;
      register_pattern state written (fun () ->
          Alternatives (List.map (build_pattern state) alternatives))

and pattern_fields state env (written : pattern) (fields : T.field list)
    (written_fields : pattern_field list) ~mutable_ ~mode =
  let bare_name (inner : pattern) =
    match inner.kind with Binding_or_constant name -> Some name.text | _ -> None
  in
  (* A pattern must name every field, or end with [..] for the rest. *)
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
  List.filter_map
    (fun (field : pattern_field) ->
      match field.kind with
      | Rest -> None
      | Named_field (name, inner) -> (
          match
            List.find_opt (fun (declared : T.field) -> declared.field_name = name.text) fields
          with
          | Some declared ->
              pattern_with state env inner declared.field_type ~mutable_ ~mode;
              Some (declared.field_name, inner)
          | None ->
              pattern_with state env inner ~mutable_ ~mode
              @@ error state Unknown_member name.span
                   ~fixes:
                     (match
                        Diagnostic.closest name.text
                          (List.map (fun (declared : T.field) -> declared.field_name) fields)
                      with
                     | Some candidate ->
                         [
                           fix
                             (Printf.sprintf "Write `%s`." candidate)
                             [ replace name.span candidate ];
                         ]
                     | None -> [])
                   (Printf.sprintf "There is no field `%s` here." name.text);
              None)
      | Field inner -> (
          let named =
            Option.bind (bare_name inner) (fun name ->
                List.find_opt (fun (declared : T.field) -> declared.field_name = name) fields)
          in
          match (named, fields) with
          | Some declared, _ | None, [ declared ] ->
              pattern_with state env inner declared.field_type ~mutable_ ~mode;
              Some (declared.field_name, inner)
          | None, _ ->
              let names =
                String.concat ", "
                  (List.map (fun (declared : T.field) -> "`" ^ declared.field_name ^ "`") fields)
              in
              pattern_with state env inner ~mutable_ ~mode
                (error state Unknown_member inner.span
                   (Printf.sprintf
                      "A bare pattern must name a field, since this has %d fields: %s. Truss has \
                       no tuples, so fields match by name."
                      (List.length fields) names));
              None))
    written_fields

(* A pattern that does not fit the type it matches still binds its names, so
   that every use of a name has a type. Each name gets the given unknown
   type (an error or a hole), and so do the sub-patterns. *)
and unknown_pattern state env (written : pattern) unknown ~mutable_ ~mode =
  state.tables.scrutinee_types.(written.id) <- Some unknown;
  match written.kind with
  | Variant { fields = Some fields; _ } | Record fields ->
      List.iter
        (fun (field : pattern_field) ->
          match field.kind with
          | Named_field (_, inner) | Field inner ->
              pattern_with state env inner unknown ~mutable_ ~mode
          | Rest -> ())
        fields
  | _ -> ()

(* A constant used as a pattern or as a bound of a range pattern. It is
   recorded under the node's id, and its type must be the matched type. *)
and constant_pattern state id span path type_ =
  state.tables.patterns.(id) <- Some (Constant_pattern path);
  match Query.demand state.database Environment.constant_type path with
  | Some constant_type ->
      if not (unify state constant_type type_) then
        mismatch state span ~expected:type_ ~found:constant_type
      else if not (structural state (resolve state constant_type)) then
        report state Not_structural span
          (Printf.sprintf
             "A constant in a pattern needs a type with structural equality, so that matching it \
              and `==` agree, and `%s` does not have it: its equality is hand-written, or it holds \
              a float, whose `==` treats `-0.0` and `0.0` as equal. Match with a guard instead, as \
              in `value if value == %s`."
             (show state constant_type)
             (match path with
             | Top { name; _ } | Member_constant { name; _ } | Method { name; _ } -> name
             | _ -> "the_constant"))
  | None -> ()

(* Whether a type has structural equality: values that are equal cannot be
   told apart. This holds for built-in equality, and for a derived [Equal]
   if every field has structural equality. *)
and structural ?(seen = []) state (type_ : T.ty) =
  if
    integer_type state type_ || T.is_builtin Bool type_ || T.is_builtin Character type_
    || T.is_builtin Unit type_ || T.is_well_known String type_
  then true
  else if T.is_float_type type_ then false
  else if List.exists (T.equal type_) seen then true
  else
    match type_ with
    | T.Named { path; arguments } -> (
        match Query.demand state.database Environment.interface path with
        | Some (Environment.Type_interface interface)
          when (not interface.opaque) || Path.package path = state.package ->
            let derives_equal =
              List.exists (fun derived -> Well_known.is Equal derived) interface.derives
            in
            let substitution =
              Option.value ~default:[] (T.substitution_of interface.type_generics arguments)
            in
            let fields_structural (fields : T.field list) =
              List.for_all
                (fun (field : T.field) ->
                  structural ~seen:(type_ :: seen) state
                    (T.substitute substitution field.field_type))
                fields
            in
            derives_equal
            && begin match interface.shape with
            | Record fields -> fields_structural fields
            | Sum variants ->
                List.for_all
                  (fun (variant : T.variant) ->
                    match variant.fields with
                    | Some fields -> fields_structural fields
                    | None -> true)
                  variants
            | Todo_type | Builtin_type _ | Error_shape _ -> false
            end
        | _ -> false)
    | _ -> false

and qualified_constant state id span constant type_ =
  let path =
    match constant with
    | Module_constant written_path -> (
        match target state written_path.last with
        | Some (Definition (Constant, path)) -> Some path
        | _ -> None)
    | Type_constant (written_path, member) -> (
        match target state written_path.last with
        | Some (Definition (Type, owner)) -> Members.own_constant state.database owner member.text
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
          (match
             match resolved with
             | T.Parameter _ | T.Projection _ -> state.unifier.integer_range resolved
             | _ -> builtin_range ~usize_bits:(usize_bits state) resolved
           with
          | Some (low, high) when Z.lt number low || Z.gt number high ->
              report state Literal_out_of_range value.span
                (Printf.sprintf "`%s` does not fit in `%s`, which holds %s to %s."
                   (Z.to_string number) (T.show resolved) (Z.to_string low) (Z.to_string high))
          | _ -> ());
          true)

(* The number of bits of [USize] and [ISize] that the package is checked
   for: 32, unless the manifest says [usize_bits = 64]. Code checked for 32
   bits is correct on every target. *)
and usize_bits state = Query.demand state.database Workspace.usize_bits state.package
and builtin_range ?usize_bits type_ = T.integer_range ?usize_bits type_

(* [Character"a"] and [UInt8"\n"]: a character or byte literal is a tagged
   string with exactly one Unicode scalar value or one ASCII character, and
   no [${...}]. *)
and character_tag state (literal : string_literal) =
  match literal.tag with
  | Some tag -> (
      match target state tag.last with
      | Some (Definition (Type, path)) -> (
          match Intrinsic.builtin_of_path path with
          | Some ((Character | UInt8) as builtin) -> Some builtin
          | _ -> None)
      | _ -> None)
  | None -> None

(* Records the value of a character or byte literal under [id], or reports
   an error. *)
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

(* A literal used as a pattern or as a bound of a range pattern. It is
   recorded under the node's id, and its type must be the matched type. *)
and literal_pattern state id (span : span) literal type_ =
  match literal with
  | Literal_integer number -> (
      state.tables.literals.(id) <- Some (Integer_value number);
      if not (integer_type state type_ || T.is_error type_ || type_ = T.Hole) then
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

(* A string literal used as a pattern matches a string. *)
and string_pattern state span type_ =
  if not (T.is_well_known String type_ || T.is_well_known String_slice type_ || T.is_error type_)
  then
    report state Mismatch span
      (Printf.sprintf "A string pattern matches a string, not `%s`." (T.show type_))
