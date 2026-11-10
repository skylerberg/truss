(* Patterns: testing whether a value matches, and binding the names a
   pattern binds. *)

open Definitions
open Lowering
open Targets
open Lir_builder

(* Patterns *)

(* A constant's static data, as a place. *)
let rec static_constant st path : Lir.place =
  match demand st.context Environment.constant_type path with
  | Some ty -> { root = Static { key = Constant path; ty = ground st ty }; projections = [] }
  | None -> bug "no type for the constant %s" (Path.show path)

(* A [String] or [StringSlice] of a literal's text, in a new local. *)
and string_place st ty text =
  let place = temporary st ty in
  (match ty with
  | Named { path = Top { name = "String"; _ }; _ } ->
      let field, storage_ty, storage = string_value st ty text in
      let built = temporary st storage_ty in
      emit st.b (Assign (built, storage));
      emit st.b (Assign (place, Build { ty; variant = None; fields = [ (field, Move built) ] }))
  | _ -> (
      match Monomorphic.shape st.context.monomorphic ty with
      | Record [ (field, Typed view) ] ->
          let bytes = temporary st view in
          emit st.b
            (Assign
               ( bytes,
                 Build
                   {
                     ty = view;
                     variant = None;
                     fields =
                       [
                         ("elements", Constant (Bytes text)); ("length", usize (String.length text));
                       ];
                   } ));
          emit st.b
            (Assign (place, Build { ty; variant = None; fields = [ (field, Lir.Copy bytes) ] }))
      | _ -> bug "a string pattern on %s" (Ground.to_string ty)));
  place

(* The fields of a record or a variant, in declaration order, which a
   constructor's parameters are numbered by. *)
and constructor_fields st ty variant =
  match (Monomorphic.shape st.context.monomorphic ty, variant) with
  | Record fields, None -> List.map fst fields
  | Sum variants, Some name -> (
      match List.find_opt (fun (v : Memory_layout.variant_shape) -> v.name = name) variants with
      | Some v -> List.map fst v.fields
      | None -> bug "no variant %s" name)
  | _ -> bug "a constructor of %s" (Ground.to_string ty)

and field_patterns st (fields : S.pattern_field list) ty variant =
  let names = constructor_fields st ty variant in
  let shape_fields =
    match (Monomorphic.shape st.context.monomorphic ty, variant) with
    | Record fields, None -> fields
    | Sum variants, Some name ->
        (List.find (fun (v : Memory_layout.variant_shape) -> v.name = name) variants).fields
    | _ -> []
  in
  List.filter_map
    (fun (field : S.pattern_field) ->
      match field.kind with
      | Named_field (name, pattern) -> Some (name.text, pattern)
      | Field ({ kind = Binding_or_constant name; _ } as pattern) when List.mem name.text names ->
          Some (name.text, pattern)
      | Field pattern -> (
          match names with
          | [ only ] -> Some (only, pattern)
          | _ -> bug "a bare pattern for a field")
      | Rest -> None)
    fields
  |> List.map (fun (name, pattern) ->
      let field_ty =
        match List.assoc_opt name shape_fields with
        | Some (Memory_layout.Typed ty) -> ty
        | _ -> bug "no field %s" name
      in
      (name, pattern, field_ty))

and field_place place variant name =
  match variant with
  | None -> place / Lir.Field name
  | Some variant -> place / Lir.Variant_field { variant; field = name }

(* Branches to [matched] if the value at [place] of type [ty] matches the
   pattern, and to [failed] otherwise, binding nothing. *)
and test_pattern st (pattern : S.pattern) place ty ~matched ~failed =
  let check rvalue =
    let ok = local st.b (Raw Bool) in
    emit st.b (Assign (at ok, rvalue));
    finish st.b
      (Switch { value = Copy (at ok); cases = [ (Z.one, matched) ]; default = Some failed })
  in
  (* A value matches a constant or a string when it is equal to it. *)
  let equal_to other =
    let ok = temporary st st.context.bool in
    trait_call st ~trait:(core "Equal") ~name:"equal" ~receiver:Read ~self:ty
      ~arguments:[ (Read, ty, place); (Read, ty, other) ]
      ~destination:ok;
    check (Use (Copy ok))
  in
  let constant () =
    match st.frame.code.checked.patterns.(pattern.id) with
    | Some (Constant_pattern path) -> equal_to (static_constant st path)
    | _ -> bug "a constant pattern with no constant"
  in
  match pattern.kind with
  | Wildcard -> finish st.b (Goto matched)
  | Binding_or_constant _ -> (
      match st.frame.code.checked.patterns.(pattern.id) with
      | Some (Constant_pattern _) -> constant ()
      | _ -> finish st.b (Goto matched))
  | Qualified_constant _ -> constant ()
  | Literal (Literal_integer _) ->
      check (Binary (Equal, Copy place, constant_of st ty (literal st pattern.id)))
  | Literal Literal_true -> check (Use (Copy place))
  | Literal Literal_false -> check (Unary (Not, Copy place))
  | Literal (Literal_string _) when st.frame.code.checked.literals.(pattern.id) <> None ->
      check (Binary (Equal, Copy place, constant_of st ty (literal st pattern.id)))
  | Literal (Literal_string literal) -> equal_to (string_place st ty literal.first.value)
  | Pattern_range { start; stop; inclusive } ->
      let bound (e : S.range_end) =
        match e.kind with
        | End_literal (Literal_integer value) -> constant_int (integer_of st ty) value
        | End_literal (Literal_string _) -> constant_of st ty (literal st e.id)
        | End_constant _ | End_name _ -> (
            match st.frame.code.checked.patterns.(e.id) with
            | Some (Constant_pattern path) -> Copy (static_constant st path)
            | _ -> bug "a range end with no constant")
        | End_literal _ -> bug "a range end that is not a number"
      in
      let low = local st.b (Raw Bool) and high = local st.b (Raw Bool) in
      emit st.b (Assign (at low, Binary (Greater_equal, Copy place, bound start)));
      emit st.b
        (Assign (at high, Binary ((if inclusive then Less_equal else Less), Copy place, bound stop)));
      check (Binary (Bit_and, Copy (at low), Copy (at high)))
  | Alternatives alternatives ->
      List.iteri
        (fun i alternative ->
          let next = if i = List.length alternatives - 1 then failed else block st.b in
          test_pattern st alternative place ty ~matched ~failed:next;
          if next <> failed then start st.b next)
        alternatives
  | Variant { name; fields } ->
      let variant = name.last.text in
      let inside = block st.b in
      let is = local st.b (Raw Bool) in
      emit st.b (Assign (at is, Is_variant (place, variant)));
      finish st.b
        (Switch { value = Copy (at is); cases = [ (Z.one, inside) ]; default = Some failed });
      start st.b inside;
      test_fields st (Option.value fields ~default:[]) place ty (Some variant) ~matched ~failed
  | Record fields -> test_fields st fields place ty None ~matched ~failed
  | Pattern_error -> bug "a pattern that did not parse"

and test_fields st fields place ty variant ~matched ~failed =
  let parts = field_patterns st fields ty variant in
  let rec go = function
    | [] -> finish st.b (Goto matched)
    | (name, pattern, field_ty) :: rest ->
        let next = block st.b in
        test_pattern st pattern (field_place place variant name) field_ty ~matched:next ~failed;
        start st.b next;
        go rest
  in
  go parts

(* Binds the names a pattern binds to the parts of the value at [place],
   once it is known to match: views of the parts, or the parts moved out
   when the value is owned. Plain parts are copied, unless [changed], when
   the names are the parts themselves, as a [mut] loop's are. *)
and bind_pattern ?(changed = false) st (pattern : S.pattern) place ty ~owned =
  match pattern.kind with
  | Binding_or_constant name -> (
      match st.frame.code.checked.patterns.(pattern.id) with
      | Some (Constant_pattern _) -> ()
      | _ ->
          if owned || (trivial st ty && not changed) then begin
            let local = binding st ~name:name.text ty in
            emit st.b
              (Assign (local, Use (if owned then owned_operand st place ty else Copy place)));
            Hashtbl.replace st.frame.bindings name.id local
          end
          else Hashtbl.replace st.frame.bindings name.id place)
  | Wildcard | Literal _ | Pattern_range _ | Qualified_constant _ -> ()
  | Alternatives (first :: _) -> bind_pattern ~changed st first place ty ~owned
  | Alternatives [] -> ()
  | Variant { name; fields } ->
      List.iter
        (fun (field, pattern, field_ty) ->
          bind_pattern ~changed st pattern
            (field_place place (Some name.last.text) field)
            field_ty ~owned)
        (field_patterns st (Option.value fields ~default:[]) ty (Some name.last.text))
  | Record fields ->
      List.iter
        (fun (field, pattern, field_ty) ->
          bind_pattern ~changed st pattern (field_place place None field) field_ty ~owned)
        (field_patterns st fields ty None)
  | Pattern_error -> bug "a pattern that did not parse"

and owned_operand st place ty = owned st place ty
