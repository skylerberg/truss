(* Derived implementations of Equal, Ordered, Hash, and Default, from a
   type's shape. *)

open Definitions
open Lowering
open Targets
open Lir_builder

(* The fields of a variant, or of a record, with their ground types. *)
let shape_fields st ty variant =
  match (Monomorphic.shape st.context.monomorphic ty, variant) with
  | Record fields, None -> fields
  | Sum variants, Some name ->
      (List.find
         (fun (variant_shape : Memory_layout.variant_shape) -> variant_shape.name = name)
         variants)
        .fields
  | _ -> []

let typed_fields fields =
  List.filter_map
    (function name, Memory_layout.Typed ty -> Some (name, ty) | _, Raw _ -> None)
    fields

let variants st ty =
  match Monomorphic.shape st.context.monomorphic ty with
  | Sum variants ->
      Some
        (List.map
           (fun (variant_shape : Memory_layout.variant_shape) -> variant_shape.name)
           variants)
  | _ -> None

(* Branches on the variant a value holds, running [f] with each variant's
   name and index, or runs [f] once for a record. *)
let each_variant st ty place body =
  match variants st ty with
  | None -> body None 0
  | Some names ->
      let after = block st.builder in
      let cases =
        List.mapi
          (fun index name ->
            let case = block st.builder in
            in_block st.builder case (fun () ->
                body (Some name) index;
                finish st.builder (Goto after));
            (name, case))
          names
      in
      finish st.builder (Switch_variant { place; cases; default = None });
      start st.builder after

let derived context ~(key : Instance.key) ~type_path ~trait ~name ~type_arguments : Lir.t =
  let ty = Ground.Named { path = type_path; arguments = type_arguments } in
  let path = match key with Code { path; _ } -> path | _ -> bug "a derived method's key" in
  let signature = signature_of context path in
  let code =
    unwritten ~definition_key:(key_of context type_path) ~anchor:type_path
      ~substitution:(bind signature.generics type_arguments)
      ~result:signature.output
  in
  let st = enter context (frame_of code ~inlined:[]) in
  let builder = st.builder in
  let convention, _ = result_of context code.substitution signature.output in
  result_slot st convention;
  let ground_parameters =
    List.map
      (fun (mode, parameter_type) -> (mode, ground st parameter_type))
      (interface_parameters signature)
  in
  let parameter_places =
    List.map
      (fun (mode, parameter_type) ->
        parameter st ~owned:(mode = Types.Own) (Monomorphic.mode mode) parameter_type)
      ground_parameters
  in
  let places = List.map snd parameter_places in
  let result_ty =
    match signature.output with
    | Returns parameter_type -> ground st parameter_type
    | _ -> bug "a derived method that yields"
  in
  let result_place =
    match result_place st with Some place -> place | None -> temporary st result_ty
  in
  start builder (block builder);
  let field_place place variant field =
    match variant with
    | None -> place / Lir.Field field
    | Some variant -> place / Lir.Variant_field { variant; field }
  in
  let trait_name = Ground.path_name trait in
  (match (trait_name, name, places) with
  | "Equal", "equal", [ self; other ] ->
      (* Two values differ at the first thing that differs: another variant,
         or a field that is not equal, after which no other field is
         compared. *)
      let differ = block builder and done_ = block builder in
      let unless_equal value =
        let go_on = block builder in
        branch builder value ~yes:go_on ~no:differ;
        start builder go_on
      in
      each_variant st ty self (fun variant _ ->
          Option.iter
            (fun variant_shape ->
              let same = local builder (Raw Bool) in
              emit builder (Assign (at same, Is_variant (other, variant_shape)));
              unless_equal (Copy (at same)))
            variant;
          List.iter
            (fun (field, field_ty) ->
              let equal = temporary st context.bool in
              trait_call st ~trait:(Well_known.path Equal) ~name:"equal" ~receiver:Read
                ~self:field_ty
                ~arguments:
                  [
                    (Read, field_ty, field_place self variant field);
                    (Read, field_ty, field_place other variant field);
                  ]
                ~destination:equal;
              unless_equal (Copy equal))
            (typed_fields (shape_fields st ty variant)));
      emit builder (Assign (result_place, Use (Constant (Bool true))));
      finish builder (Goto done_);
      start builder differ;
      emit builder (Assign (result_place, Use (Constant (Bool false))));
      finish builder (Goto done_);
      start builder done_
  | "Hash", "hash", [ self; hasher ] ->
      let hasher_ty =
        match List.nth ground_parameters 1 with _, parameter_type -> parameter_type
      in
      let hasher_path = match hasher_ty with Named { path; _ } -> path | _ -> bug "a hasher" in
      let write value =
        let path = Path.Method { owner = hasher_path; name = "write"; receiver = Mut } in
        let signature = signature_of context path in
        let word = temporary st (Monomorphic.builtin UInt64) in
        emit builder (Assign (word, Use value));
        call_instance st
          (Code { path; type_arguments = [] })
          ~signature ~substitution:[]
          ~arguments:[ (Mut, hasher_ty, hasher); (Read, Monomorphic.builtin UInt64, word) ]
          ~destination:(temporary st (Monomorphic.builtin Unit))
          ()
      in
      each_variant st ty self (fun variant index ->
          if variant <> None then write (constant_int UInt64 (Z.of_int index));
          List.iter
            (fun (field, field_ty) ->
              trait_call st ~trait:(Well_known.path Hash) ~name:"hash" ~receiver:Read ~self:field_ty
                ~arguments:
                  [ (Read, field_ty, field_place self variant field); (Mut, hasher_ty, hasher) ]
                ~destination:(temporary st (Monomorphic.builtin Unit)))
            (typed_fields (shape_fields st ty variant)))
  | "Ordered", "compare", [ self; other ] ->
      let ordering = result_ty in
      let set name =
        emit builder
          (Assign (result_place, Build { ty = ordering; variant = Some name; fields = [] }))
      in
      set "Equal";
      (* By variant, in declaration order, then by fields in declaration
         order. *)
      let index_of place =
        let index = local builder (Raw (Integer UInt32)) in
        each_variant st ty place (fun _ variant_index ->
            emit builder (Assign (at index, Use (constant_int UInt32 (Z.of_int variant_index)))));
        index
      in
      let mine = index_of self and theirs = index_of other in
      let less = local builder (Raw Bool) and greater = local builder (Raw Bool) in
      emit builder (Assign (at less, Binary (Less, Copy (at mine), Copy (at theirs))));
      emit builder (Assign (at greater, Binary (Greater, Copy (at mine), Copy (at theirs))));
      let done_ = block builder in
      when_ builder (Copy (at less)) (fun () -> set "Less");
      when_ builder (Copy (at greater)) (fun () -> set "Greater");
      let differ = local builder (Raw Bool) in
      emit builder (Assign (at differ, Binary (Bit_or, Copy (at less), Copy (at greater))));
      let same = block builder in
      branch builder (Copy (at differ)) ~yes:done_ ~no:same;
      start builder same;
      each_variant st ty self (fun variant _ ->
          List.iter
            (fun (field, field_ty) ->
              let undecided = local builder (Raw Bool) in
              emit builder (Assign (at undecided, Is_variant (result_place, "Equal")));
              when_ builder
                (Copy (at undecided))
                (fun () ->
                  trait_call st ~trait:(Well_known.path Ordered) ~name:"compare" ~receiver:Read
                    ~self:field_ty
                    ~arguments:
                      [
                        (Read, field_ty, field_place self variant field);
                        (Read, field_ty, field_place other variant field);
                      ]
                    ~destination:result_place))
            (Interface.Environment.in_declared_order context.database type_path ~variant ~name:fst
               (typed_fields (shape_fields st ty variant))));
      finish builder (Goto done_);
      start builder done_
  | "Default", "default", [] -> (
      match variants st ty with
      | Some _ -> bug "Default is derived only for records"
      | None ->
          let fields =
            List.map
              (fun (field, field_ty) ->
                let value = temporary st field_ty in
                trait_call st ~trait:(Well_known.path Default) ~name:"default" ~receiver:Static
                  ~self:field_ty ~arguments:[] ~destination:value;
                (field, Lir.Move value))
              (typed_fields (shape_fields st ty None))
          in
          emit builder (Assign (result_place, Build { ty; variant = None; fields })))
  | _ -> bug "%s cannot be derived" (Path.show path));
  {
    key;
    main = finish_function st ~first:[] ~rest:(List.filter_map fst parameter_places) ();
    nested = [||];
  }

(* Capabilities: entries, tables, and the real implementations *)

(* A state for generated code, with no source of its own. *)
