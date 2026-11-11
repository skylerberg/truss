(* Derived implementations of Equal, Ordered, Hash, and Default, from a
   type's shape. *)

open Definitions
open Lowering
open Targets
open Lir_builder

(* Derived implementations *)

(* The fields of a variant, or of a record, with their ground types. *)
let shape_fields st ty variant =
  match (Monomorphic.shape st.context.monomorphic ty, variant) with
  | Record fields, None -> fields
  | Sum variants, Some name ->
      (List.find (fun (v : Memory_layout.variant_shape) -> v.name = name) variants).fields
  | _ -> []

let typed_fields fields =
  List.filter_map
    (function name, Memory_layout.Typed ty -> Some (name, ty) | _, Raw _ -> None)
    fields

let variants st ty =
  match Monomorphic.shape st.context.monomorphic ty with
  | Sum variants -> Some (List.map (fun (v : Memory_layout.variant_shape) -> v.name) variants)
  | _ -> None

(* Branches on the variant a value holds, running [f] with each variant's
   name and index, or runs [f] once for a record. *)
let each_variant st ty place f =
  match variants st ty with
  | None -> f None 0
  | Some names ->
      let after = block st.b in
      let cases =
        List.mapi
          (fun index name ->
            let case = block st.b in
            aside st.b case (fun () ->
                f (Some name) index;
                finish st.b (Goto after));
            (name, case))
          names
      in
      finish st.b (Switch_variant { place; cases; default = None });
      start st.b after

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
  let b = st.b in
  let convention, _ = result_of context code.substitution signature.output in
  result_slot st convention;
  let ground_parameters =
    List.map (fun (mode, t) -> (mode, ground st t)) (interface_parameters signature)
  in
  let taken =
    List.map
      (fun (mode, t) -> parameter st ~owned:(mode = T.Own) (Monomorphic.mode mode) t)
      ground_parameters
  in
  let places = List.map snd taken in
  let result_ty =
    match signature.output with Returns t -> ground st t | _ -> bug "a derived method that yields"
  in
  let result_place =
    match result_place st with Some place -> place | None -> temporary st result_ty
  in
  start b (block b);
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
      let differ = block b and done_ = block b in
      let unless_equal value =
        let go_on = block b in
        finish b (Switch { value; cases = [ (Z.one, go_on) ]; default = Some differ });
        start b go_on
      in
      each_variant st ty self (fun variant _ ->
          Option.iter
            (fun v ->
              let same = local b (Raw Bool) in
              emit b (Assign (at same, Is_variant (other, v)));
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
      emit b (Assign (result_place, Use (Constant (Bool true))));
      finish b (Goto done_);
      start b differ;
      emit b (Assign (result_place, Use (Constant (Bool false))));
      finish b (Goto done_);
      start b done_
  | "Hash", "hash", [ self; hasher ] ->
      let hasher_ty = match List.nth ground_parameters 1 with _, t -> t in
      let hasher_path = match hasher_ty with Named { path; _ } -> path | _ -> bug "a hasher" in
      let write value =
        let path = Path.Method { owner = hasher_path; name = "write"; receiver = Mut } in
        let signature = signature_of context path in
        let word = temporary st (Monomorphic.builtin UInt64) in
        emit b (Assign (word, Use value));
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
        emit b (Assign (result_place, Build { ty = ordering; variant = Some name; fields = [] }))
      in
      set "Equal";
      (* By variant, in declaration order, then by fields in declaration
         order. *)
      let index_of place =
        let index = local b (Raw (Integer UInt32)) in
        each_variant st ty place (fun _ i ->
            emit b (Assign (at index, Use (constant_int UInt32 (Z.of_int i)))));
        index
      in
      let mine = index_of self and theirs = index_of other in
      let less = local b (Raw Bool) and greater = local b (Raw Bool) in
      emit b (Assign (at less, Binary (Less, Copy (at mine), Copy (at theirs))));
      emit b (Assign (at greater, Binary (Greater, Copy (at mine), Copy (at theirs))));
      let done_ = block b in
      when_ b (Copy (at less)) (fun () -> set "Less");
      when_ b (Copy (at greater)) (fun () -> set "Greater");
      let differ = local b (Raw Bool) in
      emit b (Assign (at differ, Binary (Bit_or, Copy (at less), Copy (at greater))));
      let same = block b in
      finish b
        (Switch { value = Copy (at differ); cases = [ (Z.one, done_) ]; default = Some same });
      start b same;
      each_variant st ty self (fun variant _ ->
          List.iter
            (fun (field, field_ty) ->
              let undecided = local b (Raw Bool) in
              emit b (Assign (at undecided, Is_variant (result_place, "Equal")));
              when_ b
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
            (typed_fields (shape_fields st ty variant)));
      finish b (Goto done_);
      start b done_
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
          emit b (Assign (result_place, Build { ty; variant = None; fields })))
  | _ -> bug "%s cannot be derived" (Path.show path));
  { key; main = finish_function st ~first:[] ~rest:(List.filter_map fst taken) (); nested = [||] }

(* Capabilities: entries, tables, and the real implementations *)

(* A state for generated code, with no source of its own. *)
