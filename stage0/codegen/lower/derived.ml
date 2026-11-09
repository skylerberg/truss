(* Derived implementations of Equal, Ordered, Hash, and Default, from a
   type's shape. See lower.ml. *)

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
    {
      definition_key = key_of context type_path;
      anchor = type_path;
      text = "";
      checked = Checked.create 0;
      parameters = [];
      body = { statements = []; span = S.Span.make 0 0; id = 0 };
      result = signature.output;
      parameter_types = [];
      substitution = bind signature.generics type_arguments;
      uses = [];
      has_defaults = false;
      requires = [];
    }
  in
  let b = Lir_builder.create () in
  let st =
    {
      context;
      frame =
        {
          code;
          bindings = Hashtbl.create 1;
          self_place = None;
          on_yield = None;
          inlined = [];
          exit = None;
        };
      b;
      scopes = [ { owned = [] } ];
      loops = [];
      temporaries = [];
      return_ = None;
      result_local = None;
      nested = ref [];
      evidence = [];
      pulling = false;
    }
  in
  let lir_signature, result =
    lir_signature context code.substitution ~parameters:(interface_parameters signature)
      ~has_defaults:false signature.output
  in
  let result_pointer =
    match result with Through_pointer pointer -> Some (local b ~name:"result" pointer) | _ -> None
  in
  let parameter (mode : T.mode) ty =
    match Convention.parameter context.env (Monomorphic.mode mode) ty with
    | Some (Pointer _ as pointer) ->
        let local = local b pointer in
        (Some local, { Lir.root = Local local; projections = [ Deref ] })
    | Some lir_ty ->
        let local = local b lir_ty in
        (Some local, at local)
    | None -> (None, new_local st ty)
  in
  let ground_parameters =
    List.map
      (fun (mode, t) -> (mode, Monomorphic.ground context.monomorphic code.substitution t))
      (interface_parameters signature)
  in
  let locals_and_places = List.map (fun (mode, t) -> parameter mode t) ground_parameters in
  let places = List.map snd locals_and_places in
  let result_ty =
    match signature.output with
    | Returns t -> Monomorphic.ground context.monomorphic code.substitution t
    | _ -> bug "a derived method that yields"
  in
  let result_place =
    match result_pointer with
    | Some pointer -> { Lir.root = Local pointer; projections = [ Deref ] }
    | None -> new_local st result_ty
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
      let bool = context.bool in
      emit b (Assign (result_place, Use (Constant (Bool true))));
      each_variant st ty self (fun variant _ ->
          let same = local b (Raw Bool) in
          emit b
            (Assign
               ( at same,
                 match variant with
                 | Some v -> Is_variant (other, v)
                 | None -> Use (Constant (Bool true)) ));
          let different = local b (Raw Bool) in
          emit b (Assign (at different, Unary (Not, Copy (at same))));
          when_ b
            (Copy (at different))
            (fun () -> emit b (Assign (result_place, Use (Constant (Bool false)))));
          when_ b
            (Copy (at same))
            (fun () ->
              List.iter
                (fun (field, field_ty) ->
                  let equal = new_local st bool in
                  trait_call st ~trait:(core "Equal") ~name:"equal" ~receiver:Read ~self:field_ty
                    ~arguments:
                      [
                        (Read, field_ty, field_place self variant field);
                        (Read, field_ty, field_place other variant field);
                      ]
                    ~destination:equal;
                  emit b (Assign (result_place, Binary (Bit_and, Copy result_place, Copy equal))))
                (typed_fields (shape_fields st ty variant))))
  | "Hash", "hash", [ self; hasher ] ->
      let hasher_ty = match List.nth ground_parameters 1 with _, t -> t in
      let hasher_path = match hasher_ty with Named { path; _ } -> path | _ -> bug "a hasher" in
      let write value =
        let path = Path.Method { owner = hasher_path; name = "write"; receiver = Mut } in
        let signature = signature_of context path in
        let word = new_local st (Monomorphic.builtin UInt64) in
        emit b (Assign (word, Use value));
        call_instance st
          (Code { path; type_arguments = [] })
          ~signature ~substitution:[]
          ~arguments:[ (Mut, hasher_ty, hasher); (Read, Monomorphic.builtin UInt64, word) ]
          ~mask:0
          ~destination:(new_local st (Monomorphic.builtin Unit))
      in
      each_variant st ty self (fun variant index ->
          if variant <> None then write (constant_int UInt64 (Z.of_int index));
          List.iter
            (fun (field, field_ty) ->
              trait_call st ~trait:(core "Hash") ~name:"hash" ~receiver:Read ~self:field_ty
                ~arguments:
                  [ (Read, field_ty, field_place self variant field); (Mut, hasher_ty, hasher) ]
                ~destination:(new_local st (Monomorphic.builtin Unit)))
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
                  trait_call st ~trait:(core "Ordered") ~name:"compare" ~receiver:Read
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
                let value = new_local st field_ty in
                trait_call st ~trait:(core "Default") ~name:"default" ~receiver:Static
                  ~self:field_ty ~arguments:[] ~destination:value;
                (field, Lir.Move value))
              (typed_fields (shape_fields st ty None))
          in
          emit b (Assign (result_place, Build { ty; variant = None; fields })))
  | _ -> bug "%s cannot be derived" (Path.show path));
  finish b (Return (match result with Returned _ -> Some (Lir.Move result_place) | _ -> None));
  ignore lir_signature;
  let main =
    Lir_builder.build b ?written_result:result_pointer
      ~parameters:(Option.to_list result_pointer @ List.filter_map fst locals_and_places)
      ~result:(match result with Returned t -> Some t | _ -> None)
  in
  { key; main; nested = [||] }

(* Capabilities: entries, tables, and the real implementations *)

(* A state for generated code, with no source of its own. *)
