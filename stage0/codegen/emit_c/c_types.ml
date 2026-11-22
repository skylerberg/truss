let ( ++ ) = C_text.( ++ )

module Keys = Map.Make (struct
  type t = C_text.key

  let compare = Stdlib.compare
end)

type 'text definition =
  | Typedef of 'text
  | Code_typedef of 'text
  | Struct of { body : 'text; holds : C_text.key list }

type 'text defined = { definition : 'text definition; references : C_text.key list }

let map_defined render { definition; references } =
  {
    definition =
      (match definition with
      | Typedef text -> Typedef (render text)
      | Code_typedef text -> Code_typedef (render text)
      | Struct { body; holds } -> Struct { body = render body; holds });
    references;
  }

type registry = {
  owner : Lowered.Item.t option;
  order : C_text.key Dynarray.t;
  mutable registered : unit Keys.t;
  mutable environments : (string * Lowered.ty) list Keys.t;
  mutable references : C_text.key list option;
}

type t = { env : Memory_layout.env; registry : registry }

let create env ~owner =
  {
    env;
    registry =
      {
        owner;
        order = Dynarray.create ();
        registered = Keys.empty;
        environments = Keys.empty;
        references = None;
      };
  }

let make_environment_key { registry; _ } nested_index : C_text.key =
  match registry.owner with
  | Some owner -> Environment (owner, nested_index)
  | None -> C_runtime.raise_bug "the environment %d of no function" nested_index

let add_environment types nested_index fields =
  types.registry.environments <-
    Keys.add (make_environment_key types nested_index) fields types.registry.environments

let read_environment types nested_index =
  match Keys.find_opt (make_environment_key types nested_index) types.registry.environments with
  | Some fields -> fields
  | None -> C_runtime.raise_bug "the environment %d has no fields" nested_index

let register { registry; _ } key =
  (match registry.references with
  | Some references -> registry.references <- Some (key :: references)
  | None -> ());
  if not (Keys.mem key registry.registered) then begin
    registry.registered <- Keys.add key () registry.registered;
    Dynarray.add_last registry.order key
  end

let list_keys { registry; _ } = Dynarray.to_list registry.order

let render_key types key : C_text.t =
  register types key;
  Name (Type_name key)

let compute_layout types ty = Memory_layout.of_type types.env ty

let is_struct types (ty : Ground.ty) =
  match (compute_layout types ty).form with
  | Struct _ | Array _ | Tagged _ -> true
  | Niche_encoded { dataful; _ } -> (
      match dataful.payload.form with Struct _ -> true | _ -> false)
  | Zero_size | Scalar _ | Tag_only _ -> false

let rec render_value_type types (ty : Ground.ty) : C_text.t =
  match (compute_layout types ty).form with
  | Zero_size -> Text "void"
  | Scalar scalar -> render_scalar_type types scalar
  | _ -> render_key types (Type ty)

and render_scalar_type types : Memory_layout.scalar -> C_text.t = function
  | Integer integer -> Text (C_runtime.render_integer_type integer)
  | Float32 -> Text "float"
  | Float64 -> Text "double"
  | Bool -> Text "uint8_t"
  | Character -> Text "uint32_t"
  | Pointer pointee | Nullable_pointer pointee -> render_pointee_type types pointee

and render_pointee_type types : Memory_layout.pointee -> C_text.t = function
  | Data ty -> render_value_type types ty ++ Text " *"
  | Block (ty, variant) -> render_key types (Block (ty, variant)) ++ Text " *"
  | Code function_type -> render_key types (Code function_type)
  | Opaque -> Text "void *"

let rec render_type types : Lowered.ty -> C_text.t = function
  | Value ty -> render_value_type types ty
  | Pointer { target; writable } ->
      Text (if writable then "" else "const ") ++ render_type types target ++ Text " *"
  | Raw scalar -> render_scalar_type types scalar
  | Environment nested_index -> render_key types (make_environment_key types nested_index)
  | Evidence nested_index -> render_key types (Evidence (max nested_index 1))
  | Capabilities count -> render_key types (Capabilities count)
  | Trace -> Text "struct truss_trace"
  | Lend -> Text "struct truss_lend"
  | Lend_arena -> Text "struct truss_lend_arena"

let render_member_type types : Memory_layout.member -> C_text.t = function
  | Typed ty -> render_value_type types ty
  | Raw scalar -> render_scalar_type types scalar

let list_held_keys types : Memory_layout.member -> C_text.key list = function
  | Typed ty when is_struct types ty -> [ Type ty ]
  | Typed _ | Raw _ -> []

let render_member ~indent c_type name = Text indent ++ c_type ++ Text (" " ^ name ^ ";\n")

let render_field_declarations types ~indent (fields : Memory_layout.field list) =
  ( C_text.Concat
      (List.map
         (fun (field : Memory_layout.field) ->
           render_member ~indent (render_member_type types field.member) ("f_" ^ field.name))
         fields),
    List.concat_map (fun (field : Memory_layout.field) -> list_held_keys types field.member) fields
  )

let render_signature_parameters types (parameters : Lowered.ty list) names : C_text.t =
  match parameters with
  | [] -> Text "void"
  | _ ->
      C_text.join ", "
        (List.mapi
           (fun position ty ->
             let qualified =
               match ty with
               | Lowered.Pointer _ -> render_type types ty ++ Text "restrict"
               | _ -> render_type types ty
             in
             match names with
             | None -> qualified
             | Some names -> qualified ++ Text " " ++ List.nth names position)
           parameters)

let rec define (types : t) key =
  types.registry.references <- Some [];
  let definition = define_text types key in
  let references =
    match types.registry.references with Some references -> List.rev references | None -> []
  in
  types.registry.references <- None;
  { definition; references }

and define_text types (key : C_text.key) =
  match key with
  | Type ty -> (
      match (compute_layout types ty).form with
      | Tag_only { tag; _ } -> Typedef (C_text.Text (C_runtime.render_integer_type tag))
      | Niche_encoded { dataful = { payload = { form = Scalar scalar; _ }; _ }; _ } ->
          Typedef (render_scalar_type types scalar)
      | Niche_encoded { dataful = { payload = { form = Struct fields; _ }; _ }; _ } | Struct fields
        ->
          let body, holds = render_field_declarations types ~indent:"  " fields in
          Struct { body; holds }
      | Array { element; count; _ } ->
          Struct
            {
              body =
                render_member ~indent:"  " (render_value_type types element)
                  (Printf.sprintf "items[%d]" count);
              holds = (if is_struct types element then [ Type element ] else []);
            }
      | Tagged { tag; variants; _ } ->
          let members, holds =
            List.split
              (List.filter_map
                 (fun (variant : Memory_layout.variant) ->
                   let name = "v_" ^ variant.name in
                   match variant.payload.form with
                   | Zero_size -> None
                   | Struct fields ->
                       let body, holds = render_field_declarations types ~indent:"      " fields in
                       Some (Text "    struct {\n" ++ body ++ Text ("    } " ^ name ^ ";\n"), holds)
                   | Scalar scalar ->
                       Some (render_member ~indent:"    " (render_scalar_type types scalar) name, [])
                   | _ ->
                       C_runtime.raise_bug "a variant's payload is a struct, a pointer, or nothing")
                 variants)
          in
          Struct
            {
              body =
                Text (Printf.sprintf "  %s tag;\n  union {\n" (C_runtime.render_integer_type tag))
                ++ Concat members ++ Text "  } payload;\n";
              holds = List.concat holds;
            }
      | Niche_encoded _ -> C_runtime.raise_bug "a niche-encoded payload is a struct or a pointer"
      | Zero_size | Scalar _ -> C_runtime.raise_bug "%s needs no definition" (Ground.to_string ty))
  | Block (ty, variant) -> (
      match (Memory_layout.lay_out_block types.env ty variant).form with
      | Struct fields ->
          let body, holds = render_field_declarations types ~indent:"  " fields in
          Struct { body; holds }
      | _ -> C_runtime.raise_bug "the block of %s.%s has no fields" (Ground.to_string ty) variant)
  | Code function_type ->
      let signature = Convention.make_function_value_signature types.env function_type in
      Code_typedef
        (Text "typedef "
        ++ (match signature.result with None -> Text "void" | Some ty -> render_type types ty)
        ++ Text " (*" ++ Name (Type_name key) ++ Text ")("
        ++ render_signature_parameters types signature.parameters None
        ++ Text ");\n")
  | Evidence nested_index ->
      Struct
        {
          body =
            Text
              (Printf.sprintf
                 "  struct truss_evidence evidence;\n  const struct truss_evidence *outer[%d];\n"
                 nested_index);
          holds = [];
        }
  | Capabilities count ->
      Struct
        {
          body = Text (Printf.sprintf "  struct truss_capability entries[%d];\n" (count + 1));
          holds = [];
        }
  | Environment (_, nested_index) ->
      let fields = read_environment types nested_index in
      Struct
        {
          body =
            Concat
              (List.map
                 (fun (name, ty) -> render_member ~indent:"  " (render_type types ty) ("f_" ^ name))
                 fields);
          holds =
            List.concat_map
              (fun (_, ty) ->
                match ty with
                | Lowered.Value ty when is_struct types ty -> [ C_text.Type ty ]
                | _ -> [])
              fields;
        }
