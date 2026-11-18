type key =
  | Type of Ground.ty
  | Block of Ground.ty * string
  | Code of Ground.function_type
  | Environment of string * int
  | Evidence of int
  | Capabilities of int

module Keys = Map.Make (struct
  type t = key

  let compare = Stdlib.compare
end)

let render_key_name = function
  | Type ty -> Mangling.make_type_name ty
  | Block (ty, variant) -> Mangling.make_type_name ty ^ "_Block_" ^ variant
  | Code function_type -> Mangling.make_type_name (Function function_type) ^ "_Code"
  | Environment (symbol, nested_index) -> Printf.sprintf "%s_Environment_%d" symbol nested_index
  | Evidence nested_index -> Printf.sprintf "t_Evidence_%d" nested_index
  | Capabilities count -> Printf.sprintf "t_Capabilities_%d" count

type definition =
  | Typedef of string
  | Code_typedef of string
  | Struct of { body : string; holds : key list }

type defined = { definition : definition; references : key list }

type t = {
  env : Memory_layout.env;
  mutable order : key list;
  mutable registered : unit Keys.t;
  mutable environments : (string * Lowered.ty) list Keys.t;
  mutable references : key list option;
}

let create env =
  { env; order = []; registered = Keys.empty; environments = Keys.empty; references = None }

let add_environment types key fields = types.environments <- Keys.add key fields types.environments

let register types key =
  (match types.references with
  | Some references -> types.references <- Some (key :: references)
  | None -> ());
  if not (Keys.mem key types.registered) then begin
    types.registered <- Keys.add key () types.registered;
    types.order <- key :: types.order
  end

let compute_layout types ty = Memory_layout.of_type types.env ty

let is_struct types (ty : Ground.ty) =
  match (compute_layout types ty).form with
  | Struct _ | Array _ | Tagged _ -> true
  | Niche_encoded { dataful; _ } -> (
      match dataful.payload.form with Struct _ -> true | _ -> false)
  | Zero_size | Scalar _ | Tag_only _ -> false

let rec render_value_type types (ty : Ground.ty) =
  match (compute_layout types ty).form with
  | Zero_size -> "void"
  | Scalar scalar -> render_scalar_type types scalar
  | _ ->
      register types (Type ty);
      Mangling.make_type_name ty

and render_scalar_type types : Memory_layout.scalar -> string = function
  | Integer integer -> C_runtime.render_integer_type integer
  | Float32 -> "float"
  | Float64 -> "double"
  | Bool -> "uint8_t"
  | Character -> "uint32_t"
  | Pointer pointee | Nullable_pointer pointee -> render_pointee_type types pointee

and render_pointee_type types : Memory_layout.pointee -> string = function
  | Data ty -> render_value_type types ty ^ " *"
  | Block (ty, variant) ->
      register types (Block (ty, variant));
      render_key_name (Block (ty, variant)) ^ " *"
  | Code function_type ->
      register types (Code function_type);
      render_key_name (Code function_type)
  | Opaque -> "void *"

let rec render_type types symbol : Lowered.ty -> string = function
  | Value ty -> render_value_type types ty
  | Pointer { target; writable } ->
      (if writable then "" else "const ") ^ render_type types symbol target ^ " *"
  | Raw scalar -> render_scalar_type types scalar
  | Environment nested_index ->
      register types (Environment (symbol, nested_index));
      render_key_name (Environment (symbol, nested_index))
  | Evidence nested_index ->
      let key = Evidence (max nested_index 1) in
      register types key;
      render_key_name key
  | Capabilities count ->
      register types (Capabilities count);
      render_key_name (Capabilities count)
  | Trace -> "struct t_trace"
  | Lend -> "struct t_lend"
  | Lend_mark -> "struct t_lend_mark"

let render_member_type types : Memory_layout.member -> string = function
  | Typed ty -> render_value_type types ty
  | Raw scalar -> render_scalar_type types scalar

let list_held_keys types : Memory_layout.member -> key list = function
  | Typed ty when is_struct types ty -> [ Type ty ]
  | Typed _ | Raw _ -> []

let render_field_declarations types (fields : Memory_layout.field list) =
  ( String.concat ""
      (List.map
         (fun (field : Memory_layout.field) ->
           Printf.sprintf "  %s f_%s;\n" (render_member_type types field.member) field.name)
         fields),
    List.concat_map (fun (field : Memory_layout.field) -> list_held_keys types field.member) fields
  )

let render_signature_parameters types symbol (parameters : Lowered.ty list) names =
  match parameters with
  | [] -> "void"
  | _ ->
      String.concat ", "
        (List.mapi
           (fun position ty ->
             let order = render_type types symbol ty in
             let qualified = match ty with Lowered.Pointer _ -> order ^ "restrict" | _ -> order in
             match names with
             | None -> qualified
             | Some names -> qualified ^ " " ^ List.nth names position)
           parameters)

let rec define types key =
  types.references <- Some [];
  let definition = define_text types key in
  let references =
    match types.references with Some references -> List.rev references | None -> []
  in
  types.references <- None;
  { definition; references }

and define_text types key =
  match key with
  | Type ty -> (
      match (compute_layout types ty).form with
      | Tag_only { tag; _ } -> Typedef (C_runtime.render_integer_type tag)
      | Niche_encoded { dataful = { payload = { form = Scalar scalar; _ }; _ }; _ } ->
          Typedef (render_scalar_type types scalar)
      | Niche_encoded { dataful = { payload = { form = Struct fields; _ }; _ }; _ } | Struct fields
        ->
          let body, holds = render_field_declarations types fields in
          Struct { body; holds }
      | Array { element; count; _ } ->
          Struct
            {
              body = Printf.sprintf "  %s items[%d];\n" (render_value_type types element) count;
              holds = (if is_struct types element then [ Type element ] else []);
            }
      | Tagged { tag; variants; _ } ->
          let members, holds =
            List.split
              (List.filter_map
                 (fun (variant : Memory_layout.variant) ->
                   match variant.payload.form with
                   | Zero_size -> None
                   | Struct fields ->
                       let body, holds = render_field_declarations types fields in
                       let body =
                         String.concat ""
                           (List.map
                              (fun line -> "  " ^ line ^ "\n")
                              (List.filter (( <> ) "") (String.split_on_char '\n' body)))
                       in
                       Some (Printf.sprintf "    struct {\n%s    } v_%s;\n" body variant.name, holds)
                   | Scalar scalar ->
                       Some
                         ( Printf.sprintf "    %s v_%s;\n" (render_scalar_type types scalar)
                             variant.name,
                           [] )
                   | _ ->
                       C_runtime.raise_bug "a variant's payload is a struct, a pointer, or nothing")
                 variants)
          in
          Struct
            {
              body =
                Printf.sprintf "  %s tag;\n  union {\n%s  } payload;\n"
                  (C_runtime.render_integer_type tag)
                  (String.concat "" members);
              holds = List.concat holds;
            }
      | Niche_encoded _ -> C_runtime.raise_bug "a niche-encoded payload is a struct or a pointer"
      | Zero_size | Scalar _ -> C_runtime.raise_bug "%s needs no definition" (Ground.to_string ty))
  | Block (ty, variant) -> (
      match (Memory_layout.lay_out_block types.env ty variant).form with
      | Struct fields ->
          let body, holds = render_field_declarations types fields in
          Struct { body; holds }
      | _ -> C_runtime.raise_bug "the block of %s.%s has no fields" (Ground.to_string ty) variant)
  | Code function_type ->
      let signature = Convention.make_function_value_signature types.env function_type in
      let result =
        match signature.result with None -> "void" | Some ty -> render_type types "" ty
      in
      Code_typedef
        (Printf.sprintf "typedef %s (*%s)(%s);\n" result (render_key_name key)
           (render_signature_parameters types "" signature.parameters None))
  | Evidence nested_index ->
      Struct
        {
          body =
            Printf.sprintf "  struct t_evidence evidence;\n  const struct t_evidence *outer[%d];\n"
              nested_index;
          holds = [];
        }
  | Capabilities count ->
      Struct
        { body = Printf.sprintf "  struct t_capability entries[%d];\n" (count + 1); holds = [] }
  | Environment _ ->
      let fields =
        match Keys.find_opt key types.environments with
        | Some function_type -> function_type
        | None -> []
      in
      let symbol = match key with Environment (symbol, _) -> symbol | _ -> "" in
      Struct
        {
          body =
            String.concat ""
              (List.map
                 (fun (name, ty) ->
                   Printf.sprintf "  %s f_%s;\n" (render_type types symbol ty) name)
                 fields);
          holds =
            List.concat_map
              (fun (_, ty) ->
                match ty with Lowered.Value ty when is_struct types ty -> [ Type ty ] | _ -> [])
              fields;
        }
