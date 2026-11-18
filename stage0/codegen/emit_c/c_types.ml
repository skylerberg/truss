type key =
  | Type of Ground.ty
  | Block of Ground.ty * string
  | Code of Ground.function_type
  | Environment of string * int
  | Evidence of int

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

type definition =
  | Typedef of string
  | Code_typedef of string
  | Struct of { body : string; holds : key list }

type defined = { definition : definition; references : key list }

type context = {
  env : Memory_layout.env;
  prefix : string;
  mutable order : key list;
  mutable registered : unit Keys.t;
  mutable environments : (string * Lowered.ty) list Keys.t;
  bytes : (string, int) Hashtbl.t;
  mutable prototypes : (string * string) list;
  mutable sites : Lowered.site list;
  mutable references : key list option;
  mutable helpers_used : string list;
  mutable statics : string list;
  mutable referenced_items : Lowered.Item.t list;
  mutable called : Lowered.Item.t list;
  mutable calls : (Path.t * int) list;
  mutable failures : (C_runtime.failure * Lowered.site) list;
}

let make_context env prefix =
  {
    env;
    prefix;
    order = [];
    registered = Keys.empty;
    environments = Keys.empty;
    bytes = Hashtbl.create 16;
    prototypes = [];
    sites = [];
    references = None;
    helpers_used = [];
    statics = [];
    referenced_items = [];
    called = [];
    calls = [];
    failures = [];
  }

let refer context item =
  if not (List.exists (Lowered.Item.equal item) context.referenced_items) then
    context.referenced_items <- item :: context.referenced_items

let list_referenced_items context ~referrer =
  List.filter
    (fun item -> not (Lowered.Item.equal item referrer))
    (List.rev context.referenced_items)

let use_helper context name =
  if not (List.mem name context.helpers_used) then
    context.helpers_used <- name :: context.helpers_used;
  name

let register context key =
  (match context.references with
  | Some references -> context.references <- Some (key :: references)
  | None -> ());
  if not (Keys.mem key context.registered) then begin
    context.registered <- Keys.add key () context.registered;
    context.order <- key :: context.order
  end

let compute_layout context ty = Memory_layout.of_type context.env ty

let is_struct context (ty : Ground.ty) =
  match (compute_layout context ty).form with
  | Struct _ | Array _ | Tagged _ -> true
  | Niche_encoded { dataful; _ } -> (
      match dataful.payload.form with Struct _ -> true | _ -> false)
  | Zero_size | Scalar _ | Tag_only _ -> false

let rec render_value_type context (ty : Ground.ty) =
  match (compute_layout context ty).form with
  | Zero_size -> "void"
  | Scalar scalar -> render_scalar_type context scalar
  | _ ->
      register context (Type ty);
      Mangling.make_type_name ty

and render_scalar_type context : Memory_layout.scalar -> string = function
  | Integer integer -> C_runtime.render_integer_type integer
  | Float32 -> "float"
  | Float64 -> "double"
  | Bool -> "uint8_t"
  | Character -> "uint32_t"
  | Pointer pointee | Nullable_pointer pointee -> render_pointee_type context pointee

and render_pointee_type context : Memory_layout.pointee -> string = function
  | Data ty -> render_value_type context ty ^ " *"
  | Block (ty, variant) ->
      register context (Block (ty, variant));
      render_key_name (Block (ty, variant)) ^ " *"
  | Code function_type ->
      register context (Code function_type);
      render_key_name (Code function_type)
  | Opaque -> "void *"

let rec render_type context symbol : Lowered.ty -> string = function
  | Value ty -> render_value_type context ty
  | Pointer { target; writable } ->
      (if writable then "" else "const ") ^ render_type context symbol target ^ " *"
  | Raw scalar -> render_scalar_type context scalar
  | Environment nested_index ->
      register context (Environment (symbol, nested_index));
      render_key_name (Environment (symbol, nested_index))
  | Evidence nested_index ->
      let key = Evidence (max nested_index 1) in
      register context key;
      render_key_name key
  | Trace -> "struct t_trace"
  | Lend -> "struct " ^ use_helper context "t_lend"
  | Lend_mark -> "struct " ^ use_helper context "t_lend" ^ "_mark"

let render_member_type context : Memory_layout.member -> string = function
  | Typed ty -> render_value_type context ty
  | Raw scalar -> render_scalar_type context scalar

let list_held_keys context : Memory_layout.member -> key list = function
  | Typed ty when is_struct context ty -> [ Type ty ]
  | Typed _ | Raw _ -> []

let render_field_declarations context (fields : Memory_layout.field list) =
  ( String.concat ""
      (List.map
         (fun (field : Memory_layout.field) ->
           Printf.sprintf "  %s f_%s;\n" (render_member_type context field.member) field.name)
         fields),
    List.concat_map
      (fun (field : Memory_layout.field) -> list_held_keys context field.member)
      fields )

let render_signature_parameters context symbol (parameters : Lowered.ty list) names =
  match parameters with
  | [] -> "void"
  | _ ->
      String.concat ", "
        (List.mapi
           (fun position ty ->
             let order = render_type context symbol ty in
             let qualified = match ty with Lowered.Pointer _ -> order ^ "restrict" | _ -> order in
             match names with
             | None -> qualified
             | Some names -> qualified ^ " " ^ List.nth names position)
           parameters)

let rec define context key =
  context.references <- Some [];
  let definition = define_text context key in
  let references =
    match context.references with Some references -> List.rev references | None -> []
  in
  context.references <- None;
  { definition; references }

and define_text context key =
  match key with
  | Type ty -> (
      match (compute_layout context ty).form with
      | Tag_only { tag; _ } -> Typedef (C_runtime.render_integer_type tag)
      | Niche_encoded { dataful = { payload = { form = Scalar scalar; _ }; _ }; _ } ->
          Typedef (render_scalar_type context scalar)
      | Niche_encoded { dataful = { payload = { form = Struct fields; _ }; _ }; _ } | Struct fields
        ->
          let body, holds = render_field_declarations context fields in
          Struct { body; holds }
      | Array { element; count; _ } ->
          Struct
            {
              body = Printf.sprintf "  %s items[%d];\n" (render_value_type context element) count;
              holds = (if is_struct context element then [ Type element ] else []);
            }
      | Tagged { tag; variants; _ } ->
          let members, holds =
            List.split
              (List.filter_map
                 (fun (variant : Memory_layout.variant) ->
                   match variant.payload.form with
                   | Zero_size -> None
                   | Struct fields ->
                       let body, holds = render_field_declarations context fields in
                       let body =
                         String.concat ""
                           (List.map
                              (fun line -> "  " ^ line ^ "\n")
                              (List.filter (( <> ) "") (String.split_on_char '\n' body)))
                       in
                       Some (Printf.sprintf "    struct {\n%s    } v_%s;\n" body variant.name, holds)
                   | Scalar scalar ->
                       Some
                         ( Printf.sprintf "    %s v_%s;\n"
                             (render_scalar_type context scalar)
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
      match (Memory_layout.lay_out_block context.env ty variant).form with
      | Struct fields ->
          let body, holds = render_field_declarations context fields in
          Struct { body; holds }
      | _ -> C_runtime.raise_bug "the block of %s.%s has no fields" (Ground.to_string ty) variant)
  | Code function_type ->
      let signature = Convention.make_function_value_signature context.env function_type in
      let result =
        match signature.result with None -> "void" | Some ty -> render_type context "" ty
      in
      Code_typedef
        (Printf.sprintf "typedef %s (*%s)(%s);\n" result (render_key_name key)
           (render_signature_parameters context "" signature.parameters None))
  | Evidence nested_index ->
      Struct
        {
          body =
            Printf.sprintf "  struct t_evidence evidence;\n  const struct t_evidence *outer[%d];\n"
              nested_index;
          holds = [];
        }
  | Environment _ ->
      let fields =
        match Keys.find_opt key context.environments with
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
                   Printf.sprintf "  %s f_%s;\n" (render_type context symbol ty) name)
                 fields);
          holds =
            List.concat_map
              (fun (_, ty) ->
                match ty with Lowered.Value ty when is_struct context ty -> [ Type ty ] | _ -> [])
              fields;
        }
