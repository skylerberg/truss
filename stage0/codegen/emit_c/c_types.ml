(* A file's context, and the C types and definitions of what it names:
   structs, unions, function types, and environments, each defined once and
   before what uses it. *)

open C_runtime

(* Everything a file defines besides functions: C types, each with a name. *)
type key =
  | Type of Ground.ty
  | Block of Ground.ty * string
  | Code of Ground.function_type
  | Environment of string * int  (** The instance's symbol, and the nested function *)
  | Evidence of int
      (** The evidence that a [provide] builds on the stack, with room for this many pointers to the
          evidence its [impl] uses. It has a name so that every use of it in a file is one C type: a
          region that captures such a local holds a pointer to it. *)

let compare_key a b =
  match (a, b) with
  | Type a, Type b -> Ground.compare a b
  | Block (a, v), Block (b, w) ->
      let c = Ground.compare a b in
      if c <> 0 then c else String.compare v w
  | Code a, Code b -> Ground.compare (Function a) (Function b)
  | Environment (s, n), Environment (t, m) ->
      let c = String.compare s t in
      if c <> 0 then c else Int.compare n m
  | Evidence n, Evidence m -> Int.compare n m
  | _ ->
      let rank = function
        | Type _ -> 0
        | Block _ -> 1
        | Code _ -> 2
        | Environment _ -> 3
        | Evidence _ -> 4
      in
      Int.compare (rank a) (rank b)

module Keys = Map.Make (struct
  type t = key

  let compare = compare_key
end)

let key_name = function
  | Type ty -> Instance.type_symbol ty
  | Block (ty, variant) -> Instance.type_symbol ty ^ "_Block_" ^ variant
  | Code f -> Instance.type_symbol (Function f) ^ "_Code"
  | Environment (symbol, n) -> Printf.sprintf "%s_Environment_%d" symbol n
  | Evidence n -> Printf.sprintf "t_Evidence_%d" n

(* How a key is defined: a [typedef] of a scalar or a pointer, which needs
   only forward declarations; a function pointer type; or a [struct], which
   needs the structs it holds by value defined first. *)
type definition =
  | Typedef of string
  | Code_typedef of string
  | Struct of { body : string; holds : key list }

(* A definition, and every key its text names. *)
type defined = { definition : definition; references : key list }

type context = {
  env : Memory_layout.env;
  build : build;
  mutable order : key list;  (** Registered keys, most recent first *)
  mutable registered : unit Keys.t;
  mutable environments : (string * Lir.ty) list Keys.t;
  mutable bytes : (string * string) list;  (** Text and name, most recent first *)
  mutable prototypes : (string * string) list;  (** Symbol and declaration, most recent first *)
  mutable anchors : (string * Path.t) list;
  mutable references : key list option;  (** While defining a key, what its text names *)
  mutable helpers_used : string list;
  mutable statics : string list;
      (** Static arrays and blocks that data refers to, most recent first *)
}

let helper context name =
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

let layout context ty = Memory_layout.of_type context.env ty

(* Whether a Truss type is a C [struct], which must be defined before
   anything holds it by value. *)
let is_struct context ty =
  match (layout context ty).form with
  | Struct _ | Array _ | Tagged _ -> true
  | Niche_encoded { dataful; _ } -> (
      match dataful.payload.form with Struct _ -> true | _ -> false)
  | Zero_size | Scalar _ | Tag_only _ -> false

let rec value_c context ty =
  match (layout context ty).form with
  | Zero_size -> "void"
  | Scalar scalar -> scalar_c context scalar
  | _ ->
      register context (Type ty);
      Instance.type_symbol ty

and scalar_c context : Memory_layout.scalar -> string = function
  | Integer integer -> integer_c integer
  | Float32 -> "float"
  | Float64 -> "double"
  | Bool -> "uint8_t"
  | Character -> "uint32_t"
  | Pointer pointee | Nullable_pointer pointee -> pointee_c context pointee

and pointee_c context : Memory_layout.pointee -> string = function
  | Data ty -> value_c context ty ^ " *"
  | Block (ty, variant) ->
      register context (Block (ty, variant));
      key_name (Block (ty, variant)) ^ " *"
  | Code f ->
      register context (Code f);
      key_name (Code f)
  | Opaque -> "void *"

let rec c_ty context symbol : Lir.ty -> string = function
  | Value ty -> value_c context ty
  | Pointer { target; writable } ->
      (if writable then "" else "const ") ^ c_ty context symbol target ^ " *"
  | Raw scalar -> scalar_c context scalar
  | Environment n ->
      register context (Environment (symbol, n));
      key_name (Environment (symbol, n))
  | Evidence n ->
      let key = Evidence (max n 1) in
      register context key;
      key_name key

let member_c context : Memory_layout.member -> string = function
  | Typed ty -> value_c context ty
  | Raw scalar -> scalar_c context scalar

(* The structs a member is held as by value. *)
let holds_member context : Memory_layout.member -> key list = function
  | Typed ty when is_struct context ty -> [ Type ty ]
  | Typed _ | Raw _ -> []

let field_declarations context (fields : Memory_layout.field list) =
  ( String.concat ""
      (List.map
         (fun (field : Memory_layout.field) ->
           Printf.sprintf "  %s f_%s;\n" (member_c context field.member) field.name)
         fields),
    List.concat_map (fun (field : Memory_layout.field) -> holds_member context field.member) fields
  )

let signature_parameters context symbol (parameters : Lir.ty list) names =
  match parameters with
  | [] -> "void"
  | _ ->
      String.concat ", "
        (List.mapi
           (fun i ty ->
             let c = c_ty context symbol ty in
             let qualified = match ty with Lir.Pointer _ -> c ^ "restrict" | _ -> c in
             match names with None -> qualified | Some names -> qualified ^ " " ^ List.nth names i)
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
      match (layout context ty).form with
      | Tag_only { tag; _ } -> Typedef (integer_c tag)
      | Niche_encoded { dataful = { payload = { form = Scalar scalar; _ }; _ }; _ } ->
          Typedef (scalar_c context scalar)
      | Niche_encoded { dataful = { payload = { form = Struct fields; _ }; _ }; _ } | Struct fields
        ->
          let body, holds = field_declarations context fields in
          Struct { body; holds }
      | Array { element; count; _ } ->
          Struct
            {
              body = Printf.sprintf "  %s items[%d];\n" (value_c context element) count;
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
                       let body, holds = field_declarations context fields in
                       let body =
                         String.concat ""
                           (List.map
                              (fun line -> "  " ^ line ^ "\n")
                              (List.filter (( <> ) "") (String.split_on_char '\n' body)))
                       in
                       Some (Printf.sprintf "    struct {\n%s    } v_%s;\n" body variant.name, holds)
                   | Scalar scalar ->
                       Some
                         (Printf.sprintf "    %s v_%s;\n" (scalar_c context scalar) variant.name, [])
                   | _ -> bug "a variant's payload is a struct, a pointer, or nothing")
                 variants)
          in
          Struct
            {
              body =
                Printf.sprintf "  %s tag;\n  union {\n%s  } payload;\n" (integer_c tag)
                  (String.concat "" members);
              holds = List.concat holds;
            }
      | Niche_encoded _ -> bug "a niche-encoded payload is a struct or a pointer"
      | Zero_size | Scalar _ -> bug "%s needs no definition" (Ground.to_string ty))
  | Block (ty, variant) -> (
      match (Memory_layout.block context.env ty variant).form with
      | Struct fields ->
          let body, holds = field_declarations context fields in
          Struct { body; holds }
      | _ -> bug "the block of %s.%s has no fields" (Ground.to_string ty) variant)
  | Code f ->
      let signature = Convention.function_value context.env f in
      let result = match signature.result with None -> "void" | Some ty -> c_ty context "" ty in
      Code_typedef
        (Printf.sprintf "typedef %s (*%s)(%s);\n" result (key_name key)
           (signature_parameters context "" signature.parameters None))
  | Evidence n ->
      Struct
        {
          body =
            Printf.sprintf "  struct t_evidence evidence;\n  const struct t_evidence *outer[%d];\n"
              n;
          holds = [];
        }
  | Environment _ ->
      let fields = match Keys.find_opt key context.environments with Some f -> f | None -> [] in
      let symbol = match key with Environment (symbol, _) -> symbol | _ -> "" in
      Struct
        {
          body =
            String.concat ""
              (List.map
                 (fun (name, ty) -> Printf.sprintf "  %s f_%s;\n" (c_ty context symbol ty) name)
                 fields);
          holds =
            List.concat_map
              (fun (_, ty) ->
                match ty with Lir.Value ty when is_struct context ty -> [ Type ty ] | _ -> [])
              fields;
        }
