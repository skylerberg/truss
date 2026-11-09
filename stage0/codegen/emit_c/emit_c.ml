type build = Development | Release
type linkage = External | Internal

let bug format = Printf.ksprintf (fun message -> invalid_arg ("Emit_c: " ^ message)) format
let anchor_symbol definition = "t_Anchor_" ^ Instance.path_symbol definition

let anchor_struct =
  "struct t_anchor {\n  const uint8_t *path;\n  t_usize path_length;\n  uint32_t line;\n};\n"

let integer_c : Memory_layout.integer -> string = function
  | Int8 -> "int8_t"
  | Int16 -> "int16_t"
  | Int32 -> "int32_t"
  | Int64 -> "int64_t"
  | UInt8 -> "uint8_t"
  | UInt16 -> "uint16_t"
  | UInt32 -> "uint32_t"
  | UInt64 -> "uint64_t"
  | USize -> "t_usize"
  | ISize -> "t_isize"

let unsigned_c : Memory_layout.integer -> string = function
  | Int8 | UInt8 -> "uint8_t"
  | Int16 | UInt16 -> "uint16_t"
  | Int32 | UInt32 -> "uint32_t"
  | Int64 | UInt64 -> "uint64_t"
  | USize | ISize -> "t_usize"

let signed : Memory_layout.integer -> bool = function
  | Int8 | Int16 | Int32 | Int64 | ISize -> true
  | UInt8 | UInt16 | UInt32 | UInt64 | USize -> false

(* What every file declares first: the fixed-width integers, from the
   compiler's own predefined macros, the target's [USize], and the runtime. *)
let runtime_declarations (target : Memory_layout.target) =
  let usize, isize =
    if target.usize_bytes = 8 then ("__UINT64_TYPE__", "__INT64_TYPE__")
    else ("__UINT32_TYPE__", "__INT32_TYPE__")
  in
  String.concat ""
    [
      "typedef __INT8_TYPE__ int8_t;\n";
      "typedef __INT16_TYPE__ int16_t;\n";
      "typedef __INT32_TYPE__ int32_t;\n";
      "typedef __INT64_TYPE__ int64_t;\n";
      "typedef __UINT8_TYPE__ uint8_t;\n";
      "typedef __UINT16_TYPE__ uint16_t;\n";
      "typedef __UINT32_TYPE__ uint32_t;\n";
      "typedef __UINT64_TYPE__ uint64_t;\n";
      Printf.sprintf "typedef %s t_usize;\n" usize;
      Printf.sprintf "typedef %s t_isize;\n" isize;
      anchor_struct;
      "_Noreturn void t_runtime_panic(const uint8_t *message, t_usize length, const struct \
       t_anchor *anchor, uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_assertion_failed(const uint8_t *message, t_usize length, const \
       struct t_anchor *anchor, uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_todo(const uint8_t *message, t_usize length, const struct t_anchor \
       *anchor, uint32_t line, uint32_t column);\n";
      "void t_runtime_echo(const uint8_t *text, t_usize length, const struct t_anchor *anchor, \
       uint32_t line, uint32_t column);\n";
      "_Noreturn void t_runtime_compiler_bug(void);\n";
      "uint8_t *t_runtime_program_argument(void *arguments, int32_t index, t_usize *length);\n";
      "struct t_evidence {\n\
      \  void *implementation;\n\
      \  const void *const *table;\n\
      \  const struct t_evidence *const *outer;\n\
       };\n";
      "void *t_runtime_allocate(t_usize size, t_usize alignment);\n";
      "void *t_runtime_reallocate(void *pointer, t_usize old_size, t_usize size, t_usize alignment);\n";
      "void t_runtime_free(void *pointer);\n";
      "void t_runtime_storage_grow(void **buffer, t_usize length, t_usize *capacity, t_usize size, \
       t_usize alignment, t_usize minimum);\n";
      "t_isize t_runtime_write(int32_t descriptor, const uint8_t *bytes, t_usize count);\n";
      "t_isize t_runtime_read(int32_t descriptor, uint8_t *bytes, t_usize count);\n";
      "int64_t t_runtime_clock_now(void);\n";
      "void t_runtime_random_fill(uint8_t *bytes, t_usize count);\n";
      "void t_runtime_debug_begin(void);\n";
      "void t_runtime_debug_text(const uint8_t *bytes, t_usize count);\n";
      "void t_runtime_debug_signed(int64_t value);\n";
      "void t_runtime_debug_unsigned(uint64_t value);\n";
      "void t_runtime_debug_float32(float value);\n";
      "void t_runtime_debug_float64(double value);\n";
      "void t_runtime_debug_bool(uint8_t value);\n";
      "void t_runtime_debug_character(uint32_t value);\n";
      "void t_runtime_debug_string(const uint8_t *bytes, t_usize count);\n";
      "uint8_t *t_runtime_debug_bytes(void);\n";
      "t_usize t_runtime_debug_length(void);\n";
    ]

(* Small functions that generated code calls, each emitted only into the
   files that use it. *)
let helpers =
  [
    ( "t_compare_bytes",
      {|static inline int32_t t_compare_bytes(const void *first, const void *second, t_usize count) {
  int order = __builtin_memcmp(first, second, count);
  return (order > 0) - (order < 0);
}
|}
    );
    ( "t_float64_bits",
      {|static inline uint64_t t_float64_bits(double value) {
  uint64_t bits;
  if (value != value) return 0x7ff8000000000000ULL;
  __builtin_memcpy(&bits, &value, 8);
  return bits;
}
|}
    );
    ( "t_float32_bits",
      {|static inline uint32_t t_float32_bits(float value) {
  uint32_t bits;
  if (value != value) return 0x7fc00000U;
  __builtin_memcpy(&bits, &value, 4);
  return bits;
}
|}
    );
    ( "t_float64_from_bits",
      {|static inline double t_float64_from_bits(uint64_t bits) {
  double value;
  __builtin_memcpy(&value, &bits, 8);
  return value;
}
|}
    );
    ( "t_float32_from_bits",
      {|static inline float t_float32_from_bits(uint32_t bits) {
  float value;
  __builtin_memcpy(&value, &bits, 4);
  return value;
}
|}
    );
  ]

(* Everything a file defines besides functions: C types, each with a name. *)
type key =
  | Type of Ground.ty
  | Block of Ground.ty * string
  | Code of Ground.function_type
  | Environment of string * int  (** The instance's symbol, and the nested function *)

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
  | _ ->
      let rank = function Type _ -> 0 | Block _ -> 1 | Code _ -> 2 | Environment _ -> 3 in
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

(* Places and operands *)

type function_context = { symbol : string; f : Lir.function_ }

let local_name (f : Lir.function_) local =
  match f.locals.(local).name with
  | Some name -> Printf.sprintf "l%d_%s" local name
  | None -> Printf.sprintf "l%d" local

let erased context : Lir.ty -> bool = function
  | Value ty -> (layout context ty).size = 0
  | Pointer _ | Raw _ | Environment _ -> false

let find_field (fields : Memory_layout.field list) name =
  List.find_opt (fun (field : Memory_layout.field) -> field.name = name) fields

let declare_prototype context symbol declaration =
  if not (List.mem_assoc symbol context.prototypes) then
    context.prototypes <- (symbol, declaration) :: context.prototypes

let integer_literal integer value =
  let c = integer_c integer in
  if Z.sign value >= 0 then Printf.sprintf "((%s)%sULL)" c (Z.to_string value)
  else if signed integer && Z.equal value (Z.neg (Z.shift_left Z.one 63)) then
    Printf.sprintf "((%s)(-9223372036854775807LL - 1))" c
  else Printf.sprintf "((%s)%sLL)" c (Z.to_string value)

let float64_literal context bits =
  let value = Int64.float_of_bits bits in
  if Float.is_finite value then Printf.sprintf "%h" value
  else Printf.sprintf "%s(0x%LxULL)" (helper context "t_float64_from_bits") bits

let float32_literal context bits =
  let value = Int32.float_of_bits bits in
  if Float.is_finite value then Printf.sprintf "%hf" value
  else Printf.sprintf "%s(0x%lxU)" (helper context "t_float32_from_bits") bits

let bytes_name context text =
  match List.assoc_opt text context.bytes with
  | Some name -> name
  | None ->
      let name = Printf.sprintf "t_bytes_%d" (List.length context.bytes) in
      context.bytes <- (text, name) :: context.bytes;
      name

let function_ref_symbol fc : Lir.function_ref -> string = function
  | Instance key -> Instance.symbol key
  | Nested n -> Printf.sprintf "%s_Nested_%d" fc.symbol n

let environment_of context fc n =
  match Keys.find_opt (Environment (fc.symbol, n)) context.environments with
  | Some fields -> fields
  | None -> []

(* Whether a variant of a sum type keeps its fields in a block. *)
let indirect context sum variant =
  let is_block (payload : Memory_layout.t) =
    match payload.form with Scalar (Pointer (Block _)) -> true | _ -> false
  in
  match (layout context sum).form with
  | Tagged { variants; _ } ->
      List.exists
        (fun (v : Memory_layout.variant) -> v.name = variant && is_block v.payload)
        variants
  | Niche_encoded { dataful; _ } -> dataful.name = variant && is_block dataful.payload
  | _ -> false

(* The C expression for the pointer to an [indirect] variant's block. *)
let block_pointer context text sum variant =
  match (layout context sum).form with
  | Tagged _ -> text ^ ".payload.v_" ^ variant
  | Niche_encoded _ -> text
  | _ -> bug "a block of %s, which is not a sum type" (Ground.to_string sum)

let rec place_c context fc (place : Lir.place) : (string * Lir.ty) option =
  let root =
    match place.root with
    | Local local -> (local_name fc.f local, fc.f.locals.(local).ty)
    | Static { key; ty } ->
        let symbol = Instance.symbol key in
        declare_prototype context symbol
          (Printf.sprintf "extern const %s %s;\n" (value_c context ty) symbol);
        (symbol, Lir.Value ty)
  in
  let text (text, (ty : Lir.ty)) (projection : Lir.projection) =
    match (projection, ty) with
    | Deref, _ -> "(*" ^ text ^ ")"
    | Field name, _ -> text ^ ".f_" ^ name
    | Variant_field { variant; field }, Value sum ->
        if indirect context sum variant then block_pointer context text sum variant ^ "->f_" ^ field
        else
          (match (layout context sum).form with
            | Tagged _ -> text ^ ".payload.v_" ^ variant
            | _ -> text)
          ^ ".f_" ^ field
    | Index index, Value _ -> text ^ ".items[" ^ operand_c_exn context fc index ^ "]"
    | Index index, _ -> text ^ "[" ^ operand_c_exn context fc index ^ "]"
    | Variant_field _, _ -> bug "a variant of a place that is not a value"
  in
  let rec walk ((_, ty) as current) = function
    | [] -> Some current
    | projection :: rest -> (
        match
          Lir.projection_type context.env ~environment:(environment_of context fc) ty projection
        with
        | None -> None
        | Some next -> walk (text current projection, next) rest)
  in
  if erased context (snd root) then None else walk root place.projections

and operand_c context fc : Lir.operand -> (string * Lir.ty) option = function
  | Copy place | Move place -> place_c context fc place
  | Address { place; writable } -> (
      match place_c context fc place with
      | Some (text, ty) -> Some ("(&" ^ text ^ ")", Lir.Pointer { target = ty; writable })
      | None -> bug "the address of a place of zero size")
  | Constant constant -> Some (constant_c context constant)

and operand_c_exn context fc operand =
  match operand_c context fc operand with
  | Some (text, _) -> text
  | None -> bug "an operand of zero size"

and constant_c context : Lir.constant -> string * Lir.ty = function
  | Integer (integer, value) -> (integer_literal integer value, Raw (Integer integer))
  | Float32 bits -> (float32_literal context bits, Raw Float32)
  | Float64 bits -> (float64_literal context bits, Raw Float64)
  | Bool value -> ((if value then "((uint8_t)1)" else "((uint8_t)0)"), Raw Bool)
  | Character code -> (Printf.sprintf "((uint32_t)0x%xU)" code, Raw Character)
  | Bytes text -> ("((void *)" ^ bytes_name context text ^ ")", Raw (Pointer Opaque))
  | Null -> ("((void *)0)", Raw (Nullable_pointer Opaque))
  | Symbol_address key ->
      let symbol = Instance.symbol key in
      declare_prototype context symbol
        (match key with
        | Table _ | Any_table _ -> Printf.sprintf "extern const void *const %s[];\n" symbol
        | _ -> Printf.sprintf "extern const struct t_evidence %s;\n" symbol);
      ("((void *)&" ^ symbol ^ ")", Raw (Pointer Opaque))

(* The scalar a value of a type is, for operators. *)
let scalar_of context : Lir.ty -> Memory_layout.scalar = function
  | Value ty -> (
      match (layout context ty).form with
      | Scalar scalar -> scalar
      | Tag_only { tag; _ } -> Integer tag
      | _ -> bug "an operator on %s, which is not a scalar" (Ground.to_string ty))
  | Raw scalar -> scalar
  | Pointer _ | Environment _ -> Pointer Opaque

let is_float : Memory_layout.scalar -> bool = function Float32 | Float64 -> true | _ -> false

let bit_width context (scalar : Memory_layout.scalar) =
  8 * Memory_layout.scalar_size (Memory_layout.target context.env) scalar

let unsigned_of context (scalar : Memory_layout.scalar) =
  match scalar with Integer integer -> unsigned_c integer | _ -> scalar_c context scalar

(* Float comparisons follow DESIGN.md's lawful rules: every NaN equals every
   NaN, and NaN comes after every number. *)
let lawful_equal a b = Printf.sprintf "(%s == %s || (%s != %s && %s != %s))" a b a a b b
let lawful_less a b = Printf.sprintf "(%s < %s || (%s == %s && %s != %s))" a b a a b b

let binary_c context (op : Lir.binary) (a, a_ty) (b, _) =
  let scalar = scalar_of context a_ty in
  let c = scalar_c context scalar in
  let boolean text = Printf.sprintf "((uint8_t)%s)" text in
  let arithmetic symbol =
    if is_float scalar then Printf.sprintf "(%s %s %s)" a symbol b
    else Printf.sprintf "((%s)(%s %s %s))" c a symbol b
  in
  let compare symbol = boolean (Printf.sprintf "(%s %s %s)" a symbol b) in
  let mask = bit_width context scalar - 1 in
  match op with
  | Add -> arithmetic "+"
  | Subtract -> arithmetic "-"
  | Multiply -> arithmetic "*"
  | Divide -> arithmetic "/"
  | Remainder ->
      if is_float scalar then
        Printf.sprintf "%s(%s, %s)"
          (if scalar = Float32 then "__builtin_fmodf" else "__builtin_fmod")
          a b
      else arithmetic "%"
  | Bit_and -> arithmetic "&"
  | Bit_or -> arithmetic "|"
  | Bit_xor -> arithmetic "^"
  | Shift_left ->
      Printf.sprintf "((%s)((%s)%s << (%s & %d)))" c (unsigned_of context scalar) a b mask
  | Shift_right -> Printf.sprintf "((%s)(%s >> (%s & %d)))" c a b mask
  | Equal -> if is_float scalar then boolean (lawful_equal a b) else compare "=="
  | Not_equal -> if is_float scalar then boolean ("!" ^ lawful_equal a b) else compare "!="
  | Less -> if is_float scalar then boolean (lawful_less a b) else compare "<"
  | Less_equal -> if is_float scalar then boolean ("!" ^ lawful_less b a) else compare "<="
  | Greater -> if is_float scalar then boolean (lawful_less b a) else compare ">"
  | Greater_equal -> if is_float scalar then boolean ("!" ^ lawful_less a b) else compare ">="
  | Ieee_equal -> compare "=="
  | Ieee_less -> compare "<"
  | Ieee_less_equal -> compare "<="

let unary_c context (op : Lir.unary) (a, a_ty) =
  let scalar = scalar_of context a_ty in
  let c = scalar_c context scalar in
  match op with
  | Negate -> if is_float scalar then "(-" ^ a ^ ")" else Printf.sprintf "((%s)-%s)" c a
  | Not -> "((uint8_t)!" ^ a ^ ")"
  | Complement -> Printf.sprintf "((%s)~%s)" c a

(* The C expression for the scalar a niche path reaches. *)
let niche_c text (niche : Memory_layout.niche) =
  List.fold_left
    (fun text (step : Memory_layout.step) ->
      match step with Field name -> text ^ ".f_" ^ name | Tag -> text ^ ".tag")
    text niche.path

let niche_value context (niche : Memory_layout.niche) value =
  match niche.scalar with
  | Pointer _ -> "((void *)0)"
  | scalar -> Printf.sprintf "((%s)%sULL)" (scalar_c context scalar) (Z.to_string value)

let is_variant_c context text sum variant =
  let layout = layout context sum in
  match Memory_layout.discriminant layout variant with
  | Only -> "((uint8_t)1)"
  | Tag_value value -> (
      let literal = Printf.sprintf "%sULL" (Z.to_string value) in
      match layout.form with
      | Tagged { tag; _ } ->
          Printf.sprintf "((uint8_t)(%s.tag == (%s)%s))" text (integer_c tag) literal
      | Tag_only { tag; _ } ->
          Printf.sprintf "((uint8_t)(%s == (%s)%s))" text (integer_c tag) literal
      | _ -> bug "a tag in a type without one")
  | Niche_value value -> (
      match layout.form with
      | Niche_encoded { encoding = Some niche; _ } ->
          Printf.sprintf "((uint8_t)(%s == %s))" (niche_c text niche)
            (niche_value context niche value)
      | _ -> bug "a niche in a type without one")
  | Not_niche -> (
      match layout.form with
      | Niche_encoded { encoding = Some niche; others; _ } -> (
          let at = niche_c text niche in
          match niche.scalar with
          | Pointer _ -> Printf.sprintf "((uint8_t)(%s != ((void *)0)))" at
          | scalar ->
              let c = scalar_c context scalar in
              let stop = Z.add niche.start (Z.of_int (List.length others)) in
              Printf.sprintf "((uint8_t)!(%s >= (%s)%sULL && %s < (%s)%sULL))" at c
                (Z.to_string niche.start) at c (Z.to_string stop))
      | _ -> bug "a niche in a type without one")

(* A record's or a variant's fields as C designated initializers, leaving out
   the fields of zero size. *)
let initializers context fc prefix (fields : Memory_layout.field list)
    (values : (string * Lir.operand) list) =
  String.concat ", "
    (List.filter_map
       (fun (name, operand) ->
         match find_field fields name with
         | None -> None
         | Some _ -> (
             match operand_c context fc operand with
             | Some (text, _) -> Some (Printf.sprintf "%s.f_%s = %s" prefix name text)
             | None -> None))
       values)

let payload_fields (payload : Memory_layout.t) =
  match payload.form with Struct fields -> fields | _ -> []

(* An rvalue, or for building an [indirect] variant the statements that
   allocate its block and then the value. *)
type built =
  | Expression of string
  | Allocating of { block : key; fill : string; value : string -> string }

let build_c context fc ty variant (values : (string * Lir.operand) list) =
  let c = value_c context ty in
  let layout = layout context ty in
  let block_of variant =
    let key = Block (ty, variant) in
    register context key;
    let fields = payload_fields (Memory_layout.block context.env ty variant) in
    (key, Printf.sprintf "(%s){ %s }" (key_name key) (initializers context fc "" fields values))
  in
  match (variant, layout.form) with
  | _, Zero_size -> None
  | None, Struct fields ->
      Some (Expression (Printf.sprintf "((%s){ %s })" c (initializers context fc "" fields values)))
  | Some variant, Tag_only { variants; _ } -> (
      match List.find_index (String.equal variant) variants with
      | Some index -> Some (Expression (Printf.sprintf "((%s)%d)" c index))
      | None -> bug "no variant %s" variant)
  | Some name, Tagged { variants; _ } -> (
      match List.find_opt (fun (v : Memory_layout.variant) -> v.name = name) variants with
      | None -> bug "no variant %s" name
      | Some v -> (
          match v.payload.form with
          | Zero_size -> Some (Expression (Printf.sprintf "((%s){ .tag = %d })" c v.index))
          | Struct fields ->
              Some
                (Expression
                   (Printf.sprintf "((%s){ .tag = %d, %s })" c v.index
                      (initializers context fc (".payload.v_" ^ name) fields values)))
          | Scalar (Pointer (Block _)) ->
              let block, fill = block_of name in
              Some
                (Allocating
                   {
                     block;
                     fill;
                     value =
                       (fun pointer ->
                         Printf.sprintf "((%s){ .tag = %d, .payload.v_%s = %s })" c v.index name
                           pointer);
                   })
          | _ -> bug "a payload"))
  | Some name, Niche_encoded { dataful; others; encoding } ->
      if dataful.name = name then
        match dataful.payload.form with
        | Struct fields ->
            Some
              (Expression
                 (Printf.sprintf "((%s){ %s })" c (initializers context fc "" fields values)))
        | Scalar (Pointer (Block _)) ->
            let block, fill = block_of name in
            Some (Allocating { block; fill; value = (fun pointer -> pointer) })
        | _ -> bug "a payload"
      else
        begin match (List.assoc_opt name others, encoding) with
        | Some value, Some niche -> (
            let stored = niche_value context niche value in
            match niche.path with
            | [] -> Some (Expression (Printf.sprintf "((%s)%s)" c stored))
            | path ->
                let designator =
                  String.concat ""
                    (List.map
                       (function Memory_layout.Field name -> ".f_" ^ name | Tag -> ".tag")
                       path)
                in
                Some (Expression (Printf.sprintf "((%s){ %s = %s })" c designator stored)))
        | _ -> bug "no variant %s" name
        end
  | _ -> bug "building %s" (Ground.to_string ty)

let prototype context current symbol ?names ~linkage (signature : Lir.signature) =
  let result = match signature.result with None -> "void" | Some ty -> c_ty context current ty in
  Printf.sprintf "%s%s%s %s(%s)"
    (match linkage with Internal -> "static " | External -> "")
    (if signature.returns then "" else "_Noreturn ")
    result symbol
    (signature_parameters context current signature.parameters names)

let rvalue_c context fc (target : Lir.ty) (rvalue : Lir.rvalue) : built option =
  let operand o =
    match operand_c context fc o with Some x -> x | None -> bug "an operand of zero size"
  in
  match rvalue with
  | Use o -> Option.map (fun (text, _) -> Expression text) (operand_c context fc o)
  | Unary (op, o) -> Some (Expression (unary_c context op (operand o)))
  | Binary (op, a, b) -> Some (Expression (binary_c context op (operand a) (operand b)))
  | Convert (o, scalar) ->
      Some (Expression (Printf.sprintf "((%s)%s)" (scalar_c context scalar) (fst (operand o))))
  | Build { ty; variant; fields } -> build_c context fc ty variant fields
  | Is_variant (place, variant) -> (
      match place_c context fc place with
      | Some (text, Value sum) -> Some (Expression (is_variant_c context text sum variant))
      | Some _ -> bug "a variant test on a place that is not a value"
      | None -> Some (Expression "((uint8_t)1)"))
  | Function_value { code; environment } ->
      let f =
        match target with
        | Value (Function f) -> f
        | _ -> bug "a function value stored where no function goes"
      in
      let symbol = function_ref_symbol fc code in
      (match code with
      | Instance _ ->
          declare_prototype context symbol
            (prototype context fc.symbol symbol ~linkage:External
               (Convention.function_value context.env f)
            ^ ";\n")
      | Nested _ -> ());
      let environment =
        match environment with None -> "((void *)0)" | Some e -> fst (operand e)
      in
      Some
        (Expression
           (Printf.sprintf "((%s){ .f_code = &%s, .f_environment = %s })"
              (c_ty context fc.symbol target) symbol environment))

let width_suffix context scalar = match bit_width context scalar with 64 -> "ll" | _ -> ""

let intrinsic_c context (intrinsic : Lir.intrinsic) (arguments : (string * Lir.ty) list) =
  let argument i = fst (List.nth arguments i) in
  let scalar i = scalar_of context (snd (List.nth arguments i)) in
  let width i = bit_width context (scalar i) in
  let unsigned i = Printf.sprintf "((%s)%s)" (unsigned_of context (scalar i)) (argument i) in
  let all = String.concat ", " (List.map fst arguments) in
  let float_builtin name = if scalar 0 = Float32 then name ^ "f" else name in
  match intrinsic with
  | Allocate -> "t_runtime_allocate(" ^ all ^ ")"
  | Reallocate -> "t_runtime_reallocate(" ^ all ^ ")"
  | Free -> "t_runtime_free(" ^ all ^ ")"
  | Copy_bytes -> "__builtin_memcpy(" ^ all ^ ")"
  | Move_bytes -> "__builtin_memmove(" ^ all ^ ")"
  | Compare_bytes -> helper context "t_compare_bytes" ^ "(" ^ all ^ ")"
  | Add_overflow -> "((uint8_t)__builtin_add_overflow(" ^ all ^ "))"
  | Subtract_overflow -> "((uint8_t)__builtin_sub_overflow(" ^ all ^ "))"
  | Multiply_overflow -> "((uint8_t)__builtin_mul_overflow(" ^ all ^ "))"
  | Leading_zeros ->
      Printf.sprintf "(%s == 0 ? %d : __builtin_clzll((unsigned long long)%s) - %d)" (argument 0)
        (width 0) (unsigned 0)
        (64 - width 0)
  | Trailing_zeros ->
      Printf.sprintf "(%s == 0 ? %d : __builtin_ctzll((unsigned long long)%s))" (argument 0)
        (width 0) (unsigned 0)
  | Count_ones -> Printf.sprintf "__builtin_popcountll((unsigned long long)%s)" (unsigned 0)
  | Swap_bytes -> (
      let c = scalar_c context (scalar 0) in
      match width 0 with
      | 8 -> argument 0
      | w -> Printf.sprintf "((%s)__builtin_bswap%d(%s))" c w (unsigned 0))
  | Rotate_left | Rotate_right ->
      let c = scalar_c context (scalar 0) in
      let mask = width 0 - 1 in
      let first, second = if intrinsic = Rotate_left then ("<<", ">>") else (">>", "<<") in
      Printf.sprintf "((%s)((%s %s (%s & %d)) | (%s %s ((-%s) & %d))))" c (unsigned 0) first
        (argument 1) mask (unsigned 0) second (argument 1) mask
  | Multiply_high ->
      let c = scalar_c context (scalar 0) in
      let w = width 0 in
      let signed = match scalar 0 with Integer integer -> signed integer | _ -> false in
      let wide =
        if w = 64 then if signed then "__int128" else "unsigned __int128"
        else if signed then "int64_t"
        else "uint64_t"
      in
      Printf.sprintf "((%s)(((%s)%s * (%s)%s) >> %d))" c wide (argument 0) wide (argument 1) w
  | Square_root -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_sqrt") all
  | Fused_multiply_add -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_fma") all
  | Floor -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_floor") all
  | Ceiling -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_ceil") all
  | Truncate -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_trunc") all
  | Round_even -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_roundeven") all
  | Float_bits ->
      Printf.sprintf "%s(%s)"
        (helper context (if scalar 0 = Float32 then "t_float32_bits" else "t_float64_bits"))
        all
  | Float_from_bits ->
      Printf.sprintf "%s(%s)"
        (helper context (if width 0 = 32 then "t_float32_from_bits" else "t_float64_from_bits"))
        all
  | Grow -> Printf.sprintf "t_runtime_storage_grow((void **)%s)" all
  | System_write -> "t_runtime_write(" ^ all ^ ")"
  | System_read -> "t_runtime_read(" ^ all ^ ")"
  | Clock_now -> "t_runtime_clock_now()"
  | Random_fill -> "t_runtime_random_fill(" ^ all ^ ")"
  | Debug_begin -> "t_runtime_debug_begin(" ^ all ^ ")"
  | Debug_text -> "t_runtime_debug_text(" ^ all ^ ")"
  | Debug_signed -> "t_runtime_debug_signed(" ^ all ^ ")"
  | Debug_unsigned -> "t_runtime_debug_unsigned(" ^ all ^ ")"
  | Debug_float32 -> "t_runtime_debug_float32(" ^ all ^ ")"
  | Debug_float64 -> "t_runtime_debug_float64(" ^ all ^ ")"
  | Debug_bool -> "t_runtime_debug_bool(" ^ all ^ ")"
  | Debug_character -> "t_runtime_debug_character(" ^ all ^ ")"
  | Debug_string -> "t_runtime_debug_string(" ^ all ^ ")"
  | Debug_bytes -> "t_runtime_debug_bytes(" ^ all ^ ")"
  | Debug_length -> "t_runtime_debug_length(" ^ all ^ ")"
  | Evidence_implementation ->
      Printf.sprintf "((const struct t_evidence *)%s)->implementation" (argument 0)
  | Program_argument -> "t_runtime_program_argument(" ^ all ^ ")"
  | Evidence_outer ->
      Printf.sprintf "((void *)((const struct t_evidence *)%s)->outer[%s])" (argument 0)
        (argument 1)

let call_c context fc (target : Lir.target) arguments =
  let arguments = List.filter_map (operand_c context fc) arguments in
  let texts = String.concat ", " (List.map fst arguments) in
  match target with
  | Direct { function_; signature } ->
      let symbol = function_ref_symbol fc function_ in
      let linkage = match function_ with Nested _ -> Internal | Instance _ -> External in
      declare_prototype context symbol
        (prototype context fc.symbol symbol ~linkage signature ^ ";\n");
      Printf.sprintf "%s(%s)" symbol texts
  | Indirect { value; _ } ->
      let value =
        match operand_c context fc value with
        | Some (text, _) -> text
        | None -> bug "a function value of zero size"
      in
      Printf.sprintf "%s.f_code(%s)" value
        (String.concat ", " ((value ^ ".f_environment") :: List.map fst arguments))
  | Intrinsic intrinsic -> intrinsic_c context intrinsic arguments
  | Table_call { table; slot; signature } ->
      let table =
        match operand_c context fc table with
        | Some (text, _) -> text
        | None -> bug "a table of zero size"
      in
      let result =
        match signature.result with None -> "void" | Some ty -> c_ty context fc.symbol ty
      in
      Printf.sprintf "((%s (*)(%s))((const void *const *)%s)[%d])(%s)" result
        (signature_parameters context fc.symbol signature.parameters None)
        table slot texts
  | Evidence_call { evidence; slot; signature } ->
      let evidence =
        match operand_c context fc evidence with
        | Some (text, _) -> text
        | None -> bug "evidence of zero size"
      in
      let result =
        match signature.result with None -> "void" | Some ty -> c_ty context fc.symbol ty
      in
      Printf.sprintf "((%s (*)(%s))((const struct t_evidence *)%s)->table[%d])(%s)" result
        (signature_parameters context fc.symbol signature.parameters None)
        evidence slot texts

let anchor_c context definition =
  let symbol = anchor_symbol definition in
  if not (List.mem_assoc symbol context.anchors) then
    context.anchors <- (symbol, definition) :: context.anchors;
  "&" ^ symbol

let statement_c context fc buffer (statement : Lir.statement) =
  let line format =
    Printf.ksprintf (fun text -> Buffer.add_string buffer ("  " ^ text ^ "\n")) format
  in
  match statement with
  | Assign (place, rvalue) -> (
      match place_c context fc place with
      | None -> ()
      | Some (target, target_ty) -> (
          match rvalue_c context fc target_ty rvalue with
          | None -> ()
          | Some (Expression text) -> line "%s = %s;" target text
          | Some (Allocating { block; fill; value }) ->
              let name = key_name block in
              line "{";
              line "  %s *block = t_runtime_allocate(sizeof(%s), _Alignof(%s));" name name name;
              line "  *block = %s;" fill;
              line "  %s = %s;" target (value "block");
              line "}"))
  | Call { target; arguments; result } -> (
      let call = call_c context fc target arguments in
      match Option.bind result (place_c context fc) with
      | Some (place, _) -> line "%s = %s;" place call
      | None -> line "%s;" call)
  | Drop place -> (
      match place_c context fc place with
      | None -> ()
      | Some (text, Value ty) ->
          let symbol = Instance.symbol (Drop ty) in
          declare_prototype context symbol
            (prototype context fc.symbol symbol ~linkage:External (Convention.drop_signature ty)
            ^ ";\n");
          line "%s(&%s);" symbol text
      | Some _ -> bug "a drop of a place that is not a value")
  | Echo { text; length; site } ->
      let operand o =
        match operand_c context fc o with
        | Some (text, _) -> text
        | None -> bug "an echo of nothing"
      in
      line "t_runtime_echo(%s, %s, %s, %d, %d);" (operand text) (operand length)
        (anchor_c context site.definition)
        site.line site.column
  | Free_block { place; variant } -> (
      match place_c context fc place with
      | Some (text, Value sum) ->
          line "t_runtime_free(%s);" (block_pointer context text sum variant)
      | _ -> bug "a block of a place that is not a sum type")

let unreachable_c context =
  match context.build with
  | Development -> "t_runtime_compiler_bug();"
  | Release -> "__builtin_unreachable();"

let terminator_c context fc key buffer (terminator : Lir.terminator) =
  let line format =
    Printf.ksprintf (fun text -> Buffer.add_string buffer ("  " ^ text ^ "\n")) format
  in
  let operand o =
    match operand_c context fc o with Some x -> x | None -> bug "an operand of zero size"
  in
  let default = function
    | Some block -> Printf.sprintf "goto b%d;" block
    | None -> unreachable_c context
  in
  match terminator with
  | Goto block -> line "goto b%d;" block
  | Switch { value; cases; default = otherwise } ->
      let text, ty = operand value in
      let c = scalar_c context (scalar_of context ty) in
      line "switch (%s) {" text;
      List.iter
        (fun (value, block) -> line "case (%s)%sULL: goto b%d;" c (Z.to_string value) block)
        cases;
      line "default: %s" (default otherwise);
      line "}"
  | Switch_variant { place; cases; default = otherwise } -> (
      match place_c context fc place with
      | None -> (
          match cases with
          | (_, block) :: _ -> line "goto b%d;" block
          | [] -> line "%s" (default otherwise))
      | Some (text, Value sum) -> (
          let layout = layout context sum in
          match layout.form with
          | Tagged _ | Tag_only _ ->
              line "switch (%s) {" (match layout.form with Tagged _ -> text ^ ".tag" | _ -> text);
              List.iter
                (fun (variant, block) ->
                  match Memory_layout.discriminant layout variant with
                  | Tag_value value -> line "case %sULL: goto b%d;" (Z.to_string value) block
                  | _ -> bug "a tag")
                cases;
              line "default: %s" (default otherwise);
              line "}"
          | _ ->
              List.iter
                (fun (variant, block) ->
                  line "if (%s) goto b%d;" (is_variant_c context text sum variant) block)
                cases;
              line "%s" (default otherwise))
      | Some _ -> bug "a variant switch on a place that is not a value")
  | Return None -> line "return;"
  | Return (Some value) -> (
      match (fc.f.result, operand_c context fc value) with
      | None, _ | _, None -> line "return;"
      | Some _, Some (text, _) -> line "return %s;" text)
  | Unreachable -> line "%s" (unreachable_c context)
  | Fail { failure; message; length; site } ->
      line "%s(%s, %s, %s, %d, %d);"
        (match failure with
        | Panic -> "t_runtime_panic"
        | Assertion -> "t_runtime_assertion_failed"
        | Todo -> "t_runtime_todo")
        (fst (operand message))
        (fst (operand length))
        (anchor_c context site.definition)
        site.line site.column
  | Yield _ -> bug "a yield that yield lowering left in place"

let function_c context key symbol ~linkage (f : Lir.function_) =
  let fc = { symbol = Instance.symbol key; f } in
  let buffer = Buffer.create 1024 in
  let names = List.map (local_name f) f.parameters in
  let header = prototype context fc.symbol symbol ~names ~linkage (Lir.signature f) in
  let targets = Hashtbl.create 16 in
  Array.iter
    (fun (block : Lir.basic_block) ->
      List.iter (fun b -> Hashtbl.replace targets b ()) (Lir.successors block.terminator))
    f.blocks;
  Buffer.add_string buffer (header ^ " {\n");
  Array.iteri
    (fun local (info : Lir.local_info) ->
      if (not (List.mem local f.parameters)) && not (erased context info.ty) then
        let zero =
          match info.ty with
          | Value ty when is_struct context ty -> "{0}"
          | Environment _ -> "{0}"
          | _ -> "0"
        in
        Buffer.add_string buffer
          (Printf.sprintf "  %s %s = %s;\n" (c_ty context fc.symbol info.ty) (local_name f local)
             zero))
    f.locals;
  Array.iteri
    (fun index (block : Lir.basic_block) ->
      if Hashtbl.mem targets index then Buffer.add_string buffer (Printf.sprintf "b%d:;\n" index);
      List.iter (statement_c context fc buffer) block.statements;
      terminator_c context fc key buffer block.terminator)
    f.blocks;
  Buffer.add_string buffer "}\n";
  Buffer.contents buffer

(* Static data *)

let static_name context =
  let name = Printf.sprintf "t_static_%d" (List.length context.statics) in
  name

(* A static value as a C initializer, or [None] for a value of zero size.
   Storage elements and the blocks of [indirect] variants become static
   objects of their own, defined before the data that points at them. *)
let rec initializer_c context ty (value : Lir.static_value) : string option =
  let layout = layout context ty in
  let fields_c (fields : Memory_layout.field list) (values : (string * Lir.static_value) list)
      prefix =
    String.concat ", "
      (List.filter_map
         (fun (field : Memory_layout.field) ->
           match (List.assoc_opt field.name values, field.member) with
           | Some value, Typed field_ty ->
               Option.map
                 (Printf.sprintf "%s.f_%s = %s" prefix field.name)
                 (initializer_c context field_ty value)
           | _ -> None)
         fields)
  in
  let block_c variant fields =
    let key = Block (ty, variant) in
    register context key;
    let name = static_name context in
    let block_fields =
      match (Memory_layout.block context.env ty variant).form with Struct f -> f | _ -> []
    in
    context.statics <-
      Printf.sprintf "static const %s %s = { %s };\n" (key_name key) name
        (fields_c block_fields fields "")
      :: context.statics;
    Printf.sprintf "((%s *)&%s)" (key_name key) name
  in
  match (layout.form, value) with
  | Zero_size, _ -> None
  | _, Static_storage { element; elements; owned } ->
      let element_c = value_c context element in
      let count = List.length elements in
      let buffer =
        if count = 0 || (Memory_layout.of_type context.env element).size = 0 then
          "((void *)" ^ bytes_name context "" ^ ")"
        else begin
          let name = static_name context in
          let values = List.filter_map (initializer_c context element) elements in
          context.statics <-
            Printf.sprintf "static const %s %s[%d] = { %s };\n" element_c name count
              (String.concat ", " values)
            :: context.statics;
          Printf.sprintf "((%s *)%s)" element_c name
        end
      in
      Some
        (Printf.sprintf "{ .f_buffer = %s, .f_length = %d, .f_capacity = %d }" buffer count
           (if owned then count else 0))
  | Scalar _, Static_scalar constant -> Some (fst (constant_c context constant))
  | Struct fields, Static_record values -> Some ("{ " ^ fields_c fields values "" ^ " }")
  | Array { element; _ }, Static_array values ->
      Some
        ("{ .items = { "
        ^ String.concat ", " (List.filter_map (initializer_c context element) values)
        ^ " } }")
  | Tag_only { variants; _ }, Static_variant (name, _) -> (
      match List.find_index (String.equal name) variants with
      | Some index -> Some (string_of_int index)
      | None -> bug "no variant %s" name)
  | Tagged { variants; _ }, Static_variant (name, values) -> (
      match List.find_opt (fun (v : Memory_layout.variant) -> v.name = name) variants with
      | None -> bug "no variant %s" name
      | Some v -> (
          match v.payload.form with
          | Zero_size -> Some (Printf.sprintf "{ .tag = %d }" v.index)
          | Struct fields ->
              Some
                (Printf.sprintf "{ .tag = %d, %s }" v.index
                   (fields_c fields values (".payload.v_" ^ name)))
          | Scalar (Pointer (Block _)) ->
              Some
                (Printf.sprintf "{ .tag = %d, .payload.v_%s = %s }" v.index name
                   (block_c name values))
          | _ -> bug "a payload"))
  | Niche_encoded { dataful; others; encoding }, Static_variant (name, values) ->
      if dataful.name = name then
        match dataful.payload.form with
        | Struct fields -> Some ("{ " ^ fields_c fields values "" ^ " }")
        | Scalar (Pointer (Block _)) -> Some (block_c name values)
        | _ -> bug "a payload"
      else
        begin match (List.assoc_opt name others, encoding) with
        | Some stored, Some niche -> (
            let stored = niche_value context niche stored in
            match niche.path with
            | [] -> Some stored
            | path ->
                Some
                  (Printf.sprintf "{ %s = %s }"
                     (String.concat ""
                        (List.map
                           (function Memory_layout.Field name -> ".f_" ^ name | Tag -> ".tag")
                           path))
                     stored))
        | _ -> bug "no variant %s" name
        end
  | _ -> bug "static data that does not fit %s" (Ground.to_string ty)

let table_c context (table : Lir.table) =
  let entries =
    List.map
      (fun (key, signature) ->
        let symbol = Instance.symbol key in
        declare_prototype context symbol
          (prototype context "" symbol ~linkage:External signature ^ ";\n");
        Printf.sprintf "(const void *)&%s" symbol)
      table.entries
  in
  Printf.sprintf "const void *const %s[%d] = { %s };\n" (Instance.symbol table.table_key)
    (max 1 (List.length entries))
    (if entries = [] then "0" else String.concat ", " entries)

let evidence_c context (evidence : Lir.evidence) =
  let declare key kind =
    let symbol = Instance.symbol key in
    declare_prototype context symbol
      (Printf.sprintf "extern const %s %s%s;\n" kind symbol
         (if kind = "void *const" then "[]" else ""));
    symbol
  in
  let table = declare evidence.table "void *const" in
  let table = "(const void *const *)" ^ table in
  let outer =
    match evidence.outer with
    | [] -> "0"
    | keys ->
        let name = static_name context in
        let symbols = List.map (fun key -> "&" ^ declare key "struct t_evidence") keys in
        context.statics <-
          Printf.sprintf "static const struct t_evidence *const %s[%d] = { %s };\n" name
            (List.length keys) (String.concat ", " symbols)
          :: context.statics;
        name
  in
  (* A real implementation has zero size, so the evidence points at nothing
     that is ever read. *)
  Printf.sprintf "const struct t_evidence %s = { (void *)%s, %s, %s };\n"
    (Instance.symbol evidence.evidence_key)
    (bytes_name context "") table outer

let data_c context (data : Lir.data) =
  let symbol = Instance.symbol data.data_key in
  match initializer_c context data.ty data.value with
  | None -> ""
  | Some value -> Printf.sprintf "const %s %s = %s;\n" (value_c context data.ty) symbol value

let file env build ?(data = []) ?(tables = []) ?(evidence = []) (instances : (Lir.t * linkage) list)
    =
  let context =
    {
      env;
      build;
      order = [];
      registered = Keys.empty;
      environments = Keys.empty;
      bytes = [];
      prototypes = [];
      anchors = [];
      references = None;
      helpers_used = [];
      statics = [];
    }
  in
  List.iter
    (fun ((instance : Lir.t), _) ->
      let symbol = Instance.symbol instance.key in
      Array.iteri
        (fun n (f : Lir.function_) ->
          context.environments <-
            Keys.add (Environment (symbol, n)) f.environment context.environments)
        instance.nested)
    instances;
  let bodies =
    List.concat_map
      (fun ((instance : Lir.t), linkage) ->
        let symbol = Instance.symbol instance.key in
        let nested =
          List.mapi
            (fun n f ->
              let name = Printf.sprintf "%s_Nested_%d" symbol n in
              declare_prototype context name
                (prototype context symbol name ~linkage:Internal (Lir.signature f) ^ ";\n");
              function_c context instance.key name ~linkage:Internal f)
            (Array.to_list instance.nested)
        in
        declare_prototype context symbol
          (prototype context symbol symbol ~linkage (Lir.signature instance.main) ^ ";\n");
        nested @ [ function_c context instance.key symbol ~linkage instance.main ])
      instances
  in
  let data_definitions =
    List.map (data_c context) data
    @ List.map (table_c context) tables
    @ List.map (evidence_c context) evidence
  in
  (* Define every type the code names, and every type those definitions
     name, until nothing new is named. *)
  let definitions = ref Keys.empty in
  let rec close () =
    let pending =
      List.filter (fun key -> not (Keys.mem key !definitions)) (List.rev context.order)
    in
    if pending <> [] then begin
      List.iter (fun key -> definitions := Keys.add key (define context key) !definitions) pending;
      close ()
    end
  in
  close ();
  let keys = List.rev context.order in
  let defined key = Keys.find key !definitions in
  let buffer = Buffer.create 4096 in
  Buffer.add_string buffer (runtime_declarations (Memory_layout.target env));
  List.iter
    (fun (name, text) -> if List.mem name context.helpers_used then Buffer.add_string buffer text)
    helpers;
  List.iter
    (fun key ->
      match (defined key).definition with
      | Struct _ ->
          Buffer.add_string buffer
            (Printf.sprintf "typedef struct %s %s;\n" (key_name key) (key_name key))
      | Typedef _ | Code_typedef _ -> ())
    keys;
  (* Typedefs, each after the typedefs it names; then structs, each after
     the structs it holds by value. Every struct is declared above, so
     naming one needs nothing more. *)
  let emitted = ref Keys.empty in
  let rec emit_typedef key =
    if not (Keys.mem key !emitted) then
      match (defined key).definition with
      | Struct _ -> ()
      | (Typedef _ | Code_typedef _) as definition ->
          emitted := Keys.add key () !emitted;
          List.iter emit_typedef (defined key).references;
          Buffer.add_string buffer
            (match definition with
            | Typedef c -> Printf.sprintf "typedef %s %s;\n" c (key_name key)
            | Code_typedef text -> text
            | Struct _ -> "")
  in
  List.iter emit_typedef keys;
  let rec emit key =
    if not (Keys.mem key !emitted) then begin
      emitted := Keys.add key () !emitted;
      match (defined key).definition with
      | Struct { body; holds } ->
          List.iter emit holds;
          Buffer.add_string buffer (Printf.sprintf "struct %s {\n%s};\n" (key_name key) body)
      | Typedef _ | Code_typedef _ -> ()
    end
  in
  List.iter emit keys;
  List.iter
    (fun (text, name) ->
      let bytes = List.init (String.length text) (fun i -> string_of_int (Char.code text.[i])) in
      Buffer.add_string buffer
        (Printf.sprintf "static const uint8_t %s[%d] = { %s };\n" name
           (max 1 (String.length text))
           (if bytes = [] then "0" else String.concat ", " bytes)))
    (List.rev context.bytes);
  List.iter
    (fun (symbol, _) ->
      Buffer.add_string buffer (Printf.sprintf "extern const struct t_anchor %s;\n" symbol))
    (List.rev context.anchors);
  List.iter
    (fun (_, declaration) -> Buffer.add_string buffer declaration)
    (List.rev context.prototypes);
  List.iter (Buffer.add_string buffer) (List.rev context.statics);
  List.iter (Buffer.add_string buffer) data_definitions;
  List.iter (Buffer.add_string buffer) bodies;
  Buffer.contents buffer
