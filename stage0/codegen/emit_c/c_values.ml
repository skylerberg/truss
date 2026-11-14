(* Places, operands, constants, operators, and the values a statement
   builds, as C expressions. *)

open C_runtime
open C_types

(* The function being printed: the symbol of its instance, and the C text
   and type of each local its code names. *)
type function_context = { symbol : string; local : Lir.local -> string * Lir.ty }

let local_name local = function
  | Some name -> Printf.sprintf "l%d_%s" local name
  | None -> Printf.sprintf "l%d" local

let erased context : Lir.ty -> bool = function
  | Value (Cursor _) -> false
  | Value ty -> (layout context ty).size = 0
  | Pointer _ | Raw _ | Environment _ | Evidence _ -> false

let find_field (fields : Memory_layout.field list) name =
  List.find_opt (fun (field : Memory_layout.field) -> field.name = name) fields

let declare_prototype context symbol declaration =
  if not (List.mem_assoc symbol context.prototypes) then
    context.prototypes <- (symbol, declaration) :: context.prototypes

let integer_literal integer value =
  let c_type = integer_c integer in
  if Z.sign value >= 0 then Printf.sprintf "((%s)%sULL)" c_type (Z.to_string value)
  else if signed integer && Z.equal value (Z.neg (Z.shift_left Z.one 63)) then
    Printf.sprintf "((%s)(-9223372036854775807LL - 1))" c_type
  else Printf.sprintf "((%s)%sLL)" c_type (Z.to_string value)

(* A float as an expression that C takes for a constant, since a static
   value is initialized with one. A float that is not finite has no literal;
   the C compiler's own names for an infinity and for a float that is not a
   number are constants. Every float that is not a number is the same one in
   Truss, so which one this is does not show. *)
let float_literal ~suffix value =
  if Float.is_finite value then Printf.sprintf "%h%s" value suffix
  else if Float.is_nan value then Printf.sprintf "__builtin_nan%s(\"\")" suffix
  else if value > 0. then Printf.sprintf "__builtin_inf%s()" suffix
  else Printf.sprintf "(-__builtin_inf%s())" suffix

let float64_literal bits = float_literal ~suffix:"" (Int64.float_of_bits bits)
let float32_literal bits = float_literal ~suffix:"f" (Int32.float_of_bits bits)

let bytes_name context text =
  match List.assoc_opt text context.bytes with
  | Some name -> name
  | None ->
      let name = Printf.sprintf "%s_bytes_%d" context.prefix (List.length context.bytes) in
      context.bytes <- (text, name) :: context.bytes;
      name

let function_ref_symbol fc : Lir.function_ref -> string = function
  | Instance key -> Instance.symbol key
  | Nested nested_index -> Printf.sprintf "%s_Nested_%d" fc.symbol nested_index

let environment_of context fc nested_index =
  match Keys.find_opt (Environment (fc.symbol, nested_index)) context.environments with
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
        (fun (candidate : Memory_layout.variant) ->
          candidate.name = variant && is_block candidate.payload)
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
    | Local local -> fc.local local
    | Static { key; ty } ->
        refer context key;
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
  let projected (ty : Lir.ty) (projection : Lir.projection) =
    match (ty, projection) with
    | Value (Cursor yielding), Field field -> (
        match List.assoc_opt yielding context.cursors with
        | Some fields -> (
            match List.assoc_opt field !fields with
            | Some ty -> Some ty
            | None when field = Convention.cursor_state -> Some (Raw (Integer UInt32))
            | None -> bug "the cursor has no field %s" field)
        | None ->
            Lir.projection_type context.env ~environment:(environment_of context fc) ty projection)
    | _ -> Lir.projection_type context.env ~environment:(environment_of context fc) ty projection
  in
  let rec walk ((_, ty) as current) = function
    | [] -> Some current
    | projection :: rest -> (
        match projected ty projection with
        | None -> None
        | Some next -> walk (text current projection, next) rest)
  in
  if erased context (snd root) then None else walk root place.projections

and address_c context fc (place : Lir.place) ~writable =
  match place_c context fc place with
  | Some (text, ty) ->
      let pointer = Lir.Pointer { target = ty; writable } in
      (* A pointer parameter is declared [restrict]. The cast removes the
         qualifier from the type of the parameter's address, which C does
         not convert implicitly. *)
      let text =
        match (place, ty) with
        | { root = Local _; projections = [] }, Pointer _ ->
            Printf.sprintf "((%s)&%s)" (c_ty context fc.symbol pointer) text
        | _ -> "(&" ^ text ^ ")"
      in
      Some (text, pointer)
  | None -> bug "the address of a place of zero size"

and operand_c context fc : Lir.operand -> (string * Lir.ty) option = function
  | Move { root = Static { key; _ }; _ } | Moved_address { root = Static { key; _ }; _ } ->
      bug "a move out of %s, which is static data" (Instance.to_string key)
  | Copy place | Move place -> place_c context fc place
  | Address { place; writable } -> address_c context fc place ~writable
  | Moved_address place -> address_c context fc place ~writable:true
  | Constant constant -> Some (constant_c context constant)

and operand_c_exn context fc operand =
  match operand_c context fc operand with
  | Some (text, _) -> text
  | None -> bug "an operand of zero size"

and constant_c context : Lir.constant -> string * Lir.ty = function
  | Integer (integer, value) -> (integer_literal integer value, Raw (Integer integer))
  | Float32 bits -> (float32_literal bits, Raw Float32)
  | Float64 bits -> (float64_literal bits, Raw Float64)
  | Bool value -> ((if value then "((uint8_t)1)" else "((uint8_t)0)"), Raw Bool)
  | Character code -> (Printf.sprintf "((uint32_t)0x%xU)" code, Raw Character)
  | Bytes text -> ("((void *)" ^ bytes_name context text ^ ")", Raw (Pointer Opaque))
  | Null -> ("((void *)0)", Raw (Nullable_pointer Opaque))
  | Size_of ty -> (Printf.sprintf "((t_usize)sizeof(%s))" (value_c context ty), Raw (Integer USize))
  | Alignment_of ty ->
      (Printf.sprintf "((t_usize)_Alignof(%s))" (value_c context ty), Raw (Integer USize))
  | Symbol_address key ->
      refer context key;
      let symbol = Instance.symbol key in
      declare_prototype context symbol
        (match key with
        | Table _ | Any_table _ | Locked_table _ ->
            Printf.sprintf "extern const void *const %s[];\n" symbol
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
  | Pointer _ | Environment _ | Evidence _ -> Pointer Opaque

let is_float : Memory_layout.scalar -> bool = function Float32 | Float64 -> true | _ -> false

let bit_width context (scalar : Memory_layout.scalar) =
  8 * Memory_layout.scalar_size (Memory_layout.target context.env) scalar

let unsigned_of context (scalar : Memory_layout.scalar) =
  match scalar with Integer integer -> unsigned_c integer | _ -> scalar_c context scalar

(* Float comparisons are lawful: every NaN equals every NaN, and NaN comes
   after every number. *)
let lawful_equal left right =
  Printf.sprintf "(%s == %s || (%s != %s && %s != %s))" left right left left right right

let lawful_less left right =
  Printf.sprintf "(%s < %s || (%s == %s && %s != %s))" left right left left right right

let binary_c context (op : Lir.binary) (left, a_ty) (right, _) =
  let scalar = scalar_of context a_ty in
  let c_type = scalar_c context scalar in
  let boolean text = Printf.sprintf "((uint8_t)%s)" text in
  let arithmetic symbol =
    if is_float scalar then Printf.sprintf "(%s %s %s)" left symbol right
    else Printf.sprintf "((%s)(%s %s %s))" c_type left symbol right
  in
  let compare symbol = boolean (Printf.sprintf "(%s %s %s)" left symbol right) in
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
          left right
      else arithmetic "%"
  | Bit_and -> arithmetic "&"
  | Bit_or -> arithmetic "|"
  | Bit_xor -> arithmetic "^"
  | Shift_left ->
      Printf.sprintf "((%s)((%s)%s << (%s & %d)))" c_type (unsigned_of context scalar) left right
        mask
  | Shift_right -> Printf.sprintf "((%s)(%s >> (%s & %d)))" c_type left right mask
  | Equal -> if is_float scalar then boolean (lawful_equal left right) else compare "=="
  | Not_equal -> if is_float scalar then boolean ("!" ^ lawful_equal left right) else compare "!="
  | Less -> if is_float scalar then boolean (lawful_less left right) else compare "<"
  | Less_equal -> if is_float scalar then boolean ("!" ^ lawful_less right left) else compare "<="
  | Greater -> if is_float scalar then boolean (lawful_less right left) else compare ">"
  | Greater_equal ->
      if is_float scalar then boolean ("!" ^ lawful_less left right) else compare ">="
  | Ieee_equal -> compare "=="
  | Ieee_less -> compare "<"
  | Ieee_less_equal -> compare "<="

let unary_c context (op : Lir.unary) (operand_text, a_ty) =
  let scalar = scalar_of context a_ty in
  let c_type = scalar_c context scalar in
  match op with
  | Negate ->
      if is_float scalar then "(-" ^ operand_text ^ ")"
      else Printf.sprintf "((%s)-%s)" c_type operand_text
  | Not -> "((uint8_t)!" ^ operand_text ^ ")"
  | Complement -> Printf.sprintf "((%s)~%s)" c_type operand_text

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
              let c_type = scalar_c context scalar in
              let stop = Z.add niche.start (Z.of_int (List.length others)) in
              Printf.sprintf "((uint8_t)!(%s >= (%s)%sULL && %s < (%s)%sULL))" at c_type
                (Z.to_string niche.start) at c_type (Z.to_string stop))
      | _ -> bug "a niche in a type without one")

(* A record's or a variant's fields as C designated initializers, leaving out
   the fields of zero size. A field's pointer type is never [const], so a
   read-only pointer stored in one, as a cursor keeps a read-only argument,
   is cast to the plain pointer type. *)
let initializers context fc prefix (fields : Memory_layout.field list)
    (values : (string * Lir.operand) list) =
  String.concat ", "
    (List.filter_map
       (fun (name, operand) ->
         match find_field fields name with
         | None -> None
         | Some _ -> (
             match operand_c context fc operand with
             | Some (text, Lir.Pointer { target; writable = false }) ->
                 Some
                   (Printf.sprintf "%s.f_%s = ((%s)%s)" prefix name
                      (c_ty context fc.symbol (Pointer { target; writable = true }))
                      text)
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

let build_laid_out_c context fc ty variant (values : (string * Lir.operand) list) =
  let c_type = value_c context ty in
  let layout = layout context ty in
  (* A field that has no size is left out, as one the layout does not have,
     so a field the type does not have would be left out too. *)
  (if layout.size > 0 then
     let names =
       match (Memory_layout.shape context.env ty, variant) with
       | Record members, None -> Some (List.map fst members)
       | Sum variants, Some name ->
           Option.map
             (fun (variant : Memory_layout.variant_shape) -> List.map fst variant.fields)
             (List.find_opt
                (fun (variant : Memory_layout.variant_shape) -> variant.name = name)
                variants)
       | _ -> None
     in
     match names with
     | None -> bug "a value of %s built as another type" (Ground.to_string ty)
     | Some names ->
         List.iter
           (fun (name, _) ->
             if not (List.mem name names) then
               bug "a value of %s built with a field %s, which it does not have"
                 (Ground.to_string ty) name)
           values);
  let block_of variant =
    let key = Block (ty, variant) in
    register context key;
    let fields = payload_fields (Memory_layout.block context.env ty variant) in
    (key, Printf.sprintf "(%s){ %s }" (key_name key) (initializers context fc "" fields values))
  in
  match (variant, layout.form) with
  | _, Zero_size -> None
  | None, Struct fields ->
      Some
        (Expression
           (Printf.sprintf "((%s){ %s })" c_type (initializers context fc "" fields values)))
  | Some variant, Tag_only { variants; _ } -> (
      match List.find_index (String.equal variant) variants with
      | Some index -> Some (Expression (Printf.sprintf "((%s)%d)" c_type index))
      | None -> bug "no variant %s" variant)
  | Some name, Tagged { variants; _ } -> (
      match
        List.find_opt (fun (candidate : Memory_layout.variant) -> candidate.name = name) variants
      with
      | None -> bug "no variant %s" name
      | Some candidate -> (
          match candidate.payload.form with
          | Zero_size ->
              Some (Expression (Printf.sprintf "((%s){ .tag = %d })" c_type candidate.index))
          | Struct fields ->
              Some
                (Expression
                   (Printf.sprintf "((%s){ .tag = %d, %s })" c_type candidate.index
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
                         Printf.sprintf "((%s){ .tag = %d, .payload.v_%s = %s })" c_type
                           candidate.index name pointer);
                   })
          | _ -> bug "a payload"))
  | Some name, Niche_encoded { dataful; others; encoding } ->
      if dataful.name = name then
        match dataful.payload.form with
        | Struct fields ->
            Some
              (Expression
                 (Printf.sprintf "((%s){ %s })" c_type (initializers context fc "" fields values)))
        | Scalar (Pointer (Block _)) ->
            let block, fill = block_of name in
            Some (Allocating { block; fill; value = (fun pointer -> pointer) })
        | _ -> bug "a payload"
      else
        begin match (List.assoc_opt name others, encoding) with
        | Some value, Some niche -> (
            let stored = niche_value context niche value in
            match niche.path with
            | [] -> Some (Expression (Printf.sprintf "((%s)%s)" c_type stored))
            | path ->
                let designator =
                  String.concat ""
                    (List.map
                       (function Memory_layout.Field name -> ".f_" ^ name | Tag -> ".tag")
                       path)
                in
                Some (Expression (Printf.sprintf "((%s){ %s = %s })" c_type designator stored)))
        | _ -> bug "no variant %s" name
        end
  | _ -> bug "building %s" (Ground.to_string ty)

let prototype context current symbol ?names ~linkage (signature : Lir.signature) =
  let result = match signature.result with None -> "void" | Some ty -> c_ty context current ty in
  Printf.sprintf "%s%s%s %s(%s)"
    (match linkage with Internal -> "static inline " | External -> "")
    (if signature.returns then "" else "_Noreturn ")
    result symbol
    (signature_parameters context current signature.parameters names)

(* A value built of fields. A cursor whose pulled method this code is has no
   layout yet, and names its fields alone. *)
let build_c context fc (ty : Ground.ty) variant (values : (string * Lir.operand) list) =
  match ty with
  | Cursor yielding when List.mem_assoc yielding context.cursors ->
      Some
        (Expression
           (Printf.sprintf "((%s){ %s })" (value_c context ty)
              (String.concat ", "
                 (List.filter_map
                    (fun (name, operand) ->
                      Option.map
                        (fun (text, _) -> Printf.sprintf ".f_%s = %s" name text)
                        (operand_c context fc operand))
                    values))))
  | _ -> build_laid_out_c context fc ty variant values

let rvalue_c context fc (target : Lir.ty) (rvalue : Lir.rvalue) : built option =
  let operand lir_operand =
    match operand_c context fc lir_operand with
    | Some expression -> expression
    | None -> bug "an operand of zero size"
  in
  match rvalue with
  | Use lir_operand ->
      Option.map (fun (text, _) -> Expression text) (operand_c context fc lir_operand)
  | Unary (op, lir_operand) -> Some (Expression (unary_c context op (operand lir_operand)))
  | Binary (op, left, right) ->
      Some (Expression (binary_c context op (operand left) (operand right)))
  | Convert (lir_operand, scalar) ->
      Some
        (Expression
           (Printf.sprintf "((%s)%s)" (scalar_c context scalar) (fst (operand lir_operand))))
  | Build { ty; variant; fields } -> build_c context fc ty variant fields
  | Is_variant (place, variant) -> (
      match place_c context fc place with
      | Some (text, Value sum) -> Some (Expression (is_variant_c context text sum variant))
      | Some _ -> bug "a variant test on a place that is not a value"
      | None -> Some (Expression "((uint8_t)1)"))
  | Function_value { code; environment } ->
      let function_ =
        match target with
        | Value (Function function_) -> function_
        | _ -> bug "a function value stored where no function goes"
      in
      let symbol = function_ref_symbol fc code in
      (match code with
      | Instance key ->
          refer context key;
          declare_prototype context symbol
            (prototype context fc.symbol symbol ~linkage:External
               (Convention.function_value context.env function_)
            ^ ";\n")
      | Nested _ -> ());
      let environment =
        match environment with
        | None -> "((void *)0)"
        | Some environment_operand -> fst (operand environment_operand)
      in
      Some
        (Expression
           (Printf.sprintf "((%s){ .f_code = &%s, .f_environment = %s })"
              (c_ty context fc.symbol target) symbol environment))
