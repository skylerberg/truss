type function_context = { symbol : string; render_local : Lowered.local -> string * Lowered.ty }

let render_local_name local = function
  | Some name -> Printf.sprintf "l%d_%s" local name
  | None -> Printf.sprintf "l%d" local

let find_field (fields : Memory_layout.field list) name =
  List.find_opt (fun (field : Memory_layout.field) -> field.name = name) fields

let render_integer_literal integer value =
  let c_type = C_runtime.render_integer_type integer in
  if Z.sign value >= 0 then Printf.sprintf "((%s)%sULL)" c_type (Z.to_string value)
  else if C_runtime.is_signed integer && Z.equal value (Z.neg (Z.shift_left Z.one 63)) then
    Printf.sprintf "((%s)(-9223372036854775807LL - 1))" c_type
  else Printf.sprintf "((%s)%sLL)" c_type (Z.to_string value)

let render_float_literal ~suffix value =
  if Float.is_finite value then Printf.sprintf "%h%s" value suffix
  else if Float.is_nan value then Printf.sprintf "__builtin_nan%s(\"\")" suffix
  else if value > 0. then Printf.sprintf "__builtin_inf%s()" suffix
  else Printf.sprintf "(-__builtin_inf%s())" suffix

let render_float64_literal bits = render_float_literal ~suffix:"" (Int64.float_of_bits bits)
let render_float32_literal bits = render_float_literal ~suffix:"f" (Int32.float_of_bits bits)

let render_bytes_definition (text, name) =
  let bytes =
    List.init (String.length text) (fun index -> string_of_int (Char.code text.[index]))
  in
  Printf.sprintf "static const uint8_t %s[%d] = { %s };\n" name
    (max 1 (String.length text))
    (if bytes = [] then "0" else String.concat ", " bytes)

let render_function_ref_symbol fc : Lowered.function_ref -> string = function
  | Item item -> Mangling.make_symbol item
  | Nested nested_index -> Printf.sprintf "%s_Nested_%d" fc.symbol nested_index

let list_environment (emission : Emission.t) fc nested_index =
  match
    C_types.Keys.find_opt (Environment (fc.symbol, nested_index)) emission.types.environments
  with
  | Some fields -> fields
  | None -> []

let is_indirect (emission : Emission.t) sum variant =
  let is_block (payload : Memory_layout.t) =
    match payload.form with Scalar (Pointer (Block _)) -> true | _ -> false
  in
  match (C_types.compute_layout emission.types sum).form with
  | Tagged { variants; _ } ->
      List.exists
        (fun (candidate : Memory_layout.variant) ->
          candidate.name = variant && is_block candidate.payload)
        variants
  | Niche_encoded { dataful; _ } -> dataful.name = variant && is_block dataful.payload
  | _ -> false

let render_block_pointer (emission : Emission.t) text sum variant =
  match (C_types.compute_layout emission.types sum).form with
  | Tagged _ -> text ^ ".payload.v_" ^ variant
  | Niche_encoded _ -> text
  | _ -> C_runtime.raise_bug "a block of %s, which is not a sum type" (Ground.to_string sum)

let rec render_place (emission : Emission.t) fc (place : Lowered.place) :
    (string * Lowered.ty) option =
  let root =
    match place.root with
    | Local local -> fc.render_local local
    | Static { item; ty } ->
        Emission.refer emission item;
        let symbol = Mangling.make_symbol item in
        Emission.declare_prototype emission symbol
          (Printf.sprintf "extern const %s %s;\n"
             (C_types.render_value_type emission.types ty)
             symbol);
        (symbol, Lowered.Value ty)
  in
  let render_projection (text, (ty : Lowered.ty)) (projection : Lowered.projection) =
    match (projection, ty) with
    | Deref, _ -> "(*" ^ text ^ ")"
    | Field name, _ -> text ^ ".f_" ^ name
    | Variant_field { variant; field }, Value sum ->
        if is_indirect emission sum variant then
          render_block_pointer emission text sum variant ^ "->f_" ^ field
        else
          (match (C_types.compute_layout emission.types sum).form with
            | Tagged _ -> text ^ ".payload.v_" ^ variant
            | _ -> text)
          ^ ".f_" ^ field
    | Index index, Value _ -> text ^ ".items[" ^ render_operand_exn emission fc index ^ "]"
    | Index index, _ -> text ^ "[" ^ render_operand_exn emission fc index ^ "]"
    | Variant_field _, _ -> C_runtime.raise_bug "a variant of a place that is not a value"
  in
  let find_projected_type (ty : Lowered.ty) (projection : Lowered.projection) =
    Lowered.find_projection_type emission.types.env ~list_environment:(list_environment emission fc)
      ty projection
  in
  let rec walk ((_, ty) as current) = function
    | [] -> Some current
    | projection :: rest -> (
        match find_projected_type ty projection with
        | None -> None
        | Some next -> walk (render_projection current projection, next) rest)
  in
  if Lowered.is_erased emission.types.env (snd root) then None else walk root place.projections

and render_address (emission : Emission.t) fc (place : Lowered.place) ~writable =
  match render_place emission fc place with
  | Some (text, ty) ->
      let pointer = Lowered.Pointer { target = ty; writable } in
      let text =
        match (place, ty) with
        | { root = Local _; projections = [] }, Pointer _ ->
            Printf.sprintf "((%s)&%s)" (C_types.render_type emission.types fc.symbol pointer) text
        | _ -> "(&" ^ text ^ ")"
      in
      Some (text, pointer)
  | None -> C_runtime.raise_bug "the address of a place of zero size"

and render_operand (emission : Emission.t) fc : Lowered.operand -> (string * Lowered.ty) option =
  function
  | Move { root = Static { item; _ }; _ } | Moved_address { root = Static { item; _ }; _ } ->
      C_runtime.raise_bug "a move out of %s, which is static data" (Lowered.Item.to_string item)
  | Copy place | Move place -> render_place emission fc place
  | Address { place; writable } -> render_address emission fc place ~writable
  | Moved_address place -> render_address emission fc place ~writable:true
  | Constant constant -> Some (render_constant emission constant)

and render_operand_exn (emission : Emission.t) fc operand =
  match render_operand emission fc operand with
  | Some (text, _) -> text
  | None -> C_runtime.raise_bug "an operand of zero size"

and render_constant (emission : Emission.t) : Lowered.constant -> string * Lowered.ty = function
  | Integer (integer, value) -> (render_integer_literal integer value, Raw (Integer integer))
  | Float32 bits -> (render_float32_literal bits, Raw Float32)
  | Float64 bits -> (render_float64_literal bits, Raw Float64)
  | Bool value -> ((if value then "((uint8_t)1)" else "((uint8_t)0)"), Raw Bool)
  | Character code -> (Printf.sprintf "((uint32_t)0x%xU)" code, Raw Character)
  | Bytes text ->
      ("((void *)" ^ Emission.render_bytes_name emission text ^ ")", Raw (Pointer Opaque))
  | Null -> ("((void *)0)", Raw (Nullable_pointer Opaque))
  | Size_of ty ->
      ( Printf.sprintf "((uint64_t)sizeof(%s))" (C_types.render_value_type emission.types ty),
        Raw (Integer UInt64) )
  | Alignment_of ty ->
      ( Printf.sprintf "((uint64_t)_Alignof(%s))" (C_types.render_value_type emission.types ty),
        Raw (Integer UInt64) )
  | Site site -> ("((void *)" ^ Emission.render_site emission site ^ ")", Raw (Pointer Opaque))
  | Symbol_address item ->
      Emission.refer emission item;
      let symbol = Mangling.make_symbol item in
      Emission.declare_prototype emission symbol
        (match item with
        | Table _ -> Printf.sprintf "extern const void *const %s[];\n" symbol
        | Any_drop _ -> Printf.sprintf "void %s(void *);\n" symbol
        | _ -> Printf.sprintf "extern const struct t_evidence %s;\n" symbol);
      ("((void *)&" ^ symbol ^ ")", Raw (Pointer Opaque))

let classify_scalar (emission : Emission.t) : Lowered.ty -> Memory_layout.scalar = function
  | Value ty -> (
      match (C_types.compute_layout emission.types ty).form with
      | Scalar scalar -> scalar
      | Tag_only { tag; _ } -> Integer tag
      | _ -> C_runtime.raise_bug "an operator on %s, which is not a scalar" (Ground.to_string ty))
  | Raw scalar -> scalar
  | Pointer _ | Environment _ | Evidence _ -> Pointer Opaque
  | Lend | Lend_mark -> C_runtime.raise_bug "an operator on a lend's record"
  | Trace -> C_runtime.raise_bug "an operator on a link of the call chain"
  | Capabilities _ -> C_runtime.raise_bug "an operator on a table of capabilities"

let is_float : Memory_layout.scalar -> bool = function Float32 | Float64 -> true | _ -> false
let compute_bit_width (scalar : Memory_layout.scalar) = 8 * Memory_layout.compute_scalar_size scalar

let render_unsigned_type (emission : Emission.t) (scalar : Memory_layout.scalar) =
  match scalar with
  | Integer integer -> C_runtime.render_unsigned_type integer
  | _ -> C_types.render_scalar_type emission.types scalar

let render_lawful_equal left right =
  Printf.sprintf "(%s == %s || (%s != %s && %s != %s))" left right left left right right

let render_lawful_less left right =
  Printf.sprintf "(%s < %s || (%s == %s && %s != %s))" left right left left right right

let render_binary (emission : Emission.t) (op : Lowered.binary) (left, a_ty) (right, _) =
  let scalar = classify_scalar emission a_ty in
  let c_type = C_types.render_scalar_type emission.types scalar in
  let render_boolean text = Printf.sprintf "((uint8_t)%s)" text in
  let render_arithmetic symbol =
    if is_float scalar then Printf.sprintf "(%s %s %s)" left symbol right
    else Printf.sprintf "((%s)(%s %s %s))" c_type left symbol right
  in
  let compare symbol = render_boolean (Printf.sprintf "(%s %s %s)" left symbol right) in
  let mask = compute_bit_width scalar - 1 in
  match op with
  | Add -> render_arithmetic "+"
  | Subtract -> render_arithmetic "-"
  | Multiply -> render_arithmetic "*"
  | Divide -> render_arithmetic "/"
  | Remainder ->
      if is_float scalar then
        Printf.sprintf "%s(%s, %s)"
          (if scalar = Float32 then "__builtin_fmodf" else "__builtin_fmod")
          left right
      else render_arithmetic "%"
  | Bit_and -> render_arithmetic "&"
  | Bit_or -> render_arithmetic "|"
  | Bit_xor -> render_arithmetic "^"
  | Shift_left ->
      Printf.sprintf "((%s)((%s)%s << (%s & %d)))" c_type
        (render_unsigned_type emission scalar)
        left right mask
  | Shift_right -> Printf.sprintf "((%s)(%s >> (%s & %d)))" c_type left right mask
  | Equal ->
      if is_float scalar then render_boolean (render_lawful_equal left right) else compare "=="
  | Not_equal ->
      if is_float scalar then render_boolean ("!" ^ render_lawful_equal left right)
      else compare "!="
  | Less -> if is_float scalar then render_boolean (render_lawful_less left right) else compare "<"
  | Less_equal ->
      if is_float scalar then render_boolean ("!" ^ render_lawful_less right left) else compare "<="
  | Greater ->
      if is_float scalar then render_boolean (render_lawful_less right left) else compare ">"
  | Greater_equal ->
      if is_float scalar then render_boolean ("!" ^ render_lawful_less left right) else compare ">="
  | Ieee_equal -> compare "=="
  | Ieee_less -> compare "<"
  | Ieee_less_equal -> compare "<="

let render_unary (emission : Emission.t) (op : Lowered.unary) (operand_text, a_ty) =
  let scalar = classify_scalar emission a_ty in
  let c_type = C_types.render_scalar_type emission.types scalar in
  match op with
  | Negate ->
      if is_float scalar then "(-" ^ operand_text ^ ")"
      else Printf.sprintf "((%s)-%s)" c_type operand_text
  | Not -> "((uint8_t)!" ^ operand_text ^ ")"
  | Complement -> Printf.sprintf "((%s)~%s)" c_type operand_text

let render_path text (path : Memory_layout.step list) =
  List.fold_left
    (fun text (step : Memory_layout.step) ->
      match step with Field name -> text ^ ".f_" ^ name | Tag -> text ^ ".tag")
    text path

let render_niche_value (emission : Emission.t) (niche : Memory_layout.niche) value =
  match niche.scalar with
  | Pointer _ -> "((void *)0)"
  | scalar ->
      Printf.sprintf "((%s)%sULL)"
        (C_types.render_scalar_type emission.types scalar)
        (Z.to_string value)

let render_discriminant_test (emission : Emission.t) text
    (discriminant : Memory_layout.discriminant) =
  match discriminant with
  | Only -> "((uint8_t)1)"
  | Tag_value { tag; value } ->
      Printf.sprintf "((uint8_t)(%s == (%s)%sULL))" (render_path text tag.at)
        (C_runtime.render_integer_type tag.integer)
        (Z.to_string value)
  | Niche_value { niche; value } ->
      Printf.sprintf "((uint8_t)(%s == %s))" (render_path text niche.path)
        (render_niche_value emission niche value)
  | Not_niche { niche; stop } -> (
      let at = render_path text niche.path in
      match niche.scalar with
      | Pointer _ -> Printf.sprintf "((uint8_t)(%s != ((void *)0)))" at
      | scalar ->
          let c_type = C_types.render_scalar_type emission.types scalar in
          Printf.sprintf "((uint8_t)!(%s >= (%s)%sULL && %s < (%s)%sULL))" at c_type
            (Z.to_string niche.start) at c_type (Z.to_string stop))

let render_variant_test (emission : Emission.t) text sum variant =
  render_discriminant_test emission text
    (Memory_layout.compute_discriminant (C_types.compute_layout emission.types sum) variant)

let render_initializers (emission : Emission.t) fc prefix (fields : Memory_layout.field list)
    (values : (string * Lowered.operand) list) =
  String.concat ", "
    (List.filter_map
       (fun (name, operand) ->
         match find_field fields name with
         | None -> None
         | Some _ -> (
             match render_operand emission fc operand with
             | Some (text, Lowered.Pointer { target; writable = false }) ->
                 Some
                   (Printf.sprintf "%s.f_%s = ((%s)%s)" prefix name
                      (C_types.render_type emission.types fc.symbol
                         (Pointer { target; writable = true }))
                      text)
             | Some (text, _) -> Some (Printf.sprintf "%s.f_%s = %s" prefix name text)
             | None -> None))
       values)

let list_payload_fields (payload : Memory_layout.t) =
  match payload.form with Struct fields -> fields | _ -> []

type built =
  | Expression of string
  | Allocating of { block : C_types.key; fill : string; value : string -> string }

let build_laid_out_c (emission : Emission.t) fc ty variant
    (values : (string * Lowered.operand) list) =
  let c_type = C_types.render_value_type emission.types ty in
  let layout = C_types.compute_layout emission.types ty in
  (if layout.size > 0 then
     let names =
       match (Memory_layout.compute_shape emission.types.env ty, variant) with
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
     | None -> C_runtime.raise_bug "a value of %s built as another type" (Ground.to_string ty)
     | Some names ->
         List.iter
           (fun (name, _) ->
             if not (List.mem name names) then
               C_runtime.raise_bug "a value of %s built with a field %s, which it does not have"
                 (Ground.to_string ty) name)
           values);
  let read_block variant =
    let key = C_types.Block (ty, variant) in
    C_types.register emission.types key;
    let fields = list_payload_fields (Memory_layout.lay_out_block emission.types.env ty variant) in
    ( key,
      Printf.sprintf "(%s){ %s }" (C_types.render_key_name key)
        (render_initializers emission fc "" fields values) )
  in
  match (variant, layout.form) with
  | _, Zero_size -> None
  | None, Struct fields ->
      Some
        (Expression
           (Printf.sprintf "((%s){ %s })" c_type (render_initializers emission fc "" fields values)))
  | Some variant, Tag_only { variants; _ } -> (
      match List.find_index (String.equal variant) variants with
      | Some index -> Some (Expression (Printf.sprintf "((%s)%d)" c_type index))
      | None -> C_runtime.raise_bug "no variant %s" variant)
  | Some name, Tagged { variants; _ } -> (
      match
        List.find_opt (fun (candidate : Memory_layout.variant) -> candidate.name = name) variants
      with
      | None -> C_runtime.raise_bug "no variant %s" name
      | Some candidate -> (
          match candidate.payload.form with
          | Zero_size ->
              Some (Expression (Printf.sprintf "((%s){ .tag = %d })" c_type candidate.index))
          | Struct fields ->
              Some
                (Expression
                   (Printf.sprintf "((%s){ .tag = %d, %s })" c_type candidate.index
                      (render_initializers emission fc (".payload.v_" ^ name) fields values)))
          | Scalar (Pointer (Block _)) ->
              let block, fill = read_block name in
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
          | _ -> C_runtime.raise_bug "a payload"))
  | Some name, Niche_encoded { dataful; dataless } ->
      if dataful.name = name then
        match dataful.payload.form with
        | Struct fields ->
            Some
              (Expression
                 (Printf.sprintf "((%s){ %s })" c_type
                    (render_initializers emission fc "" fields values)))
        | Scalar (Pointer (Block _)) ->
            let block, fill = read_block name in
            Some (Allocating { block; fill; value = (fun pointer -> pointer) })
        | _ -> C_runtime.raise_bug "a payload"
      else
        begin match dataless with
        | Some { niche; niche_values } -> (
            match List.assoc_opt name niche_values with
            | None -> C_runtime.raise_bug "no variant %s" name
            | Some value -> (
                let stored = render_niche_value emission niche value in
                match niche.path with
                | [] -> Some (Expression (Printf.sprintf "((%s)%s)" c_type stored))
                | path ->
                    Some
                      (Expression
                         (Printf.sprintf "((%s){ %s = %s })" c_type (render_path "" path) stored))))
        | None -> C_runtime.raise_bug "no variant %s" name
        end
  | _ -> C_runtime.raise_bug "building %s" (Ground.to_string ty)

let render_prototype (emission : Emission.t) current symbol ?names ~linkage
    (signature : Lowered.signature) =
  let result =
    match signature.result with
    | None -> "void"
    | Some ty -> C_types.render_type emission.types current ty
  in
  Printf.sprintf "%s%s%s %s(%s)"
    (match linkage with C_runtime.Internal -> "static inline " | External -> "")
    (if signature.returns then "" else "_Noreturn ")
    result symbol
    (C_types.render_signature_parameters emission.types current signature.parameters names)

let build_c (emission : Emission.t) fc (ty : Ground.ty) variant
    (values : (string * Lowered.operand) list) =
  build_laid_out_c emission fc ty variant values

let render_rvalue (emission : Emission.t) fc (target : Lowered.ty) (rvalue : Lowered.rvalue) :
    built option =
  let render_required_operand argument =
    match render_operand emission fc argument with
    | Some expression -> expression
    | None -> C_runtime.raise_bug "an operand of zero size"
  in
  match rvalue with
  | Use argument ->
      Option.map (fun (text, _) -> Expression text) (render_operand emission fc argument)
  | Unary (op, argument) ->
      Some (Expression (render_unary emission op (render_required_operand argument)))
  | Binary (op, left, right) ->
      Some
        (Expression
           (render_binary emission op (render_required_operand left) (render_required_operand right)))
  | Convert (argument, scalar) ->
      Some
        (Expression
           (Printf.sprintf "((%s)%s)"
              (C_types.render_scalar_type emission.types scalar)
              (fst (render_required_operand argument))))
  | Build { ty; variant; fields } -> build_c emission fc ty variant fields
  | Is_variant (place, variant) -> (
      match render_place emission fc place with
      | Some (text, Value sum) -> Some (Expression (render_variant_test emission text sum variant))
      | Some _ -> C_runtime.raise_bug "a variant test on a place that is not a value"
      | None -> Some (Expression "((uint8_t)1)"))
  | Function_value { code; environment } ->
      let function_ =
        match target with
        | Value (Function function_) -> function_
        | _ -> C_runtime.raise_bug "a function value stored where no function goes"
      in
      let symbol = render_function_ref_symbol fc code in
      (match code with
      | Item item ->
          Emission.refer emission item;
          Emission.declare_prototype emission symbol
            (render_prototype emission fc.symbol symbol ~linkage:External
               (Convention.make_function_value_signature emission.types.env function_)
            ^ ";\n")
      | Nested _ -> ());
      let environment =
        match environment with
        | None -> "((void *)0)"
        | Some environment_operand -> fst (render_required_operand environment_operand)
      in
      Some
        (Expression
           (Printf.sprintf "((%s){ .f_code = &%s, .f_environment = %s })"
              (C_types.render_type emission.types fc.symbol target)
              symbol environment))
