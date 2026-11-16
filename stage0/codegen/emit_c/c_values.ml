type function_context = { symbol : string; local : Lowered.local -> string * Lowered.ty }

let local_name local = function
  | Some name -> Printf.sprintf "l%d_%s" local name
  | None -> Printf.sprintf "l%d" local

let erased context : Lowered.ty -> bool = function
  | Value ty -> (C_types.layout context ty).size = 0
  | Pointer _ | Raw _ | Environment _ | Evidence _ | Lend | Lend_mark -> false

let find_field (fields : Memory_layout.field list) name =
  List.find_opt (fun (field : Memory_layout.field) -> field.name = name) fields

let declare_prototype (context : C_types.context) symbol declaration =
  if not (List.mem_assoc symbol context.prototypes) then
    context.prototypes <- (symbol, declaration) :: context.prototypes

let site_c (context : C_types.context) site =
  context.sites <- site :: context.sites;
  "&" ^ C_runtime.site_symbol site

let integer_literal integer value =
  let c_type = C_runtime.integer_c integer in
  if Z.sign value >= 0 then Printf.sprintf "((%s)%sULL)" c_type (Z.to_string value)
  else if C_runtime.signed integer && Z.equal value (Z.neg (Z.shift_left Z.one 63)) then
    Printf.sprintf "((%s)(-9223372036854775807LL - 1))" c_type
  else Printf.sprintf "((%s)%sLL)" c_type (Z.to_string value)

let float_literal ~suffix value =
  if Float.is_finite value then Printf.sprintf "%h%s" value suffix
  else if Float.is_nan value then Printf.sprintf "__builtin_nan%s(\"\")" suffix
  else if value > 0. then Printf.sprintf "__builtin_inf%s()" suffix
  else Printf.sprintf "(-__builtin_inf%s())" suffix

let float64_literal bits = float_literal ~suffix:"" (Int64.float_of_bits bits)
let float32_literal bits = float_literal ~suffix:"f" (Int32.float_of_bits bits)

let bytes_symbol (context : C_types.context) index =
  Printf.sprintf "%s_bytes_%d" context.prefix index

let bytes_name (context : C_types.context) text =
  match Hashtbl.find_opt context.bytes text with
  | Some index -> bytes_symbol context index
  | None ->
      let index = Hashtbl.length context.bytes in
      Hashtbl.replace context.bytes text index;
      bytes_symbol context index

let function_ref_symbol fc : Lowered.function_ref -> string = function
  | Instance key -> Instance.symbol key
  | Nested nested_index -> Printf.sprintf "%s_Nested_%d" fc.symbol nested_index

let environment_of (context : C_types.context) fc nested_index =
  match C_types.Keys.find_opt (Environment (fc.symbol, nested_index)) context.environments with
  | Some fields -> fields
  | None -> []

let indirect context sum variant =
  let is_block (payload : Memory_layout.t) =
    match payload.form with Scalar (Pointer (Block _)) -> true | _ -> false
  in
  match (C_types.layout context sum).form with
  | Tagged { variants; _ } ->
      List.exists
        (fun (candidate : Memory_layout.variant) ->
          candidate.name = variant && is_block candidate.payload)
        variants
  | Niche_encoded { dataful; _ } -> dataful.name = variant && is_block dataful.payload
  | _ -> false

let block_pointer context text sum variant =
  match (C_types.layout context sum).form with
  | Tagged _ -> text ^ ".payload.v_" ^ variant
  | Niche_encoded _ -> text
  | _ -> C_runtime.bug "a block of %s, which is not a sum type" (Ground.to_string sum)

let rec place_c context fc (place : Lowered.place) : (string * Lowered.ty) option =
  let root =
    match place.root with
    | Local local -> fc.local local
    | Static { key; ty } ->
        C_types.refer context key;
        let symbol = Instance.symbol key in
        declare_prototype context symbol
          (Printf.sprintf "extern const %s %s;\n" (C_types.value_c context ty) symbol);
        (symbol, Lowered.Value ty)
  in
  let text (text, (ty : Lowered.ty)) (projection : Lowered.projection) =
    match (projection, ty) with
    | Deref, _ -> "(*" ^ text ^ ")"
    | Field name, _ -> text ^ ".f_" ^ name
    | Variant_field { variant; field }, Value sum ->
        if indirect context sum variant then block_pointer context text sum variant ^ "->f_" ^ field
        else
          (match (C_types.layout context sum).form with
            | Tagged _ -> text ^ ".payload.v_" ^ variant
            | _ -> text)
          ^ ".f_" ^ field
    | Index index, Value _ -> text ^ ".items[" ^ operand_c_exn context fc index ^ "]"
    | Index index, _ -> text ^ "[" ^ operand_c_exn context fc index ^ "]"
    | Variant_field _, _ -> C_runtime.bug "a variant of a place that is not a value"
  in
  let projected (ty : Lowered.ty) (projection : Lowered.projection) =
    Lowered.find_projection_type context.env ~environment:(environment_of context fc) ty projection
  in
  let rec walk ((_, ty) as current) = function
    | [] -> Some current
    | projection :: rest -> (
        match projected ty projection with
        | None -> None
        | Some next -> walk (text current projection, next) rest)
  in
  if erased context (snd root) then None else walk root place.projections

and address_c context fc (place : Lowered.place) ~writable =
  match place_c context fc place with
  | Some (text, ty) ->
      let pointer = Lowered.Pointer { target = ty; writable } in
      let text =
        match (place, ty) with
        | { root = Local _; projections = [] }, Pointer _ ->
            Printf.sprintf "((%s)&%s)" (C_types.c_ty context fc.symbol pointer) text
        | _ -> "(&" ^ text ^ ")"
      in
      Some (text, pointer)
  | None -> C_runtime.bug "the address of a place of zero size"

and operand_c context fc : Lowered.operand -> (string * Lowered.ty) option = function
  | Move { root = Static { key; _ }; _ } | Moved_address { root = Static { key; _ }; _ } ->
      C_runtime.bug "a move out of %s, which is static data" (Instance.to_string key)
  | Copy place | Move place -> place_c context fc place
  | Address { place; writable } -> address_c context fc place ~writable
  | Moved_address place -> address_c context fc place ~writable:true
  | Constant constant -> Some (constant_c context constant)

and operand_c_exn context fc operand =
  match operand_c context fc operand with
  | Some (text, _) -> text
  | None -> C_runtime.bug "an operand of zero size"

and constant_c context : Lowered.constant -> string * Lowered.ty = function
  | Integer (integer, value) -> (integer_literal integer value, Raw (Integer integer))
  | Float32 bits -> (float32_literal bits, Raw Float32)
  | Float64 bits -> (float64_literal bits, Raw Float64)
  | Bool value -> ((if value then "((uint8_t)1)" else "((uint8_t)0)"), Raw Bool)
  | Character code -> (Printf.sprintf "((uint32_t)0x%xU)" code, Raw Character)
  | Bytes text -> ("((void *)" ^ bytes_name context text ^ ")", Raw (Pointer Opaque))
  | Null -> ("((void *)0)", Raw (Nullable_pointer Opaque))
  | Size_of ty ->
      (Printf.sprintf "((uint64_t)sizeof(%s))" (C_types.value_c context ty), Raw (Integer UInt64))
  | Alignment_of ty ->
      (Printf.sprintf "((uint64_t)_Alignof(%s))" (C_types.value_c context ty), Raw (Integer UInt64))
  | Site site -> ("((void *)" ^ site_c context site ^ ")", Raw (Pointer Opaque))
  | Symbol_address key ->
      C_types.refer context key;
      let symbol = Instance.symbol key in
      declare_prototype context symbol
        (match key with
        | Table _ -> Printf.sprintf "extern const void *const %s[];\n" symbol
        | Any_drop _ -> Printf.sprintf "void %s(void *);\n" symbol
        | _ -> Printf.sprintf "extern const struct t_evidence %s;\n" symbol);
      ("((void *)&" ^ symbol ^ ")", Raw (Pointer Opaque))

let scalar_of context : Lowered.ty -> Memory_layout.scalar = function
  | Value ty -> (
      match (C_types.layout context ty).form with
      | Scalar scalar -> scalar
      | Tag_only { tag; _ } -> Integer tag
      | _ -> C_runtime.bug "an operator on %s, which is not a scalar" (Ground.to_string ty))
  | Raw scalar -> scalar
  | Pointer _ | Environment _ | Evidence _ -> Pointer Opaque
  | Lend | Lend_mark -> C_runtime.bug "an operator on a lend's record"

let is_float : Memory_layout.scalar -> bool = function Float32 | Float64 -> true | _ -> false
let bit_width (scalar : Memory_layout.scalar) = 8 * Memory_layout.scalar_size scalar

let unsigned_of context (scalar : Memory_layout.scalar) =
  match scalar with
  | Integer integer -> C_runtime.unsigned_c integer
  | _ -> C_types.scalar_c context scalar

let lawful_equal left right =
  Printf.sprintf "(%s == %s || (%s != %s && %s != %s))" left right left left right right

let lawful_less left right =
  Printf.sprintf "(%s < %s || (%s == %s && %s != %s))" left right left left right right

let binary_c context (op : Lowered.binary) (left, a_ty) (right, _) =
  let scalar = scalar_of context a_ty in
  let c_type = C_types.scalar_c context scalar in
  let boolean text = Printf.sprintf "((uint8_t)%s)" text in
  let arithmetic symbol =
    if is_float scalar then Printf.sprintf "(%s %s %s)" left symbol right
    else Printf.sprintf "((%s)(%s %s %s))" c_type left symbol right
  in
  let compare symbol = boolean (Printf.sprintf "(%s %s %s)" left symbol right) in
  let mask = bit_width scalar - 1 in
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

let unary_c context (op : Lowered.unary) (operand_text, a_ty) =
  let scalar = scalar_of context a_ty in
  let c_type = C_types.scalar_c context scalar in
  match op with
  | Negate ->
      if is_float scalar then "(-" ^ operand_text ^ ")"
      else Printf.sprintf "((%s)-%s)" c_type operand_text
  | Not -> "((uint8_t)!" ^ operand_text ^ ")"
  | Complement -> Printf.sprintf "((%s)~%s)" c_type operand_text

let path_c text (path : Memory_layout.step list) =
  List.fold_left
    (fun text (step : Memory_layout.step) ->
      match step with Field name -> text ^ ".f_" ^ name | Tag -> text ^ ".tag")
    text path

let niche_value context (niche : Memory_layout.niche) value =
  match niche.scalar with
  | Pointer _ -> "((void *)0)"
  | scalar -> Printf.sprintf "((%s)%sULL)" (C_types.scalar_c context scalar) (Z.to_string value)

let discriminant_test_c context text (discriminant : Memory_layout.discriminant) =
  match discriminant with
  | Only -> "((uint8_t)1)"
  | Tag_value { tag; value } ->
      Printf.sprintf "((uint8_t)(%s == (%s)%sULL))" (path_c text tag.at)
        (C_runtime.integer_c tag.integer) (Z.to_string value)
  | Niche_value { niche; value } ->
      Printf.sprintf "((uint8_t)(%s == %s))" (path_c text niche.path)
        (niche_value context niche value)
  | Not_niche { niche; stop } -> (
      let at = path_c text niche.path in
      match niche.scalar with
      | Pointer _ -> Printf.sprintf "((uint8_t)(%s != ((void *)0)))" at
      | scalar ->
          let c_type = C_types.scalar_c context scalar in
          Printf.sprintf "((uint8_t)!(%s >= (%s)%sULL && %s < (%s)%sULL))" at c_type
            (Z.to_string niche.start) at c_type (Z.to_string stop))

let is_variant_c context text sum variant =
  discriminant_test_c context text (Memory_layout.discriminant (C_types.layout context sum) variant)

let initializers context fc prefix (fields : Memory_layout.field list)
    (values : (string * Lowered.operand) list) =
  String.concat ", "
    (List.filter_map
       (fun (name, operand) ->
         match find_field fields name with
         | None -> None
         | Some _ -> (
             match operand_c context fc operand with
             | Some (text, Lowered.Pointer { target; writable = false }) ->
                 Some
                   (Printf.sprintf "%s.f_%s = ((%s)%s)" prefix name
                      (C_types.c_ty context fc.symbol (Pointer { target; writable = true }))
                      text)
             | Some (text, _) -> Some (Printf.sprintf "%s.f_%s = %s" prefix name text)
             | None -> None))
       values)

let payload_fields (payload : Memory_layout.t) =
  match payload.form with Struct fields -> fields | _ -> []

type built =
  | Expression of string
  | Allocating of { block : C_types.key; fill : string; value : string -> string }

let build_laid_out_c context fc ty variant (values : (string * Lowered.operand) list) =
  let c_type = C_types.value_c context ty in
  let layout = C_types.layout context ty in
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
     | None -> C_runtime.bug "a value of %s built as another type" (Ground.to_string ty)
     | Some names ->
         List.iter
           (fun (name, _) ->
             if not (List.mem name names) then
               C_runtime.bug "a value of %s built with a field %s, which it does not have"
                 (Ground.to_string ty) name)
           values);
  let block_of variant =
    let key = C_types.Block (ty, variant) in
    C_types.register context key;
    let fields = payload_fields (Memory_layout.block context.env ty variant) in
    ( key,
      Printf.sprintf "(%s){ %s }" (C_types.key_name key) (initializers context fc "" fields values)
    )
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
      | None -> C_runtime.bug "no variant %s" variant)
  | Some name, Tagged { variants; _ } -> (
      match
        List.find_opt (fun (candidate : Memory_layout.variant) -> candidate.name = name) variants
      with
      | None -> C_runtime.bug "no variant %s" name
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
          | _ -> C_runtime.bug "a payload"))
  | Some name, Niche_encoded { dataful; dataless } ->
      if dataful.name = name then
        match dataful.payload.form with
        | Struct fields ->
            Some
              (Expression
                 (Printf.sprintf "((%s){ %s })" c_type (initializers context fc "" fields values)))
        | Scalar (Pointer (Block _)) ->
            let block, fill = block_of name in
            Some (Allocating { block; fill; value = (fun pointer -> pointer) })
        | _ -> C_runtime.bug "a payload"
      else
        begin match dataless with
        | Some { niche; niche_values } -> (
            match List.assoc_opt name niche_values with
            | None -> C_runtime.bug "no variant %s" name
            | Some value -> (
                let stored = niche_value context niche value in
                match niche.path with
                | [] -> Some (Expression (Printf.sprintf "((%s)%s)" c_type stored))
                | path ->
                    Some
                      (Expression
                         (Printf.sprintf "((%s){ %s = %s })" c_type (path_c "" path) stored))))
        | None -> C_runtime.bug "no variant %s" name
        end
  | _ -> C_runtime.bug "building %s" (Ground.to_string ty)

let prototype context current symbol ?names ~linkage (signature : Lowered.signature) =
  let result =
    match signature.result with None -> "void" | Some ty -> C_types.c_ty context current ty
  in
  Printf.sprintf "%s%s%s %s(%s)"
    (match linkage with C_runtime.Internal -> "static inline " | External -> "")
    (if signature.returns then "" else "_Noreturn ")
    result symbol
    (C_types.signature_parameters context current signature.parameters names)

let build_c context fc (ty : Ground.ty) variant (values : (string * Lowered.operand) list) =
  build_laid_out_c context fc ty variant values

let rvalue_c context fc (target : Lowered.ty) (rvalue : Lowered.rvalue) : built option =
  let operand argument =
    match operand_c context fc argument with
    | Some expression -> expression
    | None -> C_runtime.bug "an operand of zero size"
  in
  match rvalue with
  | Use argument -> Option.map (fun (text, _) -> Expression text) (operand_c context fc argument)
  | Unary (op, argument) -> Some (Expression (unary_c context op (operand argument)))
  | Binary (op, left, right) ->
      Some (Expression (binary_c context op (operand left) (operand right)))
  | Convert (argument, scalar) ->
      Some
        (Expression
           (Printf.sprintf "((%s)%s)" (C_types.scalar_c context scalar) (fst (operand argument))))
  | Build { ty; variant; fields } -> build_c context fc ty variant fields
  | Is_variant (place, variant) -> (
      match place_c context fc place with
      | Some (text, Value sum) -> Some (Expression (is_variant_c context text sum variant))
      | Some _ -> C_runtime.bug "a variant test on a place that is not a value"
      | None -> Some (Expression "((uint8_t)1)"))
  | Function_value { code; environment } ->
      let function_ =
        match target with
        | Value (Function function_) -> function_
        | _ -> C_runtime.bug "a function value stored where no function goes"
      in
      let symbol = function_ref_symbol fc code in
      (match code with
      | Instance key ->
          C_types.refer context key;
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
              (C_types.c_ty context fc.symbol target)
              symbol environment))
