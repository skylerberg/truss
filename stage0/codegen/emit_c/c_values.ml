let ( ++ ) = C_text.( ++ )

type function_context = Lowered.local -> C_text.t * Lowered.ty

let render_cast c_type text = Text "((" ++ c_type ++ Text ")" ++ text ++ Text ")"

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

let render_bytes_initializer text =
  let bytes =
    List.init (String.length text) (fun index -> string_of_int (Char.code text.[index]))
  in
  Printf.sprintf "[%d] = { %s }"
    (max 1 (String.length text))
    (if bytes = [] then "0" else String.concat ", " bytes)

let render_function_ref_symbol emission : Lowered.function_ref -> C_text.t = function
  | Item item -> Emission.render_item emission item
  | Nested nested_index -> Name (Nested_function nested_index)

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
  | Tagged _ -> text ++ Text (".payload.v_" ^ variant)
  | Niche_encoded _ -> text
  | _ -> C_runtime.raise_bug "a block of %s, which is not a sum type" (Ground.to_string sum)

let rec render_place (emission : Emission.t) fc (place : Lowered.place) :
    (C_text.t * Lowered.ty) option =
  let root =
    match place.root with
    | Local local -> fc local
    | Static { item; ty } ->
        let symbol = Emission.render_item emission item in
        Emission.declare_prototype emission symbol
          (Text "extern const "
          ++ C_types.render_value_type emission.types ty
          ++ Text " " ++ symbol ++ Text ";\n");
        (symbol, Lowered.Value ty)
  in
  let render_projection (text, (ty : Lowered.ty)) (projection : Lowered.projection) =
    match (projection, ty) with
    | Deref, _ -> Text "(*" ++ text ++ Text ")"
    | Field name, _ -> text ++ Text (".f_" ^ name)
    | Variant_field { variant; field }, Value sum ->
        if is_indirect emission sum variant then
          render_block_pointer emission text sum variant ++ Text ("->f_" ^ field)
        else
          let payload =
            match (C_types.compute_layout emission.types sum).form with
            | Tagged _ -> ".payload.v_" ^ variant
            | _ -> ""
          in
          text ++ Text (payload ^ ".f_" ^ field)
    | Index index, Value _ ->
        text ++ Text ".items[" ++ render_operand_exn emission fc index ++ Text "]"
    | Index index, _ -> text ++ Text "[" ++ render_operand_exn emission fc index ++ Text "]"
    | Variant_field _, _ -> C_runtime.raise_bug "a variant of a place that is not a value"
  in
  let find_projected_type (ty : Lowered.ty) (projection : Lowered.projection) =
    Lowered.find_projection_type emission.types.env
      ~list_environment:(C_types.read_environment emission.types)
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
      let address = Text "&" ++ text in
      let text =
        match (place, ty) with
        | { root = Local _; projections = [] }, Pointer _ ->
            render_cast (C_types.render_type emission.types pointer) address
        | _ -> Text "(" ++ address ++ Text ")"
      in
      Some (text, pointer)
  | None -> C_runtime.raise_bug "the address of a place of zero size"

and render_operand (emission : Emission.t) fc : Lowered.operand -> (C_text.t * Lowered.ty) option =
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

and render_constant (emission : Emission.t) : Lowered.constant -> C_text.t * Lowered.ty =
  let render_address name = render_cast (Text "void *") name in
  let render_measure measure ty =
    ( Text ("((uint64_t)" ^ measure ^ "(")
      ++ C_types.render_value_type emission.types ty
      ++ Text "))",
      Lowered.Raw (Integer UInt64) )
  in
  function
  | Integer (integer, value) -> (Text (render_integer_literal integer value), Raw (Integer integer))
  | Float32 bits -> (Text (render_float32_literal bits), Raw Float32)
  | Float64 bits -> (Text (render_float64_literal bits), Raw Float64)
  | Bool value -> (Text (if value then "((uint8_t)1)" else "((uint8_t)0)"), Raw Bool)
  | Character code -> (Text (Printf.sprintf "((uint32_t)0x%xU)" code), Raw Character)
  | Bytes text -> (render_address (Emission.render_bytes_name emission text), Raw (Pointer Opaque))
  | Null -> (Text "((void *)0)", Raw (Nullable_pointer Opaque))
  | Size_of ty -> render_measure "sizeof" ty
  | Alignment_of ty -> render_measure "_Alignof" ty
  | Site site -> (render_address (Emission.render_site emission site), Raw (Pointer Opaque))
  | Capability capability ->
      ( render_address (Text "&" ++ Emission.render_capability emission capability),
        Raw (Pointer Opaque) )
  | Symbol_address item ->
      let symbol = Emission.render_item emission item in
      Emission.declare_prototype emission symbol
        (match item with
        | Table _ -> Text "extern const void *const " ++ symbol ++ Text "[];\n"
        | Any_drop _ -> Text "void " ++ symbol ++ Text "(void *);\n"
        | _ -> Text "extern const struct t_evidence " ++ symbol ++ Text ";\n");
      (render_address (Text "&" ++ symbol), Raw (Pointer Opaque))

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

let render_unsigned_type (emission : Emission.t) (scalar : Memory_layout.scalar) : C_text.t =
  match scalar with
  | Integer integer -> Text (C_runtime.render_unsigned_type integer)
  | _ -> C_types.render_scalar_type emission.types scalar

let render_lawful ~symbol ~tie left right =
  Text "(" ++ left ++ Text symbol ++ right ++ Text " || (" ++ left ++ Text tie ++ left
  ++ Text " && " ++ right ++ Text " != " ++ right ++ Text "))"

let render_lawful_equal = render_lawful ~symbol:" == " ~tie:" != "
let render_lawful_less = render_lawful ~symbol:" < " ~tie:" == "

let render_required_operand (emission : Emission.t) fc operand =
  match render_operand emission fc operand with
  | Some rendered -> rendered
  | None -> C_runtime.raise_bug "an operand of zero size"

let is_unsigned : Memory_layout.scalar -> bool = function
  | Integer (UInt8 | UInt16 | UInt32 | UInt64) -> true
  | _ -> false

let is_zero : Lowered.operand -> bool = function
  | Constant (Integer (_, value)) -> Z.sign value = 0
  | _ -> false

let render_comparison (emission : Emission.t) fc ((comparison, left, right) : Lowered.test) =
  let left_text, left_ty = render_required_operand emission fc left in
  let right_text, right_ty = render_required_operand emission fc right in
  let scalar = classify_scalar emission left_ty in
  let is_unsigned_pair = is_unsigned scalar && classify_scalar emission right_ty = scalar in
  let render_boolean text = render_cast (Text "uint8_t") text in
  let negate text = Text "!" ++ text in
  let compare symbol =
    render_boolean (Text "(" ++ left_text ++ Text (" " ^ symbol ^ " ") ++ right_text ++ Text ")")
  in
  match comparison with
  | (Greater_equal | Less) when is_unsigned_pair && is_zero right ->
      render_boolean (Text (if comparison = Greater_equal then "1" else "0"))
  | (Less_equal | Greater) when is_unsigned_pair && is_zero left ->
      render_boolean (Text (if comparison = Less_equal then "1" else "0"))
  | Equal ->
      if is_float scalar then render_boolean (render_lawful_equal left_text right_text)
      else compare "=="
  | Not_equal ->
      if is_float scalar then render_boolean (negate (render_lawful_equal left_text right_text))
      else compare "!="
  | Less ->
      if is_float scalar then render_boolean (render_lawful_less left_text right_text)
      else compare "<"
  | Less_equal ->
      if is_float scalar then render_boolean (negate (render_lawful_less right_text left_text))
      else compare "<="
  | Greater ->
      if is_float scalar then render_boolean (render_lawful_less right_text left_text)
      else compare ">"
  | Greater_equal ->
      if is_float scalar then render_boolean (negate (render_lawful_less left_text right_text))
      else compare ">="
  | Ieee_equal -> compare "=="
  | Ieee_less -> compare "<"
  | Ieee_less_equal -> compare "<="

let render_binary (emission : Emission.t) (op : Lowered.binary) (left, a_ty) (right, _) =
  let scalar = classify_scalar emission a_ty in
  let c_type = C_types.render_scalar_type emission.types scalar in
  let render_arithmetic symbol =
    let operation = Text "(" ++ left ++ Text (" " ^ symbol ^ " ") ++ right ++ Text ")" in
    if is_float scalar then operation else render_cast c_type operation
  in
  let mask = Printf.sprintf " & %d)" (compute_bit_width scalar - 1) in
  match op with
  | Add -> render_arithmetic "+"
  | Subtract -> render_arithmetic "-"
  | Multiply -> render_arithmetic "*"
  | Divide -> render_arithmetic "/"
  | Remainder ->
      if is_float scalar then
        Text (if scalar = Float32 then "__builtin_fmodf(" else "__builtin_fmod(")
        ++ left ++ Text ", " ++ right ++ Text ")"
      else render_arithmetic "%"
  | Bit_and -> render_arithmetic "&"
  | Bit_or -> render_arithmetic "|"
  | Bit_xor -> render_arithmetic "^"
  | Shift_left ->
      render_cast c_type
        (Text "(("
        ++ render_unsigned_type emission scalar
        ++ Text ")" ++ left ++ Text " << (" ++ right ++ Text mask ++ Text ")")
  | Shift_right ->
      render_cast c_type (Text "(" ++ left ++ Text " >> (" ++ right ++ Text mask ++ Text ")")

let render_unary (emission : Emission.t) (op : Lowered.unary) (operand_text, a_ty) =
  let scalar = classify_scalar emission a_ty in
  let c_type = C_types.render_scalar_type emission.types scalar in
  match op with
  | Negate ->
      if is_float scalar then Text "(-" ++ operand_text ++ Text ")"
      else render_cast c_type (Text "-" ++ operand_text)
  | Not -> render_cast (Text "uint8_t") (Text "!" ++ operand_text)
  | Complement -> render_cast c_type (Text "~" ++ operand_text)

let render_path (path : Memory_layout.step list) =
  String.concat ""
    (List.map
       (fun (step : Memory_layout.step) ->
         match step with Field name -> ".f_" ^ name | Tag -> ".tag")
       path)

let render_niche_value (emission : Emission.t) (niche : Memory_layout.niche) value : C_text.t =
  match niche.scalar with
  | Pointer _ -> Text "((void *)0)"
  | scalar ->
      render_cast
        (C_types.render_scalar_type emission.types scalar)
        (Text (Z.to_string value ^ "ULL"))

let render_discriminant_test (emission : Emission.t) text
    (discriminant : Memory_layout.discriminant) : C_text.t =
  let render_boolean test = render_cast (Text "uint8_t") test in
  match discriminant with
  | Only -> Text "((uint8_t)1)"
  | Tag_value { tag; value } ->
      render_boolean
        (Text "(" ++ text
        ++ Text
             (Printf.sprintf "%s == (%s)%sULL)" (render_path tag.at)
                (C_runtime.render_integer_type tag.integer)
                (Z.to_string value)))
  | Niche_value { niche; value } ->
      render_boolean
        (Text "(" ++ text
        ++ Text (render_path niche.path ^ " == ")
        ++ render_niche_value emission niche value
        ++ Text ")")
  | Not_niche { niche; stop } -> (
      let at = text ++ Text (render_path niche.path) in
      match niche.scalar with
      | Pointer _ -> render_boolean (Text "(" ++ at ++ Text " != ((void *)0))")
      | scalar ->
          let render_bound bound =
            Text "("
            ++ C_types.render_scalar_type emission.types scalar
            ++ Text (")" ^ Z.to_string bound ^ "ULL")
          in
          render_boolean
            (Text "!(" ++ at ++ Text " >= " ++ render_bound niche.start ++ Text " && " ++ at
           ++ Text " < " ++ render_bound stop ++ Text ")"))

let render_variant_test (emission : Emission.t) text sum variant =
  render_discriminant_test emission text
    (Memory_layout.compute_discriminant (C_types.compute_layout emission.types sum) variant)

let render_initializers (emission : Emission.t) fc prefix (fields : Memory_layout.field list)
    (values : (string * Lowered.operand) list) =
  C_text.join ", "
    (List.filter_map
       (fun (name, operand) ->
         match find_field fields name with
         | None -> None
         | Some _ -> (
             let designator = Printf.sprintf "%s.f_%s = " prefix name in
             match render_operand emission fc operand with
             | Some (text, Lowered.Pointer { target; writable = false }) ->
                 Some
                   (Text designator
                   ++ render_cast
                        (C_types.render_type emission.types (Pointer { target; writable = true }))
                        text)
             | Some (text, _) -> Some (Text designator ++ text)
             | None -> None))
       values)

let list_payload_fields (payload : Memory_layout.t) =
  match payload.form with Struct fields -> fields | _ -> []

type built =
  | Expression of C_text.t
  | Allocating of { block : C_text.key; fill : C_text.t; value : C_text.t -> C_text.t }

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
  let render_literal initializers = render_cast c_type (Text "{ " ++ initializers ++ Text " }") in
  let read_block variant =
    let key : C_text.key = Block (ty, variant) in
    let fields = list_payload_fields (Memory_layout.lay_out_block emission.types.env ty variant) in
    ( key,
      Text "("
      ++ C_types.render_key emission.types key
      ++ Text "){ "
      ++ render_initializers emission fc "" fields values
      ++ Text " }" )
  in
  match (variant, layout.form) with
  | _, Zero_size -> None
  | None, Struct fields ->
      Some (Expression (render_literal (render_initializers emission fc "" fields values)))
  | Some variant, Tag_only { variants; _ } -> (
      match List.find_index (String.equal variant) variants with
      | Some index -> Some (Expression (render_cast c_type (Text (string_of_int index))))
      | None -> C_runtime.raise_bug "no variant %s" variant)
  | Some name, Tagged { variants; _ } -> (
      match
        List.find_opt (fun (candidate : Memory_layout.variant) -> candidate.name = name) variants
      with
      | None -> C_runtime.raise_bug "no variant %s" name
      | Some candidate -> (
          let tag = Printf.sprintf ".tag = %d" candidate.index in
          match candidate.payload.form with
          | Zero_size -> Some (Expression (render_literal (Text tag)))
          | Struct fields ->
              Some
                (Expression
                   (render_literal
                      (Text (tag ^ ", ")
                      ++ render_initializers emission fc (".payload.v_" ^ name) fields values)))
          | Scalar (Pointer (Block _)) ->
              let block, fill = read_block name in
              Some
                (Allocating
                   {
                     block;
                     fill;
                     value =
                       (fun pointer ->
                         render_literal (Text (tag ^ ", .payload.v_" ^ name ^ " = ") ++ pointer));
                   })
          | _ -> C_runtime.raise_bug "a payload"))
  | Some name, Niche_encoded { dataful; dataless } ->
      if dataful.name = name then
        match dataful.payload.form with
        | Struct fields ->
            Some (Expression (render_literal (render_initializers emission fc "" fields values)))
        | Scalar (Pointer (Block _)) ->
            let block, fill = read_block name in
            Some (Allocating { block; fill; value = Fun.id })
        | _ -> C_runtime.raise_bug "a payload"
      else
        begin match dataless with
        | Some { niche; niche_values } -> (
            match List.assoc_opt name niche_values with
            | None -> C_runtime.raise_bug "no variant %s" name
            | Some value -> (
                let stored = render_niche_value emission niche value in
                match niche.path with
                | [] -> Some (Expression (render_cast c_type stored))
                | path ->
                    Some (Expression (render_literal (Text (render_path path ^ " = ") ++ stored)))))
        | None -> C_runtime.raise_bug "no variant %s" name
        end
  | _ -> C_runtime.raise_bug "building %s" (Ground.to_string ty)

let render_prototype (emission : Emission.t) symbol ?names ~linkage (signature : Lowered.signature)
    =
  Text (match linkage with C_runtime.Internal -> "static inline " | External -> "")
  ++ Text (if signature.returns then "" else "_Noreturn ")
  ++ (match signature.result with
    | None -> Text "void"
    | Some ty -> C_types.render_type emission.types ty)
  ++ Text " " ++ symbol ++ Text "("
  ++ C_types.render_signature_parameters emission.types signature.parameters names
  ++ Text ")"

let render_rvalue (emission : Emission.t) fc (target : Lowered.ty) (rvalue : Lowered.rvalue) :
    built option =
  let render_required_operand = render_required_operand emission fc in
  match rvalue with
  | Use argument ->
      Option.map (fun (text, _) -> Expression text) (render_operand emission fc argument)
  | Unary (op, argument) ->
      Some (Expression (render_unary emission op (render_required_operand argument)))
  | Binary (op, left, right) ->
      Some
        (Expression
           (render_binary emission op (render_required_operand left) (render_required_operand right)))
  | Compare test -> Some (Expression (render_comparison emission fc test))
  | Convert (argument, scalar) ->
      Some
        (Expression
           (render_cast
              (C_types.render_scalar_type emission.types scalar)
              (fst (render_required_operand argument))))
  | Build { ty; variant; fields } -> build_laid_out_c emission fc ty variant fields
  | Is_variant (place, variant) -> (
      match render_place emission fc place with
      | Some (text, Value sum) -> Some (Expression (render_variant_test emission text sum variant))
      | Some _ -> C_runtime.raise_bug "a variant test on a place that is not a value"
      | None -> Some (Expression (Text "((uint8_t)1)")))
  | Function_value { code; environment } ->
      let function_ =
        match target with
        | Value (Function function_) -> function_
        | _ -> C_runtime.raise_bug "a function value stored where no function goes"
      in
      let symbol = render_function_ref_symbol emission code in
      (match code with
      | Item _ ->
          Emission.declare_prototype emission symbol
            (render_prototype emission symbol ~linkage:External
               (Convention.make_function_value_signature emission.types.env function_)
            ++ Text ";\n")
      | Nested _ -> ());
      let environment =
        match environment with
        | None -> C_text.Text "((void *)0)"
        | Some environment_operand -> fst (render_required_operand environment_operand)
      in
      Some
        (Expression
           (render_cast
              (C_types.render_type emission.types target)
              (Text "{ "
              ++ C_text.join ", "
                   (List.map
                      (fun (field, value) -> Text (".f_" ^ field ^ " = ") ++ value)
                      (Builtin_records.Function_value.list_fields ~code:(Text "&" ++ symbol)
                         ~environment))
              ++ Text " }")))
