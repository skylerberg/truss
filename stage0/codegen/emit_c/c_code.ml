(* Code as C: intrinsics, calls, statements, terminators, and functions. *)

open C_runtime
open C_types
open C_values

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
  | System_environment -> "t_runtime_environment(" ^ all ^ ")"
  | System_run -> "t_runtime_run(" ^ all ^ ")"
  | Evidence_fill ->
      let slot = argument 0 in
      let outer =
        List.mapi
          (fun i (text, _) ->
            Printf.sprintf "%s->outer[%d] = (const struct t_evidence *)%s, " slot i text)
          (List.filteri (fun i _ -> i >= 3) arguments)
      in
      Printf.sprintf
        "(%s->evidence.implementation = (void *)%s, %s->evidence.table = (const void *const *)%s, \
         %s%s->evidence.outer = %s->outer)"
        slot (argument 1) slot (argument 2) (String.concat "" outer) slot slot
  | Float_text ->
      (if scalar 0 = Float32 then "t_runtime_float32_text(" else "t_runtime_float64_text(")
      ^ all ^ ")"
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
  | Foreign declaration ->
      declare_prototype context declaration.symbol (Libc.prototype declaration);
      let given =
        try
          List.map2
            (fun c (text, _) -> Printf.sprintf "(%s)(%s)" c text)
            declaration.takes arguments
        with Invalid_argument _ ->
          bug "a call of %s with an argument of zero size" declaration.symbol
      in
      Printf.sprintf "%s(%s)" declaration.symbol (String.concat ", " given)
  | Table_call { table; value; slot; signature } ->
      let table =
        match operand_c context fc table with
        | Some (text, _) -> text
        | None -> bug "a table of zero size"
      in
      let texts =
        match operand_c context fc value with
        | Some (value, _) -> String.concat ", " (value :: List.map fst arguments)
        | None -> bug "an any value of zero size"
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
        evidence slot
        (String.concat ", " (evidence :: List.map fst arguments))

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
  | Call { target; arguments; result = Written place } ->
      line "%s;" (call_c context fc target (Address { place; writable = true } :: arguments))
  | Call { target; arguments; result } -> (
      let call = call_c context fc target arguments in
      match result with
      | Returned place -> (
          match place_c context fc place with
          | Some (place, _) -> line "%s = %s;" place call
          | None -> line "%s;" call)
      | Discarded | Written _ -> line "%s;" call)
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
          | Environment n when environment_of context fc n = [] -> "{}"
          | Environment _ | Evidence _ -> "{0}"
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
