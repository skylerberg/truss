let render_intrinsic context (intrinsic : Lowered.intrinsic)
    (arguments : (string * Lowered.ty) list) =
  let render_argument position = fst (List.nth arguments position) in
  let classify_scalar position =
    C_values.classify_scalar context (snd (List.nth arguments position))
  in
  let compute_width position = C_values.compute_bit_width (classify_scalar position) in
  let render_unsigned position =
    Printf.sprintf "((%s)%s)"
      (C_values.render_unsigned_type context (classify_scalar position))
      (render_argument position)
  in
  let all = String.concat ", " (List.map fst arguments) in
  let render_float_builtin name = if classify_scalar 0 = Float32 then name ^ "f" else name in
  match intrinsic with
  | Allocate -> "t_runtime_allocate(" ^ all ^ ")"
  | Reallocate -> "t_runtime_reallocate(" ^ all ^ ")"
  | Free -> "t_runtime_free(" ^ all ^ ")"
  | Copy_bytes -> "__builtin_memcpy(" ^ all ^ ")"
  | Move_bytes -> "__builtin_memmove(" ^ all ^ ")"
  | Compare_bytes -> C_types.use_helper context "t_compare_bytes" ^ "(" ^ all ^ ")"
  | Add_overflow -> "((uint8_t)__builtin_add_overflow(" ^ all ^ "))"
  | Subtract_overflow -> "((uint8_t)__builtin_sub_overflow(" ^ all ^ "))"
  | Multiply_overflow -> "((uint8_t)__builtin_mul_overflow(" ^ all ^ "))"
  | Leading_zeros ->
      Printf.sprintf "(%s == 0 ? %d : __builtin_clzll((unsigned long long)%s) - %d)"
        (render_argument 0) (compute_width 0) (render_unsigned 0)
        (64 - compute_width 0)
  | Trailing_zeros ->
      Printf.sprintf "(%s == 0 ? %d : __builtin_ctzll((unsigned long long)%s))" (render_argument 0)
        (compute_width 0) (render_unsigned 0)
  | Count_ones -> Printf.sprintf "__builtin_popcountll((unsigned long long)%s)" (render_unsigned 0)
  | Swap_bytes -> (
      let c_type = C_types.render_scalar_type context (classify_scalar 0) in
      match compute_width 0 with
      | 8 -> render_argument 0
      | width -> Printf.sprintf "((%s)__builtin_bswap%d(%s))" c_type width (render_unsigned 0))
  | Rotate_left | Rotate_right ->
      let c_type = C_types.render_scalar_type context (classify_scalar 0) in
      let mask = compute_width 0 - 1 in
      let first, second = if intrinsic = Rotate_left then ("<<", ">>") else (">>", "<<") in
      Printf.sprintf "((%s)((%s %s (%s & %d)) | (%s %s ((-%s) & %d))))" c_type (render_unsigned 0)
        first (render_argument 1) mask (render_unsigned 0) second (render_argument 1) mask
  | Multiply_high ->
      let c_type = C_types.render_scalar_type context (classify_scalar 0) in
      let width = compute_width 0 in
      let signed =
        match classify_scalar 0 with Integer integer -> C_runtime.is_signed integer | _ -> false
      in
      let wide =
        if width = 64 then if signed then "__int128" else "unsigned __int128"
        else if signed then "int64_t"
        else "uint64_t"
      in
      Printf.sprintf "((%s)(((%s)%s * (%s)%s) >> %d))" c_type wide (render_argument 0) wide
        (render_argument 1) width
  | Square_root -> Printf.sprintf "%s(%s)" (render_float_builtin "__builtin_sqrt") all
  | Fused_multiply_add -> Printf.sprintf "%s(%s)" (render_float_builtin "__builtin_fma") all
  | Floor -> Printf.sprintf "%s(%s)" (render_float_builtin "__builtin_floor") all
  | Ceiling -> Printf.sprintf "%s(%s)" (render_float_builtin "__builtin_ceil") all
  | Truncate -> Printf.sprintf "%s(%s)" (render_float_builtin "__builtin_trunc") all
  | Round_even -> Printf.sprintf "%s(%s)" (render_float_builtin "__builtin_roundeven") all
  | Float_bits ->
      Printf.sprintf "%s(%s)"
        (C_types.use_helper context
           (if classify_scalar 0 = Float32 then "t_float32_bits" else "t_float64_bits"))
        all
  | Float_from_bits ->
      Printf.sprintf "%s(%s)"
        (C_types.use_helper context
           (if compute_width 0 = 32 then "t_float32_from_bits" else "t_float64_from_bits"))
        all
  | Run_test -> "t_runtime_run_test(" ^ all ^ ")"
  | Coroutine_start ->
      Printf.sprintf
        "t_runtime_coroutine_start((void (*)(void *, uint64_t))%s.f_code, (void \
         *)%s.f_environment, %s)"
        (render_argument 0) (render_argument 0) (render_argument 1)
  | Coroutine_resume -> "t_runtime_coroutine_resume(" ^ all ^ ")"
  | Coroutine_suspend -> "t_runtime_coroutine_suspend()"
  | Tasks_spawn ->
      Printf.sprintf
        "t_runtime_tasks_spawn(%s, (void (*)(void *, uint64_t))%s.f_code, (void \
         *)%s.f_environment, %s)"
        (render_argument 0) (render_argument 1) (render_argument 1) (render_argument 2)
  | (Shared_allocate | Shared_retain | Shared_release | Shared_free | Shared_lock | Shared_unlock)
    as shared ->
      let symbol, result, parameters =
        match shared with
        | Shared_allocate ->
            ("t_runtime_shared_allocate", "void *", "uint64_t size, uint64_t alignment")
        | Shared_retain -> ("t_runtime_shared_retain", "void ", "void *value")
        | Shared_release -> ("t_runtime_shared_release", "uint8_t ", "void *value")
        | Shared_free -> ("t_runtime_shared_free", "void ", "void *value")
        | Shared_lock -> ("t_runtime_shared_lock", "void ", "void *value")
        | _ -> ("t_runtime_shared_unlock", "void ", "void *value")
      in
      C_values.declare_prototype context symbol
        (Printf.sprintf "%s%s(%s);\n" result symbol parameters);
      symbol ^ "(" ^ all ^ ")"
  | (Blocking_begin | Blocking_end) as blocking ->
      let symbol =
        if blocking = Blocking_begin then "t_runtime_blocking_begin" else "t_runtime_blocking_end"
      in
      C_values.declare_prototype context symbol (Printf.sprintf "void %s(void);\n" symbol);
      symbol ^ "()"
  | Report_tests_to -> "t_runtime_report_tests_to(" ^ all ^ ")"
  | ( Lend_begin | Lend_called | Lend_release | Lend_transfer | Lend_allocate | Lend_defer_drop
    | Lend_defer_write_back ) as lend ->
      let name =
        match lend with
        | Lend_begin -> "_begin"
        | Lend_called -> "_called"
        | Lend_release -> "_release"
        | Lend_transfer -> "_transfer"
        | Lend_allocate -> "_allocate"
        | Lend_defer_drop -> "_defer_drop"
        | _ -> "_defer_write_back"
      in
      C_types.use_helper context "t_lend" ^ name ^ "(" ^ all ^ ")"
  | Live_blocks -> "t_runtime_live_blocks()"
  | Environment ->
      C_values.declare_prototype context "environ" "extern char **environ;\n";
      "((void *)environ)"
  | Terminated_length ->
      Printf.sprintf "((uint64_t)__builtin_strlen((const char *)%s))" (render_argument 0)
  | Evidence_fill ->
      let slot = render_argument 0 in
      let outer =
        List.mapi
          (fun position (text, _) ->
            Printf.sprintf "%s->outer[%d] = (const struct t_evidence *)%s, " slot position text)
          (List.drop 3 arguments)
      in
      Printf.sprintf
        "(%s->evidence.implementation = (void *)%s, %s->evidence.table = (const void *const *)%s, \
         %s%s->evidence.outer = %s->outer)"
        slot (render_argument 1) slot (render_argument 2) (String.concat "" outer) slot slot
  | Trace_link ->
      Printf.sprintf "(%s->site = %s, %s->caller = (const struct t_trace *)%s)" (render_argument 0)
        (render_argument 1) (render_argument 0) (render_argument 2)
  | Evidence_implementation ->
      Printf.sprintf "((const struct t_evidence *)%s)->implementation" (render_argument 0)
  | Program_argument ->
      Printf.sprintf "((void *)((char **)%s)[%s])" (render_argument 0) (render_argument 1)
  | Evidence_outer ->
      Printf.sprintf "((void *)((const struct t_evidence *)%s)->outer[%s])" (render_argument 0)
        (render_argument 1)

let render_call context fc (target : Lowered.target) arguments =
  let arguments = List.filter_map (C_values.render_operand context fc) arguments in
  let texts = String.concat ", " (List.map fst arguments) in
  (match target with
  | Direct { signature; _ }
  | Indirect { signature; _ }
  | Evidence_call { signature; _ }
  | Table_call { signature; _ } ->
      let leading = match target with Direct _ -> 0 | _ -> 1 in
      let arity = List.length signature.parameters in
      if leading + List.length arguments <> arity then
        C_runtime.raise_bug "a call that passes %d arguments to a target that takes %d"
          (leading + List.length arguments)
          arity
  | Intrinsic _ | Foreign _ -> ());
  match target with
  | Direct { function_; signature } ->
      (match function_ with
      | Item item ->
          C_types.refer context item;
          if not (List.exists (Lowered.Item.equal item) context.called) then
            context.called <- item :: context.called
      | Nested _ -> ());
      let symbol = C_values.render_function_ref_symbol fc function_ in
      let linkage = match function_ with Nested _ -> C_runtime.Internal | Item _ -> External in
      C_values.declare_prototype context symbol
        (C_values.render_prototype context fc.symbol symbol ~linkage signature ^ ";\n");
      Printf.sprintf "%s(%s)" symbol texts
  | Indirect { value; _ } ->
      let value =
        match C_values.render_operand context fc value with
        | Some (text, _) -> text
        | None -> C_runtime.raise_bug "a function value of zero size"
      in
      Printf.sprintf "%s.f_code(%s)" value
        (String.concat ", " ((value ^ ".f_environment") :: List.map fst arguments))
  | Intrinsic intrinsic -> render_intrinsic context intrinsic arguments
  | Foreign declaration -> (
      C_values.declare_prototype context declaration.symbol (Libc.render_prototype declaration);
      let cast_arguments =
        try
          List.map2
            (fun c_type (text, _) -> Printf.sprintf "(%s)(%s)" (Libc.show_c_type c_type) text)
            declaration.takes arguments
        with Invalid_argument _ ->
          C_runtime.raise_bug "a call of %s with an argument of zero size" declaration.symbol
      in
      let called = Printf.sprintf "%s(%s)" declaration.symbol (String.concat ", " cast_arguments) in
      match declaration.returns with Pointer _ -> "((void *)" ^ called ^ ")" | _ -> called)
  | Table_call { table; value; slot; signature } ->
      let table =
        match C_values.render_operand context fc table with
        | Some (text, _) -> text
        | None -> C_runtime.raise_bug "a table of zero size"
      in
      let texts =
        match C_values.render_operand context fc value with
        | Some (value, _) -> String.concat ", " (value :: List.map fst arguments)
        | None -> C_runtime.raise_bug "an any value of zero size"
      in
      let result =
        match signature.result with
        | None -> "void"
        | Some ty -> C_types.render_type context fc.symbol ty
      in
      Printf.sprintf "((%s (*)(%s))((const void *const *)%s)[%d])(%s)" result
        (C_types.render_signature_parameters context fc.symbol signature.parameters None)
        table slot texts
  | Evidence_call { evidence; capability; slot; signature } ->
      context.calls <- (capability, slot) :: context.calls;
      let evidence =
        match C_values.render_operand context fc evidence with
        | Some (text, _) -> text
        | None -> C_runtime.raise_bug "evidence of zero size"
      in
      let result =
        match signature.result with
        | None -> "void"
        | Some ty -> C_types.render_type context fc.symbol ty
      in
      Printf.sprintf "((%s (*)(%s))((const struct t_evidence *)%s)->table[%d])(%s)" result
        (C_types.render_signature_parameters context fc.symbol signature.parameters None)
        evidence slot
        (String.concat ", " (evidence :: List.map fst arguments))

let may_alias (first : Lowered.place) (second : Lowered.place) =
  let rec overlaps (first : Lowered.projection list) (second : Lowered.projection list) =
    match (first, second) with
    | [], rest | rest, [] -> not (List.mem Lowered.Deref rest)
    | Field left :: first, Field right :: second -> left = right && overlaps first second
    | Variant_field left :: first, Variant_field right :: second ->
        left.variant <> right.variant || (left.field = right.field && overlaps first second)
    | Deref :: first, Deref :: second -> overlaps first second
    | Index left :: first, Index right :: second -> left <> right || overlaps first second
    | (Field _ | Variant_field _ | Deref | Index _) :: _, _ -> true
  in
  first.root = second.root && overlaps first.projections second.projections

let write_statement context fc buffer (statement : Lowered.statement) =
  let write_line format =
    Printf.ksprintf (fun text -> Buffer.add_string buffer ("  " ^ text ^ "\n")) format
  in
  match statement with
  | Assign (place, rvalue) -> (
      match C_values.render_place context fc place with
      | None -> ()
      | Some (target, target_ty) -> (
          match C_values.render_rvalue context fc target_ty rvalue with
          | None -> ()
          | Some (Expression text) -> write_line "%s = %s;" target text
          | Some (Allocating { block; fill; value = render_value }) ->
              let name = C_types.render_key_name block in
              write_line "{";
              write_line "  %s *block = t_runtime_allocate(sizeof(%s), _Alignof(%s));" name name
                name;
              write_line "  *block = %s;" fill;
              write_line "  %s = %s;" target (render_value "block");
              write_line "}"))
  | Call { target; arguments; result = Written place } ->
      List.iter
        (fun (argument : Lowered.operand) ->
          match argument with
          | (Address { place = passed; _ } | Moved_address passed) when may_alias place passed ->
              C_runtime.raise_bug "a call that writes its result to a place it is also given"
          | _ -> ())
        arguments;
      write_line "%s;"
        (render_call context fc target (Address { place; writable = true } :: arguments))
  | Call { target; arguments; result } -> (
      let call = render_call context fc target arguments in
      match result with
      | Returned place -> (
          match C_values.render_place context fc place with
          | Some (place, _) -> write_line "%s = %s;" place call
          | None -> write_line "%s;" call)
      | Discarded | Written _ -> write_line "%s;" call)
  | Drop place -> (
      match C_values.render_place context fc place with
      | None -> ()
      | Some (text, Value ty) ->
          C_types.refer context (Drop ty);
          let symbol = Mangling.make_symbol (Drop ty) in
          C_values.declare_prototype context symbol
            (C_values.render_prototype context fc.symbol symbol ~linkage:External
               (Convention.drop_signature ty)
            ^ ";\n");
          write_line "%s(&%s);" symbol text
      | Some _ -> C_runtime.raise_bug "a drop of a place that is not a value")
  | Echo { text; length; site } ->
      context.failures <- (Echo, site) :: context.failures;
      let render_operand argument =
        match C_values.render_operand context fc argument with
        | Some (text, _) -> text
        | None -> C_runtime.raise_bug "an echo of nothing"
      in
      write_line "t_runtime_echo(%s, %s, %s);" (render_operand text) (render_operand length)
        (C_values.render_site context site)
  | Free_block { place; variant } -> (
      match C_values.render_place context fc place with
      | Some (text, Value sum) ->
          write_line "t_runtime_free(%s);" (C_values.render_block_pointer context text sum variant)
      | _ -> C_runtime.raise_bug "a block of a place that is not a sum type")
  | Defer_free_block { lend; place; variant } -> (
      match (C_values.render_operand context fc lend, C_values.render_place context fc place) with
      | Some (lend, _), Some (text, Value sum) ->
          write_line "%s_defer_free(%s, %s);"
            (C_types.use_helper context "t_lend")
            lend
            (C_values.render_block_pointer context text sum variant)
      | _ -> C_runtime.raise_bug "a block of a place that is not a sum type")
  | Fork { branches } ->
      let render_operand argument =
        match C_values.render_operand context fc argument with
        | Some (text, _) -> text
        | None -> C_runtime.raise_bug "an environment of zero size"
      in
      write_line "{";
      write_line "  const struct t_branch branches[%d] = { %s };" (List.length branches)
        (String.concat ", "
           (List.map
              (fun (nested, environment) ->
                Printf.sprintf "{ &%s, (void *)%s }"
                  (C_values.render_function_ref_symbol fc (Nested nested))
                  (render_operand environment))
              branches));
      write_line "  t_runtime_parallel(branches, %d);" (List.length branches);
      write_line "}"
  | Fork_range { body; environment; first; last } ->
      let render_operand argument =
        match C_values.render_operand context fc argument with
        | Some (text, _) -> text
        | None -> C_runtime.raise_bug "an operand of zero size"
      in
      write_line "t_runtime_parallel_range(&%s, (void *)%s, %s, %s);"
        (C_values.render_function_ref_symbol fc (Nested body))
        (render_operand environment) (render_operand first) (render_operand last)

let render_unreachable _ = "T_UNREACHABLE();"

let write_terminator context fc buffer (terminator : Lowered.terminator) =
  let write_line format =
    Printf.ksprintf (fun text -> Buffer.add_string buffer ("  " ^ text ^ "\n")) format
  in
  let render_operand argument =
    match C_values.render_operand context fc argument with
    | Some expression -> expression
    | None -> C_runtime.raise_bug "an operand of zero size"
  in
  let render_default = function
    | Some block -> Printf.sprintf "goto b%d;" block
    | None -> render_unreachable context
  in
  match terminator with
  | Goto block -> write_line "goto b%d;" block
  | Switch { value; cases; default } ->
      let text, ty = render_operand value in
      let c_type = C_types.render_scalar_type context (C_values.classify_scalar context ty) in
      write_line "switch (%s) {" text;
      List.iter
        (fun (value, block) ->
          write_line "case (%s)%sULL: goto b%d;" c_type (Z.to_string value) block)
        cases;
      write_line "default: goto b%d;" default;
      write_line "}"
  | Switch_variant { place; cases; default = otherwise } -> (
      match C_values.render_place context fc place with
      | None -> (
          match cases with
          | (_, block) :: _ -> write_line "goto b%d;" block
          | [] -> write_line "%s" (render_default otherwise))
      | Some (text, Value sum) -> (
          match Memory_layout.dispatch (C_types.compute_layout context sum) cases with
          | Switch { tag; cases } ->
              write_line "switch (%s) {" (C_values.render_path text tag.at);
              List.iter
                (fun (value, block) -> write_line "case %sULL: goto b%d;" (Z.to_string value) block)
                cases;
              write_line "default: %s" (render_default otherwise);
              write_line "}"
          | Tests tests ->
              List.iter
                (fun (discriminant, block) ->
                  write_line "if (%s) goto b%d;"
                    (C_values.render_discriminant_test context text discriminant)
                    block)
                tests;
              write_line "%s" (render_default otherwise))
      | Some _ -> C_runtime.raise_bug "a variant switch on a place that is not a value")
  | Return None -> write_line "return;"
  | Return (Some value) -> (
      match C_values.render_operand context fc value with
      | None -> write_line "return;"
      | Some (text, _) -> write_line "return %s;" text)
  | Unreachable -> write_line "%s" (render_unreachable context)
  | Fail { failure; message; length; site; reported; trace } ->
      if match failure with Lowered.Todo -> true | Panic | Assertion -> false then
        context.failures <- (Todo, site) :: context.failures;
      let runtime =
        match failure with
        | Panic -> "t_runtime_panic"
        | Assertion -> "t_runtime_assertion_failed"
        | Todo -> "t_runtime_todo"
      in
      let site =
        match reported with
        | Some reported -> fst (render_operand reported)
        | None -> C_values.render_site context site
      in
      let chain =
        match (failure, trace) with
        | Panic, Some trace -> [ fst (render_operand trace) ]
        | Panic, None -> [ fst (render_operand (Constant Null)) ]
        | (Assertion | Todo), None -> []
        | (Assertion | Todo), Some _ ->
            C_runtime.raise_bug "a call chain on a failure that is not a panic"
      in
      write_line "%s(%s);" runtime
        (String.concat ", "
           ([ fst (render_operand message); fst (render_operand length); site ] @ chain))
