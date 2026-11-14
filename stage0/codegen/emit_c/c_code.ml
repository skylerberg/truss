(* Code as C: intrinsics, calls, statements, terminators, and functions. *)

open C_runtime
open C_types
open C_values

let intrinsic_c context (intrinsic : Lowered.intrinsic) (arguments : (string * Lowered.ty) list) =
  let argument position = fst (List.nth arguments position) in
  let scalar position = scalar_of context (snd (List.nth arguments position)) in
  let width position = bit_width context (scalar position) in
  let unsigned position =
    Printf.sprintf "((%s)%s)" (unsigned_of context (scalar position)) (argument position)
  in
  let all = String.concat ", " (List.map fst arguments) in
  let float_builtin name = if scalar 0 = Float32 then name ^ "f" else name in
  match intrinsic with
  | Allocate -> "t_runtime_allocate(" ^ all ^ ")"
  | Reallocate -> "t_runtime_reallocate(" ^ all ^ ")"
  | Free -> "t_runtime_free(" ^ all ^ ")"
  | Copy_bytes -> "__builtin_memcpy(" ^ all ^ ")"
  | Move_bytes -> "__builtin_memmove(" ^ all ^ ")"
  | Compare_bytes -> use_helper context "t_compare_bytes" ^ "(" ^ all ^ ")"
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
      let c_type = scalar_c context (scalar 0) in
      match width 0 with
      | 8 -> argument 0
      | width -> Printf.sprintf "((%s)__builtin_bswap%d(%s))" c_type width (unsigned 0))
  | Rotate_left | Rotate_right ->
      let c_type = scalar_c context (scalar 0) in
      let mask = width 0 - 1 in
      let first, second = if intrinsic = Rotate_left then ("<<", ">>") else (">>", "<<") in
      Printf.sprintf "((%s)((%s %s (%s & %d)) | (%s %s ((-%s) & %d))))" c_type (unsigned 0) first
        (argument 1) mask (unsigned 0) second (argument 1) mask
  | Multiply_high ->
      let c_type = scalar_c context (scalar 0) in
      let width = width 0 in
      let signed = match scalar 0 with Integer integer -> signed integer | _ -> false in
      let wide =
        if width = 64 then if signed then "__int128" else "unsigned __int128"
        else if signed then "int64_t"
        else "uint64_t"
      in
      Printf.sprintf "((%s)(((%s)%s * (%s)%s) >> %d))" c_type wide (argument 0) wide (argument 1)
        width
  | Square_root -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_sqrt") all
  | Fused_multiply_add -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_fma") all
  | Floor -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_floor") all
  | Ceiling -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_ceil") all
  | Truncate -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_trunc") all
  | Round_even -> Printf.sprintf "%s(%s)" (float_builtin "__builtin_roundeven") all
  | Float_bits ->
      Printf.sprintf "%s(%s)"
        (use_helper context (if scalar 0 = Float32 then "t_float32_bits" else "t_float64_bits"))
        all
  | Float_from_bits ->
      Printf.sprintf "%s(%s)"
        (use_helper context (if width 0 = 32 then "t_float32_from_bits" else "t_float64_from_bits"))
        all
  | Run_test -> "t_runtime_run_test(" ^ all ^ ")"
  | Coroutine_start ->
      Printf.sprintf
        "t_runtime_coroutine_start((void (*)(void *, uint64_t))%s.f_code, (void \
         *)%s.f_environment, %s)"
        (argument 0) (argument 0) (argument 1)
  | Coroutine_resume -> "t_runtime_coroutine_resume(" ^ all ^ ")"
  | Coroutine_suspend -> "t_runtime_coroutine_suspend()"
  | Tasks_spawn ->
      Printf.sprintf
        "t_runtime_tasks_spawn(%s, (void (*)(void *, uint64_t))%s.f_code, (void \
         *)%s.f_environment, %s)"
        (argument 0) (argument 1) (argument 1) (argument 2)
  | (Shared_allocate | Shared_retain | Shared_release | Shared_free | Shared_lock | Shared_unlock)
    as shared ->
      (* Declared in the C files that call them, so that the C of every
         other instance stays the same. *)
      let symbol, result, parameters =
        match shared with
        | Shared_allocate ->
            ("t_runtime_shared_allocate", "void *", "t_usize size, t_usize alignment")
        | Shared_retain -> ("t_runtime_shared_retain", "void ", "void *value")
        | Shared_release -> ("t_runtime_shared_release", "uint8_t ", "void *value")
        | Shared_free -> ("t_runtime_shared_free", "void ", "void *value")
        | Shared_lock -> ("t_runtime_shared_lock", "void ", "void *value")
        | _ -> ("t_runtime_shared_unlock", "void ", "void *value")
      in
      declare_prototype context symbol (Printf.sprintf "%s%s(%s);\n" result symbol parameters);
      symbol ^ "(" ^ all ^ ")"
  | (Blocking_begin | Blocking_end) as blocking ->
      let symbol =
        if blocking = Blocking_begin then "t_runtime_blocking_begin" else "t_runtime_blocking_end"
      in
      declare_prototype context symbol (Printf.sprintf "void %s(void);\n" symbol);
      symbol ^ "()"
  | Report_tests_to -> "t_runtime_report_tests_to(" ^ all ^ ")"
  | Live_blocks -> "t_runtime_live_blocks()"
  | Environment ->
      declare_prototype context "environ" "extern char **environ;\n";
      "((void *)environ)"
  | Terminated_length -> Printf.sprintf "((t_usize)__builtin_strlen((const char *)%s))" (argument 0)
  | Evidence_fill ->
      let slot = argument 0 in
      let outer =
        List.mapi
          (fun position (text, _) ->
            Printf.sprintf "%s->outer[%d] = (const struct t_evidence *)%s, " slot position text)
          (List.filteri (fun position _ -> position >= 3) arguments)
      in
      Printf.sprintf
        "(%s->evidence.implementation = (void *)%s, %s->evidence.table = (const void *const *)%s, \
         %s%s->evidence.outer = %s->outer)"
        slot (argument 1) slot (argument 2) (String.concat "" outer) slot slot
  | Evidence_implementation ->
      Printf.sprintf "((const struct t_evidence *)%s)->implementation" (argument 0)
  | Program_argument -> Printf.sprintf "((void *)((char **)%s)[%s])" (argument 0) (argument 1)
  | Evidence_outer ->
      Printf.sprintf "((void *)((const struct t_evidence *)%s)->outer[%s])" (argument 0)
        (argument 1)

let call_c context fc (target : Lowered.target) arguments =
  let arguments = List.filter_map (operand_c context fc) arguments in
  let texts = String.concat ", " (List.map fst arguments) in
  (match target with
  | Direct { signature; _ }
  | Indirect { signature; _ }
  | Evidence_call { signature; _ }
  | Table_call { signature; _ } ->
      let leading = match target with Direct _ -> 0 | _ -> 1 in
      let arity = List.length signature.parameters in
      if leading + List.length arguments <> arity then
        bug "a call that passes %d arguments to a target that takes %d"
          (leading + List.length arguments)
          arity
  | Intrinsic _ | Foreign _ -> ());
  match target with
  | Direct { function_; signature } ->
      (match function_ with
      | Instance key ->
          refer context key;
          if not (List.exists (Instance.equal key) context.called) then
            context.called <- key :: context.called
      | Nested _ -> ());
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
  | Foreign declaration -> (
      declare_prototype context declaration.symbol (Libc.prototype declaration);
      let cast_arguments =
        try
          List.map2
            (fun c_type (text, _) -> Printf.sprintf "(%s)(%s)" (Libc.show_c_type c_type) text)
            declaration.takes arguments
        with Invalid_argument _ ->
          bug "a call of %s with an argument of zero size" declaration.symbol
      in
      let called = Printf.sprintf "%s(%s)" declaration.symbol (String.concat ", " cast_arguments) in
      match declaration.returns with Pointer _ -> "((void *)" ^ called ^ ")" | _ -> called)
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
  | Evidence_call { evidence; capability; slot; signature } ->
      context.calls <- (capability, slot) :: context.calls;
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

let may_alias (first : Lowered.place) (second : Lowered.place) =
  let rec overlap (first : Lowered.projection list) (second : Lowered.projection list) =
    match (first, second) with
    | [], rest | rest, [] -> not (List.mem Lowered.Deref rest)
    | Field left :: first, Field right :: second -> left = right && overlap first second
    | Variant_field left :: first, Variant_field right :: second ->
        left.variant <> right.variant || (left.field = right.field && overlap first second)
    | Deref :: first, Deref :: second -> overlap first second
    | Index left :: first, Index right :: second -> left <> right || overlap first second
    | (Field _ | Variant_field _ | Deref | Index _) :: _, _ -> true
  in
  first.root = second.root && overlap first.projections second.projections

let statement_c context fc buffer (statement : Lowered.statement) =
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
      (* Every pointer a callee is given is [restrict], so the place it
         writes its result to is none it is also given to read. *)
      List.iter
        (fun (argument : Lowered.operand) ->
          match argument with
          | (Address { place = passed; _ } | Moved_address passed) when may_alias place passed ->
              bug "a call that writes its result to a place it is also given"
          | _ -> ())
        arguments;
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
          refer context (Drop ty);
          let symbol = Instance.symbol (Drop ty) in
          declare_prototype context symbol
            (prototype context fc.symbol symbol ~linkage:External (Convention.drop_signature ty)
            ^ ";\n");
          line "%s(&%s);" symbol text
      | Some _ -> bug "a drop of a place that is not a value")
  | Echo { text; length; site } ->
      context.failures <-
        (Echo, { definition = site.definition; line = site.line; column = site.column })
        :: context.failures;
      let operand argument =
        match operand_c context fc argument with
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
  | Fork { branches } ->
      let operand argument =
        match operand_c context fc argument with
        | Some (text, _) -> text
        | None -> bug "an environment of zero size"
      in
      line "{";
      line "  const struct t_branch branches[%d] = { %s };" (List.length branches)
        (String.concat ", "
           (List.map
              (fun (nested, environment) ->
                Printf.sprintf "{ &%s, (void *)%s }"
                  (function_ref_symbol fc (Nested nested))
                  (operand environment))
              branches));
      line "  t_runtime_parallel(branches, %d);" (List.length branches);
      line "}"
  | Fork_range { body; environment; first; last } ->
      let operand argument =
        match operand_c context fc argument with
        | Some (text, _) -> text
        | None -> bug "an operand of zero size"
      in
      line "t_runtime_parallel_range(&%s, (void *)%s, %s, %s);"
        (function_ref_symbol fc (Nested body))
        (operand environment) (operand first) (operand last)

let unreachable_c _ = "T_UNREACHABLE();"

let terminator_c context fc buffer (terminator : Lowered.terminator) =
  let line format =
    Printf.ksprintf (fun text -> Buffer.add_string buffer ("  " ^ text ^ "\n")) format
  in
  let operand argument =
    match operand_c context fc argument with
    | Some expression -> expression
    | None -> bug "an operand of zero size"
  in
  let default = function
    | Some block -> Printf.sprintf "goto b%d;" block
    | None -> unreachable_c context
  in
  match terminator with
  | Goto block -> line "goto b%d;" block
  | Switch { value; cases; default = otherwise } ->
      let text, ty = operand value in
      let c_type = scalar_c context (scalar_of context ty) in
      line "switch (%s) {" text;
      List.iter
        (fun (value, block) -> line "case (%s)%sULL: goto b%d;" c_type (Z.to_string value) block)
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
      match operand_c context fc value with
      | None -> line "return;"
      | Some (text, _) -> line "return %s;" text)
  | Unreachable -> line "%s" (unreachable_c context)
  | Fail { failure; message; length; site } ->
      if match failure with Lowered.Todo -> true | Panic | Assertion -> false then
        context.failures <-
          (Todo, { definition = site.definition; line = site.line; column = site.column })
          :: context.failures;
      line "%s(%s, %s, %s, %d, %d);"
        (match failure with
        | Panic -> "t_runtime_panic"
        | Assertion -> "t_runtime_assertion_failed"
        | Todo -> "t_runtime_todo")
        (fst (operand message))
        (fst (operand length))
        (anchor_c context site.definition)
        site.line site.column
