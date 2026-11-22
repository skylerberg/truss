let ( ++ ) = C_text.( ++ )
let render_line text = Text "  " ++ text ++ Text "\n"
let render_application name arguments = name ++ Text "(" ++ C_text.join ", " arguments ++ Text ")"
let render_runtime_call name arguments = render_application (Text name) arguments

let render_intrinsic (emission : Emission.t) (intrinsic : Lowered.intrinsic)
    (arguments : (C_text.t * Lowered.ty) list) : C_text.t =
  let render_argument position = fst (List.nth arguments position) in
  let classify_scalar position =
    C_values.classify_scalar emission (snd (List.nth arguments position))
  in
  let compute_width position = C_values.compute_bit_width (classify_scalar position) in
  let render_unsigned position =
    C_values.render_cast
      (C_values.render_unsigned_type emission (classify_scalar position))
      (render_argument position)
  in
  let all = List.map fst arguments in
  let render_float_builtin name =
    render_runtime_call (if classify_scalar 0 = Float32 then name ^ "f" else name) all
  in
  let render_scalar_type position =
    C_types.render_scalar_type emission.types (classify_scalar position)
  in
  let render_flag call = Text "((uint8_t)" ++ render_runtime_call call all ++ Text ")" in
  match intrinsic with
  | Allocate -> render_runtime_call "truss_runtime_allocate" all
  | Reallocate -> render_runtime_call "truss_runtime_reallocate" all
  | Free -> render_runtime_call "truss_runtime_free" all
  | Copy_bytes -> render_runtime_call "__builtin_memcpy" all
  | Move_bytes -> render_runtime_call "__builtin_memmove" all
  | Compare_bytes -> render_application (Emission.use_helper emission Compare_bytes) all
  | Add_overflow -> render_flag "__builtin_add_overflow"
  | Subtract_overflow -> render_flag "__builtin_sub_overflow"
  | Multiply_overflow -> render_flag "__builtin_mul_overflow"
  | Leading_zeros ->
      Text "(" ++ render_argument 0
      ++ Text (Printf.sprintf " == 0 ? %d : __builtin_clzll((unsigned long long)" (compute_width 0))
      ++ render_unsigned 0
      ++ Text (Printf.sprintf ") - %d)" (64 - compute_width 0))
  | Trailing_zeros ->
      Text "(" ++ render_argument 0
      ++ Text (Printf.sprintf " == 0 ? %d : __builtin_ctzll((unsigned long long)" (compute_width 0))
      ++ render_unsigned 0 ++ Text "))"
  | Count_ones -> Text "__builtin_popcountll((unsigned long long)" ++ render_unsigned 0 ++ Text ")"
  | Swap_bytes -> (
      match compute_width 0 with
      | 8 -> render_argument 0
      | width ->
          C_values.render_cast (render_scalar_type 0)
            (Text (Printf.sprintf "__builtin_bswap%d(" width) ++ render_unsigned 0 ++ Text ")"))
  | Rotate_left | Rotate_right ->
      let mask = Printf.sprintf " & %d)" (compute_width 0 - 1) in
      let first, second =
        if intrinsic = Rotate_left then (" << (", " >> ((-") else (" >> (", " << ((-")
      in
      C_values.render_cast (render_scalar_type 0)
        (Text "((" ++ render_unsigned 0 ++ Text first ++ render_argument 1
        ++ Text (mask ^ ") | (")
        ++ render_unsigned 0 ++ Text second ++ render_argument 1
        ++ Text (")" ^ mask ^ "))"))
  | Multiply_high ->
      let width = compute_width 0 in
      let signed =
        match classify_scalar 0 with Integer integer -> C_runtime.is_signed integer | _ -> false
      in
      let wide =
        if width = 64 then if signed then "__int128" else "unsigned __int128"
        else if signed then "int64_t"
        else "uint64_t"
      in
      C_values.render_cast (render_scalar_type 0)
        (Text (Printf.sprintf "(((%s)" wide)
        ++ render_argument 0
        ++ Text (Printf.sprintf " * (%s)" wide)
        ++ render_argument 1
        ++ Text (Printf.sprintf ") >> %d)" width))
  | Square_root -> render_float_builtin "__builtin_sqrt"
  | Fused_multiply_add -> render_float_builtin "__builtin_fma"
  | Floor -> render_float_builtin "__builtin_floor"
  | Ceiling -> render_float_builtin "__builtin_ceil"
  | Truncate -> render_float_builtin "__builtin_trunc"
  | Round_even -> render_float_builtin "__builtin_roundeven"
  | Float_bits ->
      render_application
        (Emission.use_helper emission
           (if classify_scalar 0 = Float32 then Float32_bits else Float64_bits))
        all
  | Float_from_bits ->
      render_application
        (Emission.use_helper emission
           (if compute_width 0 = 32 then Float32_from_bits else Float64_from_bits))
        all
  | Run_test -> render_runtime_call "truss_runtime_run_test" all
  | Coroutine_start ->
      Text "truss_runtime_coroutine_start((void (*)(void *, uint64_t, void *))" ++ render_argument 0
      ++ Text ", (void *)" ++ render_argument 1 ++ Text ", " ++ render_argument 2 ++ Text ")"
  | Coroutine_resume -> render_runtime_call "truss_runtime_coroutine_resume" all
  | Coroutine_suspend -> render_runtime_call "truss_runtime_coroutine_suspend" []
  | Tasks_spawn ->
      Text "truss_runtime_tasks_spawn(" ++ render_argument 0
      ++ Text ", (void (*)(void *, uint64_t, void *))" ++ render_argument 1 ++ Text ", (void *)"
      ++ render_argument 2 ++ Text ", " ++ render_argument 3 ++ Text ")"
  | (Shared_allocate | Shared_retain | Shared_release | Shared_free | Shared_lock | Shared_unlock)
    as shared ->
      let symbol, result, parameters =
        match shared with
        | Shared_allocate ->
            ("truss_runtime_shared_allocate", "void *", "uint64_t size, uint64_t alignment")
        | Shared_retain -> ("truss_runtime_shared_retain", "void ", "void *value")
        | Shared_release -> ("truss_runtime_shared_release", "uint8_t ", "void *value")
        | Shared_free -> ("truss_runtime_shared_free", "void ", "void *value")
        | Shared_lock -> ("truss_runtime_shared_lock", "void ", "void *value")
        | _ -> ("truss_runtime_shared_unlock", "void ", "void *value")
      in
      Emission.declare_prototype emission (Text symbol)
        (Text (Printf.sprintf "%s%s(%s);\n" result symbol parameters));
      render_runtime_call symbol all
  | (Blocking_begin | Blocking_end) as blocking ->
      let symbol =
        if blocking = Blocking_begin then "truss_runtime_blocking_begin"
        else "truss_runtime_blocking_end"
      in
      Emission.declare_prototype emission (Text symbol)
        (Text (Printf.sprintf "void %s(void);\n" symbol));
      render_runtime_call symbol []
  | Report_tests_to -> render_runtime_call "truss_runtime_report_tests_to" all
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
      render_application (Emission.use_helper emission Lend ++ Text name) all
  | Live_blocks -> render_runtime_call "truss_runtime_live_blocks" []
  | Environment ->
      Emission.declare_prototype emission (Text "environ") (Text "extern char **environ;\n");
      Text "((void *)environ)"
  | Terminated_length ->
      Text "((uint64_t)__builtin_strlen((const char *)" ++ render_argument 0 ++ Text "))"
  | Evidence_fill ->
      let slot = render_argument 0 in
      Text "(" ++ slot ++ Text "->evidence.implementation = (void *)" ++ render_argument 1
      ++ Text ", " ++ slot ++ Text "->evidence.table = (const void *const *)" ++ render_argument 2
      ++ Text ", "
      ++ Concat
           (List.mapi
              (fun position (text, _) ->
                slot
                ++ Text (Printf.sprintf "->outer[%d] = (const struct truss_evidence *)" position)
                ++ text ++ Text ", ")
              (List.drop 3 arguments))
      ++ slot ++ Text "->evidence.outer = " ++ slot ++ Text "->outer)"
  | Capabilities_fill ->
      let table = render_argument 0 in
      let render_entry index field value =
        table ++ Text (Printf.sprintf "->entries[%d].%s = " index field) ++ value
      in
      let rec fill index = function
        | (capability, _) :: (evidence, _) :: rest ->
            render_entry index "capability" capability
            :: render_entry index "evidence" (Text "(void *)" ++ evidence)
            :: fill (index + 1) rest
        | [] -> [ render_entry index "capability" (Text "0") ]
        | [ _ ] -> C_runtime.raise_bug "a table of capabilities with an incomplete entry"
      in
      Text "(" ++ C_text.join ", " (fill 0 (List.drop 1 arguments)) ++ Text ")"
  | Capability_find ->
      Text "truss_runtime_find_capability((const struct truss_capability *)" ++ render_argument 0
      ++ Text ", " ++ render_argument 1 ++ Text ")"
  | Trace_link ->
      Text "(" ++ render_argument 0 ++ Text "->site = " ++ render_argument 1 ++ Text ", "
      ++ render_argument 0 ++ Text "->caller = (const struct truss_trace *)" ++ render_argument 2
      ++ Text ")"
  | Evidence_implementation ->
      Text "((const struct truss_evidence *)" ++ render_argument 0 ++ Text ")->implementation"
  | Program_argument ->
      Text "((void *)((char **)" ++ render_argument 0 ++ Text ")[" ++ render_argument 1 ++ Text "])"
  | Evidence_outer ->
      Text "((void *)((const struct truss_evidence *)" ++ render_argument 0 ++ Text ")->outer["
      ++ render_argument 1 ++ Text "])"

let render_through_table (emission : Emission.t) ~pointer (signature : Lowered.signature) arguments
    =
  Text "(("
  ++ (match signature.result with
    | None -> Text "void"
    | Some ty -> C_types.render_type emission.types ty)
  ++ Text " (*)("
  ++ C_types.render_signature_parameters emission.types signature.parameters None
  ++ Text "))" ++ pointer ++ Text ")(" ++ C_text.join ", " arguments ++ Text ")"

let render_call (emission : Emission.t) fc (target : Lowered.target) arguments : C_text.t =
  let arguments = List.filter_map (C_values.render_operand emission fc) arguments in
  let texts = List.map fst arguments in
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
  let render_required operand ~description =
    match C_values.render_operand emission fc operand with
    | Some (text, _) -> text
    | None -> C_runtime.raise_bug "%s of zero size" description
  in
  match target with
  | Direct { function_; signature } ->
      let symbol, linkage =
        match function_ with
        | Item item -> (Emission.render_called_item emission item, C_runtime.External)
        | Nested nested_index -> (C_text.Name (Nested_function nested_index), Internal)
      in
      Emission.declare_prototype emission symbol
        (C_values.render_prototype emission symbol ~linkage signature ++ Text ";\n");
      render_application symbol texts
  | Indirect { code; environment; _ } ->
      render_application
        (render_required code ~description:"a function value")
        (render_required environment ~description:"a function value" :: texts)
  | Intrinsic intrinsic -> render_intrinsic emission intrinsic arguments
  | Foreign declaration -> (
      Emission.declare_prototype emission (Text declaration.symbol)
        (Text (Libc.render_prototype declaration));
      let cast_arguments =
        try
          List.map2
            (fun c_type (text, _) ->
              Text (Printf.sprintf "(%s)(" (Libc.show_c_type c_type)) ++ text ++ Text ")")
            declaration.takes arguments
        with Invalid_argument _ ->
          C_runtime.raise_bug "a call of %s with an argument of zero size" declaration.symbol
      in
      let called = render_runtime_call declaration.symbol cast_arguments in
      match declaration.returns with
      | Pointer _ -> C_values.render_cast (Text "void *") called
      | _ -> called)
  | Table_call { table; value; slot; signature } ->
      render_through_table emission
        ~pointer:
          (Text "((const void *const *)"
          ++ render_required table ~description:"a table"
          ++ Text (Printf.sprintf ")[%d]" slot))
        signature
        (render_required value ~description:"an any value" :: texts)
  | Evidence_call { evidence; capability; slot; signature } ->
      Emission.record_capability_call emission ~capability ~slot;
      let evidence = render_required evidence ~description:"evidence" in
      render_through_table emission
        ~pointer:
          (Text "((const struct truss_evidence *)" ++ evidence
          ++ Text (Printf.sprintf ")->table[%d]" slot))
        signature (evidence :: texts)

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

let render_failure_operand (emission : Emission.t) fc operand =
  match C_values.render_operand emission fc operand with
  | Some (text, _) -> text
  | None -> C_runtime.raise_bug "an operand of zero size"

let render_failure_arguments (emission : Emission.t) fc ~message ~length ~site ~reported =
  [
    render_failure_operand emission fc message;
    render_failure_operand emission fc length;
    (match reported with
    | Some reported -> render_failure_operand emission fc reported
    | None -> Emission.render_site emission site);
  ]

let render_panic_arguments (emission : Emission.t) fc ~message ~length ~site ~reported ~trace =
  render_failure_arguments emission fc ~message ~length ~site ~reported
  @ [ render_failure_operand emission fc (Option.value trace ~default:(Lowered.Constant Null)) ]

let render_statement (emission : Emission.t) fc (statement : Lowered.statement) : C_text.t =
  let render_required argument ~description =
    match C_values.render_operand emission fc argument with
    | Some (text, _) -> text
    | None -> C_runtime.raise_bug "%s of zero size" description
  in
  let render_assignment target value = render_line (target ++ Text " = " ++ value ++ Text ";") in
  let render_call_statement call = render_line (call ++ Text ";") in
  match statement with
  | Assign (place, rvalue) -> (
      match C_values.render_place emission fc place with
      | None -> C_text.empty
      | Some (target, target_ty) -> (
          match C_values.render_rvalue emission fc target_ty rvalue with
          | None -> C_text.empty
          | Some (Expression text) -> render_assignment target text
          | Some (Allocating { block; fill; value = render_value }) ->
              let name = C_types.render_key emission.types block in
              render_line (Text "{")
              ++ render_line
                   (Text "  " ++ name ++ Text " *block = truss_runtime_allocate(sizeof(" ++ name
                  ++ Text "), _Alignof(" ++ name ++ Text "));")
              ++ render_assignment (Text "  *block") fill
              ++ render_assignment (Text "  " ++ target) (render_value (Text "block"))
              ++ render_line (Text "}")))
  | Call { target; arguments; result = Written place } ->
      List.iter
        (fun (argument : Lowered.operand) ->
          match argument with
          | (Address { place = passed; _ } | Moved_address passed) when may_alias place passed ->
              C_runtime.raise_bug "a call that writes its result to a place it is also given"
          | _ -> ())
        arguments;
      render_call_statement
        (render_call emission fc target (Address { place; writable = true } :: arguments))
  | Call { target; arguments; result } -> (
      let call = render_call emission fc target arguments in
      match result with
      | Returned place -> (
          match C_values.render_place emission fc place with
          | Some (place, _) -> render_assignment place call
          | None -> render_call_statement call)
      | Discarded | Written _ -> render_call_statement call)
  | Drop place -> (
      match C_values.render_place emission fc place with
      | None -> C_text.empty
      | Some (text, Value ty) ->
          let symbol = Emission.render_item emission (Drop ty) in
          Emission.declare_prototype emission symbol
            (C_values.render_prototype emission symbol ~linkage:External
               (Convention.drop_signature ty)
            ++ Text ";\n");
          render_call_statement (render_application symbol [ Text "&" ++ text ])
      | Some _ -> C_runtime.raise_bug "a drop of a place that is not a value")
  | Echo { text; length; site } ->
      Emission.record_failure emission Echo site;
      render_call_statement
        (render_runtime_call "truss_runtime_echo"
           [
             render_required text ~description:"an echo";
             render_required length ~description:"an echo";
             Emission.render_site emission site;
           ])
  | Fail_obligation_when { test; message; length; site; reported; trace } ->
      render_call_statement
        (render_runtime_call "TRUSS_FAIL_OBLIGATION_WHEN"
           (C_values.render_comparison emission fc test
           :: render_panic_arguments emission fc ~message ~length ~site ~reported ~trace))
  | Free_block { place; variant } -> (
      match C_values.render_place emission fc place with
      | Some (text, Value sum) ->
          render_call_statement
            (render_runtime_call "truss_runtime_free"
               [ C_values.render_block_pointer emission text sum variant ])
      | _ -> C_runtime.raise_bug "a block of a place that is not a sum type")
  | Defer_free_block { lend; place; variant } -> (
      match (C_values.render_operand emission fc lend, C_values.render_place emission fc place) with
      | Some (lend, _), Some (text, Value sum) ->
          render_call_statement
            (render_application
               (Emission.use_helper emission Lend ++ Text "_defer_free")
               [ lend; C_values.render_block_pointer emission text sum variant ])
      | _ -> C_runtime.raise_bug "a block of a place that is not a sum type")
  | Fork { branches } ->
      let render_branch (nested, environment) =
        Text "{ &" ++ Name (Nested_function nested) ++ Text ", (void *)"
        ++ render_required environment ~description:"an environment"
        ++ Text " }"
      in
      render_line (Text "{")
      ++ render_line
           (Text
              (Printf.sprintf "  const struct truss_branch branches[%d] = { " (List.length branches))
           ++ C_text.join ", " (List.map render_branch branches)
           ++ Text " };")
      ++ render_line
           (Text (Printf.sprintf "  truss_runtime_parallel(branches, %d);" (List.length branches)))
      ++ render_line (Text "}")
  | Fork_range { body; environment; first; last } ->
      render_call_statement
        (render_runtime_call "truss_runtime_parallel_range"
           [
             Text "&" ++ Name (Nested_function body);
             Text "(void *)" ++ render_required environment ~description:"an operand";
             render_required first ~description:"an operand";
             render_required last ~description:"an operand";
           ])

let unreachable = "TRUSS_UNREACHABLE();"

let render_terminator (emission : Emission.t) fc (terminator : Lowered.terminator) : C_text.t =
  let render_operand argument =
    match C_values.render_operand emission fc argument with
    | Some expression -> expression
    | None -> C_runtime.raise_bug "an operand of zero size"
  in
  let render_goto block = Printf.sprintf "goto b%d;" block in
  let render_default = function Some block -> render_goto block | None -> unreachable in
  let render_text_line text = render_line (Text text) in
  let render_switch scrutinee cases ~default =
    render_line (Text "switch (" ++ scrutinee ++ Text ") {")
    ++ Concat cases
    ++ render_text_line ("default: " ^ default)
    ++ render_text_line "}"
  in
  match terminator with
  | Goto block -> render_text_line (render_goto block)
  | Branch { test; yes; no } ->
      render_line
        (Text "if (" ++ C_values.render_comparison emission fc test ++ Text (") " ^ render_goto yes))
      ++ render_text_line (render_goto no)
  | Switch { value; cases; default } ->
      let text, ty = render_operand value in
      let c_type =
        C_types.render_scalar_type emission.types (C_values.classify_scalar emission ty)
      in
      render_switch text
        (List.map
           (fun (value, block) ->
             render_line
               (Text "case (" ++ c_type
               ++ Text (Printf.sprintf ")%sULL: %s" (Z.to_string value) (render_goto block))))
           cases)
        ~default:(render_goto default)
  | Switch_variant { place; cases; default = otherwise } -> (
      match C_values.render_place emission fc place with
      | None -> (
          match cases with
          | (_, block) :: _ -> render_text_line (render_goto block)
          | [] -> render_text_line (render_default otherwise))
      | Some (text, Value sum) -> (
          match Memory_layout.dispatch (C_types.compute_layout emission.types sum) cases with
          | Switch { tag; cases } ->
              render_switch
                (text ++ Text (C_values.render_path tag.at))
                (List.map
                   (fun (value, block) ->
                     render_text_line
                       (Printf.sprintf "case %sULL: %s" (Z.to_string value) (render_goto block)))
                   cases)
                ~default:(render_default otherwise)
          | Tests tests ->
              let tests, otherwise =
                match (otherwise, List.rev tests) with
                | None, (_, last) :: earlier -> (List.rev earlier, Some last)
                | _ -> (tests, otherwise)
              in
              Concat
                (List.map
                   (fun (discriminant, block) ->
                     render_line
                       (Text "if ("
                       ++ C_values.render_discriminant_test emission text discriminant
                       ++ Text (") " ^ render_goto block)))
                   tests)
              ++ render_text_line (render_default otherwise))
      | Some _ -> C_runtime.raise_bug "a variant switch on a place that is not a value")
  | Return None -> render_text_line "return;"
  | Return (Some value) -> (
      match C_values.render_operand emission fc value with
      | None -> render_text_line "return;"
      | Some (text, _) -> render_line (Text "return " ++ text ++ Text ";"))
  | Unreachable -> render_text_line unreachable
  | Fail { failure; message; length; site; reported; trace } ->
      if failure = Lowered.Todo then Emission.record_failure emission Todo site;
      let runtime =
        match failure with
        | Panic -> "truss_runtime_panic"
        | Assertion -> "truss_runtime_assertion_failed"
        | Todo -> "truss_runtime_todo"
      in
      let arguments =
        match (failure, trace) with
        | Panic, _ -> render_panic_arguments emission fc ~message ~length ~site ~reported ~trace
        | (Assertion | Todo), None ->
            render_failure_arguments emission fc ~message ~length ~site ~reported
        | (Assertion | Todo), Some _ ->
            C_runtime.raise_bug "a call chain on a failure that is not a panic"
      in
      render_line (render_runtime_call runtime arguments ++ Text ";")
