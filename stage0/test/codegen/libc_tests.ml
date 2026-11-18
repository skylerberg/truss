let view_ty = Codegen_support.named "View" ~arguments:[ Type Codegen_support.uint8 ]
let bytes_ty = Storage.make_storage_type Codegen_support.uint8

let extra =
  [
    ( Ground.to_string view_ty,
      Storage.make_view_shape ~uint64:Codegen_support.uint64 Codegen_support.uint8 );
  ]

let intrinsic_types : Backend.For_testing.Intrinsics.types =
  { uint64 = Codegen_support.uint64; string_slice = Codegen_support.named "StringSlice" }

let operate builder ?destination ?(type_arguments = []) operation arguments =
  ignore
    (Backend.For_testing.Intrinsics.lower
       (Codegen_support.make_shape_env ~extra ())
       builder intrinsic_types operation ~type_arguments arguments ~destination
       ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
       ~trace:None)

let build_entry build_body : Codegen_support.program_fragment =
 fun env ->
  let builder = Emit_c.Builder.create env ~item:(Codegen_support.code_item "entry") in
  Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder);
  let result = build_body builder in
  Emit_c.Builder.finish builder (Return (Some (Copy (Lowered.make_local_place result))));
  Emit_c.Builder.build builder
    { parameters = []; result = Some (Codegen_support.value Codegen_support.int32); returns = true }

let make_view builder text =
  let view = Emit_c.Builder.allocate_local builder (Codegen_support.value view_ty) in
  Emit_c.Builder.emit builder
    (Assign
       ( Lowered.make_local_place view,
         Storage.build_view view_ty ~elements:(Constant (Bytes text))
           ~length:(Lowered.make_uint64_constant (String.length text)) ));
  view

let make_flags builder numbers =
  let all = Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32) in
  Emit_c.Builder.emit builder
    (Assign (Lowered.make_local_place all, Use (Codegen_support.constant_int32 0)));
  List.iter
    (fun number ->
      let one =
        Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
      in
      operate builder ~destination:(Lowered.make_local_place one) (Runtime (Libc_number number)) [];
      Emit_c.Builder.emit builder
        (Assign
           ( Lowered.make_local_place all,
             Binary
               (Bit_or, Copy (Lowered.make_local_place all), Copy (Lowered.make_local_place one)) )))
    numbers;
  all

let free builder storage =
  Emit_c.Builder.emit builder
    (Call
       {
         target = Intrinsic Free;
         arguments = [ Copy (Storage.project_buffer storage) ];
         result = Discarded;
       })

let try_compile text =
  let directory = Lazy.force Codegen_support.scratch in
  let source = Filename.temp_file ~temp_dir:directory "libc" ".c" in
  Out_channel.with_open_text source (fun channel -> output_string channel text);
  C_compiler.For_testing.compile
    (Lazy.force Codegen_support.c_compiler)
    O1 ~source ~output:(source ^ ".o")

let linux : Libc.system = { os = Linux; architecture = X86_64 }

let () =
  Codegen_support.test
    "the C library's numbers, prototypes, and structures match this system's headers" (fun () ->
      match try_compile (Libc.For_testing.check Codegen_support.host) with
      | Ok () -> ()
      | Error message -> Codegen_support.fail "the table disagrees with the headers:\n%s" message);
  Codegen_support.test "another system's numbers do not pass for this one's" (fun () ->
      let other : Libc.system =
        {
          Codegen_support.host with
          os = (match Codegen_support.host.os with Linux -> Macos | Macos -> Linux);
        }
      in
      match try_compile (Libc.For_testing.check other) with
      | Ok () ->
          Codegen_support.fail "the check takes the table of %s on %s" (Libc.show_system other)
            (Libc.show_system Codegen_support.host)
      | Error _ -> ());
  Codegen_support.test
    "a function that only macOS has is held to its headers, and to no other system's" (fun () ->
      let is_checked system =
        String.includes ~affix:"proc_pidpath" (Libc.For_testing.check system)
      in
      if not (is_checked { os = Macos; architecture = Arm64 }) then
        Codegen_support.fail "the check for macOS leaves out proc_pidpath";
      if is_checked linux then Codegen_support.fail "the check for Linux looks for proc_pidpath");
  Codegen_support.test "a call of a function the system lacks stops the program, and calls nothing"
    (fun () ->
      let env = Memory_layout.create linux ~compute_shape:(Codegen_support.compute_shape extra) in
      let builder = Emit_c.Builder.create env ~item:(Codegen_support.code_item "entry") in
      Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder);
      let length =
        Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
      in
      let path = Emit_c.Builder.allocate_local builder (Codegen_support.value bytes_ty) in
      ignore
        (Backend.For_testing.Intrinsics.lower env builder intrinsic_types
           (Runtime (Libc Proc_pidpath)) ~type_arguments:[]
           [
             Value (Codegen_support.constant_int32 1);
             Place (Lowered.make_local_place path);
             Value (Lowered.make_uint64_constant 64);
           ]
           ~destination:(Some (Lowered.make_local_place length))
           ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
           ~trace:None);
      Emit_c.Builder.finish builder (Return (Some (Copy (Lowered.make_local_place length))));
      let fragment =
        Emit_c.Builder.build builder
          {
            parameters = [];
            result = Some (Codegen_support.value Codegen_support.int32);
            returns = true;
          }
      in
      let c = Emit_c.For_testing.render_c fragment in
      if not (String.includes ~affix:"t_runtime_panic(" c) then
        Codegen_support.fail "the call does not stop the program:\n%s" c;
      if String.includes ~affix:"proc_pidpath(" c then
        Codegen_support.fail "the function is called:\n%s" c);
  Codegen_support.test "a function that takes a structure is declared with no header" (fun () ->
      Codegen_support.expect_string
        ~expected:"struct timespec;\nint clock_gettime(int, struct timespec *);\n"
        (Libc.render_prototype (Libc.make_declaration linux Clock_gettime)));
  Codegen_support.test "a function with arguments C passes through ... is declared so" (fun () ->
      Codegen_support.expect_string ~expected:"int open(const char *, int, ...);\n"
        (Libc.render_prototype (Libc.make_declaration linux Open)));
  Codegen_support.test "a number whose name in C starts with an underscore is named without it"
    (fun () ->
      Codegen_support.expect_string ~expected:"libc_sc_nprocessors_onln"
        (Intrinsic.show_operation (Runtime (Libc_number Sc_nprocessors_onln))));
  Codegen_support.test "storage a function fills is passed mut, and a view it reads is not"
    (fun () ->
      let list_modes operation =
        List.map
          (fun (parameter : Types.parameter_info) -> (parameter.name, parameter.mode))
          (Intrinsic_signatures.make_signature operation).parameters
      in
      if
        list_modes (Runtime (Libc Read))
        <> [ ("descriptor", Types.Read); ("buffer", Mut); ("count", Read) ]
        || list_modes (Runtime (Libc Write))
           <> [ ("descriptor", Types.Read); ("bytes", Read); ("count", Read) ]
      then Codegen_support.fail "read and write take their memory in the wrong modes");
  Codegen_support.test "a row's reads and writes are counted by a number the call is passed"
    (fun () ->
      List.iter
        (fun function_ ->
          let { Libc.parameters; at_most; _ } = Libc.make_signature function_ in
          let name = Libc.show_function function_ in
          let expect_passed role parameter =
            match List.assoc_opt parameter parameters with
            | Some (Libc.Value UInt64) | Some (Written (UInt32, [ _ ])) -> ()
            | _ ->
                Codegen_support.fail "%s: %s is `%s`, which is no count the call is passed" name
                  role parameter
          in
          Option.iter (expect_passed "the bound of the result") at_most;
          List.iter
            (fun (parameter, (passes : Libc.passes)) ->
              match passes with
              | Elements (_, extent) | Room (_, extent) | Elements_to_change (_, extent) -> (
                  match extent with
                  | Counted { by; each } ->
                      expect_passed ("the count of `" ^ parameter ^ "`") by;
                      if each < 1 then
                        Codegen_support.fail "%s: `%s` has no elements for each one" name parameter
                  | Exactly count ->
                      if count < 1 then
                        Codegen_support.fail "%s: `%s` has no elements" name parameter
                  | Number number ->
                      if Libc.classify_number number <> UInt64 then
                        Codegen_support.fail "%s: `%s` is counted by %s, which is no UInt64" name
                          parameter (Libc.show_number number)
                  | Through_zero -> ())
              | Value _ | Written _ | Always _ | Fixed _ -> ())
            parameters)
        Libc.functions;
      let { Libc.parameters; at_most; _ } = Libc.make_signature Read in
      if
        List.assoc "buffer" parameters <> Room (UInt8, Counted { by = "count"; each = 1 })
        || at_most <> Some "count"
      then Codegen_support.fail "read does not fill at most `count` bytes of room")

let () =
  Codegen_support.test "a program writes a view's bytes with write" (fun () ->
      let status, output, _ =
        Codegen_support.run_program ~extra
          [
            build_entry (fun builder ->
                let view = make_view builder "written\n" in
                let wrote =
                  Emit_c.Builder.allocate_local builder
                    (Codegen_support.value Codegen_support.int64)
                in
                operate builder ~destination:(Lowered.make_local_place wrote) (Runtime (Libc Write))
                  [
                    Value (Codegen_support.constant_int32 1);
                    Place (Lowered.make_local_place view);
                    Value (Lowered.make_uint64_constant 8);
                  ];
                let status =
                  Emit_c.Builder.allocate_local builder
                    (Codegen_support.value Codegen_support.int32)
                in
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place status,
                       Convert (Copy (Lowered.make_local_place wrote), Integer Int32) ));
                status);
          ]
      in
      Codegen_support.expect_int ~expected:8 status;
      Codegen_support.expect_string ~expected:"written\n" output);
  Codegen_support.test "a request that a row fixes is passed, and is no argument of the Truss call"
    (fun () ->
      let names =
        List.map
          (fun (parameter : Types.parameter_info) -> parameter.name)
          (Intrinsic_signatures.make_signature (Runtime (Libc Fcntl_dupfd_cloexec))).parameters
      in
      if names <> [ "descriptor"; "least" ] then
        Codegen_support.fail "fcntl_dupfd_cloexec takes %s" (String.concat ", " names);
      let status, output, _ =
        Codegen_support.run_program ~extra
          [
            build_entry (fun builder ->
                let copy =
                  Emit_c.Builder.allocate_local builder
                    (Codegen_support.value Codegen_support.int32)
                in
                operate builder ~destination:(Lowered.make_local_place copy)
                  (Runtime (Libc Fcntl_dupfd_cloexec))
                  [
                    Value (Codegen_support.constant_int32 1);
                    Value (Codegen_support.constant_int32 10);
                  ];
                let view = make_view builder "through the copy\n" in
                let wrote =
                  Emit_c.Builder.allocate_local builder
                    (Codegen_support.value Codegen_support.int64)
                in
                operate builder ~destination:(Lowered.make_local_place wrote) (Runtime (Libc Write))
                  [
                    Value (Copy (Lowered.make_local_place copy));
                    Place (Lowered.make_local_place view);
                    Value (Lowered.make_uint64_constant 17);
                  ];
                copy);
          ]
      in
      if status < 10 then
        Codegen_support.fail "the new descriptor is %d, which is less than the least asked for"
          status;
      Codegen_support.expect_string ~expected:"through the copy\n" output);
  Codegen_support.test "open is given its mode as C passes an argument through ..." (fun () ->
      let path = Filename.concat (Lazy.force Codegen_support.scratch) "opened" in
      Codegen_support.expect_status ~extra 0
        [
          build_entry (fun builder ->
              let name = make_view builder (path ^ "\000") in
              let wanted = make_flags builder [ O_wronly; O_creat; O_trunc ] in
              let descriptor =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              operate builder
                ~destination:(Lowered.make_local_place descriptor)
                (Runtime (Libc Open))
                [
                  Place (Lowered.make_local_place name);
                  Value (Copy (Lowered.make_local_place wanted));
                  Value (Codegen_support.constant_int32 0o600);
                ];
              let closed =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              operate builder ~destination:(Lowered.make_local_place closed) (Runtime (Libc Close))
                [ Value (Copy (Lowered.make_local_place descriptor)) ];
              closed);
        ];
      Codegen_support.expect_int ~expected:0o600 (Unix.stat path).st_perm);
  Codegen_support.test "errno is the number at the address the C library returns" (fun () ->
      Codegen_support.expect_status ~extra
        (Libc.evaluate_number Codegen_support.host Enoent)
        [
          build_entry (fun builder ->
              let name = make_view builder "/nonexistent/truss\000" in
              let wanted = make_flags builder [ O_rdonly ] in
              operate builder (Runtime (Libc Open))
                [
                  Place (Lowered.make_local_place name);
                  Value (Copy (Lowered.make_local_place wanted));
                  Value (Codegen_support.constant_int32 0);
                ];
              let error =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              operate builder ~destination:(Lowered.make_local_place error) (Runtime (Libc Errno))
                [];
              error);
        ]);
  Codegen_support.test "read fills the room storage has after its last element" (fun () ->
      let status, _, _ =
        Codegen_support.run_program ~extra ~input:"hello"
          [
            build_entry (fun builder ->
                let storage =
                  Emit_c.Builder.allocate_local builder (Codegen_support.value bytes_ty)
                in
                operate builder
                  ~destination:(Lowered.make_local_place storage)
                  ~type_arguments:[ Codegen_support.uint8 ] (Buffer Storage_with_capacity)
                  [ Value (Lowered.make_uint64_constant 16) ];
                operate builder ~type_arguments:[ Codegen_support.uint8 ] (Buffer Storage_push)
                  [
                    Place (Lowered.make_local_place storage);
                    Value (Constant (Integer (UInt8, Z.of_int 1)));
                  ];
                let got =
                  Emit_c.Builder.allocate_local builder
                    (Codegen_support.value Codegen_support.int64)
                in
                operate builder ~destination:(Lowered.make_local_place got) (Runtime (Libc Read))
                  [
                    Value (Codegen_support.constant_int32 0);
                    Place (Lowered.make_local_place storage);
                    Value (Lowered.make_uint64_constant 15);
                  ];
                let first =
                  Emit_c.Builder.allocate_local builder
                    (Codegen_support.value Codegen_support.int32)
                and count =
                  Emit_c.Builder.allocate_local builder
                    (Codegen_support.value Codegen_support.int32)
                in
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place first,
                       Convert
                         ( Copy
                             (Storage.index_element
                                (Lowered.make_local_place storage)
                                (Lowered.make_uint64_constant 1)),
                           Integer Int32 ) ));
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place count,
                       Convert (Copy (Lowered.make_local_place got), Integer Int32) ));
                Emit_c.Builder.emit builder
                  (Assign
                     ( Lowered.make_local_place first,
                       Binary
                         ( Add,
                           Copy (Lowered.make_local_place first),
                           Copy (Lowered.make_local_place count) ) ));
                free builder (Lowered.make_local_place storage);
                first);
          ]
      in
      Codegen_support.expect_int ~expected:(Char.code 'h' + 5) status);
  Codegen_support.test
    "a structure the C library writes arrives in the arguments named for its numbers" (fun () ->
      Codegen_support.expect_status ~extra 1
        [
          build_entry (fun builder ->
              let seconds =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int64)
              and nanoseconds =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int64)
              in
              Emit_c.Builder.emit builder
                (Assign (Lowered.make_local_place seconds, Use (Codegen_support.constant_int64 0)));
              Emit_c.Builder.emit builder
                (Assign
                   (Lowered.make_local_place nanoseconds, Use (Codegen_support.constant_int64 0)));
              let clock = make_flags builder [ Clock_realtime ] in
              let failed =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              operate builder ~destination:(Lowered.make_local_place failed)
                (Runtime (Libc Clock_gettime))
                [
                  Value (Copy (Lowered.make_local_place clock));
                  Place (Lowered.make_local_place seconds);
                  Place (Lowered.make_local_place nanoseconds);
                ];
              let recent = Emit_c.Builder.allocate_local builder (Raw Bool)
              and whole = Emit_c.Builder.allocate_local builder (Raw Bool) in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place recent,
                     Binary
                       ( Greater,
                         Copy (Lowered.make_local_place seconds),
                         Codegen_support.constant_int64 1_700_000_000 ) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place whole,
                     Binary
                       ( Less,
                         Copy (Lowered.make_local_place nanoseconds),
                         Codegen_support.constant_int64 1_000_000_000 ) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place recent,
                     Binary
                       ( Bit_and,
                         Copy (Lowered.make_local_place recent),
                         Copy (Lowered.make_local_place whole) ) ));
              let status =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Convert (Copy (Lowered.make_local_place recent), Integer Int32) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Binary
                       ( Subtract,
                         Copy (Lowered.make_local_place status),
                         Copy (Lowered.make_local_place failed) ) ));
              status);
        ]);
  Codegen_support.test "a number passed by address is read by the function and then written"
    (fun () ->
      let uint32 = Codegen_support.named "UInt32" in
      let extra = extra @ [ (Ground.to_string uint32, Memory_layout.Scalar (Integer UInt32)) ] in
      let operate builder ~destination operation arguments =
        ignore
          (Backend.For_testing.Intrinsics.lower
             (Codegen_support.make_shape_env ~extra ())
             builder intrinsic_types operation ~type_arguments:[] arguments
             ~destination:(Some destination)
             ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
             ~trace:None)
      in
      Codegen_support.expect_status ~extra 16
        [
          build_entry (fun builder ->
              let domain = make_flags builder [ Af_inet ]
              and kind = make_flags builder [ Sock_stream ] in
              let socket =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              operate builder ~destination:(Lowered.make_local_place socket) (Runtime (Libc Socket))
                [
                  Value (Copy (Lowered.make_local_place domain));
                  Value (Copy (Lowered.make_local_place kind));
                  Value (Codegen_support.constant_int32 0);
                ];
              let name = Emit_c.Builder.allocate_local builder (Codegen_support.value bytes_ty) in
              let operate_on_bytes ?destination operation arguments =
                ignore
                  (Backend.For_testing.Intrinsics.lower
                     (Codegen_support.make_shape_env ~extra ())
                     builder intrinsic_types operation ~type_arguments:[ Codegen_support.uint8 ]
                     arguments ~destination
                     ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
                     ~trace:None)
              in
              operate_on_bytes ~destination:(Lowered.make_local_place name)
                (Buffer Storage_with_capacity)
                [ Value (Lowered.make_uint64_constant 28) ];
              operate_on_bytes (Buffer Storage_lengthen)
                [ Place (Lowered.make_local_place name); Value (Lowered.make_uint64_constant 28) ];
              let length = Emit_c.Builder.allocate_local builder (Codegen_support.value uint32) in
              Emit_c.Builder.emit builder
                (Assign
                   (Lowered.make_local_place length, Use (Constant (Integer (UInt32, Z.of_int 28)))));
              let failed =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              operate builder ~destination:(Lowered.make_local_place failed)
                (Runtime (Libc Getsockname))
                [
                  Value (Copy (Lowered.make_local_place socket));
                  Place (Lowered.make_local_place name);
                  Place (Lowered.make_local_place length);
                ];
              let status =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Convert (Copy (Lowered.make_local_place length), Integer Int32) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Binary
                       ( Subtract,
                         Copy (Lowered.make_local_place status),
                         Copy (Lowered.make_local_place failed) ) ));
              free builder (Lowered.make_local_place name);
              status);
        ]);
  Codegen_support.test "an argument a row fixes is no argument of the Truss call" (fun () ->
      Codegen_support.expect_status ~extra 1
        [
          build_entry (fun builder ->
              let draw () =
                let value =
                  Emit_c.Builder.allocate_local builder
                    (Codegen_support.value Codegen_support.uint64)
                and failed =
                  Emit_c.Builder.allocate_local builder
                    (Codegen_support.value Codegen_support.int32)
                in
                Emit_c.Builder.emit builder
                  (Assign (Lowered.make_local_place value, Use (Constant (Integer (UInt64, Z.zero)))));
                operate builder ~destination:(Lowered.make_local_place failed)
                  (Runtime (Libc Getentropy))
                  [ Place (Lowered.make_local_place value) ];
                value
              in
              let first = draw () in
              let second = draw () in
              let differ = Emit_c.Builder.allocate_local builder (Raw Bool)
              and status =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place differ,
                     Binary
                       ( Not_equal,
                         Copy (Lowered.make_local_place first),
                         Copy (Lowered.make_local_place second) ) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place status,
                     Convert (Copy (Lowered.make_local_place differ), Integer Int32) ));
              status);
        ])

let () =
  Codegen_support.test "nothing after a call of a function that does not return is run" (fun () ->
      Codegen_support.expect_status ~extra 7
        [
          build_entry (fun builder ->
              operate builder (Runtime (Libc Exit)) [ Value (Codegen_support.constant_int32 7) ];
              let status =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign (Lowered.make_local_place status, Use (Codegen_support.constant_int32 0)));
              status);
        ]);
  Codegen_support.test
    "a pipe's two ends arrive in the arguments named for them, and poll finds the written data"
    (fun () ->
      let waited_ty = Storage.make_storage_type Codegen_support.int32 in
      Codegen_support.expect_status ~extra 1
        [
          build_entry (fun builder ->
              let read_end =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              and write_end =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign
                   (Lowered.make_local_place read_end, Use (Codegen_support.constant_int32 (-1))));
              Emit_c.Builder.emit builder
                (Assign
                   (Lowered.make_local_place write_end, Use (Codegen_support.constant_int32 (-1))));
              operate builder (Runtime (Libc Pipe))
                [
                  Place (Lowered.make_local_place read_end);
                  Place (Lowered.make_local_place write_end);
                ];
              let view = make_view builder "x" in
              operate builder (Runtime (Libc Write))
                [
                  Value (Copy (Lowered.make_local_place write_end));
                  Place (Lowered.make_local_place view);
                  Value (Lowered.make_uint64_constant 1);
                ];
              let waited =
                Emit_c.Builder.allocate_local builder (Codegen_support.value waited_ty)
              in
              operate builder ~destination:(Lowered.make_local_place waited)
                ~type_arguments:[ Codegen_support.int32 ] (Buffer Storage_with_capacity)
                [ Value (Lowered.make_uint64_constant 2) ];
              operate builder ~type_arguments:[ Codegen_support.int32 ] (Buffer Storage_push)
                [
                  Place (Lowered.make_local_place waited);
                  Value (Copy (Lowered.make_local_place read_end));
                ];
              let reading = make_flags builder [ Pollin ] in
              operate builder ~type_arguments:[ Codegen_support.int32 ] (Buffer Storage_push)
                [
                  Place (Lowered.make_local_place waited);
                  Value (Copy (Lowered.make_local_place reading));
                ];
              let ready =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              operate builder ~destination:(Lowered.make_local_place ready) (Runtime (Libc Poll))
                [
                  Place (Lowered.make_local_place waited);
                  Value (Lowered.make_uint64_constant 1);
                  Value (Codegen_support.constant_int32 1000);
                ];
              let actual =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place actual,
                     Binary
                       ( Shift_right,
                         Copy
                           (Storage.index_element (Lowered.make_local_place waited)
                              (Lowered.make_uint64_constant 1)),
                         Codegen_support.constant_int32 16 ) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place actual,
                     Binary
                       ( Bit_and,
                         Copy (Lowered.make_local_place actual),
                         Copy (Lowered.make_local_place reading) ) ));
              Emit_c.Builder.emit builder
                (Assign
                   ( Lowered.make_local_place ready,
                     Binary
                       ( Multiply,
                         Copy (Lowered.make_local_place ready),
                         Copy (Lowered.make_local_place actual) ) ));
              free builder (Lowered.make_local_place waited);
              ready);
        ])

let () =
  Codegen_support.test "dropping a handle closes its descriptor" (fun () ->
      let path = Filename.concat (Lazy.force Codegen_support.scratch) "held" in
      Out_channel.with_open_text path (fun channel -> output_string channel "held");
      let env =
        Memory_layout.create Codegen_support.host
          ~compute_shape:(Monomorphic.compute_shape Codegen_support.standard_context)
      in
      let drop_and_copy = Backend.For_testing.drop_and_copy env in
      let int32 = Ground.make_builtin Int32 in
      let view_ty = Storage.make_view_type (Ground.make_builtin UInt8) in
      let handle_ty = Ground.make_builtin Handle in
      let types : Backend.For_testing.Intrinsics.types =
        {
          uint64 = Ground.make_builtin UInt64;
          string_slice = Codegen_support.make_standard_type "text" "StringSlice" ();
        }
      in
      let entry =
        let builder = Emit_c.Builder.create env ~item:(Codegen_support.code_item "entry") in
        Emit_c.Builder.start builder (Emit_c.Builder.allocate_block builder);
        let name = Emit_c.Builder.allocate_local builder (Codegen_support.value view_ty) in
        let text = path ^ "\000" in
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place name,
               Storage.build_view view_ty ~elements:(Constant (Bytes text))
                 ~length:(Lowered.make_uint64_constant (String.length text)) ));
        let open_test_file () =
          let descriptor = Emit_c.Builder.allocate_local builder (Codegen_support.value int32) in
          ignore
            (Backend.For_testing.Intrinsics.lower env builder types (Runtime (Libc Open))
               ~type_arguments:[]
               [
                 Place (Lowered.make_local_place name);
                 Value
                   (Codegen_support.constant_int32
                      (Libc.evaluate_number Codegen_support.host O_rdonly));
                 Value (Codegen_support.constant_int32 0);
               ]
               ~destination:(Some (Lowered.make_local_place descriptor))
               ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
               ~trace:None);
          descriptor
        in
        let first = open_test_file () in
        let handle = Emit_c.Builder.allocate_local builder (Codegen_support.value handle_ty) in
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place handle,
               Build
                 {
                   ty = handle_ty;
                   variant = None;
                   fields = [ ("descriptor", Copy (Lowered.make_local_place first)) ];
                 } ));
        Emit_c.Builder.emit builder (Drop (Lowered.make_local_place handle));
        let second = open_test_file () in
        let same = Emit_c.Builder.allocate_local builder (Raw Bool)
        and status = Emit_c.Builder.allocate_local builder (Codegen_support.value int32) in
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place same,
               Binary
                 ( Equal,
                   Copy (Lowered.make_local_place first),
                   Copy (Lowered.make_local_place second) ) ));
        Emit_c.Builder.emit builder
          (Assign
             ( Lowered.make_local_place status,
               Convert (Copy (Lowered.make_local_place same), Integer Int32) ));
        Emit_c.Builder.finish builder (Return (Some (Copy (Lowered.make_local_place status))));
        Emit_c.Builder.build builder
          { parameters = []; result = Some (Codegen_support.value int32); returns = true }
      in
      let status, _, errors =
        Codegen_support.run_program ~env
          [
            Codegen_support.make_program_fragment entry;
            Codegen_support.make_program_fragment (Backend.For_testing.drop drop_and_copy handle_ty);
          ]
      in
      if status <> 1 then
        Codegen_support.fail "the descriptor was not free again (status %d, %s)" status errors)

let operate_checked builder ?destination ?(type_arguments = []) operation arguments =
  ignore
    (Backend.For_testing.Intrinsics.lower ~checks:true
       (Codegen_support.make_shape_env ~extra ())
       builder intrinsic_types operation ~type_arguments arguments ~destination
       ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
       ~trace:None)

let expect_panic ~saying program =
  let status, _, errors = Codegen_support.run_program ~extra program in
  if status <> 101 then Codegen_support.fail "expected a panic, got status %d (%s)" status errors;
  if not (String.includes ~affix:saying errors) then
    Codegen_support.fail "expected %S in %S" saying errors

let () =
  Codegen_support.test
    "a checked build stops a C library call that is given less room than it writes" (fun () ->
      expect_panic ~saying:"a call of the C library with less room than it writes"
        [
          build_entry (fun builder ->
              let storage =
                Emit_c.Builder.allocate_local builder (Codegen_support.value bytes_ty)
              in
              operate_checked builder
                ~destination:(Lowered.make_local_place storage)
                ~type_arguments:[ Codegen_support.uint8 ] (Buffer Storage_with_capacity)
                [ Value (Lowered.make_uint64_constant 4) ];
              let got =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int64)
              in
              operate_checked builder ~destination:(Lowered.make_local_place got)
                (Runtime (Libc Read))
                [
                  Value (Codegen_support.constant_int32 0);
                  Place (Lowered.make_local_place storage);
                  Value (Lowered.make_uint64_constant 100);
                ];
              let status =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign (Lowered.make_local_place status, Use (Codegen_support.constant_int32 0)));
              status);
        ]);
  Codegen_support.test
    "a checked build stops a C library call that is given fewer elements than it reads" (fun () ->
      expect_panic ~saying:"a call of the C library with fewer elements than it reads"
        [
          build_entry (fun builder ->
              let view = make_view builder "short" in
              let wrote =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int64)
              in
              operate_checked builder ~destination:(Lowered.make_local_place wrote)
                (Runtime (Libc Write))
                [
                  Value (Codegen_support.constant_int32 1);
                  Place (Lowered.make_local_place view);
                  Value (Lowered.make_uint64_constant 100);
                ];
              let status =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              Emit_c.Builder.emit builder
                (Assign (Lowered.make_local_place status, Use (Codegen_support.constant_int32 0)));
              status);
        ]);
  Codegen_support.test "a checked build stops a C library call whose text does not end with a zero"
    (fun () ->
      expect_panic ~saying:"a call of the C library with text that does not end with a zero"
        [
          build_entry (fun builder ->
              let name = make_view builder "/nonexistent/truss" in
              let wanted = make_flags builder [ O_rdonly ] in
              let descriptor =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              operate_checked builder
                ~destination:(Lowered.make_local_place descriptor)
                (Runtime (Libc Open))
                [
                  Place (Lowered.make_local_place name);
                  Value (Copy (Lowered.make_local_place wanted));
                  Value (Codegen_support.constant_int32 0);
                ];
              descriptor);
        ]);
  Codegen_support.test "a checked build passes a C library call whose arguments are large enough"
    (fun () ->
      Codegen_support.expect_status ~extra
        (Libc.evaluate_number Codegen_support.host Enoent)
        [
          build_entry (fun builder ->
              let name = make_view builder "/nonexistent/truss\000" in
              let wanted = make_flags builder [ O_rdonly ] in
              operate_checked builder (Runtime (Libc Open))
                [
                  Place (Lowered.make_local_place name);
                  Value (Copy (Lowered.make_local_place wanted));
                  Value (Codegen_support.constant_int32 0);
                ];
              let error =
                Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
              in
              operate_checked builder ~destination:(Lowered.make_local_place error)
                (Runtime (Libc Errno)) [];
              error);
        ]);
  Codegen_support.test
    "a checked build stops a float converted to an integer type that cannot hold it" (fun () ->
      let float64 = Codegen_support.named "Float64" in
      let extra = extra @ [ (Ground.to_string float64, Memory_layout.Scalar Float64) ] in
      let convert builder number =
        let result =
          Emit_c.Builder.allocate_local builder (Codegen_support.value Codegen_support.int32)
        in
        ignore
          (Backend.For_testing.Intrinsics.lower ~checks:true
             (Codegen_support.make_shape_env ~extra ())
             builder intrinsic_types (Scalar Convert)
             ~type_arguments:[ float64; Codegen_support.int32 ]
             [ Value (Constant (Float64 (Int64.bits_of_float number))) ]
             ~destination:(Some (Lowered.make_local_place result))
             ~site:{ definition = Codegen_support.definition "entry"; offset = 0 }
             ~trace:None);
        result
      in
      Codegen_support.expect_status ~extra 7 [ build_entry (fun builder -> convert builder 7.9) ];
      let status, _, errors =
        Codegen_support.run_program ~extra [ build_entry (fun builder -> convert builder 1.0e30) ]
      in
      if status <> 101 || not (String.includes ~affix:"conversion out of range" errors) then
        Codegen_support.fail "expected a panic about the conversion, got status %d (%s)" status
          errors)
