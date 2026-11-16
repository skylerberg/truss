module Intrinsics = Compile.For_testing.Intrinsics
module Builder = Emit_c.Builder

let view_ty = Codegen_support.named "View" ~arguments:[ Type Codegen_support.uint8 ]
let bytes_ty = Storage.make_storage_type Codegen_support.uint8

let extra =
  [
    ( Ground.to_string view_ty,
      Storage.make_view_shape ~uint64:Codegen_support.uint64 Codegen_support.uint8 );
  ]

let intrinsic_types : Intrinsics.types =
  { uint64 = Codegen_support.uint64; string_slice = Codegen_support.named "StringSlice" }

let operate builder ?destination ?(type_arguments = []) operation arguments =
  ignore
    (Intrinsics.lower
       (Codegen_support.shape_env ~extra ())
       builder intrinsic_types operation ~type_arguments arguments ~destination
       ~site:{ definition = Codegen_support.definition "entry"; offset = 0 })

let built_entry body : Codegen_support.instance =
 fun env ->
  let builder = Emit_c.Builder.create env ~key:(Codegen_support.key "entry") in
  Emit_c.Builder.start builder (Emit_c.Builder.block builder);
  let result = body builder in
  Emit_c.Builder.finish builder (Return (Some (Copy (Emit_c.Builder.at result))));
  Emit_c.Builder.build builder
    { parameters = []; result = Some (Codegen_support.value Codegen_support.int32); returns = true }

let view_of builder text =
  let view = Builder.local builder (Codegen_support.value view_ty) in
  Builder.emit builder
    (Assign
       ( Builder.at view,
         Storage.build_view view_ty ~elements:(Constant (Bytes text))
           ~length:(Builder.constant_uint64 (String.length text)) ));
  view

let flags builder numbers =
  let all = Builder.local builder (Codegen_support.value Codegen_support.int32) in
  Builder.emit builder (Assign (Builder.at all, Use (Codegen_support.constant_int32 0)));
  List.iter
    (fun number ->
      let one = Builder.local builder (Codegen_support.value Codegen_support.int32) in
      operate builder ~destination:(Builder.at one) (Libc_number number) [];
      Builder.emit builder
        (Assign (Builder.at all, Binary (Bit_or, Copy (Builder.at all), Copy (Builder.at one)))))
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

let compiles text =
  let directory = Lazy.force Codegen_support.scratch in
  let source = Filename.temp_file ~temp_dir:directory "libc" ".c" in
  Out_channel.with_open_text source (fun channel -> output_string channel text);
  Toolchain.compile
    (Lazy.force Codegen_support.compiler)
    ~optimization:O1
    ~extra:(Lazy.force Codegen_support.strict)
    ~source ~output:(source ^ ".o")

let linux : Libc.system = { os = Linux; architecture = X86_64 }

let () =
  Codegen_support.test
    "the C library's numbers, prototypes, and structures match this system's headers" (fun () ->
      match compiles (Libc.For_testing.check Codegen_support.host) with
      | Ok () -> ()
      | Error message -> Codegen_support.fail "the table disagrees with the headers:\n%s" message);
  Codegen_support.test "another system's numbers do not pass for this one's" (fun () ->
      let other : Libc.system =
        {
          Codegen_support.host with
          os = (match Codegen_support.host.os with Linux -> Macos | Macos -> Linux);
        }
      in
      match compiles (Libc.For_testing.check other) with
      | Ok () ->
          Codegen_support.fail "the check takes the table of %s on %s" (Libc.system_name other)
            (Libc.system_name Codegen_support.host)
      | Error _ -> ());
  Codegen_support.test
    "a function that only macOS has is held to its headers, and to no other system's" (fun () ->
      let checked system =
        Codegen_support.contains (Libc.For_testing.check system) "proc_pidpath"
      in
      if not (checked { os = Macos; architecture = Arm64 }) then
        Codegen_support.fail "the check for macOS leaves out proc_pidpath";
      if checked linux then Codegen_support.fail "the check for Linux looks for proc_pidpath");
  Codegen_support.test "a call of a function the system lacks stops the program, and calls nothing"
    (fun () ->
      let env = Memory_layout.create linux ~shape_of:(Codegen_support.shapes extra) in
      let builder = Builder.create env ~key:(Codegen_support.key "entry") in
      Builder.start builder (Builder.block builder);
      let length = Builder.local builder (Codegen_support.value Codegen_support.int32) in
      let path = Builder.local builder (Codegen_support.value bytes_ty) in
      ignore
        (Intrinsics.lower env builder intrinsic_types (Libc Proc_pidpath) ~type_arguments:[]
           [
             Value (Codegen_support.constant_int32 1);
             Place (Builder.at path);
             Value (Builder.constant_uint64 64);
           ]
           ~destination:(Some (Builder.at length))
           ~site:{ definition = Codegen_support.definition "entry"; offset = 0 });
      Builder.finish builder (Return (Some (Copy (Builder.at length))));
      let built =
        Builder.build builder
          {
            parameters = [];
            result = Some (Codegen_support.value Codegen_support.int32);
            returns = true;
          }
      in
      let c = Emit_c.For_testing.c (Emit_c.fragment env (Code built)) in
      if not (Codegen_support.contains c "t_runtime_panic(") then
        Codegen_support.fail "the call does not stop the program:\n%s" c;
      if Codegen_support.contains c "proc_pidpath(" then
        Codegen_support.fail "the function is called:\n%s" c);
  Codegen_support.test "a function that takes a structure is declared with no header" (fun () ->
      Codegen_support.expect_string
        ~expected:"struct timespec;\nint clock_gettime(int, struct timespec *);\n"
        (Libc.prototype (Libc.declaration linux Clock_gettime)));
  Codegen_support.test "a function with arguments C passes through ... is declared so" (fun () ->
      Codegen_support.expect_string ~expected:"int open(const char *, int, ...);\n"
        (Libc.prototype (Libc.declaration linux Open)));
  Codegen_support.test "a number whose name in C starts with an underscore is named without it"
    (fun () ->
      Codegen_support.expect_string ~expected:"libc_sc_nprocessors_onln"
        (Intrinsic.operation_name (Libc_number Sc_nprocessors_onln)));
  Codegen_support.test "storage a function fills is passed mut, and a view it reads is not"
    (fun () ->
      let modes operation =
        List.map
          (fun (parameter : Types.parameter_info) -> (parameter.name, parameter.mode))
          (Intrinsic_signatures.signature operation).parameters
      in
      if
        modes (Libc Read) <> [ ("descriptor", Types.Read); ("buffer", Mut); ("count", Read) ]
        || modes (Libc Write) <> [ ("descriptor", Types.Read); ("bytes", Read); ("count", Read) ]
      then Codegen_support.fail "read and write take their memory in the wrong modes");
  Codegen_support.test "a row's reads and writes are counted by a number the call is passed"
    (fun () ->
      List.iter
        (fun function_ ->
          let { Libc.parameters; at_most; _ } = Libc.signature function_ in
          let name = Libc.function_name function_ in
          let passed role parameter =
            match List.assoc_opt parameter parameters with
            | Some (Libc.Value UInt64) | Some (Written (UInt32, [ _ ])) -> ()
            | _ ->
                Codegen_support.fail "%s: %s is `%s`, which is no count the call is passed" name
                  role parameter
          in
          Option.iter (passed "the bound of the result") at_most;
          List.iter
            (fun (parameter, (passes : Libc.passes)) ->
              match passes with
              | Elements (_, extent) | Room (_, extent) | Elements_to_change (_, extent) -> (
                  match extent with
                  | Counted { by; each } ->
                      passed ("the count of `" ^ parameter ^ "`") by;
                      if each < 1 then
                        Codegen_support.fail "%s: `%s` has no elements for each one" name parameter
                  | Exactly count ->
                      if count < 1 then
                        Codegen_support.fail "%s: `%s` has no elements" name parameter
                  | Number number ->
                      if Libc.number_type number <> UInt64 then
                        Codegen_support.fail "%s: `%s` is counted by %s, which is no UInt64" name
                          parameter (Libc.number_name number)
                  | Through_zero -> ())
              | Value _ | Written _ | Always _ | Fixed _ -> ())
            parameters)
        Libc.functions;
      let { Libc.parameters; at_most; _ } = Libc.signature Read in
      if
        List.assoc "buffer" parameters <> Room (UInt8, Counted { by = "count"; each = 1 })
        || at_most <> Some "count"
      then Codegen_support.fail "read does not fill at most `count` bytes of room")

let () =
  Codegen_support.test "a program writes a view's bytes with write" (fun () ->
      let status, output, _ =
        Codegen_support.run_program ~extra
          [
            built_entry (fun builder ->
                let view = view_of builder "written\n" in
                let wrote = Builder.local builder (Codegen_support.value Codegen_support.int64) in
                operate builder ~destination:(Builder.at wrote) (Libc Write)
                  [
                    Value (Codegen_support.constant_int32 1);
                    Place (Builder.at view);
                    Value (Builder.constant_uint64 8);
                  ];
                let status = Builder.local builder (Codegen_support.value Codegen_support.int32) in
                Builder.emit builder
                  (Assign (Builder.at status, Convert (Copy (Builder.at wrote), Integer Int32)));
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
          (Intrinsic_signatures.signature (Libc Fcntl_dupfd_cloexec)).parameters
      in
      if names <> [ "descriptor"; "least" ] then
        Codegen_support.fail "fcntl_dupfd_cloexec takes %s" (String.concat ", " names);
      let status, output, _ =
        Codegen_support.run_program ~extra
          [
            built_entry (fun builder ->
                let copy = Builder.local builder (Codegen_support.value Codegen_support.int32) in
                operate builder ~destination:(Builder.at copy) (Libc Fcntl_dupfd_cloexec)
                  [
                    Value (Codegen_support.constant_int32 1);
                    Value (Codegen_support.constant_int32 10);
                  ];
                let view = view_of builder "through the copy\n" in
                let wrote = Builder.local builder (Codegen_support.value Codegen_support.int64) in
                operate builder ~destination:(Builder.at wrote) (Libc Write)
                  [
                    Value (Copy (Builder.at copy));
                    Place (Builder.at view);
                    Value (Builder.constant_uint64 17);
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
          built_entry (fun builder ->
              let name = view_of builder (path ^ "\000") in
              let wanted = flags builder [ O_wronly; O_creat; O_trunc ] in
              let descriptor =
                Builder.local builder (Codegen_support.value Codegen_support.int32)
              in
              operate builder ~destination:(Builder.at descriptor) (Libc Open)
                [
                  Place (Builder.at name);
                  Value (Copy (Builder.at wanted));
                  Value (Codegen_support.constant_int32 0o600);
                ];
              let closed = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              operate builder ~destination:(Builder.at closed) (Libc Close)
                [ Value (Copy (Builder.at descriptor)) ];
              closed);
        ];
      Codegen_support.expect_int ~expected:0o600 (Unix.stat path).st_perm);
  Codegen_support.test "errno is the number at the address the C library returns" (fun () ->
      Codegen_support.expect_status ~extra
        (Libc.value Codegen_support.host Enoent)
        [
          built_entry (fun builder ->
              let name = view_of builder "/nonexistent/truss\000" in
              let wanted = flags builder [ O_rdonly ] in
              operate builder (Libc Open)
                [
                  Place (Builder.at name);
                  Value (Copy (Builder.at wanted));
                  Value (Codegen_support.constant_int32 0);
                ];
              let error = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              operate builder ~destination:(Builder.at error) (Libc Errno) [];
              error);
        ]);
  Codegen_support.test "read fills the room storage has after its last element" (fun () ->
      let status, _, _ =
        Codegen_support.run_program ~extra ~input:"hello"
          [
            built_entry (fun builder ->
                let storage = Builder.local builder (Codegen_support.value bytes_ty) in
                operate builder ~destination:(Builder.at storage)
                  ~type_arguments:[ Codegen_support.uint8 ] Storage_with_capacity
                  [ Value (Builder.constant_uint64 16) ];
                operate builder ~type_arguments:[ Codegen_support.uint8 ] Storage_push
                  [ Place (Builder.at storage); Value (Constant (Integer (UInt8, Z.of_int 1))) ];
                let got = Builder.local builder (Codegen_support.value Codegen_support.int64) in
                operate builder ~destination:(Builder.at got) (Libc Read)
                  [
                    Value (Codegen_support.constant_int32 0);
                    Place (Builder.at storage);
                    Value (Builder.constant_uint64 15);
                  ];
                let first = Builder.local builder (Codegen_support.value Codegen_support.int32)
                and count = Builder.local builder (Codegen_support.value Codegen_support.int32) in
                Builder.emit builder
                  (Assign
                     ( Builder.at first,
                       Convert
                         ( Copy
                             (Storage.index_element (Builder.at storage) (Builder.constant_uint64 1)),
                           Integer Int32 ) ));
                Builder.emit builder
                  (Assign (Builder.at count, Convert (Copy (Builder.at got), Integer Int32)));
                Builder.emit builder
                  (Assign
                     ( Builder.at first,
                       Binary (Add, Copy (Builder.at first), Copy (Builder.at count)) ));
                free builder (Builder.at storage);
                first);
          ]
      in
      Codegen_support.expect_int ~expected:(Char.code 'h' + 5) status);
  Codegen_support.test
    "a structure the C library writes arrives in the arguments named for its numbers" (fun () ->
      Codegen_support.expect_status ~extra 1
        [
          built_entry (fun builder ->
              let seconds = Builder.local builder (Codegen_support.value Codegen_support.int64)
              and nanoseconds =
                Builder.local builder (Codegen_support.value Codegen_support.int64)
              in
              Builder.emit builder
                (Assign (Builder.at seconds, Use (Codegen_support.constant_int64 0)));
              Builder.emit builder
                (Assign (Builder.at nanoseconds, Use (Codegen_support.constant_int64 0)));
              let clock = flags builder [ Clock_realtime ] in
              let failed = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              operate builder ~destination:(Builder.at failed) (Libc Clock_gettime)
                [
                  Value (Copy (Builder.at clock));
                  Place (Builder.at seconds);
                  Place (Builder.at nanoseconds);
                ];
              let recent = Builder.local builder (Raw Bool)
              and whole = Builder.local builder (Raw Bool) in
              Builder.emit builder
                (Assign
                   ( Builder.at recent,
                     Binary
                       ( Greater,
                         Copy (Builder.at seconds),
                         Codegen_support.constant_int64 1_700_000_000 ) ));
              Builder.emit builder
                (Assign
                   ( Builder.at whole,
                     Binary
                       ( Less,
                         Copy (Builder.at nanoseconds),
                         Codegen_support.constant_int64 1_000_000_000 ) ));
              Builder.emit builder
                (Assign
                   ( Builder.at recent,
                     Binary (Bit_and, Copy (Builder.at recent), Copy (Builder.at whole)) ));
              let status = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              Builder.emit builder
                (Assign (Builder.at status, Convert (Copy (Builder.at recent), Integer Int32)));
              Builder.emit builder
                (Assign
                   ( Builder.at status,
                     Binary (Subtract, Copy (Builder.at status), Copy (Builder.at failed)) ));
              status);
        ]);
  Codegen_support.test "a number passed by address is read by the function and then written"
    (fun () ->
      let uint32 = Codegen_support.named "UInt32" in
      let extra = extra @ [ (Ground.to_string uint32, Memory_layout.Scalar (Integer UInt32)) ] in
      let operate builder ~destination operation arguments =
        ignore
          (Intrinsics.lower
             (Codegen_support.shape_env ~extra ())
             builder intrinsic_types operation ~type_arguments:[] arguments
             ~destination:(Some destination)
             ~site:{ definition = Codegen_support.definition "entry"; offset = 0 })
      in
      Codegen_support.expect_status ~extra 16
        [
          built_entry (fun builder ->
              let domain = flags builder [ Af_inet ] and kind = flags builder [ Sock_stream ] in
              let socket = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              operate builder ~destination:(Builder.at socket) (Libc Socket)
                [
                  Value (Copy (Builder.at domain));
                  Value (Copy (Builder.at kind));
                  Value (Codegen_support.constant_int32 0);
                ];
              let name = Builder.local builder (Codegen_support.value bytes_ty) in
              let operate_on_bytes ?destination operation arguments =
                ignore
                  (Intrinsics.lower
                     (Codegen_support.shape_env ~extra ())
                     builder intrinsic_types operation ~type_arguments:[ Codegen_support.uint8 ]
                     arguments ~destination
                     ~site:{ definition = Codegen_support.definition "entry"; offset = 0 })
              in
              operate_on_bytes ~destination:(Builder.at name) Storage_with_capacity
                [ Value (Builder.constant_uint64 28) ];
              operate_on_bytes Storage_lengthen
                [ Place (Builder.at name); Value (Builder.constant_uint64 28) ];
              let length = Builder.local builder (Codegen_support.value uint32) in
              Builder.emit builder
                (Assign (Builder.at length, Use (Constant (Integer (UInt32, Z.of_int 28)))));
              let failed = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              operate builder ~destination:(Builder.at failed) (Libc Getsockname)
                [
                  Value (Copy (Builder.at socket));
                  Place (Builder.at name);
                  Place (Builder.at length);
                ];
              let status = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              Builder.emit builder
                (Assign (Builder.at status, Convert (Copy (Builder.at length), Integer Int32)));
              Builder.emit builder
                (Assign
                   ( Builder.at status,
                     Binary (Subtract, Copy (Builder.at status), Copy (Builder.at failed)) ));
              free builder (Builder.at name);
              status);
        ]);
  Codegen_support.test "an argument a row fixes is no argument of the Truss call" (fun () ->
      Codegen_support.expect_status ~extra 1
        [
          built_entry (fun builder ->
              let draw () =
                let value = Builder.local builder (Codegen_support.value Codegen_support.uint64)
                and failed = Builder.local builder (Codegen_support.value Codegen_support.int32) in
                Builder.emit builder
                  (Assign (Builder.at value, Use (Constant (Integer (UInt64, Z.zero)))));
                operate builder ~destination:(Builder.at failed) (Libc Getentropy)
                  [ Place (Builder.at value) ];
                value
              in
              let first = draw () in
              let second = draw () in
              let differ = Builder.local builder (Raw Bool)
              and status = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              Builder.emit builder
                (Assign
                   ( Builder.at differ,
                     Binary (Not_equal, Copy (Builder.at first), Copy (Builder.at second)) ));
              Builder.emit builder
                (Assign (Builder.at status, Convert (Copy (Builder.at differ), Integer Int32)));
              status);
        ])

let () =
  Codegen_support.test "nothing after a call of a function that does not return is run" (fun () ->
      Codegen_support.expect_status ~extra 7
        [
          built_entry (fun builder ->
              operate builder (Libc Exit) [ Value (Codegen_support.constant_int32 7) ];
              let status = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              Builder.emit builder
                (Assign (Builder.at status, Use (Codegen_support.constant_int32 0)));
              status);
        ]);
  Codegen_support.test
    "a pipe's two ends arrive in the arguments named for them, and poll finds the written data"
    (fun () ->
      let waited_ty = Storage.make_storage_type Codegen_support.int32 in
      Codegen_support.expect_status ~extra 1
        [
          built_entry (fun builder ->
              let read_end = Builder.local builder (Codegen_support.value Codegen_support.int32)
              and write_end = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              Builder.emit builder
                (Assign (Builder.at read_end, Use (Codegen_support.constant_int32 (-1))));
              Builder.emit builder
                (Assign (Builder.at write_end, Use (Codegen_support.constant_int32 (-1))));
              operate builder (Libc Pipe)
                [ Place (Builder.at read_end); Place (Builder.at write_end) ];
              let view = view_of builder "x" in
              operate builder (Libc Write)
                [
                  Value (Copy (Builder.at write_end));
                  Place (Builder.at view);
                  Value (Builder.constant_uint64 1);
                ];
              let waited = Builder.local builder (Codegen_support.value waited_ty) in
              operate builder ~destination:(Builder.at waited)
                ~type_arguments:[ Codegen_support.int32 ] Storage_with_capacity
                [ Value (Builder.constant_uint64 2) ];
              operate builder ~type_arguments:[ Codegen_support.int32 ] Storage_push
                [ Place (Builder.at waited); Value (Copy (Builder.at read_end)) ];
              let reading = flags builder [ Pollin ] in
              operate builder ~type_arguments:[ Codegen_support.int32 ] Storage_push
                [ Place (Builder.at waited); Value (Copy (Builder.at reading)) ];
              let ready = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              operate builder ~destination:(Builder.at ready) (Libc Poll)
                [
                  Place (Builder.at waited);
                  Value (Builder.constant_uint64 1);
                  Value (Codegen_support.constant_int32 1000);
                ];
              let actual = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              Builder.emit builder
                (Assign
                   ( Builder.at actual,
                     Binary
                       ( Shift_right,
                         Copy
                           (Storage.index_element (Builder.at waited) (Builder.constant_uint64 1)),
                         Codegen_support.constant_int32 16 ) ));
              Builder.emit builder
                (Assign
                   ( Builder.at actual,
                     Binary (Bit_and, Copy (Builder.at actual), Copy (Builder.at reading)) ));
              Builder.emit builder
                (Assign
                   ( Builder.at ready,
                     Binary (Multiply, Copy (Builder.at ready), Copy (Builder.at actual)) ));
              free builder (Builder.at waited);
              ready);
        ])

let () =
  Codegen_support.test "dropping a handle closes its descriptor" (fun () ->
      let path = Filename.concat (Lazy.force Codegen_support.scratch) "held" in
      Out_channel.with_open_text path (fun channel -> output_string channel "held");
      let env =
        Memory_layout.create Codegen_support.host
          ~shape_of:(Monomorphic.shape Codegen_support.standard_context)
      in
      let drop_and_copy = Compile.For_testing.drop_and_copy env in
      let int32 = Ground.builtin Int32 in
      let view_ty = Storage.make_view_type (Ground.builtin UInt8) in
      let handle_ty = Ground.builtin Handle in
      let types : Intrinsics.types =
        {
          uint64 = Ground.builtin UInt64;
          string_slice = Codegen_support.standard "text" "StringSlice" ();
        }
      in
      let entry =
        let builder = Emit_c.Builder.create env ~key:(Codegen_support.key "entry") in
        Builder.start builder (Builder.block builder);
        let name = Builder.local builder (Codegen_support.value view_ty) in
        let text = path ^ "\000" in
        Builder.emit builder
          (Assign
             ( Builder.at name,
               Storage.build_view view_ty ~elements:(Constant (Bytes text))
                 ~length:(Builder.constant_uint64 (String.length text)) ));
        let opened () =
          let descriptor = Builder.local builder (Codegen_support.value int32) in
          ignore
            (Intrinsics.lower env builder types (Libc Open) ~type_arguments:[]
               [
                 Place (Builder.at name);
                 Value (Codegen_support.constant_int32 (Libc.value Codegen_support.host O_rdonly));
                 Value (Codegen_support.constant_int32 0);
               ]
               ~destination:(Some (Builder.at descriptor))
               ~site:{ definition = Codegen_support.definition "entry"; offset = 0 });
          descriptor
        in
        let first = opened () in
        let handle = Builder.local builder (Codegen_support.value handle_ty) in
        Builder.emit builder
          (Assign
             ( Builder.at handle,
               Build
                 {
                   ty = handle_ty;
                   variant = None;
                   fields = [ ("descriptor", Copy (Builder.at first)) ];
                 } ));
        Builder.emit builder (Drop (Builder.at handle));
        let second = opened () in
        let same = Builder.local builder (Raw Bool)
        and status = Builder.local builder (Codegen_support.value int32) in
        Builder.emit builder
          (Assign
             (Builder.at same, Binary (Equal, Copy (Builder.at first), Copy (Builder.at second))));
        Builder.emit builder
          (Assign (Builder.at status, Convert (Copy (Builder.at same), Integer Int32)));
        Builder.finish builder (Return (Some (Copy (Builder.at status))));
        Builder.build builder
          { parameters = []; result = Some (Codegen_support.value int32); returns = true }
      in
      let status, _, errors =
        Codegen_support.run_program ~env
          [
            Codegen_support.printed entry;
            Codegen_support.printed (Compile.For_testing.drop drop_and_copy handle_ty);
          ]
      in
      if status <> 1 then
        Codegen_support.fail "the descriptor was not free again (status %d, %s)" status errors)

let checked builder ?destination ?(type_arguments = []) operation arguments =
  ignore
    (Intrinsics.lower ~checks:true
       (Codegen_support.shape_env ~extra ())
       builder intrinsic_types operation ~type_arguments arguments ~destination
       ~site:{ definition = Codegen_support.definition "entry"; offset = 0 })

let expect_panic ~saying instances =
  let status, _, errors = Codegen_support.run_program ~extra instances in
  if status <> 101 then Codegen_support.fail "expected a panic, got status %d (%s)" status errors;
  if not (Codegen_support.contains errors saying) then
    Codegen_support.fail "expected %S in %S" saying errors

let () =
  Codegen_support.test
    "a checked build stops a C library call that is given less room than it writes" (fun () ->
      expect_panic ~saying:"a call of the C library with less room than it writes"
        [
          built_entry (fun builder ->
              let storage = Builder.local builder (Codegen_support.value bytes_ty) in
              checked builder ~destination:(Builder.at storage)
                ~type_arguments:[ Codegen_support.uint8 ] Storage_with_capacity
                [ Value (Builder.constant_uint64 4) ];
              let got = Builder.local builder (Codegen_support.value Codegen_support.int64) in
              checked builder ~destination:(Builder.at got) (Libc Read)
                [
                  Value (Codegen_support.constant_int32 0);
                  Place (Builder.at storage);
                  Value (Builder.constant_uint64 100);
                ];
              let status = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              Builder.emit builder
                (Assign (Builder.at status, Use (Codegen_support.constant_int32 0)));
              status);
        ]);
  Codegen_support.test
    "a checked build stops a C library call that is given fewer elements than it reads" (fun () ->
      expect_panic ~saying:"a call of the C library with fewer elements than it reads"
        [
          built_entry (fun builder ->
              let view = view_of builder "short" in
              let wrote = Builder.local builder (Codegen_support.value Codegen_support.int64) in
              checked builder ~destination:(Builder.at wrote) (Libc Write)
                [
                  Value (Codegen_support.constant_int32 1);
                  Place (Builder.at view);
                  Value (Builder.constant_uint64 100);
                ];
              let status = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              Builder.emit builder
                (Assign (Builder.at status, Use (Codegen_support.constant_int32 0)));
              status);
        ]);
  Codegen_support.test "a checked build stops a C library call whose text does not end with a zero"
    (fun () ->
      expect_panic ~saying:"a call of the C library with text that does not end with a zero"
        [
          built_entry (fun builder ->
              let name = view_of builder "/nonexistent/truss" in
              let wanted = flags builder [ O_rdonly ] in
              let descriptor =
                Builder.local builder (Codegen_support.value Codegen_support.int32)
              in
              checked builder ~destination:(Builder.at descriptor) (Libc Open)
                [
                  Place (Builder.at name);
                  Value (Copy (Builder.at wanted));
                  Value (Codegen_support.constant_int32 0);
                ];
              descriptor);
        ]);
  Codegen_support.test "a checked build passes a C library call whose arguments are large enough"
    (fun () ->
      Codegen_support.expect_status ~extra
        (Libc.value Codegen_support.host Enoent)
        [
          built_entry (fun builder ->
              let name = view_of builder "/nonexistent/truss\000" in
              let wanted = flags builder [ O_rdonly ] in
              checked builder (Libc Open)
                [
                  Place (Builder.at name);
                  Value (Copy (Builder.at wanted));
                  Value (Codegen_support.constant_int32 0);
                ];
              let error = Builder.local builder (Codegen_support.value Codegen_support.int32) in
              checked builder ~destination:(Builder.at error) (Libc Errno) [];
              error);
        ]);
  Codegen_support.test
    "a checked build stops a float converted to an integer type that cannot hold it" (fun () ->
      let float64 = Codegen_support.named "Float64" in
      let extra = extra @ [ (Ground.to_string float64, Memory_layout.Scalar Float64) ] in
      let convert builder number =
        let result = Builder.local builder (Codegen_support.value Codegen_support.int32) in
        ignore
          (Intrinsics.lower ~checks:true
             (Codegen_support.shape_env ~extra ())
             builder intrinsic_types Convert
             ~type_arguments:[ float64; Codegen_support.int32 ]
             [ Value (Constant (Float64 (Int64.bits_of_float number))) ]
             ~destination:(Some (Builder.at result))
             ~site:{ definition = Codegen_support.definition "entry"; offset = 0 });
        result
      in
      Codegen_support.expect_status ~extra 7 [ built_entry (fun builder -> convert builder 7.9) ];
      let status, _, errors =
        Codegen_support.run_program ~extra [ built_entry (fun builder -> convert builder 1.0e30) ]
      in
      if status <> 101 || not (Codegen_support.contains errors "conversion out of range") then
        Codegen_support.fail "expected a panic about the conversion, got status %d (%s)" status
          errors)
