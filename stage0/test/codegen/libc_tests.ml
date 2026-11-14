module Intrinsics = Compile.For_testing.Intrinsics

(* Calling the C library: its table against the system's headers, and
   programs that call its functions. *)

open Codegen_support

let view_ty = named "View" ~arguments:[ Type uint8 ]
let bytes_ty = Storage.of_elements uint8
let isize = named "ISize"

let extra =
  [
    (Ground.to_string view_ty, Storage.view_shape ~usize uint8);
    (Ground.to_string isize, Memory_layout.Scalar (Integer ISize));
  ]

let intrinsic_types : Intrinsics.types = { usize; string_slice = named "StringSlice" }

let operate builder ?destination ?(type_arguments = []) operation arguments =
  ignore
    (Intrinsics.lower (shape_env ~extra ()) builder intrinsic_types operation ~type_arguments
       arguments ~destination
       ~site:{ definition = definition "entry"; line = 0; column = 1 })

(* An [entry] built with the builder: [body] writes its statements and
   returns the local to exit with. *)
let built_entry body =
  let builder = Lir_builder.create () in
  Lir_builder.start builder (Lir_builder.block builder);
  let result = body builder in
  Lir_builder.finish builder (Return (Some (Copy (Lir_builder.at result))));
  instance "entry" (Lir_builder.build builder ~parameters:[] ~result:(Some (value int32)))

let view_of builder text =
  let open Lir_builder in
  let view = local builder (value view_ty) in
  emit builder
    (Assign
       ( at view,
         Storage.view view_ty ~elements:(Constant (Bytes text)) ~length:(usize (String.length text))
       ));
  view

(* The C library's numbers, joined with [or]. *)
let flags builder numbers =
  let open Lir_builder in
  let all = local builder (value int32) in
  emit builder (Assign (at all, Use (constant_int32 0)));
  List.iter
    (fun number ->
      let one = local builder (value int32) in
      operate builder ~destination:(at one) (Libc_number number) [];
      emit builder (Assign (at all, Binary (Bit_or, Copy (at all), Copy (at one)))))
    numbers;
  all

let free builder storage =
  Lir_builder.emit builder
    (Call
       {
         target = Intrinsic Free;
         arguments = [ Copy (Storage.buffer storage) ];
         result = Discarded;
       })

let compiles text =
  let directory = Lazy.force scratch in
  let source = Filename.temp_file ~temp_dir:directory "libc" ".c" in
  Out_channel.with_open_text source (fun channel -> output_string channel text);
  Toolchain.compile (Lazy.force compiler) ~optimization:O1 ~extra:strict ~source
    ~output:(source ^ ".o") ()

let linux : Libc.system = { os = Linux; architecture = X86_64 }

let () =
  test "the C library's numbers, prototypes, and structures match this system's headers" (fun () ->
      match compiles (Libc.For_testing.check host) with
      | Ok () -> ()
      | Error message -> fail "the table disagrees with the headers:\n%s" message);
  test "another system's numbers do not pass for this one's" (fun () ->
      let other : Libc.system =
        { host with os = (match host.os with Linux -> Macos | Macos -> Linux) }
      in
      match compiles (Libc.For_testing.check other) with
      | Ok () ->
          fail "the check takes the table of %s on %s" (Libc.system_name other)
            (Libc.system_name host)
      | Error _ -> ());
  test "a function that only macOS has is held to its headers, and to no other system's" (fun () ->
      let checked system = contains (Libc.For_testing.check system) "proc_pidpath" in
      if not (checked { os = Macos; architecture = Arm64 }) then
        fail "the check for macOS leaves out proc_pidpath";
      if checked linux then fail "the check for Linux looks for proc_pidpath");
  test "a call of a function the system lacks stops the program, and calls nothing" (fun () ->
      let open Lir_builder in
      let builder = create () in
      start builder (block builder);
      let length = local builder (value int32) in
      let path = local builder (value bytes_ty) in
      ignore
        (Intrinsics.lower
           (Memory_layout.create (Memory_layout.target_64 linux) ~shape_of:(shapes extra))
           builder intrinsic_types (Libc Proc_pidpath) ~type_arguments:[]
           [ Value (constant_int32 1); Place (at path); Value (usize 64) ]
           ~destination:(Some (at length))
           ~site:{ definition = definition "entry"; line = 0; column = 1 });
      finish builder (Return (Some (Copy (at length))));
      let lowered = build builder ~parameters:[] ~result:(Some (value int32)) in
      let blocks = Array.to_list lowered.blocks in
      if
        not
          (List.exists
             (fun (block : Lir.basic_block) ->
               match block.terminator with Fail _ -> true | _ -> false)
             blocks)
      then fail "the call does not stop the program";
      if
        List.exists
          (fun (block : Lir.basic_block) ->
            List.exists
              (function Lir.Call { target = Foreign _; _ } -> true | _ -> false)
              block.statements)
          blocks
      then fail "the function is called");
  test "a function that takes a structure is declared with no header" (fun () ->
      expect_string ~expected:"struct timespec;\nint clock_gettime(int, struct timespec *);\n"
        (Libc.prototype (Libc.declaration linux Clock_gettime)));
  test "a function with arguments C passes through ... is declared so" (fun () ->
      expect_string ~expected:"int open(const char *, int, ...);\n"
        (Libc.prototype (Libc.declaration linux Open)));
  test "a number whose name in C starts with an underscore is named without it" (fun () ->
      expect_string ~expected:"libc_sc_nprocessors_onln"
        (Intrinsic.operation_name (Libc_number Sc_nprocessors_onln)));
  test "storage a function fills is passed mut, and a view it reads is not" (fun () ->
      let modes operation =
        List.map
          (fun (parameter : Types.parameter_info) -> (parameter.name, parameter.mode))
          (Intrinsic_signatures.signature operation).parameters
      in
      if
        modes (Libc Read) <> [ ("descriptor", Types.Read); ("buffer", Mut); ("count", Read) ]
        || modes (Libc Write) <> [ ("descriptor", Types.Read); ("bytes", Read); ("count", Read) ]
      then fail "read and write take their memory in the wrong modes");
  test "a row's reads and writes are counted by a number the call is passed" (fun () ->
      List.iter
        (fun function_ ->
          let { Libc.parameters; at_most; _ } = Libc.signature function_ in
          let name = Libc.function_name function_ in
          let passed role parameter =
            match List.assoc_opt parameter parameters with
            | Some (Libc.Value USize) | Some (Written (UInt32, [ _ ])) -> ()
            | _ -> fail "%s: %s is `%s`, which is no count the call is passed" name role parameter
          in
          Option.iter (passed "the bound of the result") at_most;
          List.iter
            (fun (parameter, (passes : Libc.passes)) ->
              match passes with
              | Elements (_, extent) | Room (_, extent) | Elements_to_change (_, extent) -> (
                  match extent with
                  | Counted { by; each } ->
                      passed ("the count of `" ^ parameter ^ "`") by;
                      if each < 1 then fail "%s: `%s` has no elements for each one" name parameter
                  | Exactly count ->
                      if count < 1 then fail "%s: `%s` has no elements" name parameter
                  | Number number ->
                      if Libc.number_type number <> USize then
                        fail "%s: `%s` is counted by %s, which is no USize" name parameter
                          (Libc.number_name number)
                  | Through_zero -> ())
              | Value _ | Written _ | Always _ | Fixed _ -> ())
            parameters)
        Libc.functions;
      let { Libc.parameters; at_most; _ } = Libc.signature Read in
      if
        List.assoc "buffer" parameters <> Room (UInt8, Counted { by = "count"; each = 1 })
        || at_most <> Some "count"
      then fail "read does not fill at most `count` bytes of room")

let () =
  test "a program writes a view's bytes with write" (fun () ->
      let open Lir_builder in
      let status, output, _ =
        run_program ~extra
          [
            built_entry (fun builder ->
                let view = view_of builder "written\n" in
                let wrote = local builder (value isize) in
                operate builder ~destination:(at wrote) (Libc Write)
                  [ Value (constant_int32 1); Place (at view); Value (usize 8) ];
                let status = local builder (value int32) in
                emit builder (Assign (at status, Convert (Copy (at wrote), Integer Int32)));
                status);
          ]
      in
      expect_int ~expected:8 status;
      expect_string ~expected:"written\n" output);
  test "a request that a row fixes is passed, and is no argument of the Truss call" (fun () ->
      let open Lir_builder in
      let names =
        List.map
          (fun (parameter : Types.parameter_info) -> parameter.name)
          (Intrinsic_signatures.signature (Libc Fcntl_dupfd_cloexec)).parameters
      in
      if names <> [ "descriptor"; "least" ] then
        fail "fcntl_dupfd_cloexec takes %s" (String.concat ", " names);
      let status, output, _ =
        run_program ~extra
          [
            built_entry (fun builder ->
                let copy = local builder (value int32) in
                operate builder ~destination:(at copy) (Libc Fcntl_dupfd_cloexec)
                  [ Value (constant_int32 1); Value (constant_int32 10) ];
                let view = view_of builder "through the copy\n" in
                let wrote = local builder (value isize) in
                operate builder ~destination:(at wrote) (Libc Write)
                  [ Value (Copy (at copy)); Place (at view); Value (usize 17) ];
                copy);
          ]
      in
      if status < 10 then
        fail "the new descriptor is %d, which is less than the least asked for" status;
      expect_string ~expected:"through the copy\n" output);
  test "open is given its mode as C passes an argument through ..." (fun () ->
      let open Lir_builder in
      let path = Filename.concat (Lazy.force scratch) "opened" in
      expect_status ~extra 0
        [
          built_entry (fun builder ->
              let name = view_of builder (path ^ "\000") in
              let wanted = flags builder [ O_wronly; O_creat; O_trunc ] in
              let descriptor = local builder (value int32) in
              operate builder ~destination:(at descriptor) (Libc Open)
                [ Place (at name); Value (Copy (at wanted)); Value (constant_int32 0o600) ];
              let closed = local builder (value int32) in
              operate builder ~destination:(at closed) (Libc Close) [ Value (Copy (at descriptor)) ];
              closed);
        ];
      expect_int ~expected:0o600 (Unix.stat path).st_perm);
  test "errno is the number at the address the C library returns" (fun () ->
      let open Lir_builder in
      expect_status ~extra (Libc.value host Enoent)
        [
          built_entry (fun builder ->
              let name = view_of builder "/nonexistent/truss\000" in
              let wanted = flags builder [ O_rdonly ] in
              operate builder (Libc Open)
                [ Place (at name); Value (Copy (at wanted)); Value (constant_int32 0) ];
              let error = local builder (value int32) in
              operate builder ~destination:(at error) (Libc Errno) [];
              error);
        ]);
  test "read fills the room storage has after its last element" (fun () ->
      let open Lir_builder in
      let status, _, _ =
        run_program ~extra ~input:"hello"
          [
            built_entry (fun builder ->
                let storage = local builder (value bytes_ty) in
                operate builder ~destination:(at storage) ~type_arguments:[ uint8 ]
                  Storage_with_capacity
                  [ Value (usize 16) ];
                operate builder ~type_arguments:[ uint8 ] Storage_push
                  [ Place (at storage); Value (Constant (Integer (UInt8, Z.of_int 1))) ];
                let got = local builder (value isize) in
                operate builder ~destination:(at got) (Libc Read)
                  [ Value (constant_int32 0); Place (at storage); Value (usize 15) ];
                (* The first byte read comes after the one the storage had. *)
                let first = local builder (value int32) and count = local builder (value int32) in
                emit builder
                  (Assign
                     (at first, Convert (Copy (Storage.at (at storage) (usize 1)), Integer Int32)));
                emit builder (Assign (at count, Convert (Copy (at got), Integer Int32)));
                emit builder (Assign (at first, Binary (Add, Copy (at first), Copy (at count))));
                free builder (at storage);
                first);
          ]
      in
      expect_int ~expected:(Char.code 'h' + 5) status);
  test "a structure the C library writes arrives in the arguments named for its numbers" (fun () ->
      let open Lir_builder in
      expect_status ~extra 1
        [
          built_entry (fun builder ->
              let seconds = local builder (value int64)
              and nanoseconds = local builder (value int64) in
              let clock = flags builder [ Clock_realtime ] in
              let failed = local builder (value int32) in
              operate builder ~destination:(at failed) (Libc Clock_gettime)
                [ Value (Copy (at clock)); Place (at seconds); Place (at nanoseconds) ];
              (* Later than 2023, and less than a second of nanoseconds. *)
              let recent = local builder (Raw Bool) and whole = local builder (Raw Bool) in
              emit builder
                (Assign
                   (at recent, Binary (Greater, Copy (at seconds), constant_int64 1_700_000_000)));
              emit builder
                (Assign
                   (at whole, Binary (Less, Copy (at nanoseconds), constant_int64 1_000_000_000)));
              emit builder (Assign (at recent, Binary (Bit_and, Copy (at recent), Copy (at whole))));
              let status = local builder (value int32) in
              emit builder (Assign (at status, Convert (Copy (at recent), Integer Int32)));
              emit builder
                (Assign (at status, Binary (Subtract, Copy (at status), Copy (at failed))));
              status);
        ]);
  test "a number passed by address is read by the function and then written" (fun () ->
      let open Lir_builder in
      let uint32 = named "UInt32" in
      let extra = extra @ [ (Ground.to_string uint32, Memory_layout.Scalar (Integer UInt32)) ] in
      let operate builder ?destination operation arguments =
        ignore
          (Intrinsics.lower (shape_env ~extra ()) builder intrinsic_types operation
             ~type_arguments:[] arguments ~destination
             ~site:{ definition = definition "entry"; line = 0; column = 1 })
      in
      (* A new socket's name is 16 bytes. The system is told there is room
         for 28, which it could not know from a number it only writes. *)
      expect_status ~extra 16
        [
          built_entry (fun builder ->
              let domain = flags builder [ Af_inet ] and kind = flags builder [ Sock_stream ] in
              let socket = local builder (value int32) in
              operate builder ~destination:(at socket) (Libc Socket)
                [ Value (Copy (at domain)); Value (Copy (at kind)); Value (constant_int32 0) ];
              let name = local builder (value bytes_ty) in
              emit builder
                (Assign
                   ( at name,
                     Build
                       {
                         ty = bytes_ty;
                         variant = None;
                         fields =
                           [
                             ("buffer", Constant (Bytes (String.make 28 '\000')));
                             ("length", usize 28);
                             ("capacity", usize 0);
                           ];
                       } ));
              let length = local builder (value uint32) in
              emit builder (Assign (at length, Use (Constant (Integer (UInt32, Z.of_int 28)))));
              let failed = local builder (value int32) in
              operate builder ~destination:(at failed) (Libc Getsockname)
                [ Value (Copy (at socket)); Place (at name); Place (at length) ];
              let status = local builder (value int32) in
              emit builder (Assign (at status, Convert (Copy (at length), Integer Int32)));
              emit builder
                (Assign (at status, Binary (Subtract, Copy (at status), Copy (at failed))));
              free builder (at name);
              status);
        ]);
  test "an argument a row fixes is no argument of the Truss call" (fun () ->
      let open Lir_builder in
      let uint64 = named "UInt64" in
      expect_status ~extra 1
        [
          built_entry (fun builder ->
              (* Two draws of eight random bytes differ. *)
              let draw () =
                let value = local builder (value uint64) and failed = local builder (value int32) in
                operate builder ~destination:(at failed) (Libc Getentropy) [ Place (at value) ];
                value
              in
              let first = draw () in
              let second = draw () in
              let differ = local builder (Raw Bool) and status = local builder (value int32) in
              emit builder
                (Assign (at differ, Binary (Not_equal, Copy (at first), Copy (at second))));
              emit builder (Assign (at status, Convert (Copy (at differ), Integer Int32)));
              status);
        ])

let () =
  test "nothing after a call of a function that does not return is run" (fun () ->
      let open Lir_builder in
      expect_status ~extra 7
        [
          built_entry (fun builder ->
              operate builder (Libc Exit) [ Value (constant_int32 7) ];
              let status = local builder (value int32) in
              emit builder (Assign (at status, Use (constant_int32 0)));
              status);
        ]);
  test "a pipe's two ends arrive in the arguments named for them, and poll finds the written data"
    (fun () ->
      let open Lir_builder in
      let waited_ty = Storage.of_elements int32 in
      expect_status ~extra 1
        [
          built_entry (fun builder ->
              let read_end = local builder (value int32)
              and write_end = local builder (value int32) in
              operate builder (Libc Pipe) [ Place (at read_end); Place (at write_end) ];
              let view = view_of builder "x" in
              operate builder (Libc Write)
                [ Value (Copy (at write_end)); Place (at view); Value (usize 1) ];
              let waited = local builder (value waited_ty) in
              operate builder ~destination:(at waited) ~type_arguments:[ int32 ]
                Storage_with_capacity
                [ Value (usize 2) ];
              operate builder ~type_arguments:[ int32 ] Storage_push
                [ Place (at waited); Value (Copy (at read_end)) ];
              let reading = flags builder [ Pollin ] in
              operate builder ~type_arguments:[ int32 ] Storage_push
                [ Place (at waited); Value (Copy (at reading)) ];
              let ready = local builder (value int32) in
              operate builder ~destination:(at ready) (Libc Poll)
                [ Place (at waited); Value (usize 1); Value (constant_int32 1000) ];
              (* The returned events are the high half of the second number. *)
              let actual = local builder (value int32) in
              emit builder
                (Assign
                   ( at actual,
                     Binary (Shift_right, Copy (Storage.at (at waited) (usize 1)), constant_int32 16)
                   ));
              emit builder
                (Assign (at actual, Binary (Bit_and, Copy (at actual), Copy (at reading))));
              emit builder (Assign (at ready, Binary (Multiply, Copy (at ready), Copy (at actual))));
              free builder (at waited);
              ready);
        ])

(* With the standard library's own types, whose drop code generation makes. *)
let () =
  test "dropping a handle closes its descriptor" (fun () ->
      let open Lir_builder in
      let path = Filename.concat (Lazy.force scratch) "held" in
      Out_channel.with_open_text path (fun channel -> output_string channel "held");
      let env = Memory_layout.create target_64 ~shape_of:(Monomorphic.shape standard_context) in
      let glue =
        Glue.create env
          ~representation:(Monomorphic.representation standard_context)
          ~usize:(Monomorphic.builtin USize) ()
      in
      let int32 = Monomorphic.builtin Int32 in
      let view_ty = Storage.view_of_elements (Monomorphic.builtin UInt8) in
      let handle_ty = Monomorphic.builtin Handle in
      let types : Intrinsics.types =
        { usize = Monomorphic.builtin USize; string_slice = standard "text" "StringSlice" () }
      in
      let entry =
        let builder = Lir_builder.create () in
        start builder (block builder);
        let name = local builder (value view_ty) in
        let text = path ^ "\000" in
        emit builder
          (Assign
             ( at name,
               Storage.view view_ty ~elements:(Constant (Bytes text))
                 ~length:(usize (String.length text)) ));
        (* [open] gives the lowest descriptor that is free, so the second
           gets the first's exactly when the first was closed. *)
        let opened () =
          let descriptor = local builder (value int32) in
          ignore
            (Intrinsics.lower env builder types (Libc Open) ~type_arguments:[]
               [
                 Place (at name);
                 Value (constant_int32 (Libc.value host O_rdonly));
                 Value (constant_int32 0);
               ]
               ~destination:(Some (at descriptor))
               ~site:{ definition = definition "entry"; line = 0; column = 1 });
          descriptor
        in
        let first = opened () in
        let handle = local builder (value handle_ty) in
        emit builder
          (Assign
             ( at handle,
               Build
                 { ty = handle_ty; variant = None; fields = [ ("descriptor", Copy (at first)) ] } ));
        emit builder (Drop (at handle));
        let second = opened () in
        let same = local builder (Raw Bool) and status = local builder (value int32) in
        emit builder (Assign (at same, Binary (Equal, Copy (at first), Copy (at second))));
        emit builder (Assign (at status, Convert (Copy (at same), Integer Int32)));
        finish builder (Return (Some (Copy (at status))));
        instance "entry" (build builder ~parameters:[] ~result:(Some (value int32)))
      in
      let status, _, errors = run_program ~env [ entry; Glue.drop glue handle_ty ] in
      if status <> 1 then fail "the descriptor was not free again (status %d, %s)" status errors)

(* The checks of a build that does not wait for proofs *)

let checked builder ?destination ?(type_arguments = []) operation arguments =
  ignore
    (Intrinsics.lower ~checks:true (shape_env ~extra ()) builder intrinsic_types operation
       ~type_arguments arguments ~destination
       ~site:{ definition = definition "entry"; line = 0; column = 1 })

(* The position that a panic in [entry] reports. *)
let anchors = [ { Positions.definition = definition "entry"; path = "test.truss"; first_line = 1 } ]

let expect_panic ~saying instances =
  let status, _, errors = run_program ~extra ~anchors instances in
  if status <> 101 then fail "expected a panic, got status %d (%s)" status errors;
  if not (contains errors saying) then fail "expected %S in %S" saying errors

let () =
  test "a checked build stops a C library call that is given less room than it writes" (fun () ->
      let open Lir_builder in
      expect_panic ~saying:"a call of the C library with less room than it writes"
        [
          built_entry (fun builder ->
              let storage = local builder (value bytes_ty) in
              checked builder ~destination:(at storage) ~type_arguments:[ uint8 ]
                Storage_with_capacity
                [ Value (usize 4) ];
              let got = local builder (value isize) in
              checked builder ~destination:(at got) (Libc Read)
                [ Value (constant_int32 0); Place (at storage); Value (usize 100) ];
              let status = local builder (value int32) in
              emit builder (Assign (at status, Use (constant_int32 0)));
              status);
        ]);
  test "a checked build stops a C library call that is given fewer elements than it reads"
    (fun () ->
      let open Lir_builder in
      expect_panic ~saying:"a call of the C library with fewer elements than it reads"
        [
          built_entry (fun builder ->
              let view = view_of builder "short" in
              let wrote = local builder (value isize) in
              checked builder ~destination:(at wrote) (Libc Write)
                [ Value (constant_int32 1); Place (at view); Value (usize 100) ];
              let status = local builder (value int32) in
              emit builder (Assign (at status, Use (constant_int32 0)));
              status);
        ]);
  test "a checked build stops a C library call whose text does not end with a zero" (fun () ->
      let open Lir_builder in
      expect_panic ~saying:"a call of the C library with text that does not end with a zero"
        [
          built_entry (fun builder ->
              let name = view_of builder "/nonexistent/truss" in
              let wanted = flags builder [ O_rdonly ] in
              let descriptor = local builder (value int32) in
              checked builder ~destination:(at descriptor) (Libc Open)
                [ Place (at name); Value (Copy (at wanted)); Value (constant_int32 0) ];
              descriptor);
        ]);
  test "a checked build passes a C library call whose arguments are large enough" (fun () ->
      let open Lir_builder in
      expect_status ~extra ~anchors (Libc.value host Enoent)
        [
          built_entry (fun builder ->
              let name = view_of builder "/nonexistent/truss\000" in
              let wanted = flags builder [ O_rdonly ] in
              checked builder (Libc Open)
                [ Place (at name); Value (Copy (at wanted)); Value (constant_int32 0) ];
              let error = local builder (value int32) in
              checked builder ~destination:(at error) (Libc Errno) [];
              error);
        ]);
  test "a checked build stops a float converted to an integer type that cannot hold it" (fun () ->
      let open Lir_builder in
      let float64 = named "Float64" in
      let extra = extra @ [ (Ground.to_string float64, Memory_layout.Scalar Float64) ] in
      let convert builder number =
        let result = local builder (value int32) in
        ignore
          (Intrinsics.lower ~checks:true (shape_env ~extra ()) builder intrinsic_types Convert
             ~type_arguments:[ float64; int32 ]
             [ Value (Constant (Float64 (Int64.bits_of_float number))) ]
             ~destination:(Some (at result))
             ~site:{ definition = definition "entry"; line = 0; column = 1 });
        result
      in
      expect_status ~extra ~anchors 7 [ built_entry (fun builder -> convert builder 7.9) ];
      let status, _, errors =
        run_program ~extra ~anchors [ built_entry (fun builder -> convert builder 1.0e30) ]
      in
      if status <> 101 || not (contains errors "conversion out of range") then
        fail "expected a panic about the conversion, got status %d (%s)" status errors)
