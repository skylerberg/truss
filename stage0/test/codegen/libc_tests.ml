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

let operate b ?destination ?(type_arguments = []) operation arguments =
  ignore
    (Intrinsics.lower (shape_env ~extra ()) b intrinsic_types operation ~type_arguments arguments
       ~destination
       ~site:{ definition = definition "entry"; line = 0; column = 1 })

(* An [entry] built with the builder: [body] writes its statements and
   returns the local to exit with. *)
let built_entry body =
  let b = Lir_builder.create () in
  Lir_builder.start b (Lir_builder.block b);
  let result = body b in
  Lir_builder.finish b (Return (Some (Copy (Lir_builder.at result))));
  instance "entry" (Lir_builder.build b ~parameters:[] ~result:(Some (value int32)))

(* A view of static bytes. *)
let view_of b text =
  let open Lir_builder in
  let view = local b (value view_ty) in
  emit b
    (Assign
       ( at view,
         Storage.view view_ty ~elements:(Constant (Bytes text)) ~length:(usize (String.length text))
       ));
  view

(* The C library's numbers, joined with [or]. *)
let flags b numbers =
  let open Lir_builder in
  let all = local b (value int32) in
  emit b (Assign (at all, Use (constant_int32 0)));
  List.iter
    (fun number ->
      let one = local b (value int32) in
      operate b ~destination:(at one) (Libc_number number) [];
      emit b (Assign (at all, Binary (Bit_or, Copy (at all), Copy (at one)))))
    numbers;
  all

let free b storage =
  Lir_builder.emit b
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
  test "the C library's numbers, prototypes, and structures are what this system's headers give"
    (fun () ->
      match compiles (Libc.check host) with
      | Ok () -> ()
      | Error message -> fail "the table disagrees with the headers:\n%s" message);
  test "another system's numbers do not pass for this one's" (fun () ->
      let other : Libc.system =
        { host with os = (match host.os with Linux -> Macos | Macos -> Linux) }
      in
      match compiles (Libc.check other) with
      | Ok () ->
          fail "the check takes the table of %s on %s" (Libc.system_name other)
            (Libc.system_name host)
      | Error _ -> ());
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
  test "what a row says a call reads and writes is counted by a number the call is passed"
    (fun () ->
      List.iter
        (fun function_ ->
          let { Libc.parameters; at_most; _ } = Libc.signature function_ in
          let name = Libc.function_name function_ in
          let passed what parameter =
            match List.assoc_opt parameter parameters with
            | Some (Libc.Value USize) -> ()
            | _ -> fail "%s: %s is `%s`, which is no USize the call is passed" name what parameter
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
              | Value _ | Written _ | Always _ | Environment -> ())
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
            built_entry (fun b ->
                let view = view_of b "written\n" in
                let wrote = local b (value isize) in
                operate b ~destination:(at wrote) (Libc Write)
                  [ Value (constant_int32 1); Place (at view); Value (usize 8) ];
                let status = local b (value int32) in
                emit b (Assign (at status, Convert (Copy (at wrote), Integer Int32)));
                status);
          ]
      in
      expect_int ~expected:8 status;
      expect_string ~expected:"written\n" output);
  test "open is given its mode as C passes an argument through ..." (fun () ->
      let open Lir_builder in
      let path = Filename.concat (Lazy.force scratch) "opened" in
      expect_status ~extra 0
        [
          built_entry (fun b ->
              let name = view_of b (path ^ "\000") in
              let wanted = flags b [ O_wronly; O_creat; O_trunc ] in
              let descriptor = local b (value int32) in
              operate b ~destination:(at descriptor) (Libc Open)
                [ Place (at name); Value (Copy (at wanted)); Value (constant_int32 0o600) ];
              let closed = local b (value int32) in
              operate b ~destination:(at closed) (Libc Close) [ Value (Copy (at descriptor)) ];
              closed);
        ];
      expect_int ~expected:0o600 (Unix.stat path).st_perm);
  test "errno is the number at the address the C library returns" (fun () ->
      let open Lir_builder in
      expect_status ~extra (Libc.value host Enoent)
        [
          built_entry (fun b ->
              let name = view_of b "/nonexistent/truss\000" in
              let wanted = flags b [ O_rdonly ] in
              operate b (Libc Open)
                [ Place (at name); Value (Copy (at wanted)); Value (constant_int32 0) ];
              let error = local b (value int32) in
              operate b ~destination:(at error) (Libc Errno) [];
              error);
        ]);
  test "read fills the room storage has after its last element" (fun () ->
      let open Lir_builder in
      let status, _, _ =
        run_program ~extra ~input:"hello"
          [
            built_entry (fun b ->
                let storage = local b (value bytes_ty) in
                operate b ~destination:(at storage) ~type_arguments:[ uint8 ] Storage_with_capacity
                  [ Value (usize 16) ];
                operate b ~type_arguments:[ uint8 ] Storage_push
                  [ Place (at storage); Value (Constant (Integer (UInt8, Z.of_int 1))) ];
                let got = local b (value isize) in
                operate b ~destination:(at got) (Libc Read)
                  [ Value (constant_int32 0); Place (at storage); Value (usize 15) ];
                (* The first byte read comes after the one the storage had. *)
                let first = local b (value int32) and count = local b (value int32) in
                emit b
                  (Assign
                     (at first, Convert (Copy (Storage.at (at storage) (usize 1)), Integer Int32)));
                emit b (Assign (at count, Convert (Copy (at got), Integer Int32)));
                emit b (Assign (at first, Binary (Add, Copy (at first), Copy (at count))));
                free b (at storage);
                first);
          ]
      in
      expect_int ~expected:(Char.code 'h' + 5) status);
  test "a structure the C library writes arrives in the arguments named for its numbers" (fun () ->
      let open Lir_builder in
      expect_status ~extra 1
        [
          built_entry (fun b ->
              let seconds = local b (value int64) and nanoseconds = local b (value int64) in
              let clock = flags b [ Clock_realtime ] in
              let failed = local b (value int32) in
              operate b ~destination:(at failed) (Libc Clock_gettime)
                [ Value (Copy (at clock)); Place (at seconds); Place (at nanoseconds) ];
              (* Later than 2023, and less than a second of nanoseconds. *)
              let recent = local b (Raw Bool) and whole = local b (Raw Bool) in
              emit b
                (Assign
                   (at recent, Binary (Greater, Copy (at seconds), constant_int64 1_700_000_000)));
              emit b
                (Assign
                   (at whole, Binary (Less, Copy (at nanoseconds), constant_int64 1_000_000_000)));
              emit b (Assign (at recent, Binary (Bit_and, Copy (at recent), Copy (at whole))));
              let status = local b (value int32) in
              emit b (Assign (at status, Convert (Copy (at recent), Integer Int32)));
              emit b (Assign (at status, Binary (Subtract, Copy (at status), Copy (at failed))));
              status);
        ]);
  test "an argument a row fixes is no argument of the Truss call" (fun () ->
      let open Lir_builder in
      let uint64 = named "UInt64" in
      expect_status ~extra 1
        [
          built_entry (fun b ->
              (* Two draws of eight random bytes differ. *)
              let draw () =
                let value = local b (value uint64) and failed = local b (value int32) in
                operate b ~destination:(at failed) (Libc Getentropy) [ Place (at value) ];
                value
              in
              let first = draw () in
              let second = draw () in
              let differ = local b (Raw Bool) and status = local b (value int32) in
              emit b (Assign (at differ, Binary (Not_equal, Copy (at first), Copy (at second))));
              emit b (Assign (at status, Convert (Copy (at differ), Integer Int32)));
              status);
        ])

let () =
  test "nothing after a call of a function that does not return is run" (fun () ->
      let open Lir_builder in
      expect_status ~extra 7
        [
          built_entry (fun b ->
              operate b (Libc Exit) [ Value (constant_int32 7) ];
              let status = local b (value int32) in
              emit b (Assign (at status, Use (constant_int32 0)));
              status);
        ]);
  test "a pipe's two ends arrive in the arguments named for them, and poll finds what was written"
    (fun () ->
      let open Lir_builder in
      let waited_ty = Storage.of_elements int32 in
      expect_status ~extra 1
        [
          built_entry (fun b ->
              let read_end = local b (value int32) and write_end = local b (value int32) in
              operate b (Libc Pipe) [ Place (at read_end); Place (at write_end) ];
              let view = view_of b "x" in
              operate b (Libc Write)
                [ Value (Copy (at write_end)); Place (at view); Value (usize 1) ];
              let waited = local b (value waited_ty) in
              operate b ~destination:(at waited) ~type_arguments:[ int32 ] Storage_with_capacity
                [ Value (usize 2) ];
              operate b ~type_arguments:[ int32 ] Storage_push
                [ Place (at waited); Value (Copy (at read_end)) ];
              let reading = flags b [ Pollin ] in
              operate b ~type_arguments:[ int32 ] Storage_push
                [ Place (at waited); Value (Copy (at reading)) ];
              let ready = local b (value int32) in
              operate b ~destination:(at ready) (Libc Poll)
                [ Place (at waited); Value (usize 1); Value (constant_int32 1000) ];
              (* What was found is the high half of the second number. *)
              let found = local b (value int32) in
              emit b
                (Assign
                   ( at found,
                     Binary (Shift_right, Copy (Storage.at (at waited) (usize 1)), constant_int32 16)
                   ));
              emit b (Assign (at found, Binary (Bit_and, Copy (at found), Copy (at reading))));
              emit b (Assign (at ready, Binary (Multiply, Copy (at ready), Copy (at found))));
              free b (at waited);
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
          ~kind_of:(Monomorphic.kind standard_context)
          ~usize:(Monomorphic.builtin USize) ()
      in
      let int32 = Monomorphic.builtin Int32 in
      let view_ty = Storage.view_of_elements (Monomorphic.builtin UInt8) in
      let handle_ty = Monomorphic.builtin Handle in
      let types : Intrinsics.types =
        { usize = Monomorphic.builtin USize; string_slice = standard "text" "StringSlice" () }
      in
      let entry =
        let b = Lir_builder.create () in
        start b (block b);
        let name = local b (value view_ty) in
        let text = path ^ "\000" in
        emit b
          (Assign
             ( at name,
               Storage.view view_ty ~elements:(Constant (Bytes text))
                 ~length:(usize (String.length text)) ));
        (* [open] gives the lowest descriptor that is free, so the second
           gets the first's exactly when the first was closed. *)
        let opened () =
          let descriptor = local b (value int32) in
          ignore
            (Intrinsics.lower env b types (Libc Open) ~type_arguments:[]
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
        let handle = local b (value handle_ty) in
        emit b
          (Assign
             ( at handle,
               Build
                 { ty = handle_ty; variant = None; fields = [ ("descriptor", Copy (at first)) ] } ));
        emit b (Drop (at handle));
        let second = opened () in
        let same = local b (Raw Bool) and status = local b (value int32) in
        emit b (Assign (at same, Binary (Equal, Copy (at first), Copy (at second))));
        emit b (Assign (at status, Convert (Copy (at same), Integer Int32)));
        finish b (Return (Some (Copy (at status))));
        instance "entry" (build b ~parameters:[] ~result:(Some (value int32)))
      in
      let status, _, errors = run_program ~env [ entry; Glue.drop glue handle_ty ] in
      if status <> 1 then fail "the descriptor was not free again (status %d, %s)" status errors)

let () = Harness.finish ()
