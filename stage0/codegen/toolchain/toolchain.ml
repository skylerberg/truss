type t = { compiler : string; identity : string }

let read_all channel =
  let buffer = Buffer.create 256 in
  (try
     while true do
       Buffer.add_channel buffer channel 1
     done
   with End_of_file -> ());
  Buffer.contents buffer

(* Runs a program with arguments, with no shell, and returns its status and
   what it wrote to standard output and standard error. *)
(* A process's status as a shell reports it: its exit code, or [128 +
   signal] for a process a signal ended. *)
let exit_code (status : Unix.process_status) =
  match status with
  | WEXITED code -> code
  | WSIGNALED signal | WSTOPPED signal ->
      (* OCaml numbers signals its own way; report the system's number. *)
      let system =
        List.assoc_opt signal
          [
            (Sys.sigabrt, 6);
            (Sys.sigsegv, 11);
            (Sys.sigkill, 9);
            (Sys.sigbus, 10);
            (Sys.sigfpe, 8);
            (Sys.sigill, 4);
            (Sys.sigterm, 15);
          ]
      in
      128 + Option.value system ~default:signal

let run ?input program arguments =
  let stdout_read, stdout_write = Unix.pipe ~cloexec:true () in
  let stderr_read, stderr_write = Unix.pipe ~cloexec:true () in
  let stdin_read, stdin_write =
    match input with
    | Some _ ->
        let read, write = Unix.pipe ~cloexec:true () in
        (read, Some write)
    | None -> (Unix.stdin, None)
  in
  let pid =
    Unix.create_process program
      (Array.of_list (program :: arguments))
      stdin_read stdout_write stderr_write
  in
  Unix.close stdout_write;
  Unix.close stderr_write;
  (* Write the input on another domain too, and close it, so the program
     sees its end. *)
  let writer =
    match (input, stdin_write) with
    | Some text, Some write ->
        (* A program that ends without reading it all closes the pipe, which
           must not end this process. *)
        Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
        Unix.close stdin_read;
        Some
          (Domain.spawn (fun () ->
               let channel = Unix.out_channel_of_descr write in
               (try output_string channel text with Sys_error _ -> ());
               try close_out channel with Sys_error _ -> ()))
    | _ -> None
  in
  (* Read standard error on another domain, so neither pipe fills while the
     other is read. *)
  let errors = Domain.spawn (fun () -> read_all (Unix.in_channel_of_descr stderr_read)) in
  let output = read_all (Unix.in_channel_of_descr stdout_read) in
  let errors = Domain.join errors in
  Option.iter Domain.join writer;
  Unix.close stdout_read;
  Unix.close stderr_read;
  let _, status = Unix.waitpid [] pid in
  (exit_code status, output, errors)

let identify compiler =
  match run compiler [ "--version" ] with
  | 0, version, _ -> Ok { compiler; identity = String.trim version ^ "\n" ^ compiler }
  | _ -> Error (compiler ^ " --version failed")
  | exception Unix.Unix_error _ -> Error ("cannot run " ^ compiler)

let find () =
  let candidates =
    match Sys.getenv_opt "TRUSS_CC" with Some cc when cc <> "" -> [ cc ] | _ -> [ "clang"; "cc" ]
  in
  let rec first errors = function
    | [] -> Error ("no C compiler found: " ^ String.concat "; " (List.rev errors))
    | candidate :: rest -> (
        match identify candidate with Ok t -> Ok t | Error e -> first (e :: errors) rest)
  in
  first [] candidates

let required_flags =
  [
    "-std=c11";
    "-fwrapv";
    "-fno-strict-aliasing";
    "-fno-finite-loops";
    "-ffp-contract=off";
    "-fno-fast-math";
    "-fno-math-errno";
    "-fno-common";
    "-fvisibility=hidden";
    "-fno-exceptions";
    "-fno-asynchronous-unwind-tables";
  ]

type optimization = O1 | O2

let optimization_flag = function O1 -> "-O1" | O2 -> "-O2"

let compile t ~optimization ?(extra = []) ~source ~output () =
  let arguments =
    (optimization_flag optimization :: required_flags) @ extra @ [ "-c"; source; "-o"; output ]
  in
  match run t.compiler arguments with 0, _, _ -> Ok () | _, out, err -> Error (out ^ err)

let link t ~objects ~output =
  (* [fma] can be a call into libm where the processor has no instruction
     for it, as on baseline x86-64. macOS accepts [-lm] as part of its libc. *)
  match run t.compiler (objects @ [ "-o"; output; "-lm" ]) with
  | 0, _, _ -> Ok ()
  | _, out, err -> Error (out ^ err)

let run_attached program arguments =
  let pid =
    Unix.create_process program
      (Array.of_list (program :: arguments))
      Unix.stdin Unix.stdout Unix.stderr
  in
  let _, status = Unix.waitpid [] pid in
  exit_code status
