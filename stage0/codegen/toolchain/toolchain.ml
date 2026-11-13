type t = { compiler : string; identity : string }

let identify compiler =
  match Process.run compiler [ "--version" ] with
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
        match identify candidate with
        | Ok toolchain -> Ok toolchain
        | Error error -> first (error :: errors) rest)
  in
  first [] candidates

let added_flags_variable = "TRUSS_CFLAGS"

let split_flags text =
  String.map (function '\t' | '\n' | '\r' -> ' ' | character -> character) text
  |> String.split_on_char ' '
  |> List.filter (( <> ) "")

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

(* Clang's ThinLTO where the compiler is clang, and otherwise full LTO,
   which GCC has. *)
let link_time_optimization toolchain =
  if Substring.contains toolchain.identity "clang" then [ "-flto=thin" ] else [ "-flto" ]

let optimization_flag = function O1 -> "-O1" | O2 -> "-O2"

let compile toolchain ~optimization ?(extra = []) ~source ~output () =
  let arguments =
    (optimization_flag optimization :: required_flags) @ extra @ [ "-c"; source; "-o"; output ]
  in
  match Process.run toolchain.compiler arguments with
  | 0, _, _ -> Ok ()
  | _, out, err -> Error (out ^ err)

(* A path as one word of a response file, which the C compiler reads as it
   reads a command line: in quotes, with a backslash before a quote or a
   backslash. *)
let response_word path =
  let buffer = Buffer.create (String.length path + 2) in
  Buffer.add_char buffer '"';
  String.iter
    (fun compiler ->
      if compiler = '"' || compiler = '\\' then Buffer.add_char buffer '\\';
      Buffer.add_char buffer compiler)
    path;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let link toolchain ?(extra = []) ~objects ~output () =
  (* The objects are named in a response file: a program has one for each
     instance, and a command line holds only so many bytes. *)
  let response = output ^ ".objects" in
  Out_channel.with_open_bin response (fun channel ->
      List.iter (fun path -> output_string channel (response_word path ^ "\n")) objects);
  (* [fma] can be a call into libm where the processor has no instruction
     for it, as on baseline x86-64. macOS accepts [-lm] as part of its libc. *)
  let result =
    Process.run toolchain.compiler (extra @ [ "@" ^ response; "-o"; output; "-lm"; "-pthread" ])
  in
  (try Sys.remove response with Sys_error _ -> ());
  match result with 0, _, _ -> Ok () | _, out, err -> Error (out ^ err)
