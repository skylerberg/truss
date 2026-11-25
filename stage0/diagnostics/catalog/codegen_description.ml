let show_location ~show_file ({ file; line; column } : Codegen.location) =
  Printf.sprintf "%s:%d:%d" (show_file file) line column

let show_construct : Codegen.construct -> string = function
  | Lending_capability_method { capability; method_ } ->
      Printf.sprintf "`%s.%s`, a capability method that lends" (Path.show capability) method_

let show_evaluated : Codegen.evaluated -> string = function
  | Constant path -> Printf.sprintf "`%s`" (Path.show path)
  | Assertion { definition; _ } -> Printf.sprintf "an assertion in `%s`" (Path.show definition)

let rec describe_stop ~show_file : Codegen.stop -> string = function
  | Depends_on_itself path -> Printf.sprintf "the value of `%s` depends on itself" (Path.show path)
  | Ended { ending = Panicked; message } -> "panic: " ^ message
  | Ended { ending = Assertion_failed; message } -> "assertion failed: " ^ message
  | Ended { ending = Incomplete | Timed_out | Crashed; message } -> message
  | Unbuildable failure -> describe_failure ~show_file failure

and describe_failure ~show_file : Codegen.failure -> string = function
  | Unsupported { construct; location } ->
      Printf.sprintf "%sStage0 cannot build this yet: %s."
        (match location with
        | Some location -> show_location ~show_file location ^ ": "
        | None -> "")
        (show_construct construct)
  | Todo_types todo_types ->
      String.concat "\n"
        (List.map
           (fun ({ type_; location } : Codegen.todo_type) ->
             Printf.sprintf "the type `%s` is defined as todo\n  at %s" (Path.show type_)
               (show_location ~show_file location))
           todo_types)
  | Todo_types_reached_by_main todo_types ->
      String.concat "\n"
        (List.map
           (fun ({ type_; location } : Codegen.todo_type) ->
             Printf.sprintf
               "%s: the type `%s` is defined as todo, and `main` can reach it, so the program \
                cannot be built."
               (show_location ~show_file location)
               (Path.show type_))
           todo_types)
  | Evaluation_stopped { evaluated; stop } ->
      Printf.sprintf "Evaluating %s stopped: %s" (show_evaluated evaluated)
        (describe_stop ~show_file stop)
  | Test_program_ended { status; errors } ->
      Printf.sprintf "The test program ended with status %d before reporting every test:\n%s" status
        errors
  | C_compiler_failed message -> message
  | Unreadable_test_report message -> "A test report cannot be read: " ^ message
