let failures = ref 0
let count = ref 0
let current_test = ref ""

let fail format =
  Printf.ksprintf
    (fun message ->
      incr failures;
      Printf.printf "FAIL %s: %s\n" !current_test message)
    format

let test name body =
  incr count;
  current_test := name;
  match body () with
  | () -> ()
  | exception exception_ -> fail "raised %s" (Printexc.to_string exception_)

let finish () =
  if !failures > 0 then begin
    Printf.printf "%d failures in %d tests\n" !failures !count;
    exit 1
  end
  else Printf.printf "%d tests pass\n" !count
