let failures = ref 0
let count = ref 0
let current_test = ref ""

let fail format =
  Printf.ksprintf
    (fun message ->
      incr failures;
      Printf.printf "FAIL %s: %s\n" !current_test message)
    format

(* Every engine a test makes is audited when the test ends: each result it
   holds is computed again in a new engine with the same inputs, and must
   come out the same. So every test of every stage also tests that the
   code database kept each result current. *)
let () = Engine.auditing := true

let test name body =
  incr count;
  current_test := name;
  (match body () with
  | () -> ()
  | exception exception_ ->
      (* With OCAMLRUNPARAM=b, the backtrace says where. *)
      fail "raised %s%s" (Printexc.to_string exception_) (Printexc.get_backtrace ()));
  match Engine.audit_all () with
  | problems ->
      List.iter (fun problem -> fail "the code database kept a stale result: %s" problem) problems
  | exception exception_ -> fail "auditing raised %s" (Printexc.to_string exception_)

let finish () =
  if !failures > 0 then begin
    Printf.printf "%d failures in %d tests\n" !failures !count;
    exit 1
  end
  else Printf.printf "%d tests pass\n" !count
