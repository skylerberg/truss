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

(* With [TRUSS_TEST] set, only the tests whose names contain it run, for
   working on one. *)
let wanted =
  match Sys.getenv_opt "TRUSS_TEST" with
  | None | Some "" -> fun _ -> true
  | Some part ->
      fun name ->
        let length = String.length part in
        let rec from start =
          start + length <= String.length name
          && (String.sub name start length = part || from (start + 1))
        in
        from 0

let test name body =
  if wanted name then begin
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
  end

let finish () =
  if !failures > 0 then begin
    Printf.printf "%d failures in %d tests\n" !failures !count;
    exit 1
  end
  else Printf.printf "%d tests pass\n" !count
