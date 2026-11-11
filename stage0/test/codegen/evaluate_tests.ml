(* The prover deciding a tagged template's check by running it, through
   code generation. *)

open Harness
open Codegen_support

(* What the solver said, set in the engine, as the database does for a
   session. *)
let tell database said =
  let engine = Engine.of_context database in
  List.iter (fun (key, told) -> Engine.set engine Prover.told key told) said

let solver =
  lazy (match Solver.find () with Ok solver -> solver | Error message -> failwith message)

(* The prover's diagnostics of a module, deciding template checks by
   running them. *)
let proven_with_running text =
  let database, compile = load text in
  Prover.diagnostics
    ~running:(Running.through (lazy compile))
    ~tell:(tell database) database (Lazy.force solver) example

let shout =
  {|use standard::text

type Shout(text: String)

fn is_quiet(literals: List[text::Literal]) -> Bool
  cost time finite
{
  var quiet = true
  for literal in literals {
    let text = literal.text()
    for index in 0..text.length() {
      let byte = text.byte(index)
      if byte >= 65 && byte <= 90 {
        quiet = false
      }
    }
  }
  quiet
}

impl FromTemplate for Shout {
  type Part = String

  fn from_template(template: Template[String]) -> Shout
    requires is_quiet(template.literals)
  {
    Shout(text: "")
  }
}
|}

let () =
  test "a template check that holds is proven by running it" (fun () ->
      match
        proven_with_running
          (shout ^ "\nfn f(name: String) -> Shout {\n  Shout\"hey ${name.copy()}!\"\n}\n")
      with
      | [] -> ()
      | found ->
          fail "%s" (String.concat "; " (List.map (fun (d : Diagnostic.t) -> d.message) found)));
  test "a template check that does not hold fails, saying it ran" (fun () ->
      match proven_with_running (shout ^ "\nfn f() -> Shout {\n  Shout\"HEY\"\n}\n") with
      | [ diagnostic ] ->
          if Diagnostic.Code.name diagnostic.code <> "prover.requires" then
            fail "%s" (Diagnostic.Code.name diagnostic.code);
          let ran = "Running it on this template's text gives `false`." in
          let length = String.length ran and message = diagnostic.message in
          let rec contains i =
            i + length <= String.length message
            && (String.sub message i length = ran || contains (i + 1))
          in
          if not (contains 0) then fail "%s" message
      | found -> fail "%d diagnostics" (List.length found));
  test "a check that reads a template's parts is not run" (fun () ->
      let text =
        {|type Count(total: USize)

impl FromTemplate for Count {
  type Part = String

  fn from_template(template: Template[String]) -> Count
    requires template.parts.length() == 0
  {
    Count(total: 0)
  }
}

fn f() -> Count {
  Count"none"
}
|}
      in
      match proven_with_running text with
      | [] -> ()
      | found ->
          fail "%s" (String.concat "; " (List.map (fun (d : Diagnostic.t) -> d.message) found)))

let counting =
  {|fn count_up(value: UInt8) -> UInt8
  cost time finite
{
  var count: UInt8 = 0
  for _ in 0..value
    invariant count == yielded.length()
  {
    count += 1
  }
  count
}
|}

let () =
  test "a call whose arguments are known is worked out by running it" (fun () ->
      match
        proven_with_running
          (counting ^ "\nfn f() -> UInt8\n  ensures result == 7\n{\n  count_up(7)\n}\n")
      with
      | [] -> ()
      | found ->
          fail "%s" (String.concat "; " (List.map (fun (d : Diagnostic.t) -> d.message) found)));
  test "without running it, such a call is known only by its contract" (fun () ->
      let database, _ =
        load (counting ^ "\nfn f() -> UInt8\n  ensures result == 7\n{\n  count_up(7)\n}\n")
      in
      match Prover.diagnostics ~tell:(tell database) database (Lazy.force solver) example with
      | [ _ ] -> ()
      | found -> fail "%d diagnostics" (List.length found));
  test "what running a call gives is what it gives, not what was hoped" (fun () ->
      match
        proven_with_running
          (counting ^ "\nfn f() -> UInt8\n  ensures result == 8\n{\n  count_up(7)\n}\n")
      with
      | [ _ ] -> ()
      | found -> fail "%d diagnostics" (List.length found))

let () =
  test "a call that is run uses the argument it gives a parameter that has a default" (fun () ->
      let source promised =
        "fn count_to(limit: UInt8 = 3) -> UInt8\n\
        \  cost time finite\n\
         {\n\
        \  var count: UInt8 = 0\n\
        \  for _ in 0..limit\n\
        \    invariant count == yielded.length()\n\
        \  {\n\
        \    count += 1\n\
        \  }\n\
        \  count\n\
         }\n\n\
         fn f() -> UInt8\n\
        \  ensures result == " ^ promised ^ "\n{\n  count_to(limit: 4)\n}\n"
      in
      (match proven_with_running (source "4") with
      | [] -> ()
      | found ->
          fail "%s" (String.concat "; " (List.map (fun (d : Diagnostic.t) -> d.message) found)));
      match proven_with_running (source "3") with
      | [ _ ] -> ()
      | found -> fail "%d diagnostics for the default's value" (List.length found))

(* The same tag at the same path with the same text, checked by code that
   differs: a check is kept under the code that ran, not under its name. *)
let () =
  test "a template's check is done again when the code it runs has changed" (fun () ->
      let use = "\nfn f() -> Shout {\n  Shout\"HEY\"\n}\n" in
      let accepts_all =
        let refuses = "        quiet = false" in
        let at = ref 0 in
        while String.sub shout !at (String.length refuses) <> refuses do
          incr at
        done;
        String.sub shout 0 !at ^ "        quiet = true"
        ^ String.sub shout
            (!at + String.length refuses)
            (String.length shout - !at - String.length refuses)
      in
      (match proven_with_running (shout ^ use) with
      | [ _ ] -> ()
      | found -> fail "expected the first check to fail, got %d diagnostics" (List.length found));
      match proven_with_running (accepts_all ^ use) with
      | [] -> ()
      | found ->
          fail "%s" (String.concat "; " (List.map (fun (d : Diagnostic.t) -> d.message) found)))

let () = Harness.finish ()
