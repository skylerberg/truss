(* The prover deciding a tagged template's check by running it, through
   code generation. *)

open Harness
open Codegen_support

let solver =
  lazy (match Solver.find () with Ok solver -> solver | Error message -> failwith message)

(* The prover's diagnostics of a module, deciding template checks by
   running them. *)
let proven_with_running text =
  let database, compile = load text in
  Prover.diagnostics ~running:(Running.through (lazy compile)) database (Lazy.force solver) example

let shout =
  {|type Shout(text: String)

fn is_quiet(literals: List[Literal]) -> Bool
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
        proven_with_running (shout ^ "\nfn f(name: String) -> Shout {\n  Shout\"hey ${name}!\"\n}\n")
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
      match Prover.diagnostics database (Lazy.force solver) example with
      | [ _ ] -> ()
      | found -> fail "%d diagnostics" (List.length found));
  test "what running a call gives is what it gives, not what was hoped" (fun () ->
      match
        proven_with_running
          (counting ^ "\nfn f() -> UInt8\n  ensures result == 8\n{\n  count_up(7)\n}\n")
      with
      | [ _ ] -> ()
      | found -> fail "%d diagnostics" (List.length found))

let () = Harness.finish ()
