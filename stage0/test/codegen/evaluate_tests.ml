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
  let evaluate (evaluation : Prover.Translate.evaluation) : Prover.evaluated option =
    match
      Compile.check_template compile ~time_limit:10_000 ~from_template:evaluation.from_template
        ~texts:evaluation.texts
    with
    | Ok (Ran found) ->
        Option.map
          (fun holds -> if holds then Prover.Holds else Prover.Fails)
          (List.assoc_opt evaluation.clause found)
    | Ok Ran_too_long -> Some Too_long
    | Error message -> failwith message
  in
  Prover.diagnostics ~evaluate database (Lazy.force solver) example

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

let () = Harness.finish ()
