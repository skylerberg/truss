open Harness

let module_of text : Path.module_ =
  match String.split_on_char ':' text |> List.filter (( <> ) "") with
  | package :: modules -> { package; modules }
  | [] -> invalid_arg text

(* The standard library as a fixed base, shared by every test in a run, so
   that it is checked once. *)
let standard = lazy (Database.standard_layer ())

let setup files =
  let database = Engine.context (Engine.create ~log:true ~bases:[ Lazy.force standard ] ()) in
  let files = List.map (fun (name, text) -> (module_of name, text)) files in
  List.iter
    (fun package ->
      Database.load_package (Engine.of_context database) ~name:package ~dependencies:[]
        (List.filter (fun ((module_ : Path.module_), _) -> module_.package = package) files))
    (List.sort_uniq compare (List.map (fun ((module_ : Path.module_), _) -> module_.package) files));
  database

let parse_errors database module_ =
  List.map
    (fun (d : Diagnostic.t) -> d.message)
    (Query.demand database Workspace.file module_).diagnostics

let codes diagnostics = List.map (fun (d : Diagnostic.t) -> Diagnostic.Code.name d.code) diagnostics

let checked ~check database name =
  let module_ = module_of name in
  (match parse_errors database module_ with
  | [] -> ()
  | errors -> fail "the test input does not parse: %s" (String.concat " " errors));
  check database module_

let no_diagnostics ~check files =
  let database = setup files in
  List.iter
    (fun (name, _) ->
      match checked ~check database name with
      | [] -> ()
      | found ->
          fail "%s: %s" name
            (String.concat "; "
               (List.map
                  (fun (d : Diagnostic.t) -> Diagnostic.Code.name d.code ^ " " ^ d.message)
                  found)))
    files

let one_diagnostic ~check ?(others = []) ?fixed text code =
  let database = setup (("app::main", text) :: others) in
  match checked ~check database "app::main" with
  | [ (diagnostic : Diagnostic.t) ] -> (
      let actual = Diagnostic.Code.name diagnostic.code in
      if actual <> code then fail "expected %s, got %s: %s" code actual diagnostic.message;
      match (fixed, diagnostic.fixes) with
      | None, _ -> ()
      | Some _, [] -> fail "no fix"
      | Some expected, fix :: _ -> (
          let after = Diagnostic.apply_fix text fix in
          if after <> expected then fail "fixed to %S" after
          else
            let database = setup (("app::main", after) :: others) in
            match checked ~check database "app::main" with
            | [] -> ()
            | left -> fail "after the fix: %s" (String.concat "; " (codes left))))
  | found ->
      fail "expected one %s, got [%s]" code
        (String.concat "; "
           (List.map
              (fun (d : Diagnostic.t) -> Diagnostic.Code.name d.code ^ " " ^ d.message)
              found))
