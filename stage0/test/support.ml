open Harness

let module_of text : Path.module_ =
  match String.split_on_char ':' text |> List.filter (( <> ) "") with
  | name :: modules -> { package = { owner = None; name }; modules }
  | [] -> invalid_arg text

let file_of text : Path.file =
  match String.index_opt text '/' with
  | Some slash ->
      {
        module_ = module_of (String.sub text 0 slash);
        name = String.sub text (slash + 1) (String.length text - slash - 1);
      }
  | None ->
      let module_ = module_of text in
      { module_; name = (match List.rev module_.modules with last :: _ -> last | [] -> "main") }

let standard_state = lazy (Workspace.For_testing.standard_state ())
let database packages = Database.create ~loaded:[ Lazy.force standard_state ] packages

let setup ?(dependencies = []) files : Project.package list =
  let files = List.map (fun (name, text) -> (file_of name, text)) files in
  let package_of ((file : Path.file), _) = file.module_.package in
  List.map
    (fun (package : Path.package) : Project.package ->
      {
        name = package;
        dependencies =
          List.filter_map
            (fun (dependent, dependency) ->
              if dependent = package.name then
                Some { Manifest.package = { owner = None; name = dependency }; capabilities = [] }
              else None)
            dependencies;
        files = List.filter (fun file -> package_of file = package) files;
      })
    (List.sort_uniq compare (List.map package_of files))

let with_dependencies packages name dependencies =
  List.map
    (fun (package : Project.package) ->
      if package.name = name then { package with dependencies } else package)
    packages

let source packages (file : Path.file) =
  match
    List.find_map
      (fun (package : Project.package) -> List.assoc_opt file package.files)
      (packages : Project.package list)
  with
  | Some text -> Source.create ~path:(Path.show_file file) text
  | None -> failwith ("no file " ^ Path.show_file file)

let parse_errors packages file =
  List.map
    (fun (diagnostic : Diagnostic.t) -> diagnostic.message)
    (Parsed.parse (source packages file)).diagnostics

let diagnostics database (file : Path.file) =
  Database.check database [ file.module_.package ];
  Database.file_diagnostics database file

let codes diagnostics =
  List.map (fun (diagnostic : Diagnostic.t) -> Diagnostic.Code.name diagnostic.code) diagnostics

let checked ~check packages name =
  let file = file_of name in
  (match parse_errors packages file with
  | [] -> ()
  | errors -> fail "the test input does not parse: %s" (String.concat " " errors));
  check packages file

type core_nodes = {
  expressions : Core.expression list;
  statements : Core.statement list;
  patterns : Core.pattern list;
}

let core_nodes packages (key : Resolve.Names.key) : core_nodes =
  match Database.For_testing.checked_body (database packages) key with
  | None -> failwith (Printf.sprintf "%s has no core form" (Resolve.Names.show_key key))
  | Some { form; _ } ->
      let expressions = ref [] and statements = ref [] and patterns = ref [] in
      Core_walk.definition
        {
          Core_walk.ignore_all with
          expression = (fun node -> expressions := node :: !expressions);
          statement = (fun node -> statements := node :: !statements);
          pattern = (fun node -> patterns := node :: !patterns);
        }
        form.definition;
      {
        expressions = List.rev !expressions;
        statements = List.rev !statements;
        patterns = List.rev !patterns;
      }

let names packages (package : Path.package) = Database.names (database packages) [ package ]

let declarations packages (module_ : Path.module_) =
  (names packages module_.package).declarations module_

let first_core_nodes text =
  let packages = setup [ ("app::main", text) ] in
  core_nodes packages
    (Resolve.Names.key_of (List.hd (declarations packages (module_of "app::main"))))

let no_diagnostics ~check files =
  let packages = setup files in
  let database = database packages in
  List.iter
    (fun (name, _) ->
      (match checked ~check packages name with
      | [] -> ()
      | reported ->
          fail "%s: %s" name
            (String.concat "; "
               (List.map
                  (fun (diagnostic : Diagnostic.t) ->
                    Diagnostic.Code.name diagnostic.code ^ " " ^ diagnostic.message)
                  reported)));
      ignore
        (Core_lint.check_file
           (Database.interface_lookups database [ (file_of name).module_.package ])
           ~core:(fun key ->
             Option.map
               (fun (checked : Infer.checked) -> checked.form)
               (Database.For_testing.checked_body database key))
           (file_of name)))
    files

let one_diagnostic ~check ?(setup = fun files -> setup files) ?(file = "app::main") ?(others = [])
    ?fixed ?says text code =
  let packages = setup ((file, text) :: others) in
  match checked ~check packages file with
  | [ (diagnostic : Diagnostic.t) ] -> (
      let actual = Diagnostic.Code.name diagnostic.code in
      if actual <> code then fail "expected %s, got %s: %s" code actual diagnostic.message;
      Option.iter
        (fun says ->
          if not (Substring.contains diagnostic.message says) then
            fail "expected a message that says %S, got: %s" says diagnostic.message)
        says;
      match (fixed, diagnostic.fixes) with
      | None, _ -> ()
      | Some _, [] -> fail "no fix"
      | Some expected, fix :: _ -> (
          let after = Diagnostic.apply_fix text fix in
          if after <> expected then fail "fixed to %S" after
          else
            let packages = setup ((file, after) :: others) in
            match checked ~check packages file with
            | [] -> ()
            | left -> fail "after the fix: %s" (String.concat "; " (codes left))))
  | reported ->
      fail "expected one %s, got [%s]" code
        (String.concat "; "
           (List.map
              (fun (diagnostic : Diagnostic.t) ->
                Diagnostic.Code.name diagnostic.code ^ " " ^ diagnostic.message)
              reported))

let solver =
  lazy
    (match Solver.find () with
    | Ok solver -> solver
    | Error message ->
        prerr_endline message;
        exit 1)

let proven database file = Database.prove database [ file ]

let verdicts database file =
  Prover.decide ~runs:[]
    (Database.make_proof_lookups database)
    (Lazy.force solver)
    (Database.list_proofs (proven database file))

let proof_diagnostics database file = Prover.list_diagnostics (verdicts database file) file
let proof_states database file = Prover.list_states (verdicts database file) file

let proofs database file =
  let proofs = proven database file in
  fun key ->
    match Database.proof proofs key with
    | Some (Value proof) -> proof
    | Some (Failed _ | Blocked) ->
        failwith ("the proof of " ^ Resolve.Names.show_key key ^ " is blocked")
    | None -> failwith (Resolve.Names.show_key key ^ " is not proven")
