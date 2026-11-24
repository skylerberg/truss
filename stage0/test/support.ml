let parse_module text : Path.module_ =
  match Path.parse_names text with
  | Some (name :: modules) -> { package = { owner = None; name }; modules }
  | Some [] | None -> invalid_arg text

let make_top_path module_ name : Path.t = Top { module_ = parse_module module_; name }

let parse_file text : Path.file =
  match String.split_first ~sep:"/" text with
  | Some (module_, name) -> { module_ = parse_module module_; name }
  | None ->
      let module_ = parse_module text in
      { module_; name = (match List.rev module_.modules with last :: _ -> last | [] -> "main") }

let locate_occurrence ~sub ~occurrence text =
  let rec search start remaining =
    match String.find_first ~sub ~start text with
    | None -> failwith (Printf.sprintf "no occurrence %d of %S" occurrence sub)
    | Some offset -> if remaining = 1 then offset else search (offset + 1) (remaining - 1)
  in
  search 0 occurrence

let standard_package_database = lazy (Workspace.For_testing.load_standard_package_database ())

let make_database packages =
  Database.create ~loaded:[ Lazy.force standard_package_database ] packages

let extend_standard_library (packages : Project.package list) =
  Database.For_testing.extend_package
    ~loaded:(Lazy.force standard_package_database)
    (List.concat_map
       (fun (package : Project.package) ->
         if package.name <> Path.standard_package then
           failwith (Path.show_package package.name ^ " is not the standard package");
         package.files)
       packages)

let setup ?(dependencies = []) files : Project.package list =
  let files = List.map (fun (name, text) -> (parse_file name, text)) files in
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

let read_source packages (file : Path.file) =
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
    (snd (Parser.parse_source (read_source packages file)))

let list_codes diagnostics =
  List.map (fun (diagnostic : Diagnostic.t) -> Diagnostic.Code.name diagnostic.code) diagnostics

let expect_error ~list_diagnostics ?fixed ?(alternatives = []) ?(occurrence = 1) text ~code ~at =
  match list_diagnostics text with
  | [ (diagnostic : Diagnostic.t) ] -> (
      let message = diagnostic.message in
      if
        message = ""
        || (not (Char.uppercase_ascii message.[0] = message.[0] && message.[0] <> ' '))
        || message.[String.length message - 1] <> '.'
      then Harness.fail "the message %S is not written in sentences" message;
      if diagnostic.code <> code then
        Harness.fail "expected %s, got %s" (Diagnostic.Code.name code)
          (Diagnostic.Code.name diagnostic.code);
      let expected = locate_occurrence ~sub:at ~occurrence text in
      if diagnostic.span.start <> expected then
        Harness.fail "expected the error at %d (%S), got %d" expected at diagnostic.span.start;
      let results =
        List.map
          (fun (fix : Source.span Diagnostic.fix) -> Diagnostic.apply_edits text fix.edits)
          diagnostic.fixes
      in
      match (fixed, results) with
      | None, [] -> ()
      | None, result :: _ -> Harness.fail "expected no fix, got one giving %S" result
      | Some _, [] -> Harness.fail "expected a fix, got none"
      | Some fixed, results ->
          if fixed :: alternatives <> results then
            Harness.fail "expected the fixes to give [%s], got [%s]"
              (String.concat "; " (List.map (Printf.sprintf "%S") (fixed :: alternatives)))
              (String.concat "; " (List.map (Printf.sprintf "%S") results));
          List.iter
            (fun result ->
              List.iter
                (Harness.fail "the fixed text %S has %s" result)
                (list_codes (list_diagnostics result)))
            results)
  | diagnostics ->
      Harness.fail "expected one diagnostic, got [%s] for %S"
        (String.concat "; " (list_codes diagnostics))
        text

let run_check ~check packages name =
  let file = parse_file name in
  (match parse_errors packages file with
  | [] -> ()
  | errors -> Harness.fail "the test input does not parse: %s" (String.concat " " errors));
  check packages file

type core_nodes = {
  expressions : Core.expression list;
  statements : Core.statement list;
  patterns : Core.pattern list;
}

let collect_core_nodes packages (key : Resolve.Names.key) : core_nodes =
  match Database.read_checked_body (make_database packages) key with
  | None -> failwith (Printf.sprintf "%s has no core form" (Resolve.Names.show_key key))
  | Some { form; _ } ->
      let expressions = ref [] and statements = ref [] and patterns = ref [] in
      Core_walk.walk_definition
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

let make_names packages = Database.make_name_lookups (make_database packages)

let list_declarations packages (module_ : Path.module_) =
  (make_names packages).list_declarations module_

let collect_first_core_nodes text =
  let packages = setup [ ("app.main", text) ] in
  collect_core_nodes packages (List.hd (list_declarations packages (parse_module "app.main"))).key

let expect_no_diagnostics ~check files =
  let packages = setup files in
  let database = make_database packages in
  List.iter
    (fun (name, _) ->
      (match run_check ~check packages name with
      | [] -> ()
      | reported ->
          Harness.fail "%s: %s" name
            (String.concat "; "
               (List.map
                  (fun (diagnostic : Diagnostic.t) ->
                    Diagnostic.Code.name diagnostic.code ^ " " ^ diagnostic.message)
                  reported)));
      ignore (Core_lint.check_file database (parse_file name)))
    files

let expect_one_diagnostic ~check ?(setup = fun files -> setup files) ?(file = "app.main")
    ?(others = []) ?fixed ?says ?at ?notes text code =
  let packages = setup ((file, text) :: others) in
  match run_check ~check packages file with
  | [ (diagnostic : Diagnostic.t) ] -> (
      let actual = Diagnostic.Code.name diagnostic.code in
      if actual <> code then Harness.fail "expected %s, got %s: %s" code actual diagnostic.message;
      Option.iter
        (fun says ->
          if not (String.includes ~affix:says diagnostic.message) then
            Harness.fail "expected a message that says %S, got: %s" says diagnostic.message)
        says;
      Option.iter
        (fun (written, occurrence) ->
          let expected = locate_occurrence ~sub:written ~occurrence text in
          if diagnostic.span.start <> expected then
            Harness.fail "expected the diagnostic at occurrence %d of %S, offset %d, got offset %d"
              occurrence written expected diagnostic.span.start)
        at;
      Option.iter
        (fun expected_notes ->
          let actual_notes =
            List.map (fun ((span : Source.span), note) -> (note, span.start)) diagnostic.notes
          in
          if
            actual_notes
            <> List.map
                 (fun (note, (written, occurrence)) ->
                   (note, locate_occurrence ~sub:written ~occurrence text))
                 expected_notes
          then
            Harness.fail "expected the notes [%s], got [%s]"
              (String.concat "; "
                 (List.map
                    (fun (note, (written, occurrence)) ->
                      Printf.sprintf "%S at occurrence %d of %S" note occurrence written)
                    expected_notes))
              (String.concat "; "
                 (List.map
                    (fun (note, offset) -> Printf.sprintf "%S at offset %d" note offset)
                    actual_notes)))
        notes;
      match (fixed, diagnostic.fixes) with
      | None, _ -> ()
      | Some _, [] -> Harness.fail "no fix"
      | Some expected, fix :: _ -> (
          let after = Diagnostic.apply_edits text fix.edits in
          if after <> expected then Harness.fail "fixed to %S" after
          else
            let packages = setup ((file, after) :: others) in
            match run_check ~check packages file with
            | [] -> ()
            | left -> Harness.fail "after the fix: %s" (String.concat "; " (list_codes left))))
  | reported ->
      Harness.fail "expected one %s, got [%s]" code
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

let prove database file = Database.prove database (In_files [ file ])

let c_compiler =
  lazy
    (match
       C_compiler.find ~x86_64_level:X86_64_level.default
         ~objects:(Cache.make_objects_directory (Workspace.open_cache ()))
         ()
     with
    | Ok c_compiler -> c_compiler
    | Error message ->
        prerr_endline message;
        exit 1)

let run_evaluations database packages proofs =
  match Database.list_evaluations proofs with
  | [] -> ()
  | evaluated ->
      let backend =
        Backend.create
          (match Database.find_lowered_lookups database packages with
          | Ok lookups -> lookups
          | Error message -> failwith message)
          (Lazy.force c_compiler) Development
      in
      ignore (Backend.evaluate backend evaluated)

let decide database (scope : Database.proof_scope) =
  let proofs = Database.prove database scope in
  run_evaluations database
    (match scope with
    | In_packages packages -> packages
    | In_files files -> List.map (fun (file : Path.file) -> file.module_.package) files)
    proofs;
  Database.decide proofs solver

let list_proof_diagnostics database file =
  decide database (In_files [ file ]);
  Database.list_proof_diagnostics database file

let list_proof_states database file =
  decide database (In_files [ file ]);
  Database.list_proof_states database file

let read_proofs database file =
  let proofs = prove database file in
  fun key ->
    match Database.For_testing.find_proof proofs key with
    | Some (Value proof) -> proof
    | Some (Failed | Blocked) ->
        failwith ("the proof of " ^ Resolve.Names.show_key key ^ " is blocked")
    | None -> failwith (Resolve.Names.show_key key ^ " is not proven")
