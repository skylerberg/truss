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
    ~loaded:[ Lazy.force standard_package_database ]
    ~package:Path.standard_package
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
    (let tokens, lexer_diagnostics = Lexer.lex (read_source packages file) in
     lexer_diagnostics @ snd (Parser.parse tokens ~lexer_diagnostics))

let list_fragment_diagnostics database file =
  List.filter
    (fun (diagnostic : Diagnostic.t) ->
      not (Diagnostic.For_testing.is_unused_definition diagnostic.code))
    (Database.list_file_diagnostics database file)

let list_codes diagnostics =
  List.map (fun (diagnostic : Diagnostic.t) -> Diagnostic.Code.name diagnostic.code) diagnostics

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
  let packages = setup [ ("app::main", text) ] in
  collect_core_nodes packages
    (Resolve.Names.make_key (List.hd (list_declarations packages (parse_module "app::main"))))

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
      ignore
        (Core_lint.check_file
           (Database.make_interface_lookups database)
           ~find_core:(fun key ->
             Option.map
               (fun (checked : Infer.checked) -> checked.form)
               (Database.read_checked_body database key))
           (parse_file name)))
    files

let expect_one_diagnostic ~check ?(setup = fun files -> setup files) ?(file = "app::main")
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

let prove database file = Database.prove database [ file ]

let compute_verdicts database file =
  Prover.decide ~runs:[]
    (Database.make_proof_lookups database)
    (Lazy.force solver)
    (Database.list_proofs (prove database file))

let list_proof_diagnostics database file =
  Prover.list_diagnostics (compute_verdicts database file) file

let list_proof_states database file = Prover.list_states (compute_verdicts database file) file

let read_proofs database file =
  let proofs = prove database file in
  fun key ->
    match Database.For_testing.find_proof proofs key with
    | Some (Value proof) -> proof
    | Some (Failed _ | Blocked) ->
        failwith ("the proof of " ^ Resolve.Names.show_key key ^ " is blocked")
    | None -> failwith (Resolve.Names.show_key key ^ " is not proven")
