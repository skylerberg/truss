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

let top_key module_name name : Resolve.Names.key =
  let module_ = module_of module_name in
  { module_; path = Top { module_; name }; ordinal = 0 }

(* The standard library as a fixed base, shared by every test in a run, so
   that it is checked once. *)
let standard = lazy (Database.For_testing.standard_base ())

let setup ?(dependencies = []) files =
  let database = Engine.context (Engine.create ~log:true ~bases:[ Lazy.force standard ] ()) in
  let files = List.map (fun (name, text) -> (file_of name, text)) files in
  let package_of ((file : Path.file), _) = file.module_.package in
  let dependencies_of (package : Path.package) =
    List.filter_map
      (fun (dependent, dependency) ->
        if dependent = package.name then
          Some { Manifest.package = { owner = None; name = dependency }; capabilities = [] }
        else None)
      dependencies
  in
  List.iter
    (fun package ->
      Database.load_package (Engine.of_context database) ~name:package
        ~dependencies:(dependencies_of package)
        (List.filter (fun file -> package_of file = package) files))
    (List.sort_uniq compare (List.map package_of files));
  database

let parse_errors database file =
  List.map
    (fun (diagnostic : Diagnostic.t) -> diagnostic.message)
    (Query.demand database Parsed.file file).diagnostics

let codes diagnostics =
  List.map (fun (diagnostic : Diagnostic.t) -> Diagnostic.Code.name diagnostic.code) diagnostics

let checked ~check database name =
  let file = file_of name in
  (match parse_errors database file with
  | [] -> ()
  | errors -> fail "the test input does not parse: %s" (String.concat " " errors));
  check database file

type core_nodes = {
  expressions : Core.expression list;
  statements : Core.statement list;
  patterns : Core.pattern list;
}

let core_nodes database (key : Resolve.Names.key) : core_nodes =
  match Query.demand database Infer.core key with
  | None -> failwith (Printf.sprintf "%s has no core form" (Resolve.Names.show_key key))
  | Some form ->
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

let first_core_nodes text =
  let database = setup [ ("app::main", text) ] in
  core_nodes database
    (Resolve.Names.key_of
       (List.hd (Query.demand database Resolve.Names.declarations (module_of "app::main"))))

(* Fails the test unless every file checks without a diagnostic and every
   core form satisfies [Core_lint.check]. *)
let no_diagnostics ~check files =
  let database = setup files in
  List.iter
    (fun (name, _) ->
      (match checked ~check database name with
      | [] -> ()
      | reported ->
          fail "%s: %s" name
            (String.concat "; "
               (List.map
                  (fun (diagnostic : Diagnostic.t) ->
                    Diagnostic.Code.name diagnostic.code ^ " " ^ diagnostic.message)
                  reported)));
      ignore (Core_lint.check_file database (file_of name)))
    files

let one_diagnostic ~check ?(setup = fun files -> setup files) ?(file = "app::main") ?(others = [])
    ?fixed ?says text code =
  let database = setup ((file, text) :: others) in
  match checked ~check database file with
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
            let database = setup ((file, after) :: others) in
            match checked ~check database file with
            | [] -> ()
            | left -> fail "after the fix: %s" (String.concat "; " (codes left))))
  | reported ->
      fail "expected one %s, got [%s]" code
        (String.concat "; "
           (List.map
              (fun (diagnostic : Diagnostic.t) ->
                Diagnostic.Code.name diagnostic.code ^ " " ^ diagnostic.message)
              reported))

let record database responses =
  let engine = Engine.of_context database in
  List.iter (fun (key, response) -> Engine.set engine Prover.oracle_response key response) responses

let solver =
  lazy
    (match Solver.find () with
    | Ok solver -> solver
    | Error message ->
        prerr_endline message;
        exit 1)
