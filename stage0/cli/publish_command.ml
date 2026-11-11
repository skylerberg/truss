(* [truss publish]: adds the package it is run in to the registry, as its
   next version, once it is finished and breaks nothing the version before
   it offered. The registry gives the version its number. *)

module Names = Resolve.Names
module Version = Registry.Version
module Lock = Registry.Lock

(* Every [todo] and [echo] of the package, with where it is. Truss has no
   comments, and a string is one token, so the keyword is always the thing
   itself. *)
let unfinished (project : Project.t) =
  List.concat_map
    (fun module_ ->
      let file = Project.parsed project module_ in
      let source = Project.source project module_ in
      List.filter_map
        (fun (token : Token.t) ->
          match token.kind with
          | Keyword ((Todo | Echo) as keyword) ->
              let line, column = Source.position source token.span.start in
              Some
                ( (match keyword with Todo -> "todo" | _ -> "echo"),
                  Source.path source,
                  line,
                  column )
          | _ -> None)
        (Array.to_list file.tokens))
    (Project.modules project)

(* The files a package is published as: its own, with the lock file that
   records what it is published with in place of its project's. *)
let files (package : Project.package) (record : Lock.t) =
  List.filter (fun (path, _) -> path <> "truss.lock") (Registry.Content.files package.directory)
  @ if record = [] then [] else [ ("truss.lock", Lock.print record) ]

(* What a package is published with: each registry package its code reaches,
   its tests apart, at the build's version. A dependency that is one of the
   project's packages counts as the registry's only when its files are
   those of a version the registry holds, which is then its version. Each
   that is not is a problem, since a package is published with registry
   packages only. *)
let record (project : Project.t) registry (package : Project.package) =
  let session = project.session in
  let root = Database.root session in
  let built = Database.registry_packages session in
  let directory_of name =
    Option.map
      (fun (relative, _) -> if relative = "" then root else Filename.concat root relative)
      (List.find_opt (fun (_, other) -> other = name) (Database.packages session))
  in
  let in_registry name = List.find_opt (fun (other, _, _) -> other = name) built in
  let dependencies ~code name =
    match Query.find project.context Workspace.packages name with
    | Some (found : Workspace.package) ->
        let used = if code then Database.code_packages session name else [] in
        List.filter_map
          (fun (dependency : Workspace.dependency) ->
            if (not code) || List.mem dependency.package used then Some dependency.package else None)
          found.dependencies
    | None -> []
  in
  let problems = ref [] in
  let rec closure name : Lock.t =
    let seen = Hashtbl.create 16 and entries = ref [] in
    let add name version hash = entries := { Lock.name; version; hash; holds = [] } :: !entries in
    let rec visit name =
      if not (Hashtbl.mem seen name) then begin
        Hashtbl.replace seen name ();
        match (in_registry name, directory_of name) with
        | Some (_, version, hash), _ ->
            add name version hash;
            (* What a registry package takes on is in the build already. *)
            List.iter
              (fun next -> if in_registry next <> None || directory_of next <> None then visit next)
              (dependencies ~code:false name)
        | None, Some directory -> (
            match published_as name directory with
            | Some (version, hash) ->
                add name version hash;
                List.iter visit (dependencies ~code:true name)
            | None ->
                problems :=
                  Printf.sprintf
                    "`%s` is a package of this project, and its files are not those of a version \
                     the registry holds. A package is published with registry packages only, so \
                     publish `%s` first."
                    name name
                  :: !problems)
        | None, None -> ()
      end
    in
    List.iter visit (dependencies ~code:true name);
    List.sort (fun (left : Lock.entry) right -> String.compare left.name right.name) !entries
  and published_as name directory =
    let hash = Registry.Content.hash (files { name; directory } (closure name)) in
    List.find_map
      (fun (version, found) -> if found = hash then Some (version, hash) else None)
      (Registry.Index.versions registry name)
  in
  let entries = closure package.name in
  (entries, List.sort_uniq compare !problems)

(* The package's tests that have no [uses] and do not pass, each with how it
   ended. *)
let failed_tests (project : Project.t) (package : Project.package) =
  let tests =
    List.filter
      (fun (test : Test_command.test) ->
        test.module_.package = package.name
        &&
        match Query.demand project.context Interface.Environment.interface test.path with
        | Some (Test_interface []) -> true
        | _ -> false)
      (Test_command.select project ~paths:[] ~match_:None)
  in
  if tests = [] then []
  else
    let compile = Compiler.create project Development in
    match
      Compile.run_tests ~results:(Compiler.test_results ()) compile
        ~time_limit:(Database.time_limit project.session * 1000)
        (List.map (fun (test : Test_command.test) -> test.path) tests)
    with
    | Error message -> Project.cannot_run "%s" message
    | Ok records ->
        Database.flush_store ();
        List.concat
          (List.map2
             (fun (test : Test_command.test) (record : Compile.record) ->
               if record.outcome = Passed then []
               else
                 [
                   Printf.sprintf "%s: %s" (Test_command.label test)
                     (Compile.show_outcome record.outcome);
                 ])
             tests records)

(* The name a package would be published under once it breaks what its
   name has offered: the next number after [_v]. *)
let next_name name =
  let major = Version.major_of_name name in
  let base =
    if major = 1 then name
    else
      let suffix = Printf.sprintf "_v%d" major in
      if String.ends_with ~suffix name then
        String.sub name 0 (String.length name - String.length suffix)
      else name
  in
  Printf.sprintf "%s_v%d" base (major + 1)

type outcome =
  | Published of {
      version : Version.t;
      files : (string * string) list;
      grows : (Path.t * string) list;
    }
  | Unchanged of Version.t
  | Refused of string list

let decide (project : Project.t) registry (package : Project.package) =
  let name = package.name in
  match record project registry package with
  | _, (_ :: _ as problems) -> Refused problems
  | record, [] -> (
      let files = files package record in
      let hash = Registry.Content.hash files in
      match Registry.Index.newest registry name with
      | None -> Published { version = Version.first name; files; grows = [] }
      | Some (version, newest) when newest = hash -> Unchanged version
      | Some (((major, minor, patch) as version), _) -> (
          match Database.published name version with
          | Error message -> Refused [ message ]
          | Ok published ->
              let found, narrowed =
                Compatibility.compare ~before:(Database.context published) ~after:project.context
                  name
              in
              let breaks =
                List.map
                  (fun (path, what) ->
                    let was = Impact_command.signature (Database.context published) path
                    and now = Impact_command.signature project.context path in
                    String.concat ""
                      (Printf.sprintf "%s %s." (Path.show path) what
                      ::
                      (if was <> now then
                         List.filter_map Fun.id
                           [
                             Option.map (Printf.sprintf "\n    was: %s") was;
                             Option.map (Printf.sprintf "\n    now: %s") now;
                           ]
                       else [])))
                  (Compatibility.breaks found)
                @
                if narrowed then
                  [
                    Printf.sprintf "`%s` ran on every target, and now says `usize_bits = 64`." name;
                  ]
                else []
              in
              if breaks <> [] then
                Refused
                  (Printf.sprintf
                     "This would break what `%s` %s offers, so it cannot be published under that \
                      name:"
                     name (Version.show version)
                   :: List.map (fun sentence -> "  " ^ sentence) breaks
                  @ [ Printf.sprintf "Publish it under a new name, such as `%s`." (next_name name) ]
                  )
              else
                let grows = Compatibility.grows found in
                Published
                  {
                    version =
                      (if grows = [] then (major, minor, patch + 1) else (major, minor + 1, 0));
                    files;
                    grows;
                  }))

let run ~directory ~json =
  let project = Project.load directory in
  let package = Project.package project in
  let name = package.name in
  if List.length (Path.package_parts name) <> 2 then
    Project.cannot_run
      "`%s` has no owner in its name, which a published package's has, such as `acme::%s`." name
      name;
  let registry =
    match Registry.Index.current () with
    | Some registry -> registry
    | None ->
        Project.cannot_run "No registry is set: `%s` names its directory." Registry.Index.variable
  in
  let report = Report.gather ~proofs:true project in
  let refuse sentences =
    if json then
      Json.print
        (Report.document report
           [ ("refused", Json.List (List.map (fun sentence -> Json.String sentence) sentences)) ])
    else begin
      Report.print report;
      List.iter Output.eprint_line sentences
    end;
    1
  in
  if not (Report.clean report) then refuse [ "A package is published only when it has no errors." ]
  else
    match unfinished project with
    | _ :: _ as found ->
        refuse
          (List.map
             (fun (keyword, file, line, column) ->
               Printf.sprintf "%s:%d:%d: `%s` is not finished code." file line column keyword)
             found
          @ [ "A package is published only when it has no `todo` and no `echo`." ])
    | [] -> (
        match failed_tests project package with
        | _ :: _ as failed ->
            refuse (failed @ [ "A package is published only when its tests pass." ])
        | [] -> (
            match decide project registry package with
            | Refused sentences -> refuse sentences
            | Unchanged version ->
                if json then
                  Json.print
                    (Report.document report [ ("version", Json.String (Version.show version)) ])
                else Output.printf "`%s` %s is these files already.\n" name (Version.show version);
                0
            | Published { version; files; grows } ->
                Registry.Index.add registry name version files;
                let hash = Registry.Content.hash files in
                if json then
                  Json.print
                    (Report.document report
                       [
                         ("package", Json.String name);
                         ("version", Json.String (Version.show version));
                         ("hash", Json.String hash);
                         ( "grows",
                           Json.List
                             (List.map
                                (fun (path, what) ->
                                  Json.Object
                                    [
                                      ("path", Json.String (Path.show path));
                                      ("what", Json.String what);
                                    ])
                                grows) );
                       ])
                else begin
                  Output.printf "Published `%s` %s.\n" name (Version.show version);
                  List.iter
                    (fun (path, what) -> Output.printf "  %s %s.\n" (Path.show path) what)
                    grows
                end;
                0))
