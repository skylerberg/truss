let usage =
  "database_fuzz [--seed N] [--count N] [--depth N] [--verbose] [FILE...]\n\n\
   Edits the files of a project at random and propagates each edit through the project's database \
   in .truss, then compares that database with one built from the edited files. At random points \
   it commits the database and opens it again, before or after the edit is propagated through \
   every stage, or stops a commit before its rename. With no file, it edits the corpus beside it."

let example : Path.module_ = { package = { owner = None; name = "example" }; modules = [] }
let standard_package_database = lazy (Workspace.For_testing.load_standard_package_database ())

type file = { name : string; text : string }

let path_of file : Path.file = { module_ = example; name = file.name }

let build files =
  let database =
    Database.create
      ~loaded:[ Lazy.force standard_package_database ]
      [
        {
          name = example.package;
          dependencies = [];
          files = List.map (fun file -> (path_of file, file.text)) files;
        };
      ]
  in
  Database.propagate database;
  database

let split_lines text =
  match List.rev (String.split_on_char '\n' text) with
  | "" :: rest -> List.rev rest
  | lines -> List.rev lines

let starts_definition line =
  String.length line > 0 && match line.[0] with 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false

let split_chunks text =
  List.rev
    (List.fold_left
       (fun chunks line ->
         match chunks with
         | current :: rest when not (starts_definition line) -> (current ^ line ^ "\n") :: rest
         | chunks -> (line ^ "\n") :: chunks)
       [] (split_lines text))

let generator = ref (Random.State.make [| 0 |])
let draw_number bound = Random.State.int !generator bound
let pick items = List.nth items (draw_number (List.length items))

let replace_nth items index replacement =
  List.concat (List.mapi (fun at item -> if at = index then replacement else [ item ]) items)

let is_identifier_start = function 'a' .. 'z' | '_' -> true | _ -> false
let is_identifier_part = function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false
let is_digit = function '0' .. '9' -> true | _ -> false

let list_words ~starts ~continues text =
  let length = String.length text in
  let rec scan at found =
    if at >= length then List.rev found
    else if starts text.[at] && (at = 0 || not (is_identifier_part text.[at - 1])) then begin
      let stop = ref at in
      while !stop < length && continues text.[!stop] do
        incr stop
      done;
      scan !stop ((at, String.sub text at (!stop - at)) :: found)
    end
    else scan (at + 1) found
  in
  scan 0 []

let keywords = List.map fst Token.keywords

let list_identifiers text =
  List.filter
    (fun (_, word) -> not (List.mem word keywords))
    (list_words ~starts:is_identifier_start ~continues:is_identifier_part text)

let splice text at length replacement =
  String.sub text 0 at ^ replacement
  ^ String.sub text (at + length) (String.length text - at - length)

let rename_all word replacement text =
  List.fold_left
    (fun text (at, found) ->
      if found = word then splice text at (String.length word) replacement else text)
    text
    (List.rev (list_identifiers text))

let types = [ "Int64"; "Int32"; "UInt8"; "Bool"; "String" ]

type edit = { description : string; files : file list }

let with_file files index text =
  List.mapi (fun at file -> if at = index then { file with text } else file) files

let make_random_edit files =
  let index = draw_number (List.length files) in
  let file = List.nth files index in
  let pieces = split_chunks file.text in
  let make_file_edit description text = Some { description; files = with_file files index text } in
  let make_chunk_edit describe change =
    match pieces with
    | [] -> None
    | _ ->
        let at = draw_number (List.length pieces) in
        let description = describe (String.trim (List.hd (split_lines (List.nth pieces at)))) in
        make_file_edit description (String.concat "" (change at pieces))
  in
  let choices =
    [
      (fun () ->
        make_chunk_edit
          (fun first -> Printf.sprintf "delete `%s` in %s" first file.name)
          (fun at pieces -> replace_nth pieces at []));
      (fun () ->
        make_chunk_edit
          (fun first -> Printf.sprintf "duplicate `%s` in %s" first file.name)
          (fun at pieces -> replace_nth pieces at [ List.nth pieces at; List.nth pieces at ]));
      (fun () ->
        make_chunk_edit
          (fun first -> Printf.sprintf "move `%s` within %s" first file.name)
          (fun at pieces ->
            let piece = List.nth pieces at in
            let rest = replace_nth pieces at [] in
            let target = draw_number (List.length rest + 1) in
            List.take target rest @ [ piece ] @ List.drop target rest));
      (fun () ->
        match (pieces, files) with
        | [], _ | _, [ _ ] -> None
        | _ ->
            let at = draw_number (List.length pieces) in
            let piece = List.nth pieces at in
            let other = (index + 1 + draw_number (List.length files - 1)) mod List.length files in
            let moved =
              with_file
                (with_file files index (String.concat "" (replace_nth pieces at [])))
                other
                ((List.nth files other).text ^ piece)
            in
            Some
              {
                description =
                  Printf.sprintf "move `%s` from %s to %s"
                    (String.trim (List.hd (split_lines piece)))
                    file.name (List.nth files other).name;
                files = moved;
              });
      (fun () ->
        match list_identifiers file.text with
        | [] -> None
        | found ->
            let _, word = pick found in
            let replacement = word ^ "_renamed" in
            Some
              {
                description = Printf.sprintf "rename `%s` to `%s` everywhere" word replacement;
                files =
                  List.map
                    (fun file -> { file with text = rename_all word replacement file.text })
                    files;
              });
      (fun () ->
        match list_identifiers file.text with
        | [] -> None
        | found ->
            let at, word = pick found in
            make_file_edit
              (Printf.sprintf "rename one `%s` in %s" word file.name)
              (splice file.text at (String.length word) (word ^ "_renamed")));
      (fun () ->
        match list_words ~starts:is_digit ~continues:is_digit file.text with
        | [] -> None
        | found ->
            let at, digits = pick found in
            let changed = Z.to_string (Z.succ (Z.of_string digits)) in
            make_file_edit
              (Printf.sprintf "change %s to %s in %s" digits changed file.name)
              (splice file.text at (String.length digits) changed));
      (fun () ->
        match
          List.filter
            (fun (_, word) -> List.mem word types)
            (list_words
               ~starts:(function 'A' .. 'Z' -> true | _ -> false)
               ~continues:is_identifier_part file.text)
        with
        | [] -> None
        | found ->
            let at, ty = pick found in
            let other = pick (List.filter (( <> ) ty) types) in
            make_file_edit
              (Printf.sprintf "change a %s to %s in %s" ty other file.name)
              (splice file.text at (String.length ty) other));
      (fun () ->
        let starts =
          List.filter_map
            (fun (at, _) ->
              match String.index_from_opt file.text at '(' with
              | Some open_at
                when not (String.contains (String.sub file.text at (open_at - at)) '\n') ->
                  Some (open_at + 1)
              | _ -> None)
            (List.filter
               (fun (at, word) -> word = "type" && (at = 0 || file.text.[at - 1] = '\n'))
               (list_words ~starts:is_identifier_start ~continues:is_identifier_part file.text))
        in
        match starts with
        | [] -> None
        | starts ->
            let at = pick starts in
            make_file_edit
              (Printf.sprintf "add a field at offset %d of %s" at file.name)
              (splice file.text at 0 "added: Bool = false, "));
      (fun () ->
        make_file_edit (Printf.sprintf "add a line at the top of %s" file.name) ("\n" ^ file.text));
    ]
  in
  let rec attempt tries =
    if tries = 0 then None
    else match (pick choices) () with Some edit -> Some edit | None -> attempt (tries - 1)
  in
  attempt 20

let capture_outcome run = match run () with value -> Ok value | exception failure -> Error failure

let show_failure = function
  | Compiler_bug.Bug bug -> Compiler_bug.to_string bug
  | failure -> Printexc.to_string failure

let corpus = "stage0/tools/database_fuzz/corpus"

let write_project root files =
  File_system.write
    (Filename.concat root "truss.toml")
    (Printf.sprintf "[package]\nname = \"%s\"\ntruss = \"0.1\"\n" example.package.name);
  List.iter
    (fun file -> File_system.write (Filename.concat root (file.name ^ ".truss")) file.text)
    files

let open_database root =
  match Workspace.take_snapshot root with
  | Ok (snapshot, _) -> Workspace.open_database snapshot
  | Error message -> failwith message

let check_and_reopen root =
  Database.check (open_database root) [ example.package ];
  Workspace.flush ()

let find_reopening root =
  match draw_number 8 with
  | 0 | 1 -> Some ("commit and reopen", Workspace.flush)
  | 2 ->
      Some
        ( "stop a commit before its rename",
          fun () -> Workspace.For_testing.interrupt_commit (Unix.realpath root) )
  | _ -> None

let () =
  let seed = ref (int_of_float (Unix.time ())) in
  let count = ref 100 in
  let depth = ref 8 in
  let verbose = ref false in
  let paths = ref [] in
  Arg.parse
    [
      ("--seed", Arg.Set_int seed, "N  the random seed");
      ("--count", Arg.Set_int count, "N  the number of edits");
      ("--depth", Arg.Set_int depth, "N  the number of edits before the files are restored");
      ("--verbose", Arg.Set verbose, " print each edit");
    ]
    (fun path -> paths := path :: !paths)
    usage;
  generator := Random.State.make [| !seed |];
  let paths =
    match List.rev !paths with
    | [] ->
        List.map (Filename.concat corpus)
          (List.filter
             (fun name -> Filename.check_suffix name ".truss")
             (List.sort compare (Array.to_list (Sys.readdir corpus))))
    | paths -> paths
  in
  let files =
    List.map
      (fun path ->
        {
          name = Filename.chop_suffix (Filename.basename path) ".truss";
          text = File_system.read path;
        })
      paths
  in
  Printf.printf "seed %d, %d files, %d edits\n%!" !seed (List.length files) !count;
  let root = Filename.temp_dir "database-fuzz" "" in
  at_exit (fun () -> try File_system.remove root with Sys_error _ | Unix.Unix_error _ -> ());
  write_project root files;
  Database.propagate (open_database root);
  let current = ref files in
  let failures = ref 0 and skipped = ref 0 in
  let report step (edit : edit) problem =
    incr failures;
    Printf.printf "seed %d, edit %d (%s): %s\n%!" !seed step edit.description problem
  in
  let start_over () =
    Workspace.flush ();
    File_system.remove (Filename.concat root ".truss")
  in
  for step = 1 to !count do
    match
      if step mod (!depth + 1) = 0 then Some { description = "restore the files"; files }
      else make_random_edit !current
    with
    | None -> ()
    | Some edit -> (
        if !verbose then Printf.printf "%d: %s\n%!" step edit.description;
        write_project root edit.files;
        if draw_number 4 = 0 then begin
          if !verbose then Printf.printf "  check, commit and reopen\n%!";
          ignore (capture_outcome (fun () -> check_and_reopen root))
        end;
        let propagated =
          capture_outcome (fun () ->
              let hot = open_database root in
              Database.propagate hot;
              hot)
        in
        match (propagated, capture_outcome (fun () -> build edit.files)) with
        | Ok hot, Ok cold -> (
            current := edit.files;
            match Database.For_testing.list_differences hot cold with
            | [] -> (
                match find_reopening root with
                | Some (description, reopen) ->
                    if !verbose then Printf.printf "  %s\n%!" description;
                    reopen ()
                | None -> ())
            | parts ->
                report step edit
                  ("the propagated database differs from a cold build in "
                  ^ String.concat ", " (List.take 20 parts));
                start_over ())
        | Error failure, Ok _ ->
            report step edit ("propagating it raised " ^ show_failure failure);
            start_over ();
            current := edit.files
        | (Ok _ | Error _), Error failure ->
            incr skipped;
            if !verbose then
              Printf.printf "  skipped: a cold build raises %s\n%!" (show_failure failure);
            write_project root !current)
  done;
  Workspace.flush ();
  Printf.printf "%d edits, %d skipped because a cold build raises, %d failures\n" !count !skipped
    !failures;
  exit (if !failures > 0 then 1 else 0)
