type test = { path : Path.t; module_ : Path.module_; name : string; file : string; line : int }

let select snapshot database packages ~paths ~match_ =
  let names = Database.make_name_lookups database packages in
  List.concat_map
    (fun (file : Path.file) ->
      let source = Command_packages.read_source snapshot packages file in
      List.filter_map
        (fun (declaration : Resolve.Names.declaration) ->
          match declaration.path with
          | Test { name; _ }
            when declaration.ordinal = 0
                 && match match_ with Some text -> String.includes ~affix:text name | None -> true
            ->
              let line =
                fst
                  (Source.compute_position source
                     (names.place (Resolve.Names.make_key declaration)).base)
              in
              Some
                {
                  path = declaration.path;
                  module_ = file.module_;
                  name;
                  file = Source.path source;
                  line;
                }
          | _ -> None)
        (names.declarations_in file))
    (Command_packages.select_files snapshot packages paths)

let label_test test = Path.show_module test.module_ ^ " " ^ Diagnostic.quote test.name

let show_duration microseconds =
  if microseconds >= 1_000_000 then Printf.sprintf "%.2fs" (float microseconds /. 1e6)
  else if microseconds >= 1_000 then Printf.sprintf "%dms" (microseconds / 1_000)
  else Printf.sprintf "%dµs" microseconds

let show_seconds microseconds = Printf.sprintf "%.1fs" (float microseconds /. 1e6)
let read_microseconds () = int_of_float (Unix.gettimeofday () *. 1e6)

let print_indented text =
  String.split_on_char '\n' text
  |> List.filter (( <> ) "")
  |> List.iter (fun line -> Output.print_line ("    " ^ line))

let summarize (records : Compile.record list) =
  let count outcome =
    List.length (List.filter (fun (record : Compile.record) -> record.outcome = outcome) records)
  in
  let cached = List.length (List.filter (fun (record : Compile.record) -> record.cached) records) in
  List.filter_map
    (fun outcome ->
      match count outcome with
      | 0 -> None
      | count ->
          let words = Compile.show_outcome outcome in
          let words = String.map (function '_' -> ' ' | character -> character) words in
          if outcome = Passed && cached > 0 then
            Some (Printf.sprintf "%d %s (%d cached)" count words cached)
          else Some (Printf.sprintf "%d %s" count words))
    [ Passed; Failed; Panicked; Incomplete; Timed_out; Crashed ]
  |> String.concat ", "

type timings = { check : int; build : int; tests : int; total : int }

let print_report tests (records : Compile.record list) ~timings:show_timings timings =
  List.iter2
    (fun test (record : Compile.record) ->
      if record.outcome <> Passed then begin
        Output.printf "%s: %s\n" (label_test test) (Compile.show_outcome record.outcome);
        Option.iter print_indented record.message;
        Option.iter print_indented record.echo
      end)
    tests records;
  if List.exists (fun (record : Compile.record) -> record.outcome <> Passed) records then
    Output.print_line "";
  if show_timings then begin
    let rows =
      List.combine tests records
      |> List.stable_sort (fun (_, (left : Compile.record)) (_, (right : Compile.record)) ->
          compare right.microseconds left.microseconds)
    in
    let shown =
      List.map (fun (_, (record : Compile.record)) -> show_duration record.microseconds) rows
    in
    let width = List.fold_left (fun widest name -> max widest (String.length name)) 0 shown in
    List.iter2
      (fun (test, (record : Compile.record)) text ->
        Output.printf "%*s  %s%s\n" width text (label_test test)
          (if record.cached then "  cached" else ""))
      rows shown;
    Output.print_line ""
  end;
  Output.printf "%s in %s (check %s, build %s, tests %s)\n"
    (if records = [] then "No tests" else summarize records)
    (show_seconds timings.total) (show_seconds timings.check) (show_seconds timings.build)
    (show_seconds timings.tests)

let test_json test (record : Compile.record) =
  Json.Object
    [
      ("module", Json.String (Path.show_module test.module_));
      ("name", Json.String test.name);
      ("file", Json.String test.file);
      ("line", Json.Int test.line);
      ("outcome", Json.String (Compile.show_outcome record.outcome));
      ("cached", Json.Bool record.cached);
      ("microseconds", Json.Int record.microseconds);
      ("message", Json.encode_option (fun message -> Json.String message) record.message);
      ("echo", Json.encode_option (fun echo -> Json.String echo) record.echo);
    ]

let encode_timings timings =
  Json.Object
    [
      ("check", Json.Int timings.check);
      ("build", Json.Int timings.build);
      ("tests", Json.Int timings.tests);
      ("total", Json.Int timings.total);
    ]

type progress = {
  line : Status_line.t;
  tests : test array;
  mutable ended : int;
  mutable not_passed : int;
  mutable running_since : int option;
  running : (int, int) Hashtbl.t;
}

let draw progress =
  let now = read_microseconds () in
  let total = Array.length progress.tests in
  let width = String.length (string_of_int total) in
  let parts =
    [ Printf.sprintf "[%*d/%d]" width progress.ended total ]
    @ (if progress.not_passed > 0 then [ Printf.sprintf "%d not passed" progress.not_passed ]
       else [])
    @ (match progress.running_since with
      | Some start -> [ show_seconds (now - start) ]
      | None -> [])
    @
    match
      Hashtbl.fold
        (fun test start oldest ->
          match oldest with
          | Some (_, oldest_start) when oldest_start <= start -> oldest
          | _ -> Some (test, start))
        progress.running None
    with
    | Some (test, start) ->
        [
          Printf.sprintf "running %s (%s)"
            (label_test progress.tests.(test))
            (show_seconds (now - start));
        ]
    | None -> []
  in
  Status_line.show progress.line (String.concat " · " parts)

let handle_progress progress ~build_ended (event : Compile.progress) =
  match event with
  | Lowering -> Status_line.show progress.line "building · lowering"
  | Compiling { compiled; total } ->
      Status_line.show progress.line
        (Printf.sprintf "building · compiling %d/%d C files" compiled total)
  | Running _ ->
      let now = read_microseconds () in
      build_ended := Some now;
      progress.running_since <- Some now;
      draw progress
  | Started { test } ->
      Hashtbl.replace progress.running test (read_microseconds ());
      draw progress
  | Ended { test; record } ->
      Hashtbl.remove progress.running test;
      progress.ended <- progress.ended + 1;
      if record.outcome <> Passed then progress.not_passed <- progress.not_passed + 1;
      draw progress

let run_tests ?rerun ?progress database snapshot packages tests =
  if tests = [] then []
  else
    match
      Compile.run_tests ?rerun ?progress
        (Compiler.create database snapshot packages Development)
        ~time_limit_ms:(Workspace.time_limit_ms snapshot)
        (List.map (fun test -> test.path) tests)
    with
    | Ok records -> records
    | Error message -> Outcome.raise_cannot_run "%s" message

let run ~paths ~match_ ~timings:show_timings ~rerun =
  let json = Output.json () in
  let started = read_microseconds () in
  let snapshot, packages = Command_packages.load_current () in
  let database = Workspace.open_database snapshot in
  let report = Report.gather database snapshot packages in
  let checked = read_microseconds () in
  let tests = select snapshot database packages ~paths ~match_ in
  if not (Report.clean report) then raise (Report.Errors report);
  let progress =
    {
      line = Status_line.create ~enabled:(not json);
      tests = Array.of_list tests;
      ended = 0;
      not_passed = 0;
      running_since = None;
      running = Hashtbl.create 16;
    }
  in
  let build_ended = ref None in
  let records =
    Fun.protect
      ~finally:(fun () -> Status_line.clear progress.line)
      (fun () ->
        run_tests ~rerun
          ~progress:(handle_progress progress ~build_ended)
          database snapshot packages tests)
  in
  let ended = read_microseconds () in
  let build_end = Option.value !build_ended ~default:ended in
  let timings =
    {
      check = checked - started;
      build = build_end - checked;
      tests = ended - build_end;
      total = ended - started;
    }
  in
  if json then
    Json.print
      (Json.make_document ~diagnostics:[]
         [
           ("tests", Json.List (List.map2 test_json tests records));
           ("timings", encode_timings timings);
         ])
  else print_report tests records ~timings:show_timings timings;
  if List.for_all (fun (record : Compile.record) -> record.outcome = Passed) records then 0 else 1

module For_testing = struct
  let duration = show_duration
end
