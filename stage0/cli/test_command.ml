(* [truss test]: checks the package, then runs the tests whose results are
   not kept. *)

type test = { path : Path.t; module_ : Path.module_; name : string; file : string; line : int }

(* The tests defined in the selected modules, in the package's order, whose
   names contain [match_]. *)
let select (project : Project.t) ~paths ~match_ =
  List.concat_map
    (fun module_ ->
      let source = Project.source project module_ in
      List.filter_map
        (fun (declaration : Resolve.Names.declaration) ->
          match declaration.path with
          | Test { name; _ }
            when declaration.ordinal = 0
                 && match match_ with Some text -> Substring.contains name text | None -> true ->
              let line =
                match
                  Query.demand project.context Resolve.Names.base (Resolve.Names.key_of declaration)
                with
                | Some (_, base) -> fst (Source.position source base)
                | None -> 0
              in
              Some { path = declaration.path; module_; name; file = Source.path source; line }
          | _ -> None)
        (Query.demand project.context Resolve.Names.declarations module_))
    (Project.selected project paths)

let label test = Path.show_module test.module_ ^ " " ^ Diagnostic.quote test.name

(* A duration for people: [2.31s], [42ms], or [87µs]. *)
let duration microseconds =
  if microseconds >= 1_000_000 then Printf.sprintf "%.2fs" (float microseconds /. 1e6)
  else if microseconds >= 1_000 then Printf.sprintf "%dms" (microseconds / 1_000)
  else Printf.sprintf "%dµs" microseconds

let seconds microseconds = Printf.sprintf "%.1fs" (float microseconds /. 1e6)
let now_microseconds () = int_of_float (Unix.gettimeofday () *. 1e6)

let indented text =
  String.split_on_char '\n' text
  |> List.filter (( <> ) "")
  |> List.iter (fun line -> Output.print_line ("    " ^ line))

(* How many tests ended each way, in the order the runner names outcomes,
   leaving out those that none did. *)
let summary (records : Compile.record list) =
  let count outcome =
    List.length (List.filter (fun (r : Compile.record) -> r.outcome = outcome) records)
  in
  let cached = List.length (List.filter (fun (r : Compile.record) -> r.cached) records) in
  List.filter_map
    (fun outcome ->
      match count outcome with
      | 0 -> None
      | n ->
          let words = Compile.show_outcome outcome in
          let words = String.map (function '_' -> ' ' | c -> c) words in
          if outcome = Passed && cached > 0 then
            Some (Printf.sprintf "%d %s (%d cached)" n words cached)
          else Some (Printf.sprintf "%d %s" n words))
    [ Passed; Failed; Panicked; Incomplete; Timed_out; Crashed ]
  |> String.concat ", "

type timings = { check : int; build : int; tests : int; total : int }

let print_report tests (records : Compile.record list) ~timings:show_timings timings =
  List.iter2
    (fun test (record : Compile.record) ->
      if record.outcome <> Passed then begin
        Output.printf "%s: %s\n" (label test) (Compile.show_outcome record.outcome);
        Option.iter indented record.message;
        Option.iter indented record.echo
      end)
    tests records;
  if List.exists (fun (r : Compile.record) -> r.outcome <> Passed) records then Output.print_line "";
  if show_timings then begin
    let rows =
      List.combine tests records
      |> List.stable_sort (fun (_, (a : Compile.record)) (_, (b : Compile.record)) ->
          compare b.microseconds a.microseconds)
    in
    let shown = List.map (fun (_, (r : Compile.record)) -> duration r.microseconds) rows in
    let width = List.fold_left (fun w s -> max w (String.length s)) 0 shown in
    List.iter2
      (fun (test, (record : Compile.record)) text ->
        Output.printf "%*s  %s%s\n" width text (label test)
          (if record.cached then "  cached" else ""))
      rows shown;
    Output.print_line ""
  end;
  Output.printf "%s in %s (check %s, build %s, tests %s)\n"
    (if records = [] then "No tests" else summary records)
    (seconds timings.total) (seconds timings.check) (seconds timings.build) (seconds timings.tests)

let test_json test (record : Compile.record option) =
  Json.Object
    ([
       ("module", Json.String (Path.show_module test.module_));
       ("name", Json.String test.name);
       ("file", Json.String test.file);
       ("line", Json.Int test.line);
     ]
    @
    match record with
    | None -> []
    | Some record ->
        [
          ("outcome", Json.String (Compile.show_outcome record.outcome));
          ("cached", Json.Bool record.cached);
          ("microseconds", Json.Int record.microseconds);
          ("message", Json.option (fun m -> Json.String m) record.message);
          ("echo", Json.option (fun e -> Json.String e) record.echo);
        ])

let timings_json timings =
  Json.Object
    [
      ("check", Json.Int timings.check);
      ("build", Json.Int timings.build);
      ("tests", Json.Int timings.tests);
      ("total", Json.Int timings.total);
    ]

(* The status line while tests build and run. *)
type progress = {
  line : Status_line.t;
  tests : test array;
  mutable ended : int;
  mutable not_passed : int;
  mutable running_since : int option;  (** When the first test started *)
  running : (int, int) Hashtbl.t;  (** Each running test's start *)
}

let draw progress =
  let now = now_microseconds () in
  let total = Array.length progress.tests in
  let width = String.length (string_of_int total) in
  let parts =
    [ Printf.sprintf "[%*d/%d]" width progress.ended total ]
    @ (if progress.not_passed > 0 then [ Printf.sprintf "%d not passed" progress.not_passed ]
       else [])
    @ (match progress.running_since with Some start -> [ seconds (now - start) ] | None -> [])
    @
    match
      Hashtbl.fold
        (fun test start oldest ->
          match oldest with Some (_, s) when s <= start -> oldest | _ -> Some (test, start))
        progress.running None
    with
    | Some (test, start) ->
        [ Printf.sprintf "running %s (%s)" (label progress.tests.(test)) (seconds (now - start)) ]
    | None -> []
  in
  Status_line.show progress.line (String.concat " · " parts)

let on_progress progress ~build_ended (event : Compile.progress) =
  match event with
  | Lowering -> Status_line.show progress.line "building · lowering"
  | Compiling { compiled; total } ->
      Status_line.show progress.line
        (Printf.sprintf "building · compiling %d/%d C files" compiled total)
  | Running _ ->
      let now = now_microseconds () in
      build_ended := Some now;
      progress.running_since <- Some now;
      draw progress
  | Started { test } ->
      Hashtbl.replace progress.running test (now_microseconds ());
      draw progress
  | Ended { test; record } ->
      Hashtbl.remove progress.running test;
      progress.ended <- progress.ended + 1;
      if record.outcome <> Passed then progress.not_passed <- progress.not_passed + 1;
      draw progress

(* Runs each package's tests with its own time limit, one test program a
   package, and reports each test by its place among them all. *)
let run_all (project : Project.t) compile ~results ~rerun ~progress tests =
  let offset = ref 0 in
  List.fold_left
    (fun outcome (package : Project.package) ->
      match outcome with
      | Error _ -> outcome
      | Ok done_ -> (
          let own = List.filter (fun t -> t.module_.package = package.name) tests in
          let base = !offset in
          offset := base + List.length own;
          let shifted : Compile.progress -> Compile.progress = function
            | Started { test } -> Started { test = test + base }
            | Ended { test; record } -> Ended { test = test + base; record }
            | other -> other
          in
          if own = [] then outcome
          else
            match
              Compile.run_tests ?results ~rerun
                ~progress:(fun event -> progress (shifted event))
                compile
                ~time_limit:(Database.time_limit project.session * 1000)
                (List.map (fun t -> t.path) own)
            with
            | Ok records -> Ok (done_ @ records)
            | Error message -> Error message))
    (Ok []) project.packages

let run ~directory ~paths ~match_ ~timings:show_timings ~rerun ~json ~sanitize =
  let started = now_microseconds () in
  let project = Project.load directory in
  let report = Report.gather project in
  let checked = now_microseconds () in
  (* In the packages' order, so each package's tests are together. *)
  let tests =
    let selected = select project ~paths ~match_ in
    List.concat_map
      (fun (package : Project.package) ->
        List.filter (fun t -> t.module_.package = package.name) selected)
      project.packages
  in
  if not (Report.clean report) then begin
    if json then
      Json.print
        (Report.document report
           [ ("tests", Json.List (List.map (fun t -> test_json t None) tests)) ])
    else Report.print report;
    1
  end
  else
    let compile = Compiler.create ~sanitize project Development in
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
    (* A sanitized run keeps no results, since it checks what a plain one
       does not. *)
    let results = if sanitize then None else Some (Compiler.test_results ()) in
    let outcome =
      run_all project compile ~results ~rerun ~progress:(on_progress progress ~build_ended) tests
    in
    Status_line.clear progress.line;
    Database.flush_store ();
    match outcome with
    | Error message -> Project.cannot_run "%s" message
    | Ok records ->
        let ended = now_microseconds () in
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
            (Json.document ~diagnostics:[]
               [
                 ("tests", Json.List (List.map2 (fun t r -> test_json t (Some r)) tests records));
                 ("timings", timings_json timings);
               ])
        else print_report tests records ~timings:show_timings timings;
        if List.for_all (fun (r : Compile.record) -> r.outcome = Passed) records then 0 else 1
