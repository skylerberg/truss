(* Measuring how fast the lexer and the parser are. This is a tool, not a
   test. See IMPLEMENTATION.md, "Testing".

     dune exec stage0/tools/benchmark/benchmark.exe -- FILE...

   It lexes and parses each file several times and prints, for each stage,
   the best time and the speed in megabytes per second. *)

let best_time run =
  let best = ref infinity in
  for _ = 1 to 5 do
    let start = Unix.gettimeofday () in
    run ();
    best := Float.min !best (Unix.gettimeofday () -. start)
  done;
  !best

let () =
  let files = ref [] in
  Arg.parse [] (fun file -> files := file :: !files) "benchmark FILE...";
  List.iter
    (fun path ->
      let source = Source.read_file path in
      let megabytes = float_of_int (String.length (Source.text source)) /. 1_000_000. in
      let tokens, _ = Lexer.lex source in
      let report stage seconds =
        Printf.printf "%s: %s %.2f MB in %.3f s, %.1f MB/s\n" path stage megabytes seconds
          (megabytes /. seconds)
      in
      report "lexing" (best_time (fun () -> ignore (Lexer.lex source)));
      report "parsing" (best_time (fun () -> ignore (Parser.parse source tokens))))
    (List.rev !files)
