(* Measuring how fast the lexer is. This is a tool, not a test. See
   IMPLEMENTATION.md, "Testing".

     dune exec stage0/tools/benchmark/benchmark.exe -- FILE...

   It lexes each file several times and prints the best time and the speed
   in megabytes per second. *)

let () =
  let files = ref [] in
  Arg.parse [] (fun file -> files := file :: !files) "benchmark FILE...";
  List.iter
    (fun path ->
      let source = Source.read_file path in
      let megabytes = float_of_int (String.length (Source.text source)) /. 1_000_000. in
      let best = ref infinity in
      for _ = 1 to 5 do
        let start = Unix.gettimeofday () in
        ignore (Lexer.lex source);
        best := Float.min !best (Unix.gettimeofday () -. start)
      done;
      Printf.printf "%s: %.2f MB in %.3f s, %.1f MB/s\n" path megabytes !best (megabytes /. !best))
    (List.rev !files)
