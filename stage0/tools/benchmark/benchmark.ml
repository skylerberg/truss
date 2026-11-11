(* Measures the speed of the lexer and the parser. This is a tool, not a
   test.

     dune exec stage0/tools/benchmark/benchmark.exe -- FILE...
     dune exec stage0/tools/benchmark/benchmark.exe -- --worst-cases

   For each file, it lexes and parses the file several times and prints,
   for each stage, the best time and the speed in megabytes per second.

   With [--worst-cases], it generates the inputs that once took the lexer
   or the parser time quadratic in their size, each at one size and at
   twice that size, and prints the ratio of the two times. A stage that is
   linear has a ratio near 2, and one that is quadratic a ratio near 4. *)

let best_time run =
  let best = ref infinity in
  for _ = 1 to 5 do
    let start = Unix.gettimeofday () in
    run ();
    best := Float.min !best (Unix.gettimeofday () -. start)
  done;
  !best

let lexing source = best_time (fun () -> ignore (Lexer.lex source))

let parsing source =
  let tokens, _ = Lexer.lex source in
  best_time (fun () -> ignore (Parser.parse source tokens))

let file path =
  let source = Source.read_file path in
  let megabytes = float_of_int (String.length (Source.text source)) /. 1_000_000. in
  let report stage seconds =
    Printf.printf "%s: %s %.2f MB in %.3f s, %.1f MB/s\n" path stage megabytes seconds
      (megabytes /. seconds)
  in
  report "lexing" (lexing source);
  report "parsing" (parsing source)

let repeated count text = String.concat "" (List.init count (fun _ -> text))

(* Each input, by the construct that repeats [count] times in it. *)
let worst_cases =
  [
    ("unclosed openers", fun count -> "let x: Int64 = " ^ String.make count '(' ^ "\n");
    ( "closers with no opener",
      fun count -> "let x: Int64 = " ^ String.make count '(' ^ String.make count ']' ^ "\n" );
    ( "unclosed openers before a closer",
      fun count -> "let x: Int64 = (((((" ^ repeated count "([)" ^ "\n" );
    ("trailing zeros of a float", fun count -> "let x: Float64 = 1" ^ String.make count '0' ^ ".0\n");
    ("digits of an integer", fun count -> "let x: Int64 = " ^ String.make count '7' ^ "\n");
    ("binary operators", fun count -> "let x: Int64 = 1" ^ repeated count " + 1" ^ "\n");
    ("postfix operations", fun count -> "let x: Int64 = a" ^ repeated count ".b" ^ "\n");
    ("nested loop bodies", fun count -> "fn f() {\n" ^ repeated count "while x {\n");
    ("interpolations", fun count -> "let x: String = \"" ^ repeated count "${a}" ^ "\"\n");
  ]

let worst_case (name, input) =
  let size = 100_000 in
  let source count = Source.create ~path:"worst_case.truss" (input count) in
  let report stage time =
    let small = time (source size) and large = time (source (2 * size)) in
    Printf.printf "%-34s %-8s %.3f s, %.3f s at twice the size" name stage small large;
    (* A ratio of two times this short is noise. *)
    if small >= 0.005 then Printf.printf ", ratio %.1f" (large /. small);
    print_newline ()
  in
  report "lexing" lexing;
  report "parsing" parsing

let () =
  let files = ref [] and worst = ref false in
  Arg.parse
    [ ("--worst-cases", Arg.Set worst, " Time the inputs that were once quadratic") ]
    (fun file -> files := file :: !files)
    "benchmark [--worst-cases] FILE...";
  List.iter file (List.rev !files);
  if !worst then List.iter worst_case worst_cases
