(* Fuzzing the lexer. This is a tool, not a test: run it by hand to look for
   inputs that break the lexer, and turn each one it finds into a focused
   test. See IMPLEMENTATION.md, "Testing".

     dune exec stage0/tools/fuzz/fuzz.exe -- [--seed N] [--count N] FILE...

   The files are Markdown documents; their ```truss blocks are the inputs it
   mutates. It checks that:

   - no input raises, every token and diagnostic span is in bounds and in
     order, and brackets are balanced;
   - for one mistake inserted into an example, every fix removes its
     diagnostic and adds no other;
   - valid tokens printed with spaces between them lex back to the same
     tokens.

   It prints each failing input and exits with status 1 if there was one. *)

open Token

let failures = ref 0

let fail format =
  Printf.ksprintf
    (fun message ->
      incr failures;
      if !failures <= 50 then print_endline message)
    format

let lex text = Lexer.lex (Source.create ~path:"fuzz.truss" text)

let read path =
  let channel = open_in_bin path in
  let text = really_input_string channel (in_channel_length channel) in
  close_in channel;
  text

let truss_blocks text =
  let rec loop inside current blocks = function
    | [] -> List.rev blocks
    | line :: rest ->
        let trimmed = String.trim line in
        if inside then
          if String.starts_with ~prefix:"```" trimmed then loop false [] (String.concat "\n" (List.rev current) :: blocks) rest
          else loop true (line :: current) blocks rest
        else loop (trimmed = "```truss") [] blocks rest
  in
  loop false [] [] (String.split_on_char '\n' text)

(* Robustness *)

let rec check_tokens text ~start ~stop (tokens : Token.t array) =
  let quoted = Diagnostic.quote text in
  let length = Array.length tokens in
  if length = 0 || tokens.(length - 1).kind <> End_of_file then fail "no End_of_file in %s" quoted;
  let stack = ref [] and previous = ref start in
  Array.iter
    (fun (token : Token.t) ->
      if token.span.start < start || token.span.stop > stop then fail "span out of bounds in %s" quoted;
      if token.span.start < !previous then fail "tokens out of order in %s" quoted;
      previous := token.span.start;
      match token.kind with
      | Punctuation (Open bracket) -> stack := bracket :: !stack
      | Punctuation (Close bracket) -> (
          match !stack with
          | top :: rest when top = bracket -> stack := rest
          | _ -> fail "unbalanced brackets in %s" quoted)
      | String literal ->
          Array.iter
            (fun (interpolation : interpolation) ->
              check_tokens text ~start:interpolation.span.start ~stop:interpolation.span.stop interpolation.tokens)
            (interpolations literal)
      | _ -> ())
    tokens;
  if !stack <> [] then fail "unbalanced brackets in %s" quoted

let check_robust text =
  match lex text with
  | exception exception_ -> fail "raised %s on %s" (Printexc.to_string exception_) (Diagnostic.quote text)
  | tokens, diagnostics ->
      check_tokens text ~start:0 ~stop:(String.length text) tokens;
      List.iter
        (fun (d : Diagnostic.t) ->
          if d.span.stop > String.length text then fail "diagnostic out of bounds in %s" (Diagnostic.quote text))
        diagnostics

(* Fixes for single mistakes *)

(* Applying a fix removes its diagnostic and adds no other: what is left is
   the other diagnostics, or fewer. *)
let check_fixes_work text =
  let codes text = List.sort compare (List.map (fun (d : Diagnostic.t) -> d.code) (snd (lex text))) in
  let before = codes text in
  List.iter
    (fun (diagnostic : Diagnostic.t) ->
      List.iter
        (fun (fix : Diagnostic.fix) ->
          let rec remove_one = function [] -> [] | code :: rest -> if code = diagnostic.code then rest else code :: remove_one rest in
          let rec contained smaller larger =
            match (smaller, larger) with
            | [], _ -> true
            | _ :: _, [] -> false
            | first :: rest, candidate :: larger_rest ->
                if first = candidate then contained rest larger_rest
                else if first > candidate then contained smaller larger_rest
                else false
          in
          match Diagnostic.apply_fix text fix with
          | exception Invalid_argument _ -> fail "the fix %S has overlapping edits in %s" fix.title (Diagnostic.quote text)
          | fixed ->
              if not (contained (codes fixed) (remove_one before)) then
                fail "the fix %S for %s leaves or adds an error in %s" fix.title
                  (Diagnostic.Code.name diagnostic.code) (Diagnostic.quote text))
        diagnostic.fixes)
    (snd (lex text))

let mistakes =
  [| "\""; "\"\"\""; "$"; "${"; "}"; "{"; "("; ")"; "["; "]"; "\n"; "\r"; "\\"; "'"; "/*"; "//"; "#"; ";"; "0x";
     "1e"; "_"; "\xe2\x80\xae"; "\xe2\x80\x8b"; "\xff"; "\x01"; "===" ; "++"; "@"; "aB"; "A_b" |]

(* Round trips *)

let round_trip random =
  let pick array = array.(Random.State.int random (Array.length array)) in
  let names = [| ("count", Lower "count"); ("user_name", Lower "user_name"); ("Point", Upper "Point"); ("O", Upper "O") |] in
  let others =
    Array.of_list
      (List.map (fun (spelling, keyword) -> (spelling, Keyword keyword)) Token.keywords
      @ List.map (fun (spelling, reserved) -> (spelling, Reserved reserved)) Token.reserved_words
      @ List.filter_map
          (fun (spelling, punctuation) ->
            match punctuation with Open _ | Close _ -> None | _ -> Some (spelling, Punctuation punctuation))
          Token.punctuation)
  in
  let items = List.init (1 + Random.State.int random 30) (fun _ ->
      if Random.State.bool random then pick names
      else if Random.State.int random 4 = 0 then
        let value = Z.of_int (Random.State.bits random) in
        (Z.to_string value, Integer value)
      else pick others)
  in
  let text = String.concat " " (List.map fst items) in
  let tokens, diagnostics = lex text in
  if diagnostics <> [] then fail "diagnostics for valid tokens %s" (Diagnostic.quote text);
  let kinds =
    Array.to_list tokens |> List.map (fun (t : Token.t) -> t.kind) |> List.filter (fun kind -> kind <> Newline && kind <> End_of_file)
  in
  if kinds <> List.map snd items then fail "the tokens of %s do not round-trip" (Diagnostic.quote text)

let () =
  let seed = ref 0 and count = ref 10_000 and files = ref [] in
  Arg.parse
    [ ("--seed", Arg.Set_int seed, " The random seed"); ("--count", Arg.Set_int count, " How many inputs of each kind") ]
    (fun file -> files := file :: !files)
    "fuzz [--seed N] [--count N] FILE...";
  let random = Random.State.make [| !seed |] in
  let examples = Array.of_list (List.concat_map (fun file -> truss_blocks (read file)) !files) in
  if Array.length examples = 0 then (prerr_endline "fuzz: give Markdown files with ```truss blocks"; exit 2);
  let example () = examples.(Random.State.int random (Array.length examples)) in
  let insert text piece =
    let at = Random.State.int random (String.length text + 1) in
    String.sub text 0 at ^ piece ^ String.sub text at (String.length text - at)
  in
  for _ = 1 to !count do
    check_robust (String.init (Random.State.int random 120) (fun _ -> Char.chr (Random.State.int random 256)));
    let several = ref (example ()) in
    for _ = 1 to 1 + Random.State.int random 4 do
      several := insert !several (mistakes.(Random.State.int random (Array.length mistakes)))
    done;
    check_robust !several;
    check_fixes_work (insert (example ()) mistakes.(Random.State.int random (Array.length mistakes)));
    round_trip random
  done;
  if !failures > 0 then begin
    Printf.printf "%d failures\n" !failures;
    exit 1
  end
  else Printf.printf "%d inputs of each kind pass\n" !count
