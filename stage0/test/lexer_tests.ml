(* The lexer's tests other than the golden files (LEXER.md, "Testing"):

   - the keyword, punctuation, and line-break lists in GRAMMAR.md agree with
     Token and Layout;
   - every ```truss block in the documents lexes with no diagnostics;
   - every fix removes its diagnostic without adding another;
   - random sequences of valid tokens lex back to the same tokens;
   - random bytes and mutated documents never raise, and always give spans
     that are in bounds, in order, and balanced;
   - spot checks of the Unicode module.

   The documents are read from the repository root, two directories up from
   where dune runs the test. *)

open Token

let failures = ref 0

let fail format =
  Printf.ksprintf
    (fun message ->
      incr failures;
      if !failures <= 100 then print_endline ("FAIL: " ^ message))
    format

let check condition format =
  Printf.ksprintf (fun message -> if not condition then fail "%s" message) format

let read path =
  let channel = open_in_bin path in
  let text = really_input_string channel (in_channel_length channel) in
  close_in channel;
  text

let document name = read (Filename.concat "../.." name)
let lex text = Lexer.lex (Source.create ~path:"test.truss" text)
let lines text = String.split_on_char '\n' text

let starts_with ~prefix text = String.starts_with ~prefix text

let contains text part =
  let rec search index =
    index + String.length part <= String.length text
    && (String.sub text index (String.length part) = part || search (index + 1))
  in
  search 0

(* The contents of the first fenced block after the first line containing
   [marker]. *)
let block_after document marker =
  let rec skip_to_marker = function
    | [] -> failwith ("marker not found: " ^ marker)
    | line :: rest ->
        if contains line marker then rest else skip_to_marker rest
  in
  let rec skip_to_fence = function
    | [] -> failwith ("no block after " ^ marker)
    | line :: rest -> if starts_with ~prefix:"```" line then rest else skip_to_fence rest
  in
  let rec take acc = function
    | [] -> List.rev acc
    | line :: rest -> if starts_with ~prefix:"```" line then List.rev acc else take (line :: acc) rest
  in
  take [] (skip_to_fence (skip_to_marker (lines document)))

let words block =
  List.concat_map (String.split_on_char ' ') block |> List.filter (fun word -> word <> "")

(* The text between two markers. *)
let between document first second =
  let index_of text start marker =
    let rec search index =
      if index + String.length marker > String.length text then failwith ("missing " ^ marker)
      else if String.sub text index (String.length marker) = marker then index
      else search (index + 1)
    in
    search start
  in
  let start = index_of document 0 first + String.length first in
  (* Lines wrap anywhere in prose, so runs of whitespace become one space. *)
  String.sub document start (index_of document start second - start)
  |> String.split_on_char '\n'
  |> List.map String.trim
  |> String.concat " "

(* Every `...` in a piece of Markdown. *)
let backticked text =
  let rec loop index acc =
    match String.index_from_opt text index '`' with
    | None -> List.rev acc
    | Some opening -> (
        match String.index_from_opt text (opening + 1) '`' with
        | None -> List.rev acc
        | Some closing ->
            loop (closing + 1) (String.sub text (opening + 1) (closing - opening - 1) :: acc))
  in
  loop 0 []

let sorted list = List.sort_uniq compare list

(* The documents agree with the code *)

let kind_of_spelling spelling =
  match Token.word spelling with
  | Some kind -> Some kind
  | None -> (
      if spelling = "_" then Some Underscore
      else
        match List.assoc_opt spelling Token.punctuation with
        | Some punctuation -> Some (Punctuation punctuation)
        | None -> None)

let test_documents_agree () =
  let grammar = document "GRAMMAR.md" in
  let spellings list = sorted (List.map fst list) in
  check
    (sorted (words (block_after grammar "Reserved everywhere:")) = spellings Token.keywords)
    "GRAMMAR.md's keywords match Token.keywords";
  check
    (sorted (words (block_after grammar "Reserved for later use")) = spellings Token.reserved_words)
    "GRAMMAR.md's reserved words match Token.reserved_words";
  check
    (sorted (words (block_after grammar "### Punctuation")) = spellings Token.punctuation)
    "GRAMMAR.md's punctuation matches Token.punctuation";
  (* The contextual words are names to the lexer. *)
  List.iter
    (fun word ->
      match (fst (lex word)).(0).kind with
      | Upper name | Lower name when name = word -> ()
      | _ -> fail "the contextual word %s lexes as a name" word)
    (words (block_after grammar "The lexer has no contextual keywords"));
  (* Each rejected sequence is an error, or a foreign token for the parser. *)
  List.iter
    (fun sequence ->
      let tokens, diagnostics = lex ("x " ^ sequence ^ " y\n") in
      let foreign = Array.exists (fun token -> match token.kind with Foreign _ -> true | _ -> false) tokens in
      check (diagnostics <> [] || foreign) "the rejected sequence %s is reported" sequence)
    (words (block_after grammar "### Rejected sequences"));
  (* The line-break sets. Names, `_`, and literals are named in prose, and
     the rest are in backticks. *)
  let can_end_text = between grammar "**can end a statement**:" "- the first token after it" in
  let can_begin_text = between grammar "**can begin a statement**:" "3. Several line feeds" in
  let continue_text = between grammar "Every other token continues the line before it:" "So no `NEWLINE`" in
  List.iter
    (fun (text, phrase) -> check (contains text phrase) "GRAMMAR.md says %S" phrase)
    [ (can_end_text, "a name"); (can_end_text, "a number or string literal");
      (can_begin_text, "a name"); (can_begin_text, "a number or string literal");
      (can_begin_text, "a reserved word") ];
  let universe =
    List.map (fun (spelling, keyword) -> (spelling, Keyword keyword)) Token.keywords
    @ List.map (fun (spelling, reserved) -> (spelling, Reserved reserved)) Token.reserved_words
    @ List.map (fun (spelling, punctuation) -> (spelling, Punctuation punctuation)) Token.punctuation
    @ [ ("_", Underscore) ]
  in
  let listed text = List.filter_map kind_of_spelling (backticked text) in
  let can_end_listed = listed can_end_text and can_begin_listed = listed can_begin_text in
  List.iter
    (fun (spelling, kind) ->
      check (Layout.can_end kind = List.mem kind can_end_listed) "can_end %s agrees with GRAMMAR.md" spelling;
      let begins = List.mem kind can_begin_listed || (match kind with Reserved _ -> true | _ -> false) in
      check (Layout.can_begin kind = begins) "can_begin %s agrees with GRAMMAR.md" spelling)
    universe;
  List.iter
    (fun kind ->
      check (Layout.can_end kind && Layout.can_begin kind) "names and literals can end and begin statements")
    [ Upper "Point"; Lower "x"; Integer Z.one; String { tag = None; form = Ordinary; first = { value = ""; span = Source.zero_width 0 }; rest = [||] } ];
  (* That paragraph names `-` only to leave it out. *)
  let continuing =
    List.filter (fun kind -> kind <> Punctuation Minus) (listed continue_text)
  in
  check (contains continue_text "binary operators other than `-`") "GRAMMAR.md leaves `-` out of the continuing tokens";
  List.iter
    (fun kind ->
      check (not (Layout.can_begin kind)) "%s, which GRAMMAR.md says continues a line, cannot begin one"
        (match kind with
        | Keyword keyword -> Token.keyword_spelling keyword
        | Punctuation punctuation -> Token.punctuation_spelling punctuation
        | _ -> "a token"))
    continuing;
  (* Every keyword is in one list or the other. *)
  List.iter
    (fun (spelling, keyword) ->
      check
        (List.mem (Keyword keyword) can_begin_listed || List.mem (Keyword keyword) (listed continue_text))
        "GRAMMAR.md says whether %s begins a statement" spelling)
    Token.keywords

(* The documents as a corpus *)

let truss_blocks name =
  let rec loop inside current blocks = function
    | [] -> List.rev blocks
    | line :: rest ->
        let trimmed = String.trim line in
        if inside then
          if starts_with ~prefix:"```" trimmed then
            loop false [] (String.concat "\n" (List.rev current) :: blocks) rest
          else loop true (line :: current) blocks rest
        else if trimmed = "```truss" then loop true [] blocks rest
        else loop false [] blocks rest
  in
  (* Blocks inside list items are indented; remove the indentation of their
     first line from every line. *)
  let dedent block =
    let block_lines = lines block in
    let indentation =
      match List.find_opt (fun line -> String.trim line <> "") block_lines with
      | Some line ->
          let rec count index = if index < String.length line && line.[index] = ' ' then count (index + 1) else index in
          count 0
      | None -> 0
    in
    String.concat "\n"
      (List.map
         (fun line ->
           if String.length line >= indentation then String.sub line indentation (String.length line - indentation)
           else String.trim line)
         block_lines)
    ^ "\n"
  in
  List.map dedent (loop false [] [] (lines (document name)))

let corpus () =
  List.concat_map
    (fun name -> List.mapi (fun index block -> (Printf.sprintf "%s block %d" name (index + 1), block)) (truss_blocks name))
    [ "SYNTAX.md"; "DESIGN.md"; "GRAMMAR.md" ]

let test_corpus corpus =
  check (List.length corpus > 50) "the documents hold more than 50 truss blocks";
  List.iter
    (fun (name, text) ->
      let source = Source.create ~path:name text in
      let _, diagnostics = Lexer.lex source in
      List.iter (fun diagnostic -> fail "%s:\n%s" name (Diagnostic.render source diagnostic)) diagnostics)
    corpus

(* Fixes work *)

let codes diagnostics = List.sort compare (List.map (fun (d : Diagnostic.t) -> d.code) diagnostics)
let code_names codes = String.concat ", " (List.map Diagnostic.Code.name codes)

(* Whether [smaller] is a sub-multiset of [larger]; both sorted. *)
let rec submultiset smaller larger =
  match (smaller, larger) with
  | [], _ -> true
  | _ :: _, [] -> false
  | first :: rest, candidate :: larger_rest ->
      if first = candidate then submultiset rest larger_rest
      else if first > candidate then submultiset smaller larger_rest
      else false

let rec remove_one code = function
  | [] -> []
  | first :: rest -> if first = code then rest else first :: remove_one code rest

let test_fixes name text =
  let _, diagnostics = lex text in
  List.iter
      (fun (diagnostic : Diagnostic.t) ->
        List.iter
          (fun (fix : Diagnostic.fix) ->
            let fixed = Diagnostic.apply_fix text fix in
            let _, after = lex fixed in
            let allowed = remove_one diagnostic.code (codes diagnostics) in
            if not (submultiset (codes after) allowed) then
              fail "%s: the fix %S for %s leaves or adds %s, in:\n%s\nwhich becomes:\n%s" name fix.title
                (Diagnostic.Code.name diagnostic.code)
                (code_names (codes after))
                (Diagnostic.quote text) (Diagnostic.quote fixed))
          diagnostic.fixes)
      diagnostics

(* The fixes for ordinary mistakes are right as built, so checking them
   removes none. *)
let test_no_fix_dropped name text =
  let source = Source.create ~path:name text in
  let _, unchecked = Lexer.lex ~check_fixes:false source in
  let _, checked = Lexer.lex source in
  List.iter2
    (fun (before : Diagnostic.t) (after : Diagnostic.t) ->
      List.iter
        (fun (fix : Diagnostic.fix) ->
          if not (List.mem fix after.fixes) then
            fail "%s: the fix %S for %s fails its check, in:\n%s" name fix.title (Diagnostic.Code.name before.code)
              (Diagnostic.quote text))
        before.fixes)
    unchecked checked

(* Well-formed output *)

let rec check_tokens name text ~start ~stop (tokens : Token.t array) =
  let text_length = String.length text in
  let length = Array.length tokens in
  check (length > 0 && tokens.(length - 1).kind = End_of_file) "%s: the tokens end with End_of_file" name;
  let stack = ref [] in
  let previous = ref start in
  Array.iter
    (fun (token : Token.t) ->
      check
        (token.span.start >= start && token.span.start <= token.span.stop && token.span.stop <= stop
       && token.span.stop <= text_length)
        "%s: span %d-%d in bounds" name token.span.start token.span.stop;
      check (token.span.start >= !previous) "%s: token at %d in order" name token.span.start;
      previous := token.span.start;
      (match token.kind with
      | Punctuation (Open bracket) -> stack := bracket :: !stack
      | Punctuation (Close bracket) -> (
          match !stack with
          | top :: rest when top = bracket -> stack := rest
          | _ -> fail "%s: unbalanced closer at %d" name token.span.start)
      | String literal ->
          Array.iter
            (fun (interpolation : Token.interpolation) ->
              check_tokens name text ~start:interpolation.span.start ~stop:interpolation.span.stop
                interpolation.tokens)
            (Token.interpolations literal)
      | _ -> ()))
    tokens;
  check (!stack = []) "%s: brackets balanced" name

let check_output name text =
  match lex text with
  | exception exception_ -> fail "%s: raised %s" name (Printexc.to_string exception_)
  | tokens, diagnostics ->
      let length = String.length text in
      check_tokens name text ~start:0 ~stop:length tokens;
      List.iter
        (fun (diagnostic : Diagnostic.t) ->
          check
            (diagnostic.span.start >= 0 && diagnostic.span.start <= diagnostic.span.stop
           && diagnostic.span.stop <= length)
            "%s: diagnostic span in bounds" name;
          List.iter
            (fun (fix : Diagnostic.fix) ->
              match Diagnostic.apply_fix text fix with
              | _ -> ()
              | exception exception_ -> fail "%s: fix raised %s" name (Printexc.to_string exception_))
            diagnostic.fixes)
        diagnostics;
      check (List.length (Diagnostic.shown diagnostics) <= Diagnostic.limit + 1) "%s: diagnostics shown are capped" name

(* TRUSS_TEST_SEED picks other random inputs, for longer fuzzing runs. *)
let seed default =
  match Sys.getenv_opt "TRUSS_TEST_SEED" with
  | Some value -> [| default; int_of_string value |]
  | None -> [| default |]

let test_robustness corpus =
  let random = Random.State.make (seed 2026) in
  let pick list = List.nth list (Random.State.int random (List.length list)) in
  (* Bytes that matter to the lexer, and some that do not. *)
  let interesting =
    [ "\""; "\"\"\""; "$"; "${"; "}"; "{"; "("; ")"; "["; "]"; "\n"; "\r"; "\r\n"; "\\"; "'"; "/*"; "*/";
      "//"; "#"; ";"; "0x"; "1e"; "_"; "\xe2\x80\xae"; "\xe2\x80\x8b"; "\xff"; "\xc3"; "\xe2\x80\x8d";
      "\xd0\xb0"; "fn"; "\t"; " "; "\"\"\"\n"; "$$\"\"\"" ]
  in
  for iteration = 1 to 10_000 do
    let length = Random.State.int random 120 in
    let text =
      String.init length (fun _ ->
          if Random.State.bool random then Char.chr (Random.State.int random 256)
          else "\"${}()[]{}\n\\$ \t'_a0x.e"
               .[Random.State.int random 22])
    in
    check_output (Printf.sprintf "random bytes %d" iteration) text
  done;
  let corpus = Array.of_list corpus in
  for iteration = 1 to 20_000 do
    let _, original = corpus.(Random.State.int random (Array.length corpus)) in
    let buffer = Buffer.create (String.length original + 16) in
    let position = ref 0 in
    let mutations = 1 + Random.State.int random 4 in
    let cuts = List.sort compare (List.init mutations (fun _ -> Random.State.int random (String.length original + 1))) in
    List.iter
      (fun cut ->
        let cut = max cut !position in
        Buffer.add_substring buffer original !position (cut - !position);
        (match Random.State.int random 3 with
        | 0 -> Buffer.add_string buffer (pick interesting)
        | 1 -> Buffer.add_char buffer (Char.chr (Random.State.int random 256))
        | _ -> ());
        position := min (String.length original) (cut + Random.State.int random 3))
      cuts;
    if !position < String.length original then
      Buffer.add_substring buffer original !position (String.length original - !position);
    let text = Buffer.contents buffer in
    let name = Printf.sprintf "mutation %d" iteration in
    check_output name text;
    if iteration mod 5 = 0 then test_fixes name text
  done;
  (* A binary file gives a short report. *)
  let binary = String.init 100_000 (fun index -> Char.chr ((index * 7919) land 0xFF)) in
  check (List.length (Diagnostic.shown (snd (lex binary))) <= Diagnostic.limit + 1) "a binary file gives at most %d diagnostics" (Diagnostic.limit + 1)

(* Round trips *)

let test_round_trips () =
  let random = Random.State.make (seed 18) in
  let pick array = array.(Random.State.int random (Array.length array)) in
  let names =
    [| ("count", Lower "count"); ("user_name", Lower "user_name"); ("x1", Lower "x1");
       ("Point", Upper "Point"); ("UInt8", Upper "UInt8"); ("O", Upper "O");
       ("_", Underscore) |]
  in
  let non_brackets =
    Array.of_list
      (List.filter
         (fun (_, punctuation) -> match punctuation with Open _ | Close _ -> false | _ -> true)
         Token.punctuation)
  in
  let integer () =
    let value = Z.of_int64 (Random.State.int64 random Int64.max_int) in
    let value = if Random.State.bool random then Z.mul value (Z.pow (Z.of_int 10) 20) else value in
    let spelling =
      match Random.State.int random 4 with
      | 0 -> Z.to_string value
      | 1 -> "0x" ^ Z.format "%x" value
      | 2 -> "0b" ^ Z.format "%b" value
      | _ -> "0o" ^ Z.format "%o" value
    in
    (spelling, Integer value)
  in
  let float () =
    let whole = Random.State.int random 1000 in
    let fraction = Random.State.int random 1000 in
    let exponent = Random.State.int random 40 - 20 in
    let spelling = Printf.sprintf "%d.%03de%d" whole fraction exponent in
    let significand = Z.of_int ((whole * 1000) + fraction) in
    let rec normalize significand exponent =
      if Z.equal significand Z.zero then (Z.zero, Z.zero)
      else if Z.equal (Z.rem significand (Z.of_int 10)) Z.zero then
        normalize (Z.div significand (Z.of_int 10)) (Z.succ exponent)
      else (significand, exponent)
    in
    let significand, exponent = normalize significand (Z.of_int (exponent - 3)) in
    (spelling, `Float (significand, exponent))
  in
  let string () =
    let pieces = [| ("a", "a"); ("\\n", "\n"); ("\\\"", "\""); ("\\\\", "\\"); ("$", "$"); ("}", "}");
                    ("\\${", "${"); ("\\u{1F600}", "\xf0\x9f\x98\x80"); ("\xc3\xa9", "\xc3\xa9"); (" ", " ") |] in
    let count = Random.State.int random 6 in
    let parts = List.init count (fun _ -> pick pieces) in
    let spelling = "\"" ^ String.concat "" (List.map fst parts) ^ "\"" in
    let value = String.concat "" (List.map snd parts) in
    let raw = Random.State.int random 3 = 0 && value <> "" && not (String.contains value '"') in
    if raw && not (String.contains value '\n' || String.contains value '\\' || String.contains value '$') then
      ("\"\"\"" ^ value ^ "\"\"\"", value, true)
    else (spelling, value, false)
  in
  let describe_expected = function
    | `Kind kind -> (match kind with Integer v -> "Integer " ^ Z.to_string v | _ -> "token")
    | `String value -> Printf.sprintf "String %S" value
    | `Float (significand, exponent) -> Printf.sprintf "Float %se%s" (Z.to_string significand) (Z.to_string exponent)
  in
  for iteration = 1 to 2000 do
    let spellings = ref [] and expected = ref [] in
    let add spelling item =
      spellings := spelling :: !spellings;
      expected := item :: !expected
    in
    let rec items depth count =
      for _ = 1 to count do
        match Random.State.int random 9 with
        | 0 -> let spelling, kind = pick names in add spelling (`Kind kind)
        | 1 -> let spelling, keyword = pick (Array.of_list Token.keywords) in add spelling (`Kind (Keyword keyword))
        | 2 -> let spelling, reserved = pick (Array.of_list Token.reserved_words) in add spelling (`Kind (Reserved reserved))
        | 3 -> let spelling, punctuation = pick non_brackets in add spelling (`Kind (Punctuation punctuation))
        | 4 -> let spelling, kind = integer () in add spelling (`Kind kind)
        | 5 -> let spelling, value = float () in add spelling value
        | 6 -> let spelling, value, _ = string () in add spelling (`String value)
        | _ when depth < 4 ->
            let opener, closer =
              let bracket = pick [| Paren; Square; Curly |] in
              (Open bracket, Close bracket)
            in
            add (Token.punctuation_spelling opener) (`Kind (Punctuation opener));
            items (depth + 1) (Random.State.int random 4);
            add (Token.punctuation_spelling closer) (`Kind (Punctuation closer))
        | _ -> ()
      done
    in
    items 0 (1 + Random.State.int random 20);
    let text = String.concat " " (List.rev !spellings) in
    let tokens, diagnostics = lex text in
    check (diagnostics = []) "round trip %d: %S lexes without diagnostics" iteration text;
    let actual =
      Array.to_list tokens
      |> List.filter (fun (token : Token.t) -> match token.kind with Newline | End_of_file -> false | _ -> true)
    in
    let expected = List.rev !expected in
    if List.length actual <> List.length expected then
      fail "round trip %d: %S gives %d tokens, expected %d" iteration text (List.length actual) (List.length expected)
    else
      List.iter2
        (fun (token : Token.t) item ->
          let matches =
            match (item, token.kind) with
            | `String value, String { first; rest = [||]; _ } -> first.value = value
            | `Kind (Integer expected), Integer actual -> Z.equal expected actual
            | `Float (significand, exponent), Float actual ->
                Z.equal significand actual.significand && Z.equal exponent actual.exponent
            | `Kind kind, actual -> kind = actual
            | _ -> false
          in
          check matches "round trip %d: %S: expected %s" iteration text (describe_expected item))
        actual expected
  done

(* Unicode spot checks *)

let test_unicode () =
  check (Unicode.version = "18.0.0") "the pinned Unicode version";
  (* Names are ASCII: a word with a letter outside ASCII is one name, with
     one error. *)
  List.iter
    (fun word ->
      let tokens, diagnostics = lex ("let " ^ word ^ " = 1\n") in
      check
        (List.map (fun (d : Diagnostic.t) -> d.code) diagnostics = [ Diagnostic.Code.Name_not_ascii ]
        && Array.length tokens = 6)
        "%S is one name with one error" word)
    [ "caf\xc3\xa9"; "\xe5\x90\x8d\xe5\x89\x8d"; "p\xd0\xb0ypal"; "\xc3\x84rger" ];
  check (Unicode.is_forbidden 0x202E && Unicode.is_forbidden 0x200B && Unicode.is_forbidden 0xE0041)
    "Bidi controls, zero-width space, and tags are forbidden";
  check (not (Unicode.is_forbidden 0x200D || Unicode.is_forbidden 0xFE0F || Unicode.is_forbidden 0x09))
    "joiners, variation selectors, and tab are allowed";
  check (Unicode.forbidden_name 0x202E = Some "RIGHT-TO-LEFT OVERRIDE") "names of forbidden characters";
  check (Unicode.decode "\xc0\xaf" 0 < 0 && Unicode.decode "\xed\xa0\x80" 0 < 0 && Unicode.decode "\xf4\x90\x80\x80" 0 < 0)
    "overlong forms, surrogates, and values above U+10FFFF are invalid UTF-8"

let () =
  let corpus = corpus () in
  test_unicode ();
  test_documents_agree ();
  test_corpus corpus;
  List.iter (fun (name, text) -> test_fixes name text) corpus;
  Array.iter
    (fun file ->
      if Filename.check_suffix file ".truss" then
        let text = read (Filename.concat "golden" file) in
        test_fixes file text;
        test_no_fix_dropped file text)
    (Sys.readdir "golden");
  test_round_trips ();
  test_robustness corpus;
  if !failures > 0 then begin
    Printf.printf "%d failures\n" !failures;
    exit 1
  end
  else
    Printf.printf
      "%d document blocks lex cleanly; fixes, 2000 round trips, and 30000 random inputs pass\n"
      (List.length corpus)
