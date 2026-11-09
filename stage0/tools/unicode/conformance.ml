(* Checks the Unicode module against the data files in the directory given as
   the only argument: NFC and NFD against NormalizationTest.txt, and each
   property against the lines of the file its table came from. The property
   checks go through the module's public functions, so they cover the
   generator's merging of ranges and the module's lookups together.
   regenerate.sh runs this after writing new tables. *)

let data_directory = Sys.argv.(1)
let failures = ref 0

let fail format =
  Printf.ksprintf
    (fun message ->
      incr failures;
      if !failures <= 50 then prerr_endline message)
    format

let read_lines name =
  let channel = open_in_bin (Filename.concat data_directory name) in
  let rec loop lines =
    match input_line channel with
    | line -> loop (line :: lines)
    | exception End_of_file ->
        close_in channel;
        List.rev lines
  in
  loop []

let records name =
  read_lines name
  |> List.filter_map (fun line ->
         let line =
           match String.index_opt line '#' with
           | Some index -> String.sub line 0 index
           | None -> line
         in
         if String.trim line = "" then None
         else Some (List.map String.trim (String.split_on_char ';' line)))

let code_point text = int_of_string ("0x" ^ text)

let each_in_range text action =
  match String.index_opt text '.' with
  | Some index ->
      let first = code_point (String.sub text 0 index) in
      let last = code_point (String.sub text (index + 2) (String.length text - index - 2)) in
      for value = first to last do
        action value
      done
  | None -> action (code_point text)

let sequence text =
  String.split_on_char ' ' text
  |> List.filter (fun part -> part <> "")
  |> List.map code_point
  |> Unicode.of_code_points

let is_scalar value = value < 0xD800 || (value > 0xDFFF && value <= 0x10FFFF)

(* Checks that exactly the code points the file lists with [value] have the
   property. *)
let check_property ~file ~name ~listed property =
  let expected = Array.make 0x110000 false in
  List.iter
    (function
      | range :: value :: _ when listed value -> each_in_range range (fun c -> expected.(c) <- true)
      | _ -> ())
    (records file);
  for value = 0 to 0x10FFFF do
    if is_scalar value && property value <> expected.(value) then
      fail "%s: U+%04X: expected %b" name value expected.(value)
  done

let normalization () =
  let tested = Array.make 0x110000 false in
  let in_part_one = ref false in
  List.iter
    (fun line ->
      if String.starts_with ~prefix:"@Part" line then in_part_one := String.starts_with ~prefix:"@Part1" line
      else if line = "" || line.[0] = '#' then ()
      else
        match String.split_on_char ';' line with
        | c1 :: c2 :: c3 :: c4 :: c5 :: _ ->
            let c1, c2, c3, c4, c5 = (sequence c1, sequence c2, sequence c3, sequence c4, sequence c5) in
            let expect form source expected =
              let actual = (if form = "NFC" then Unicode.nfc else Unicode.nfd) source in
              if actual <> expected then fail "%s of %S: expected %S, got %S" form source expected actual
            in
            List.iter (fun source -> expect "NFC" source c2) [ c1; c2; c3 ];
            List.iter (fun source -> expect "NFC" source c4) [ c4; c5 ];
            List.iter (fun source -> expect "NFD" source c3) [ c1; c2; c3 ];
            List.iter (fun source -> expect "NFD" source c5) [ c4; c5 ];
            if !in_part_one then begin
              match Unicode.code_points c1 with [ value ] -> tested.(value) <- true | _ -> ()
            end
        | _ -> fail "NormalizationTest.txt: unexpected line %S" line)
    (read_lines "NormalizationTest.txt");
  (* Every character not listed in Part 1 is unchanged by both forms. *)
  for value = 0 to 0x10FFFF do
    if is_scalar value && not tested.(value) then
      let text = Unicode.of_code_points [ value ] in
      if Unicode.nfc text <> text || Unicode.nfd text <> text then
        fail "U+%04X should be unchanged by normalization" value
  done

let () =
  normalization ();
  let core = "DerivedCoreProperties.txt" in
  check_property ~file:core ~name:"XID_Start" ~listed:(( = ) "XID_Start") Unicode.is_xid_start;
  check_property ~file:core ~name:"XID_Continue" ~listed:(( = ) "XID_Continue")
    Unicode.is_xid_continue;
  check_property ~file:"DerivedGeneralCategory.txt" ~name:"Lu or Lt"
    ~listed:(fun category -> category = "Lu" || category = "Lt")
    Unicode.is_uppercase_or_titlecase;
  check_property ~file:"PropList.txt" ~name:"Bidi_Control" ~listed:(( = ) "Bidi_Control")
    Unicode.is_bidi_control;
  check_property ~file:"DerivedGeneralCategory.txt" ~name:"Cc" ~listed:(( = ) "Cc")
    Unicode.is_control;
  check_property ~file:"IdentifierStatus.txt" ~name:"Identifier_Status=Allowed"
    ~listed:(( = ) "Allowed") Unicode.is_identifier_allowed;
  check_property ~file:"DerivedNormalizationProps.txt" ~name:"NFC_QC"
    ~listed:(fun value -> value = "NFC_QC")
    (fun value -> not (Unicode.is_nfc_quick_check_yes value));
  (* Forbidden: Bidi_Control, Cc other than tab, line feed, and carriage
     return, and Default_Ignorable_Code_Point other than the joiners and the
     variation selectors. *)
  let listed file property =
    let set = Array.make 0x110000 false in
    List.iter
      (function
        | range :: value :: _ when value = property -> each_in_range range (fun c -> set.(c) <- true)
        | _ -> ())
      (records file);
    set
  in
  let ignorable = listed core "Default_Ignorable_Code_Point" in
  let selector = listed "PropList.txt" "Variation_Selector" in
  let bidi = listed "PropList.txt" "Bidi_Control" in
  let control = listed "DerivedGeneralCategory.txt" "Cc" in
  for value = 0 to 0x10FFFF do
    if is_scalar value then begin
      let expected =
        bidi.(value)
        || (control.(value) && value <> 0x09 && value <> 0x0A && value <> 0x0D)
        || (ignorable.(value) && (not selector.(value)) && value <> 0x200C && value <> 0x200D)
      in
      if Unicode.is_forbidden value <> expected then fail "forbidden: U+%04X: expected %b" value expected;
      if expected && control.(value) && Unicode.forbidden_name value = None then
        fail "forbidden control U+%04X has no name" value
    end
  done;
  (* Case mappings. *)
  List.iter
    (function
      | value :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: upper :: lower :: _ ->
          let value = code_point value in
          let expect name actual mapped =
            let expected = if mapped = "" then value else code_point mapped in
            if actual value <> expected then fail "%s of U+%04X" name value
          in
          expect "uppercase" Unicode.to_uppercase upper;
          expect "lowercase" Unicode.to_lowercase lower
      | _ -> ())
    (records "UnicodeData.txt");
  (* Scripts: a character whose Script_Extensions is one script is a
     single-script name on its own. *)
  List.iter
    (function
      | range :: script :: _ ->
          let expected = String.map (function '_' -> ' ' | c -> c) script in
          each_in_range range (fun value ->
              let text = Unicode.of_code_points [ value ] in
              match Unicode.script_names text with
              | [] when script = "Common" || script = "Inherited" -> ()
              | [ name ] when name = expected -> ()
              | _ -> fail "script of U+%04X: expected %s" value expected)
      | _ -> ())
    (records "Scripts.txt");
  (* Confusables: each source's skeleton is the skeleton of its prototype. *)
  List.iter
    (function
      | source :: target :: _ ->
          let source = sequence source and target = sequence target in
          if Unicode.skeleton source <> Unicode.skeleton target then
            fail "skeleton of %S should equal that of %S" source target
      | _ -> ())
    (records "confusables.txt");
  if !failures > 0 then begin
    Printf.eprintf "%d failures\n" !failures;
    exit 1
  end
  else Printf.printf "Unicode %s tables conform to the data files\n" Unicode.version
