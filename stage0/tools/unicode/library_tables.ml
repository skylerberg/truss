let directory =
  match Sys.argv with
  | [| _; directory |] -> directory
  | _ ->
      prerr_endline "usage: library_tables.exe DIRECTORY";
      exit 2

let read_records = Ucd.read_records directory
let parse_code_point = Ucd.parse_code_point

let parse_code_points text =
  List.map parse_code_point (List.filter (fun part -> part <> "") (String.split_on_char ' ' text))

let select_property rows name =
  Ucd.merge
    (List.filter_map
       (function
         | range :: property_name :: _ when property_name = name ->
             Some (Ucd.parse_code_point_range range)
         | _ -> None)
       rows)

type character = {
  code : int;
  category : string;
  combining : int;
  decomposition : string;
  upper : string;
  lower : string;
}

let characters =
  let _, characters =
    List.fold_left
      (fun (first, characters) fields ->
        match fields with
        | code_text :: name :: category :: _ ->
            let code = parse_code_point code_text in
            let read_field index = List.nth fields index in
            if String.ends_with ~suffix:", First>" name then (Some code, characters)
            else if String.ends_with ~suffix:", Last>" name then
              let start = Option.value first ~default:code in
              ( None,
                List.rev_append
                  (List.init
                     (code - start + 1)
                     (fun offset ->
                       {
                         code = start + offset;
                         category;
                         combining = 0;
                         decomposition = "";
                         upper = "";
                         lower = "";
                       }))
                  characters )
            else
              ( None,
                {
                  code;
                  category;
                  combining = int_of_string (read_field 3);
                  decomposition = read_field 5;
                  upper = read_field 12;
                  lower = read_field 13;
                }
                :: characters )
        | _ -> (first, characters))
      (None, []) (read_records "UnicodeData.txt")
  in
  List.sort (fun left right -> compare left.code right.code) characters

let list_in_categories names =
  Ucd.merge
    (List.filter_map
       (fun character ->
         if List.mem character.category names then Some (character.code, character.code) else None)
       characters)

let number_category category =
  match category with
  | "Cc" -> 6
  | "Cf" -> 7
  | "Cs" -> 8
  | "Co" -> 9
  | "Cn" -> 10
  | _ -> (
      match category.[0] with
      | 'L' -> 0
      | 'M' -> 1
      | 'N' -> 2
      | 'P' -> 3
      | 'S' -> 4
      | 'Z' -> 5
      | _ -> failwith ("an unknown category: " ^ category))

let category_ranges =
  List.fold_left
    (fun runs character ->
      let number = number_category character.category in
      match runs with
      | (first, last, earlier) :: rest when last = character.code - 1 && earlier = number ->
          (first, character.code, number) :: rest
      | _ -> (character.code, character.code, number) :: runs)
    [] characters
  |> List.rev

let list_simple_mappings select_mapping =
  List.concat_map
    (fun character ->
      match select_mapping character with
      | "" -> []
      | text -> [ character.code; parse_code_point text ])
    characters

let expand code mapped =
  match mapped with
  | [ first; second ] -> [ code; first; second; 0 ]
  | [ first; second; third ] -> [ code; first; second; third ]
  | _ -> failwith "an expansion has two or three code points"

let list_special_casing column =
  List.concat_map
    (fun fields ->
      match fields with
      | code_text :: lower :: _title :: upper :: rest
        when List.for_all (fun field -> field = "") rest -> (
          match parse_code_points (if column = `Upper then upper else lower) with
          | [] | [ _ ] -> []
          | mapped -> [ expand (parse_code_point code_text) mapped ])
      | _ -> [])
    (read_records "SpecialCasing.txt")
  |> List.sort compare |> List.concat

let case_folding = read_records "CaseFolding.txt"

let fold_mappings =
  List.concat_map
    (function
      | [ code_text; "C"; mapped; _ ] | [ code_text; "C"; mapped ] ->
          [ parse_code_point code_text; parse_code_point mapped ]
      | _ -> [])
    case_folding

let fold_expansions =
  List.concat_map
    (function
      | code_text :: "F" :: mapped :: _ ->
          [ expand (parse_code_point code_text) (parse_code_points mapped) ]
      | _ -> [])
    case_folding
  |> List.sort compare |> List.concat

let combining_class_ranges =
  List.fold_left
    (fun runs character ->
      if character.combining = 0 then runs
      else
        match runs with
        | (first, last, earlier) :: rest
          when last = character.code - 1 && earlier = character.combining ->
            (first, character.code, earlier) :: rest
        | _ -> (character.code, character.code, character.combining) :: runs)
    [] characters
  |> List.rev

let decomposition_steps =
  let steps = Hashtbl.create 8192 in
  List.iter
    (fun character ->
      match
        List.filter (fun part -> part <> "") (String.split_on_char ' ' character.decomposition)
      with
      | [] -> ()
      | tag :: parts when tag.[0] = '<' ->
          Hashtbl.replace steps character.code (`Compatibility, List.map parse_code_point parts)
      | parts -> Hashtbl.replace steps character.code (`Canonical, List.map parse_code_point parts))
    characters;
  steps

let rec decompose_fully ~compatibility code =
  match Hashtbl.find_opt decomposition_steps code with
  | Some (`Canonical, parts) -> List.concat_map (decompose_fully ~compatibility) parts
  | Some (`Compatibility, parts) when compatibility ->
      List.concat_map (decompose_fully ~compatibility) parts
  | _ -> [ code ]

let canonical_decompositions =
  List.filter_map
    (fun character ->
      match Hashtbl.find_opt decomposition_steps character.code with
      | Some (`Canonical, _) ->
          Some (character.code, decompose_fully ~compatibility:false character.code)
      | _ -> None)
    characters

let compatibility_decompositions =
  List.filter_map
    (fun character ->
      let whole = decompose_fully ~compatibility:true character.code in
      if whole = decompose_fully ~compatibility:false character.code then None
      else Some (character.code, whole))
    characters

let pool_decompositions decompositions =
  let index, pool, _ =
    List.fold_left
      (fun (index, pool, start) (code, parts) ->
        let length = List.length parts in
        (List.rev_append [ code; start; length ] index, List.rev_append parts pool, start + length))
      ([], [], 0) decompositions
  in
  (List.rev index, List.rev pool)

let list_composition_pairs excluded =
  let is_excluded code =
    List.exists (fun (first, last) -> first <= code && code <= last) excluded
  in
  List.filter_map
    (fun character ->
      match Hashtbl.find_opt decomposition_steps character.code with
      | Some (`Canonical, [ first; second ]) when not (is_excluded character.code) ->
          Some [ first; second; character.code ]
      | _ -> None)
    characters
  |> List.sort compare |> List.concat

let list_grapheme_ranges ~breaks ~core ~emoji =
  let properties = Hashtbl.create 16384 in
  let add number ranges =
    List.iter
      (fun (first, last) ->
        for code = first to last do
          Hashtbl.replace properties code
            (number lor Option.value ~default:0 (Hashtbl.find_opt properties code))
        done)
      ranges
  in
  List.iteri
    (fun index name -> add (index + 1) (select_property breaks name))
    [
      "CR";
      "LF";
      "Control";
      "Extend";
      "ZWJ";
      "Regional_Indicator";
      "Prepend";
      "SpacingMark";
      "L";
      "V";
      "T";
    ];
  let list_conjunct name =
    List.filter_map
      (function
        | range :: "InCB" :: property_name :: _ when property_name = name ->
            Some (Ucd.parse_code_point_range range)
        | _ -> None)
      core
  in
  List.iteri
    (fun index name -> add (16 * (index + 1)) (list_conjunct name))
    [ "Consonant"; "Extend"; "Linker" ];
  add 64 (select_property emoji "Extended_Pictographic");
  Hashtbl.fold (fun code property_bits all -> (code, property_bits) :: all) properties []
  |> List.sort compare
  |> List.fold_left
       (fun runs (code, property_bits) ->
         match runs with
         | (first, last, earlier) :: rest when last = code - 1 && earlier = property_bits ->
             (first, code, earlier) :: rest
         | _ -> (code, code, property_bits) :: runs)
       []
  |> List.rev
  |> List.concat_map (fun (first, last, property_bits) -> [ first; last; property_bits ])

let flatten ranges = List.concat_map (fun (first, last) -> [ first; last ]) ranges

let print_table name numbers =
  Printf.printf "internal let %s: Array[UInt32, %d] = [\n" name (List.length numbers);
  let rec write_rows = function
    | [] -> ()
    | numbers ->
        let row = List.take 12 numbers in
        Printf.printf "  %s,\n" (String.concat ", " (List.map string_of_int row));
        write_rows (List.drop 12 numbers)
  in
  write_rows numbers;
  print_string "]\n"

let () =
  let core = read_records "DerivedCoreProperties.txt" in
  let width = read_records "EastAsianWidth.txt" in
  let normalization = read_records "DerivedNormalizationProps.txt" in
  let breaks = read_records "GraphemeBreakProperty.txt" in
  let emoji = read_records "emoji-data.txt" in
  let canonical_index, canonical_pool = pool_decompositions canonical_decompositions in
  let compatibility_index, compatibility_pool = pool_decompositions compatibility_decompositions in
  let tables =
    [
      ("alphabetic_ranges", flatten (select_property core "Alphabetic"));
      ("numeric_ranges", flatten (list_in_categories [ "Nd"; "Nl"; "No" ]));
      ("uppercase_ranges", flatten (select_property core "Uppercase"));
      ("lowercase_ranges", flatten (select_property core "Lowercase"));
      ("cased_ranges", flatten (select_property core "Cased"));
      ("case_ignorable_ranges", flatten (select_property core "Case_Ignorable"));
      ("wide_ranges", flatten (Ucd.merge (select_property width "W" @ select_property width "F")));
      ("zero_width_ranges", flatten (list_in_categories [ "Mn"; "Me"; "Cf"; "Cc" ]));
      ("uppercase_mappings", list_simple_mappings (fun character -> character.upper));
      ("lowercase_mappings", list_simple_mappings (fun character -> character.lower));
      ("fold_mappings", fold_mappings);
      ("uppercase_expansions", list_special_casing `Upper);
      ("lowercase_expansions", list_special_casing `Lower);
      ("fold_expansions", fold_expansions);
      ( "category_ranges",
        List.concat_map (fun (first, last, number) -> [ first; last; number ]) category_ranges );
      ( "combining_class_ranges",
        List.concat_map
          (fun (first, last, number) -> [ first; last; number ])
          combining_class_ranges );
      ("canonical_decomposition_index", canonical_index);
      ("canonical_decomposition_pool", canonical_pool);
      ("compatibility_decomposition_index", compatibility_index);
      ("compatibility_decomposition_pool", compatibility_pool);
      ( "composition_pairs",
        list_composition_pairs (select_property normalization "Full_Composition_Exclusion") );
      ("grapheme_ranges", list_grapheme_ranges ~breaks ~core ~emoji);
    ]
  in
  List.iteri
    (fun index (name, numbers) ->
      if index > 0 then print_newline ();
      print_table name numbers)
    tables
