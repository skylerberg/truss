(* Writes standard/text/unicode_data.truss, the tables of character
   properties, case mappings, normalization, and grapheme cluster boundaries
   that the standard library reads, from the Unicode data files in the
   directory given as the only argument. See regenerate.sh, which downloads those files and checks their
   hashes first. *)

let directory =
  match Sys.argv with
  | [| _; directory |] -> directory
  | _ ->
      prerr_endline "usage: library_tables.exe DIRECTORY";
      exit 2

let records = Ucd.records directory
let code_point = Ucd.code_point

let code_points text =
  List.map code_point (List.filter (fun part -> part <> "") (String.split_on_char ' ' text))

(* The ranges that a file of [range; property] lines gives a property. *)
let property rows name =
  Ucd.merge
    (List.filter_map
       (function
         | range :: property_name :: _ when property_name = name ->
             Some (Ucd.code_point_range range)
         | _ -> None)
       rows)

(* A code point of UnicodeData.txt: its general category, its canonical
   combining class, its decomposition, and its simple uppercase and
   lowercase mappings. A pair of lines named [First] and [Last] stands for
   every code point between them. *)
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
            let code = code_point code_text in
            let field index = List.nth fields index in
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
                  combining = int_of_string (field 3);
                  decomposition = field 5;
                  upper = field 12;
                  lower = field 13;
                }
                :: characters )
        | _ -> (first, characters))
      (None, []) (records "UnicodeData.txt")
  in
  List.sort (fun a b -> compare a.code b.code) characters

let in_categories names =
  Ucd.merge
    (List.filter_map
       (fun character ->
         if List.mem character.category names then Some (character.code, character.code) else None)
       characters)

(* The number that [unicode::category] reads for a general category. *)
let category_number category =
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

(* Runs of consecutive code points with one category number, as
   [first; last; number]. *)
let category_ranges =
  List.fold_left
    (fun runs character ->
      let number = category_number character.category in
      match runs with
      | (first, last, earlier) :: rest when last = character.code - 1 && earlier = number ->
          (first, character.code, number) :: rest
      | _ -> (character.code, character.code, number) :: runs)
    [] characters
  |> List.rev

let simple_mappings mapped =
  List.concat_map
    (fun character ->
      match mapped character with "" -> [] | text -> [ character.code; code_point text ])
    characters

(* A mapping to two or three code points, as [code; first; second; third]
   with 0 for a missing third. *)
let expansion code mapped =
  match mapped with
  | [ first; second ] -> [ code; first; second; 0 ]
  | [ first; second; third ] -> [ code; first; second; third ]
  | _ -> failwith "an expansion has two or three code points"

(* The mappings of SpecialCasing.txt that hold in every context. *)
let special_casing column =
  List.concat_map
    (fun fields ->
      match fields with
      | code_text :: lower :: _title :: upper :: rest
        when List.for_all (fun field -> field = "") rest -> (
          match code_points (if column = `Upper then upper else lower) with
          | [] | [ _ ] -> []
          | mapped -> [ expansion (code_point code_text) mapped ])
      | _ -> [])
    (records "SpecialCasing.txt")
  |> List.sort compare |> List.concat

let case_folding = records "CaseFolding.txt"

let fold_mappings =
  List.concat_map
    (function
      | [ code_text; "C"; mapped; _ ] | [ code_text; "C"; mapped ] ->
          [ code_point code_text; code_point mapped ]
      | _ -> [])
    case_folding

let fold_expansions =
  List.concat_map
    (function
      | code_text :: "F" :: mapped :: _ -> [ expansion (code_point code_text) (code_points mapped) ]
      | _ -> [])
    case_folding
  |> List.sort compare |> List.concat

(* Runs of consecutive code points with one canonical combining class that
   is not 0, as [first; last; class]. *)
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

(* One step of each character's decomposition: the code points its
   decomposition field lists. A field that starts with a tag is a
   compatibility decomposition. *)
let decomposition_steps =
  let steps = Hashtbl.create 8192 in
  List.iter
    (fun character ->
      match
        List.filter (fun part -> part <> "") (String.split_on_char ' ' character.decomposition)
      with
      | [] -> ()
      | tag :: parts when tag.[0] = '<' ->
          Hashtbl.replace steps character.code (`Compatibility, List.map code_point parts)
      | parts -> Hashtbl.replace steps character.code (`Canonical, List.map code_point parts))
    characters;
  steps

(* A code point's decomposition with every part decomposed in turn. The
   canonical decomposition takes canonical steps only. *)
let rec full_decomposition ~compatibility code =
  match Hashtbl.find_opt decomposition_steps code with
  | Some (`Canonical, parts) -> List.concat_map (full_decomposition ~compatibility) parts
  | Some (`Compatibility, parts) when compatibility ->
      List.concat_map (full_decomposition ~compatibility) parts
  | _ -> [ code ]

let canonical_decompositions =
  List.filter_map
    (fun character ->
      match Hashtbl.find_opt decomposition_steps character.code with
      | Some (`Canonical, _) ->
          Some (character.code, full_decomposition ~compatibility:false character.code)
      | _ -> None)
    characters

(* Only the characters whose compatibility decomposition is not their
   canonical one. *)
let compatibility_decompositions =
  List.filter_map
    (fun character ->
      let whole = full_decomposition ~compatibility:true character.code in
      if whole = full_decomposition ~compatibility:false character.code then None
      else Some (character.code, whole))
    characters

(* An index of [code; start; length] rows, and the pool of code points that
   each row's start and length select. *)
let index_and_pool decompositions =
  let index, pool, _ =
    List.fold_left
      (fun (index, pool, start) (code, parts) ->
        let length = List.length parts in
        (List.rev_append [ code; start; length ] index, List.rev_append parts pool, start + length))
      ([], [], 0) decompositions
  in
  (List.rev index, List.rev pool)

(* [first; second; composite] for each character whose canonical
   decomposition is a pair and that composition does not exclude. *)
let composition_pairs excluded =
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

(* [first; last; properties] for each run of code points with the same
   properties that decide grapheme cluster boundaries: the grapheme cluster
   break class, 16 times the Indic conjunct break class, and 64 for
   Extended_Pictographic. The Hangul syllables are left out, because the
   library tells LV from LVT by arithmetic. *)
let grapheme_ranges ~breaks ~core ~emoji =
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
    (fun index name -> add (index + 1) (property breaks name))
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
  let conjunct name =
    List.filter_map
      (function
        | range :: "InCB" :: property_name :: _ when property_name = name ->
            Some (Ucd.code_point_range range)
        | _ -> None)
      core
  in
  List.iteri
    (fun index name -> add (16 * (index + 1)) (conjunct name))
    [ "Consonant"; "Extend"; "Linker" ];
  add 64 (property emoji "Extended_Pictographic");
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

let flat ranges = List.concat_map (fun (first, last) -> [ first; last ]) ranges

let print_table name numbers =
  Printf.printf "internal let %s: Array[UInt32, %d] = [\n" name (List.length numbers);
  let rec rows = function
    | [] -> ()
    | numbers ->
        let row = List.filteri (fun index _ -> index < 12) numbers in
        Printf.printf "  %s,\n" (String.concat ", " (List.map string_of_int row));
        rows (List.filteri (fun index _ -> index >= 12) numbers)
  in
  rows numbers;
  print_string "]\n"

let () =
  let core = records "DerivedCoreProperties.txt" in
  let width = records "EastAsianWidth.txt" in
  let normalization = records "DerivedNormalizationProps.txt" in
  let breaks = records "GraphemeBreakProperty.txt" in
  let emoji = records "emoji-data.txt" in
  let canonical_index, canonical_pool = index_and_pool canonical_decompositions in
  let compatibility_index, compatibility_pool = index_and_pool compatibility_decompositions in
  let tables =
    [
      ("alphabetic_ranges", flat (property core "Alphabetic"));
      ("numeric_ranges", flat (in_categories [ "Nd"; "Nl"; "No" ]));
      ("uppercase_ranges", flat (property core "Uppercase"));
      ("lowercase_ranges", flat (property core "Lowercase"));
      ("cased_ranges", flat (property core "Cased"));
      ("case_ignorable_ranges", flat (property core "Case_Ignorable"));
      ("wide_ranges", flat (Ucd.merge (property width "W" @ property width "F")));
      ("zero_width_ranges", flat (in_categories [ "Mn"; "Me"; "Cf"; "Cc" ]));
      ("uppercase_mappings", simple_mappings (fun character -> character.upper));
      ("lowercase_mappings", simple_mappings (fun character -> character.lower));
      ("fold_mappings", fold_mappings);
      ("uppercase_expansions", special_casing `Upper);
      ("lowercase_expansions", special_casing `Lower);
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
      ("composition_pairs", composition_pairs (property normalization "Full_Composition_Exclusion"));
      ("grapheme_ranges", grapheme_ranges ~breaks ~core ~emoji);
    ]
  in
  List.iteri
    (fun index (name, numbers) ->
      if index > 0 then print_newline ();
      print_table name numbers)
    tables
